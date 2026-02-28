{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // foundry // gpu // renderer
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.GPU.Renderer
Description : Visual element to GPU command renderer
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Converts visual elements from website extraction into GPU commands
that can be rendered via WebGPU/Hydrogen.

== Rendering Pipeline

1. Parse visual elements with styles
2. Convert CSS colors to GPU Color4
3. Convert bounding boxes to DrawRect commands
4. Sort by z-index for proper layering
5. Emit command buffer

== Dependencies

Requires: Foundry.Core.GPU.Command
Required by: Hydrogen WebGPU interpreter

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.GPU.Renderer
  ( -- * Rendering
    RenderResult (..)
  , RenderOptions (..)
  , defaultRenderOptions
  , renderElements
  
    -- * Color Parsing
  , parseColor
  , parseCSSColor
  
    -- * Bounding Box Conversion
  , boundingBoxToRect
  ) where

import Data.Char (isDigit, isHexDigit, toLower)
import Data.List (sortOn)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word32)
import Foundry.Core.GPU.Command
  ( Color4 (..)
  , CommandBuffer
  , DrawCommand (..)
  , DrawRect (..)
  , addCommand
  , addCommands
  , emptyBuffer
  )

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Options for rendering
data RenderOptions = RenderOptions
  { roViewportWidth  :: !Float
    -- ^ Viewport width
  , roViewportHeight :: !Float
    -- ^ Viewport height
  , roScale          :: !Float
    -- ^ Scale factor (1.0 = 100%)
  , roBackgroundColor :: !Color4
    -- ^ Default background color
  , roDebugOutlines  :: !Bool
    -- ^ Draw debug outlines around elements
  }
  deriving stock (Eq, Show)

-- | Default render options
defaultRenderOptions :: RenderOptions
defaultRenderOptions = RenderOptions
  { roViewportWidth = 1920
  , roViewportHeight = 1080
  , roScale = 1.0
  , roBackgroundColor = Color4 1 1 1 1  -- White
  , roDebugOutlines = False
  }

-- | Result of rendering
data RenderResult = RenderResult
  { rrCommandBuffer :: !CommandBuffer
    -- ^ GPU command buffer
  , rrElementCount  :: !Int
    -- ^ Number of elements rendered
  , rrCommandCount  :: !Int
    -- ^ Number of commands generated
  }
  deriving stock (Eq, Show)

-- | A simplified visual element for rendering
-- This mirrors the structure from Extract.Types.Visual
data RenderElement = RenderElement
  { reX          :: !Float
  , reY          :: !Float
  , reWidth      :: !Float
  , reHeight     :: !Float
  , reZIndex     :: !Int
  , reFillColor  :: !(Maybe Color4)
  , reBorderRadius :: !Float
  , rePickId     :: !Word32
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- Main Rendering Function
--------------------------------------------------------------------------------

-- | Render a list of element data to GPU commands.
--
-- Takes a list of tuples: (x, y, width, height, zIndex, backgroundColor, borderRadius, pickId)
renderElements 
  :: RenderOptions 
  -> [(Float, Float, Float, Float, Int, Maybe Text, Maybe Text, Word32)]
  -> RenderResult
renderElements opts elements = RenderResult
  { rrCommandBuffer = buffer
  , rrElementCount = length renderElems
  , rrCommandCount = length commands
  }
  where
    -- Convert to RenderElements
    renderElems :: [RenderElement]
    renderElems = mapMaybe toRenderElement elements

    toRenderElement :: (Float, Float, Float, Float, Int, Maybe Text, Maybe Text, Word32) 
                    -> Maybe RenderElement
    toRenderElement (x, y, w, h, z, mBgColor, mBorderRadius, pickId) = 
      Just RenderElement
        { reX = x * roScale opts
        , reY = y * roScale opts
        , reWidth = w * roScale opts
        , reHeight = h * roScale opts
        , reZIndex = z
        , reFillColor = mBgColor >>= parseCSSColor
        , reBorderRadius = maybe 0 parseBorderRadius mBorderRadius
        , rePickId = pickId
        }

    -- Sort by z-index (back to front)
    sorted :: [RenderElement]
    sorted = sortOn reZIndex renderElems

    -- Generate commands
    commands :: [DrawCommand]
    commands = map renderElementToCommand sorted

    -- Build command buffer
    buffer :: CommandBuffer
    buffer = addCommands commands emptyBuffer

-- | Convert a RenderElement to a DrawCommand
renderElementToCommand :: RenderElement -> DrawCommand
renderElementToCommand RenderElement{..} = DCRect DrawRect
  { drX = reX
  , drY = reY
  , drWidth = reWidth
  , drHeight = reHeight
  , drRadiusTL = reBorderRadius
  , drRadiusTR = reBorderRadius
  , drRadiusBR = reBorderRadius
  , drRadiusBL = reBorderRadius
  , drFill = fillColor
  , drPickId = rePickId
  }
  where
    fillColor = case reFillColor of
      Just c  -> c
      Nothing -> Color4 0 0 0 0  -- Transparent

--------------------------------------------------------------------------------
-- Color Parsing
--------------------------------------------------------------------------------

-- | Parse a CSS color string to Color4
parseCSSColor :: Text -> Maybe Color4
parseCSSColor = parseColor . T.unpack

-- | Parse a color string to Color4
parseColor :: String -> Maybe Color4
parseColor s = case map toLower (filter (/= ' ') s) of
  -- Hex colors
  '#':rest -> parseHex rest
  
  -- RGB/RGBA
  'r':'g':'b':'(':rest -> parseRGB rest
  'r':'g':'b':'a':'(':rest -> parseRGBA rest
  
  -- Named colors
  "transparent" -> Just (Color4 0 0 0 0)
  "white" -> Just (Color4 1 1 1 1)
  "black" -> Just (Color4 0 0 0 1)
  "red" -> Just (Color4 1 0 0 1)
  "green" -> Just (Color4 0 0.5 0 1)  -- CSS green is #008000
  "blue" -> Just (Color4 0 0 1 1)
  "purple" -> Just (Color4 0.5 0 0.5 1)
  
  -- Unknown
  _ -> Nothing

-- | Parse hex color (#RGB, #RRGGBB, #RRGGBBAA)
parseHex :: String -> Maybe Color4
parseHex s
  | length s == 3 = parseHex3 s
  | length s == 6 = parseHex6 s
  | length s == 8 = parseHex8 s
  | otherwise = Nothing
  where
    parseHex3 [r, g, b] = Just $ Color4
      (fromIntegral (hexDigit r * 17) / 255)
      (fromIntegral (hexDigit g * 17) / 255)
      (fromIntegral (hexDigit b * 17) / 255)
      1
    parseHex3 _ = Nothing

    parseHex6 [r1, r2, g1, g2, b1, b2] = Just $ Color4
      (fromIntegral (hexDigit r1 * 16 + hexDigit r2) / 255)
      (fromIntegral (hexDigit g1 * 16 + hexDigit g2) / 255)
      (fromIntegral (hexDigit b1 * 16 + hexDigit b2) / 255)
      1
    parseHex6 _ = Nothing

    parseHex8 [r1, r2, g1, g2, b1, b2, a1, a2] = Just $ Color4
      (fromIntegral (hexDigit r1 * 16 + hexDigit r2) / 255)
      (fromIntegral (hexDigit g1 * 16 + hexDigit g2) / 255)
      (fromIntegral (hexDigit b1 * 16 + hexDigit b2) / 255)
      (fromIntegral (hexDigit a1 * 16 + hexDigit a2) / 255)
    parseHex8 _ = Nothing

    hexDigit :: Char -> Int
    hexDigit c
      | c >= '0' && c <= '9' = fromEnum c - fromEnum '0'
      | c >= 'a' && c <= 'f' = fromEnum c - fromEnum 'a' + 10
      | c >= 'A' && c <= 'F' = fromEnum c - fromEnum 'A' + 10
      | otherwise = 0

-- | Parse rgb(r, g, b) color
parseRGB :: String -> Maybe Color4
parseRGB s = case parseNumbers (takeWhile (/= ')') s) of
  [r, g, b] -> Just $ Color4 (r / 255) (g / 255) (b / 255) 1
  _ -> Nothing

-- | Parse rgba(r, g, b, a) color
parseRGBA :: String -> Maybe Color4
parseRGBA s = case parseNumbers (takeWhile (/= ')') s) of
  [r, g, b, a] -> Just $ Color4 (r / 255) (g / 255) (b / 255) a
  _ -> Nothing

-- | Parse comma-separated numbers
parseNumbers :: String -> [Float]
parseNumbers s = mapMaybe parseNumber (splitOn ',' s)
  where
    splitOn :: Char -> String -> [String]
    splitOn c = foldr f [[]]
      where
        f x (y:ys)
          | x == c = [] : y : ys
          | otherwise = (x:y) : ys
        f _ [] = []

    parseNumber :: String -> Maybe Float
    parseNumber str = case reads (filter (\c -> isDigit c || c == '.' || c == '-') str) of
      [(n, _)] -> Just n
      _ -> Nothing

--------------------------------------------------------------------------------
-- Border Radius Parsing
--------------------------------------------------------------------------------

-- | Parse CSS border-radius value
parseBorderRadius :: Text -> Float
parseBorderRadius t = case reads (T.unpack (T.filter (\c -> isDigit c || c == '.') t)) of
  [(n, _)] -> n
  _ -> 0

--------------------------------------------------------------------------------
-- Bounding Box Conversion
--------------------------------------------------------------------------------

-- | Convert a bounding box to a DrawRect (helper for external use)
boundingBoxToRect 
  :: Float  -- ^ X
  -> Float  -- ^ Y
  -> Float  -- ^ Width
  -> Float  -- ^ Height
  -> Color4 -- ^ Fill color
  -> Word32 -- ^ Pick ID
  -> DrawRect
boundingBoxToRect x y w h fill pickId = DrawRect
  { drX = x
  , drY = y
  , drWidth = w
  , drHeight = h
  , drRadiusTL = 0
  , drRadiusTR = 0
  , drRadiusBR = 0
  , drRadiusBL = 0
  , drFill = fill
  , drPickId = pickId
  }
