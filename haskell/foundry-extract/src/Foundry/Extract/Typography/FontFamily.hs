{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                       // foundry // extract // typography/fontfamily
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Typography.FontFamily
Description : Font family parsing and analysis
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Parses CSS font-family declarations and identifies primary fonts.

== Design Notes

Font stacks are parsed into a primary font name and fallbacks. Generic
families (serif, sans-serif, monospace) are recognized and handled
specially.

== Dependencies

Requires: attoparsec, text
Required by: Foundry.Extract.Typography

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Typography.FontFamily
  ( -- * Types
    FontStack (..)
  , GenericFamily (..)

    -- * Parsing
  , parseFontFamily
  , parseFontStack

    -- * Analysis
  , isSystemFont
  , isWebFont
  , genericFamilyName
  ) where

import Data.Attoparsec.Text
  ( Parser
  , char
  , many1
  , option
  , parseOnly
  , satisfy
  , sepBy1
  , skipSpace
  , takeWhile1
  )
import Data.Char (isAlphaNum, isSpace)
import Data.Text (Text)
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | A parsed font stack
data FontStack = FontStack
  { fsPrimary   :: !Text
    -- ^ Primary font name
  , fsFallbacks :: ![Text]
    -- ^ Fallback fonts in order
  , fsGeneric   :: !(Maybe GenericFamily)
    -- ^ Generic family (last in stack)
  }
  deriving stock (Eq, Show)

-- | CSS generic font families
data GenericFamily
  = Serif
  | SansSerif
  | Monospace
  | Cursive
  | Fantasy
  | SystemUI
  | UISerif
  | UISansSerif
  | UIMonospace
  | UIRounded
  | Emoji
  | Math
  | Fangsong
  deriving stock (Eq, Ord, Show, Enum, Bounded)

--------------------------------------------------------------------------------
-- Parsing
--------------------------------------------------------------------------------

-- | Parse a font-family CSS value into a FontStack
parseFontFamily :: Text -> Maybe FontStack
parseFontFamily t = case parseOnly fontStackParser (T.strip t) of
  Left _  -> Nothing
  Right s -> Just s

-- | Attoparsec parser for font stacks
parseFontStack :: Parser FontStack
parseFontStack = fontStackParser

fontStackParser :: Parser FontStack
fontStackParser = do
  fonts <- fontNameParser `sepBy1` (skipSpace >> char ',' >> skipSpace)
  let (families, mGeneric) = splitGeneric fonts
  case families of
    []     -> fail "No font families found"
    (p:fs) -> pure $ FontStack p fs mGeneric

-- | Parse a single font name (quoted or unquoted)
fontNameParser :: Parser Text
fontNameParser = quotedFont <|> unquotedFont

quotedFont :: Parser Text
quotedFont = do
  q <- satisfy (\c -> c == '"' || c == '\'')
  name <- takeWhile1 (/= q)
  _ <- char q
  pure name

unquotedFont :: Parser Text
unquotedFont = do
  parts <- many1 fontWord
  pure $ T.intercalate " " parts
  where
    fontWord = do
      skipSpace
      w <- takeWhile1 (\c -> isAlphaNum c || c == '-' || c == '_')
      pure w

-- | Attoparsec choice combinator
(<|>) :: Parser a -> Parser a -> Parser a
p1 <|> p2 = option Nothing (Just <$> p1) >>= \case
  Just x  -> pure x
  Nothing -> p2

-- | Split font list into named fonts and generic family
splitGeneric :: [Text] -> ([Text], Maybe GenericFamily)
splitGeneric [] = ([], Nothing)
splitGeneric fonts =
  let lastFont = T.toLower $ T.strip $ Prelude.last fonts
      mGeneric = textToGeneric lastFont
  in case mGeneric of
       Just g  -> (Prelude.init fonts, Just g)
       Nothing -> (fonts, Nothing)

-- | Convert text to generic family
textToGeneric :: Text -> Maybe GenericFamily
textToGeneric t = case t of
  "serif"         -> Just Serif
  "sans-serif"    -> Just SansSerif
  "monospace"     -> Just Monospace
  "cursive"       -> Just Cursive
  "fantasy"       -> Just Fantasy
  "system-ui"     -> Just SystemUI
  "ui-serif"      -> Just UISerif
  "ui-sans-serif" -> Just UISansSerif
  "ui-monospace"  -> Just UIMonospace
  "ui-rounded"    -> Just UIRounded
  "emoji"         -> Just Emoji
  "math"          -> Just Math
  "fangsong"      -> Just Fangsong
  _               -> Nothing

--------------------------------------------------------------------------------
-- Analysis
--------------------------------------------------------------------------------

-- | Check if font is a system font
isSystemFont :: Text -> Bool
isSystemFont t =
  let lower = T.toLower t
  in lower `elem` systemFonts

systemFonts :: [Text]
systemFonts =
  [ "system-ui"
  , "-apple-system"
  , "blinkmacsystemfont"
  , "segoe ui"
  , "roboto"
  , "helvetica"
  , "arial"
  , "sans-serif"
  , "serif"
  , "monospace"
  , "ui-serif"
  , "ui-sans-serif"
  , "ui-monospace"
  ]

-- | Check if font is likely a custom web font
isWebFont :: Text -> Bool
isWebFont t = not (isSystemFont t) && not (isGenericName t)

isGenericName :: Text -> Bool
isGenericName t = case textToGeneric (T.toLower t) of
  Just _  -> True
  Nothing -> False

-- | Get the display name for a generic family
genericFamilyName :: GenericFamily -> Text
genericFamilyName = \case
  Serif       -> "serif"
  SansSerif   -> "sans-serif"
  Monospace   -> "monospace"
  Cursive     -> "cursive"
  Fantasy     -> "fantasy"
  SystemUI    -> "system-ui"
  UISerif     -> "ui-serif"
  UISansSerif -> "ui-sans-serif"
  UIMonospace -> "ui-monospace"
  UIRounded   -> "ui-rounded"
  Emoji       -> "emoji"
  Math        -> "math"
  Fangsong    -> "fangsong"
