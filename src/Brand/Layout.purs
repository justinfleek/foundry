-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Layout Layer: Grid systems, margins, safe zones,
-- | and print/digital specifications.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Grid systems and layout rules govern how content is composed across
-- | different formats. These ensure visual consistency and proper hierarchy.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Content zones map palette colors to regions
-- |   M - Memorable: Consistent grid creates recognizable structure
-- |   A - Agile: Separate specs for print vs digital
-- |   R - Responsive: Safe zones ensure logo/text legibility
-- |   T - Targeted: Platform-appropriate ratios
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Layout
  ( -- * Grid System
    GridSystem
  , mkGridSystem
  , gridColumns
  , gridGutter
  , gridMargins
  
  -- * Page Margins
  , PageMargins
  , mkPageMargins
  , marginTop
  , marginBottom
  , marginLeft
  , marginRight
  
  -- * Content Zone
  , ContentZone
      ( HeaderZone
      , BodyZone
      , FooterZone
      , SidebarZone
      , HeroZone
      )
  , contentZoneToString
  , parseContentZone
  
  , ZoneColorMapping
  , mkZoneColorMapping
  , zoneType
  , zonePrimaryColor
  , zoneSecondaryColor
  
  -- * Logo Placement
  , LogoPlacement
  , mkLogoPlacement
  , placementLockup
  , placementZone
  , placementAlignment
  
  -- * Print Layout (Portrait)
  , PrintLayoutSpec
  , mkPrintLayoutSpec
  , printGrid
  , printMargins
  , printFirstPageLogo
  , printSubsequentLogo
  , printContentZones
  
  -- * Digital Resolution
  , DigitalResolution
  , mkDigitalResolution
  , resolutionWidth
  , resolutionHeight
  , resolutionName
  
  -- * Safe Zone
  , SafeZone
  , mkSafeZone
  , safeZonePercentage
  , safeZoneDescription
  
  -- * Digital Layout
  , DigitalLayoutSpec
  , mkDigitalLayoutSpec
  , digitalMinResolution
  , digitalVerticalGrid
  , digitalHorizontalGrid
  , digitalSafeZone
  , digitalContentZones
  
  -- * Complete Layout Specification
  , LayoutSpecification
  , mkLayoutSpecification
  , layoutPrint
  , layoutDigital
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (>)
  , (&&)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // grid system
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grid system definition.
type GridSystem =
  { columns :: Int        -- Number of columns (e.g., 8, 12, 16)
  , gutter :: Number      -- Gutter width (relative units or px)
  , margins :: Number     -- Outer margins
  }

-- | Create grid system.
mkGridSystem :: Int -> Number -> Number -> Maybe GridSystem
mkGridSystem cols gutter margins =
  if cols >= 1 && gutter >= 0.0 && margins >= 0.0
    then Just { columns: cols, gutter: gutter, margins: margins }
    else Nothing

-- | Get column count.
gridColumns :: GridSystem -> Int
gridColumns gs = gs.columns

-- | Get gutter width.
gridGutter :: GridSystem -> Number
gridGutter gs = gs.gutter

-- | Get margin size.
gridMargins :: GridSystem -> Number
gridMargins gs = gs.margins

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // page margins
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page margin specification (in inches or relative units).
type PageMargins =
  { top :: Number
  , bottom :: Number
  , left :: Number
  , right :: Number
  }

-- | Create page margins.
mkPageMargins :: Number -> Number -> Number -> Number -> Maybe PageMargins
mkPageMargins t b l r =
  if t >= 0.0 && b >= 0.0 && l >= 0.0 && r >= 0.0
    then Just { top: t, bottom: b, left: l, right: r }
    else Nothing

-- | Get top margin.
marginTop :: PageMargins -> Number
marginTop pm = pm.top

-- | Get bottom margin.
marginBottom :: PageMargins -> Number
marginBottom pm = pm.bottom

-- | Get left margin.
marginLeft :: PageMargins -> Number
marginLeft pm = pm.left

-- | Get right margin.
marginRight :: PageMargins -> Number
marginRight pm = pm.right

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // content zone
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of content zone.
data ContentZone
  = HeaderZone    -- Top area for logo/navigation
  | BodyZone      -- Main content area
  | FooterZone    -- Bottom area for contact/legal
  | SidebarZone   -- Side navigation/info
  | HeroZone      -- Hero/feature area

derive instance eqContentZone :: Eq ContentZone

instance ordContentZone :: Ord ContentZone where
  compare z1 z2 = compare (zoneToInt z1) (zoneToInt z2)
    where
      zoneToInt :: ContentZone -> Int
      zoneToInt HeaderZone = 0
      zoneToInt BodyZone = 1
      zoneToInt FooterZone = 2
      zoneToInt SidebarZone = 3
      zoneToInt HeroZone = 4

instance showContentZone :: Show ContentZone where
  show = contentZoneToString

-- | Convert content zone to string.
contentZoneToString :: ContentZone -> String
contentZoneToString HeaderZone = "header"
contentZoneToString BodyZone = "body"
contentZoneToString FooterZone = "footer"
contentZoneToString SidebarZone = "sidebar"
contentZoneToString HeroZone = "hero"

-- | Parse content zone from string.
parseContentZone :: String -> Maybe ContentZone
parseContentZone s = case String.toLower s of
  "header" -> Just HeaderZone
  "body" -> Just BodyZone
  "main" -> Just BodyZone
  "content" -> Just BodyZone
  "footer" -> Just FooterZone
  "sidebar" -> Just SidebarZone
  "side" -> Just SidebarZone
  "hero" -> Just HeroZone
  "feature" -> Just HeroZone
  _ -> Nothing

-- | Mapping of content zone to brand colors.
type ZoneColorMapping =
  { zone :: ContentZone
  , primaryColor :: String      -- Primary color hex for this zone
  , secondaryColor :: String    -- Secondary color hex
  }

-- | Create zone color mapping.
mkZoneColorMapping :: ContentZone -> String -> String -> Maybe ZoneColorMapping
mkZoneColorMapping zone primary secondary =
  if String.length primary >= 4 && String.length secondary >= 4
    then Just { zone: zone, primaryColor: primary, secondaryColor: secondary }
    else Nothing

-- | Get zone type.
zoneType :: ZoneColorMapping -> ContentZone
zoneType zcm = zcm.zone

-- | Get primary color.
zonePrimaryColor :: ZoneColorMapping -> String
zonePrimaryColor zcm = zcm.primaryColor

-- | Get secondary color.
zoneSecondaryColor :: ZoneColorMapping -> String
zoneSecondaryColor zcm = zcm.secondaryColor

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // logo placement
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Logo placement rule.
type LogoPlacement =
  { lockupName :: String     -- Which lockup to use
  , zone :: ContentZone      -- Which zone to place in
  , alignment :: String      -- e.g., "left", "center", "right"
  }

-- | Create logo placement.
mkLogoPlacement :: String -> ContentZone -> String -> Maybe LogoPlacement
mkLogoPlacement lockup zone align =
  if String.length lockup >= 1 && String.length align >= 1
    then Just { lockupName: lockup, zone: zone, alignment: align }
    else Nothing

-- | Get lockup name.
placementLockup :: LogoPlacement -> String
placementLockup lp = lp.lockupName

-- | Get zone.
placementZone :: LogoPlacement -> ContentZone
placementZone lp = lp.zone

-- | Get alignment.
placementAlignment :: LogoPlacement -> String
placementAlignment lp = lp.alignment

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // print layout (portrait)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Print layout specification (typically portrait/letter).
type PrintLayoutSpec =
  { grid :: GridSystem
  , margins :: PageMargins
  , firstPageLogo :: LogoPlacement
  , subsequentLogo :: LogoPlacement
  , contentZones :: Array ZoneColorMapping
  }

-- | Create print layout spec.
mkPrintLayoutSpec
  :: GridSystem
  -> PageMargins
  -> LogoPlacement
  -> LogoPlacement
  -> Array ZoneColorMapping
  -> PrintLayoutSpec
mkPrintLayoutSpec grid margins firstLogo subLogo zones =
  { grid: grid
  , margins: margins
  , firstPageLogo: firstLogo
  , subsequentLogo: subLogo
  , contentZones: zones
  }

-- | Get grid system.
printGrid :: PrintLayoutSpec -> GridSystem
printGrid pls = pls.grid

-- | Get margins.
printMargins :: PrintLayoutSpec -> PageMargins
printMargins pls = pls.margins

-- | Get first page logo placement.
printFirstPageLogo :: PrintLayoutSpec -> LogoPlacement
printFirstPageLogo pls = pls.firstPageLogo

-- | Get subsequent page logo placement.
printSubsequentLogo :: PrintLayoutSpec -> LogoPlacement
printSubsequentLogo pls = pls.subsequentLogo

-- | Get content zone mappings.
printContentZones :: PrintLayoutSpec -> Array ZoneColorMapping
printContentZones pls = pls.contentZones

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // digital resolution
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Digital resolution specification.
type DigitalResolution =
  { width :: Int
  , height :: Int
  , name :: String     -- e.g., "1080p", "4K"
  }

-- | Create digital resolution.
mkDigitalResolution :: Int -> Int -> String -> Maybe DigitalResolution
mkDigitalResolution w h name =
  if w >= 1 && h >= 1 && String.length name >= 1
    then Just { width: w, height: h, name: name }
    else Nothing

-- | Get width.
resolutionWidth :: DigitalResolution -> Int
resolutionWidth dr = dr.width

-- | Get height.
resolutionHeight :: DigitalResolution -> Int
resolutionHeight dr = dr.height

-- | Get resolution name.
resolutionName :: DigitalResolution -> String
resolutionName dr = dr.name

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // safe zone
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Safe zone specification.
-- |
-- | Defines where logos and main text must stay within composition.
-- | Any placement outside requires approval.
type SafeZone =
  { percentage :: Number     -- Percentage from each edge (e.g., 10 = 10%)
  , description :: String    -- Rule description
  }

-- | Create safe zone.
mkSafeZone :: Number -> String -> Maybe SafeZone
mkSafeZone pct desc =
  if pct >= 0.0 && pct <= 50.0 && String.length desc >= 1
    then Just { percentage: pct, description: desc }
    else Nothing

-- | Get safe zone percentage.
safeZonePercentage :: SafeZone -> Number
safeZonePercentage sz = sz.percentage

-- | Get safe zone description.
safeZoneDescription :: SafeZone -> String
safeZoneDescription sz = sz.description

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // digital layout
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Digital layout specification (web & social).
type DigitalLayoutSpec =
  { minResolution :: DigitalResolution
  , verticalGrid :: GridSystem       -- For vertical compositions
  , horizontalGrid :: GridSystem     -- For horizontal compositions
  , safeZone :: SafeZone
  , contentZones :: Array ZoneColorMapping
  }

-- | Create digital layout spec.
mkDigitalLayoutSpec
  :: DigitalResolution
  -> GridSystem
  -> GridSystem
  -> SafeZone
  -> Array ZoneColorMapping
  -> DigitalLayoutSpec
mkDigitalLayoutSpec minRes vertGrid horizGrid safe zones =
  { minResolution: minRes
  , verticalGrid: vertGrid
  , horizontalGrid: horizGrid
  , safeZone: safe
  , contentZones: zones
  }

-- | Get minimum resolution.
digitalMinResolution :: DigitalLayoutSpec -> DigitalResolution
digitalMinResolution dls = dls.minResolution

-- | Get vertical grid.
digitalVerticalGrid :: DigitalLayoutSpec -> GridSystem
digitalVerticalGrid dls = dls.verticalGrid

-- | Get horizontal grid.
digitalHorizontalGrid :: DigitalLayoutSpec -> GridSystem
digitalHorizontalGrid dls = dls.horizontalGrid

-- | Get safe zone.
digitalSafeZone :: DigitalLayoutSpec -> SafeZone
digitalSafeZone dls = dls.safeZone

-- | Get content zones.
digitalContentZones :: DigitalLayoutSpec -> Array ZoneColorMapping
digitalContentZones dls = dls.contentZones

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // layout specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete layout specification for a brand.
type LayoutSpecification =
  { print :: PrintLayoutSpec
  , digital :: DigitalLayoutSpec
  }

-- | Create layout specification.
mkLayoutSpecification
  :: PrintLayoutSpec
  -> DigitalLayoutSpec
  -> LayoutSpecification
mkLayoutSpecification printSpec digitalSpec =
  { print: printSpec
  , digital: digitalSpec
  }

-- | Get print layout.
layoutPrint :: LayoutSpecification -> PrintLayoutSpec
layoutPrint ls = ls.print

-- | Get digital layout.
layoutDigital :: LayoutSpecification -> DigitalLayoutSpec
layoutDigital ls = ls.digital
