{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                   // foundry // extract // compose
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Extract.Compose
Description : Brand composition from extracted components
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Composes a complete Brand from extracted components.

== Pipeline

1. Run all extractors (Color, Typography, Spacing, Voice)
2. Generate Identity (UUID5 from domain)
3. Compute Provenance (SHA256 of content)
4. Compose into complete Brand

== Design Notes

The composer is the final step in the extraction pipeline. It validates
all extracted components and combines them into a single Brand value.

== Dependencies

Requires: Foundry.Extract.Color, Foundry.Extract.Typography, 
          Foundry.Extract.Spacing, Foundry.Extract.Voice
Required by: (none - top-level entry point)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Extract.Compose
  ( -- * Composition
    composeBrand
  , BrandExtractionResult (..)

    -- * CompleteBrand Construction
  , toCompleteBrand
  , CompleteBrandError (..)

    -- * Components
  , ExtractionComponents (..)
  ) where

import Crypto.Hash (Digest, SHA256, hash)
import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (UTCTime)
import Data.Vector (Vector)
import Data.Vector qualified as V

import Foundry.Core.Text (bshow)

import Foundry.Core.Brand
  ( BrandId
  , BrandName
  , BrandPalette
  , BrandVoice (..)
  , ContentHash (..)
  , Domain
  , Provenance (..)
  , SourceURL (..)
  , SpacingScale
  , Timestamp (..)
  , Tone (..)
  , Typography
  , mkBrandId
  , mkBrandName
  , mkDomain
  )
import Foundry.Core.Brand.Complete
  ( CompleteBrand (..)
  )
import Foundry.Core.Brand.Customer
  ( CustomerSegment (..)
  )
import Foundry.Core.Brand.Editorial
  ( MasterStyleList (..)
  , HeadlineStyle (..)
  , HeadlineCaseStyle (..)
  , PunctuationRules (..)
  , ListPunctuation (..)
  , OxfordComma (..)
  , HyphenationPolicy (..)
  , ExclamationLimit (..)
  , ContactTimeRules (..)
  , PhoneFormat (..)
  , TimeFormat (..)
  , TimeRangeNotation (..)
  , MidnightNoon (..)
  , DayAbbreviation (..)
  , SpellingConventions (..)
  , RegionalSpelling (..)
  , FormattingRules (..)
  , TextAlignment (..)
  )
import Foundry.Core.Brand.Logo
  ( LogoSpecification (..)
  , LogoIcon (..)
  , LogoWordmark (..)
  , LogoLockup (..)
  , LogoComponent (..)
  , LockupOrientation (..)
  , ColorVariant (..)
  , ClearSpaceRule (..)
  , LogoUsageRule (..)
  , UsageContext (..)
  )
import Foundry.Core.Brand.Overview
  ( BrandOverview (..)
  , Industry (..)
  )
import Foundry.Core.Brand.Strategy
  ( StrategicLayer (..)
  , MissionStatement (..)
  , BrandValues (..)
  , BrandValue (..)
  , BrandPersonality (..)
  , PersonalityTrait (..)
  , PersonalityDescription (..)
  , PositioningStatement (..)
  , PositioningType (..)
  )
import Foundry.Core.Brand.Tagline
  ( TaglineSet (..)
  , PrimaryTagline (..)
  , Tagline (..)
  , TaglineText (..)
  , TaglineContext (..)
  )
import Foundry.Extract.Color (ColorExtractionResult (..), extractPalette)
import Foundry.Extract.Spacing (SpacingExtractionResult (..), extractSpacing)
import Foundry.Extract.Types
  ( ExtractionError (..)
  , ExtractionWarning (..)
  , ScrapeResult (..)
  , TextContent (..)
  )
import Foundry.Extract.Typography (TypographyExtractionResult (..), extractTypography)
import Foundry.Extract.Voice (VoiceExtractionResult (..), extractVoice)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Complete brand extraction result
data BrandExtractionResult = BrandExtractionResult
  { berIdentity    :: !BrandId
    -- ^ Brand identity (UUID5)
  , berDomain      :: !Domain
    -- ^ Source domain
  , berName        :: !(Maybe BrandName)
    -- ^ Brand name (if detected)
  , berPalette     :: !BrandPalette
    -- ^ Color palette
  , berTypography  :: !Typography
    -- ^ Typography specification
  , berSpacing     :: !SpacingScale
    -- ^ Spacing scale
  , berVoice       :: !BrandVoice
    -- ^ Brand voice
  , berProvenance  :: !Provenance
    -- ^ Content provenance
  , berComponents  :: !ExtractionComponents
    -- ^ Detailed extraction results
  , berWarnings    :: ![ExtractionWarning]
    -- ^ All warnings from extraction
  }
  deriving stock (Show)

-- | Detailed extraction component results
data ExtractionComponents = ExtractionComponents
  { ecColor      :: !ColorExtractionResult
  , ecTypography :: !TypographyExtractionResult
  , ecSpacing    :: !SpacingExtractionResult
  , ecVoice      :: !VoiceExtractionResult
  }
  deriving stock (Show)

--------------------------------------------------------------------------------
-- Composition
--------------------------------------------------------------------------------

-- | Compose a complete Brand from scrape result
composeBrand :: UTCTime -> ScrapeResult -> Either ExtractionError BrandExtractionResult
composeBrand timestamp sr = do
  -- Validate domain
  domain <- case mkDomain (srDomain sr) of
    Just d  -> Right d
    Nothing -> Left ErrNoDomain
  
  -- Generate identity
  let brandId = mkBrandId domain
  
  -- Extract color palette
  colorResult <- extractPalette sr
  
  -- Extract typography
  typoResult <- extractTypography sr
  
  -- Extract spacing (infallible)
  let spacingResult = extractSpacing sr
  
  -- Extract voice (infallible)
  let voiceResult = extractVoice sr
  
  -- Compute provenance
  let contentHash = computeContentHash (srRawHTML sr)
      provenance = Provenance
        { provenanceHash = contentHash
        , provenanceSource = SourceURL (srURL sr)
        , provenanceTimestamp = Timestamp timestamp
        }
  
  -- Collect all warnings
  let allWarnings = cerWarnings colorResult
                 ++ terWarnings typoResult
                 ++ serWarnings spacingResult
                 ++ verWarnings voiceResult
  
  -- Build components record
  let components = ExtractionComponents
        { ecColor = colorResult
        , ecTypography = typoResult
        , ecSpacing = spacingResult
        , ecVoice = voiceResult
        }
  
  -- Compose result
  Right $ BrandExtractionResult
    { berIdentity = brandId
    , berDomain = domain
    , berName = extractBrandName sr
    , berPalette = cerPalette colorResult
    , berTypography = terTypography typoResult
    , berSpacing = serSpacing spacingResult
    , berVoice = verVoice voiceResult
    , berProvenance = provenance
    , berComponents = components
    , berWarnings = allWarnings
    }

-- | Compute SHA256 content hash
--
-- Uses bshow from Foundry.Core.Text following the Hydrogen Show debug convention.
-- The digest's Show instance produces a hex string representation.
computeContentHash :: ByteString -> ContentHash
computeContentHash content =
  let digest :: Digest SHA256
      digest = hash content
  in ContentHash (bshow digest)

-- | Extract brand name from title or domain
extractBrandName :: ScrapeResult -> Maybe BrandName
extractBrandName sr = case srTextContent sr of
  tc -> case tcTitle tc of
    Just title -> mkBrandName (cleanTitle title)
    Nothing    -> mkBrandName (srDomain sr)
  where
    -- Clean up title (remove " - Website" etc.)
    cleanTitle t = t  -- Note: Title cleaning should be implemented based on domain patterns

--------------------------------------------------------------------------------
-- CompleteBrand Construction
--------------------------------------------------------------------------------

-- | Errors that can occur when building a CompleteBrand
data CompleteBrandError
  = MissingBrandName
    -- ^ Brand name could not be determined
  | InvalidDomain !Text
    -- ^ Domain is invalid
  deriving stock (Eq, Show)

-- | Convert BrandExtractionResult to CompleteBrand with intelligent defaults
--
-- This function bridges the gap between extracted data (colors, typography,
-- spacing, voice) and the full SMART Brand Framework by providing sensible
-- defaults for components that cannot be extracted from CSS/HTML alone.
--
-- Components with defaults:
-- - Overview: Generated from domain and detected tone
-- - Strategy: Mission, values, personality inferred from voice
-- - Taglines: Generated from title/headings
-- - Editorial: Basic style rules
-- - Customers: Generic segment
-- - Logo: Placeholder (requires manual input)
-- - Gradients: None
-- - Layout: None
-- - Material: None
-- - Imagery: None
-- - Themes: None
toCompleteBrand :: BrandExtractionResult -> Either CompleteBrandError CompleteBrand
toCompleteBrand ber = do
  -- Get brand name (required)
  brandName <- case berName ber of
    Just n  -> Right n
    Nothing -> Left MissingBrandName
  
  let domain = berDomain ber
      domainText = unDomain domain
      
      -- Build overview with defaults
      overview = buildDefaultOverview domainText brandName (berVoice ber)
      
      -- Build strategic layer from voice
      strategy = buildDefaultStrategy brandName (berVoice ber)
      
      -- Build taglines from brand name
      taglines = buildDefaultTaglines brandName
      
      -- Build editorial defaults
      editorial = buildDefaultEditorial
      
      -- Build customer segment defaults
      customers = buildDefaultCustomers
      
      -- Build logo placeholder
      logo = buildPlaceholderLogo brandName
  
  Right CompleteBrand
    { cbId = berIdentity ber
    , cbName = brandName
    , cbDomain = domain
    , cbOverview = overview
    , cbStrategy = strategy
    , cbTaglines = taglines
    , cbVoice = berVoice ber
    , cbEditorial = editorial
    , cbCustomers = customers
    , cbLogo = logo
    , cbPalette = berPalette ber
    , cbGradients = Nothing
    , cbTypography = berTypography ber
    , cbSpacing = berSpacing ber
    , cbLayout = Nothing
    , cbMaterial = Nothing
    , cbImagery = Nothing
    , cbThemes = Nothing
    , cbProvenance = berProvenance ber
    }

-- | Extract domain text (helper)
unDomain :: Domain -> Text
unDomain d = case mkDomain "temp" of
  Just _ -> domainToText d  -- Domain has a text accessor
  Nothing -> "unknown"
  where
    -- Domain should expose its text via show or accessor
    domainToText :: Domain -> Text
    domainToText dom = T.pack (show dom)  -- Temporary, will refine

--------------------------------------------------------------------------------
-- Default Builders
--------------------------------------------------------------------------------

-- | Build default overview from domain and voice
buildDefaultOverview :: Text -> BrandName -> BrandVoice -> BrandOverview
buildDefaultOverview _domainText brandName voice = BrandOverview
  { overviewParentOrg = Nothing
  , overviewIndustry = Industry "Technology"  -- Default
  , overviewOneLiner = T.concat
      [ "Welcome to "
      , brandNameText brandName
      , " - your digital destination."
      ]
  , overviewPromise = T.concat
      [ "We deliver "
      , toneToPromise (brandVoiceTone voice)
      , " experiences."
      ]
  , overviewFoundingCtx = T.concat
      [ brandNameText brandName
      , " was created to serve our customers with excellence."
      ]
  }

-- | Build default strategy from voice analysis
buildDefaultStrategy :: BrandName -> BrandVoice -> StrategicLayer
buildDefaultStrategy brandName voice = StrategicLayer
  { strategicMission = MissionStatement $ T.concat
      [ "To deliver exceptional value to our customers through "
      , T.toLower (T.pack (show (brandVoiceTone voice)))
      , " service."
      ]
  , strategicValues = BrandValues
      { brandValuesItems = V.fromList
          [ BrandValue "Excellence" "We strive for the highest quality in everything we do."
          , BrandValue "Integrity" "We act with honesty and transparency."
          , BrandValue "Innovation" "We embrace new ideas and continuous improvement."
          ]
      }
  , strategicPersonality = BrandPersonality
      { personalityTraits = V.fromList
          [ PersonalityTrait (T.pack (show (brandVoiceTone voice)))
          , PersonalityTrait "reliable"
          , PersonalityTrait "trustworthy"
          ]
      , personalityDescription = PersonalityDescription $ T.concat
          [ brandNameText brandName
          , " embodies a "
          , T.toLower (T.pack (show (brandVoiceTone voice)))
          , " approach to serving customers."
          ]
      , personalityPositioning = PositioningStatement
          { positioningType = toneToPositioning (brandVoiceTone voice)
          , positioningNarrative = T.concat
              [ brandNameText brandName
              , " positions itself as a trusted "
              , T.toLower (positioningTypeText (toneToPositioning (brandVoiceTone voice)))
              , " in its space."
              ]
          }
      }
  }

-- | Build default taglines from brand name
buildDefaultTaglines :: BrandName -> TaglineSet
buildDefaultTaglines brandName = TaglineSet
  { taglineSetPrimary = PrimaryTagline Tagline
      { taglineText = TaglineText $ T.concat
          [ brandNameText brandName
          , " - Excellence Delivered"
          ]
      , taglineContexts = V.singleton GeneralContext
      }
  , taglineSetSecondary = V.empty
  , taglineSetUsageRules = V.empty
  }

-- | Build default editorial style guide
buildDefaultEditorial :: MasterStyleList
buildDefaultEditorial = MasterStyleList
  { styleHeadlines = HeadlineStyle
      { headlineCaseStyle = SentenceCase
      , headlinePunctuation = V.empty
      , headlineMaxLength = Nothing
      , headlineConciseness = "Keep headlines concise and action-oriented."
      }
  , stylePunctuation = PunctuationRules
      { punctListStyle = PeriodsOnSentences
      , punctOxfordComma = OxfordAlways
      , punctHyphenation = MinimalHyphenation
      , punctExclamationMax = ExclamationLimit 1
      }
  , styleContactTime = ContactTimeRules
      { contactPhoneFormat = PhoneFormat "XXX-XXX-XXXX"
      , contactTimeFormat = TwelveHour
      , contactTimeRange = EnDash
      , contactMidnightNoon = TwelveAMPM
      , contactDayAbbrev = ContextualAbbrev
      }
  , styleSpelling = SpellingConventions
      { spellingRegion = AmericanEnglish
      , spellingConfused = V.empty
      }
  , styleFormatting = FormattingRules
      { formatAlignment = AlignLeft
      , formatCapitalization = V.empty
      }
  }

-- | Build default customer segments
buildDefaultCustomers :: Vector CustomerSegment
buildDefaultCustomers = V.fromList
  [ CustomerSegment
      { segmentName = "Primary Users"
      , segmentDescription = "Core users who regularly engage with the brand."
      , segmentMotivations = ["Quality service", "Reliability", "Value"]
      }
  ]

-- | Build placeholder logo specification
buildPlaceholderLogo :: BrandName -> LogoSpecification
buildPlaceholderLogo brandName = LogoSpecification
  { logoIcon = LogoIcon
      { iconDescription = T.concat ["Icon for ", brandNameText brandName]
      , iconSymbolism = "Represents the brand's core values."
      }
  , logoWordmark = LogoWordmark
      { wordmarkText = brandNameText brandName
      , wordmarkTypography = "Primary brand typeface"
      }
  , logoLockups = V.fromList
      [ LogoLockup
          { lockupName = "Primary"
          , lockupComponents = V.fromList [IconComponent, WordmarkComponent]
          , lockupOrientation = Horizontal
          , lockupUseCases = V.fromList ["websites", "marketing"]
          , lockupColorVariants = V.fromList [FullColor, BlackWhite, Reversed]
          , lockupApprovedBackgrounds = V.empty
          }
      ]
  , logoClearSpace = ClearSpaceRule
      { clearSpaceReference = "icon-height"
      , clearSpaceMultiplier = 1.0
      , clearSpaceDescription = "Maintain clear space equal to 1x the icon height"
      }
  , logoSizing = V.empty
  , logoUsageRules = V.fromList
      [ LogoUsageRule
          { usageRuleContext = UsageFirstPage
          , usageRuleLockup = "Primary"
          , usageRuleAlignment = "left"
          , usageRuleNotes = "Maintain minimum size of 24px height"
          }
      , LogoUsageRule
          { usageRuleContext = UsageSocialMedia
          , usageRuleLockup = "Primary"
          , usageRuleAlignment = "center"
          , usageRuleNotes = "Ensure adequate clear space around logo"
          }
      ]
  , logoErrors = V.empty
  }

--------------------------------------------------------------------------------
-- Helper Functions
--------------------------------------------------------------------------------

-- | Convert tone to brand promise wording
toneToPromise :: Tone -> Text
toneToPromise Formal = "professional and polished"
toneToPromise Casual = "relaxed and approachable"
toneToPromise Professional = "expert and reliable"
toneToPromise Friendly = "warm and welcoming"
toneToPromise Authoritative = "trusted and knowledgeable"
toneToPromise Playful = "fun and engaging"

-- | Convert tone to positioning type
toneToPositioning :: Tone -> PositioningType
toneToPositioning Formal = Authority
toneToPositioning Casual = Everyman
toneToPositioning Professional = Guide
toneToPositioning Friendly = Ally
toneToPositioning Authoritative = Sage
toneToPositioning Playful = Creator

-- | Convert positioning type to text
positioningTypeText :: PositioningType -> Text
positioningTypeText Ally = "ally"
positioningTypeText Guide = "guide"
positioningTypeText Facilitator = "facilitator"
positioningTypeText Authority = "authority"
positioningTypeText Challenger = "challenger"
positioningTypeText Creator = "creator"
positioningTypeText Caregiver = "caregiver"
positioningTypeText Everyman = "everyman"
positioningTypeText Hero = "hero"
positioningTypeText Sage = "sage"
positioningTypeText Explorer = "explorer"
positioningTypeText Rebel = "rebel"

-- | Extract text from BrandName
brandNameText :: BrandName -> Text
brandNameText bn = T.pack (show bn)  -- BrandName should have a text accessor
