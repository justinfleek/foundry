{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // foundry // core // brand // imagery
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Imagery
Description : Photography and illustration guidelines
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the imagery guidelines for a brand including photography style,
illustration rules, color grading, and image treatment specifications.

== SMART Brand Framework Section

This module implements imagery guidelines for brand visual consistency.

== Dependencies

Requires: vector, text, aeson
Required by: Foundry.Core.Brand.Complete

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Imagery
  ( -- * Photography Style
    PhotographyStyle (..)
  , photographyStyleToText
  , LightingStyle (..)
  , lightingStyleToText
  , SubjectFocus (..)
  , subjectFocusToText
  , PhotographyGuidelines (..)
  , mkPhotographyGuidelines

    -- * Color Grading
  , ColorGrading (..)
  , GradingPreset (..)
  , gradingPresetToText
  , mkColorGrading

    -- * Illustration Style
  , IllustrationStyle (..)
  , illustrationStyleToText
  , LineWeight (..)
  , mkLineWeight
  , IllustrationGuidelines (..)
  , mkIllustrationGuidelines

    -- * Image Treatment
  , ImageTreatment (..)
  , treatmentToText
  , CornerRadius (..)
  , mkCornerRadius
  , ImageFrame (..)
  , mkImageFrame

    -- * Aspect Ratios
  , AspectRatio (..)
  , mkAspectRatio
  , aspectRatioToText
  , commonAspectRatios

    -- * Imagery System
  , ImageryGuidelines (..)
  , mkImageryGuidelines
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.:?), (.=))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Photography Style
--------------------------------------------------------------------------------

-- | Overall photography aesthetic
data PhotographyStyle
  = PhotoMinimal
    -- ^ Clean, minimal compositions
  | PhotoLifestyle
    -- ^ Natural, candid lifestyle shots
  | PhotoEditorial
    -- ^ High-fashion editorial style
  | PhotoDocumentary
    -- ^ Authentic documentary approach
  | PhotoProduct
    -- ^ Clean product photography
  | PhotoAbstract
    -- ^ Abstract, artistic imagery
  | PhotoCustom !Text
    -- ^ Custom style description
  deriving stock (Eq, Show, Generic)

instance ToJSON PhotographyStyle where
  toJSON PhotoMinimal = "minimal"
  toJSON PhotoLifestyle = "lifestyle"
  toJSON PhotoEditorial = "editorial"
  toJSON PhotoDocumentary = "documentary"
  toJSON PhotoProduct = "product"
  toJSON PhotoAbstract = "abstract"
  toJSON (PhotoCustom t) = toJSON t

instance FromJSON PhotographyStyle where
  parseJSON = withText "PhotographyStyle" $ \t ->
    pure $ case t of
      "minimal" -> PhotoMinimal
      "lifestyle" -> PhotoLifestyle
      "editorial" -> PhotoEditorial
      "documentary" -> PhotoDocumentary
      "product" -> PhotoProduct
      "abstract" -> PhotoAbstract
      custom -> PhotoCustom custom

-- | Convert to text
photographyStyleToText :: PhotographyStyle -> Text
photographyStyleToText PhotoMinimal = "minimal"
photographyStyleToText PhotoLifestyle = "lifestyle"
photographyStyleToText PhotoEditorial = "editorial"
photographyStyleToText PhotoDocumentary = "documentary"
photographyStyleToText PhotoProduct = "product"
photographyStyleToText PhotoAbstract = "abstract"
photographyStyleToText (PhotoCustom t) = t

-- | Lighting approach
data LightingStyle
  = LightingNatural
    -- ^ Natural/ambient lighting
  | LightingStudio
    -- ^ Controlled studio lighting
  | LightingDramatic
    -- ^ High contrast, dramatic
  | LightingSoft
    -- ^ Soft, diffused lighting
  | LightingMixed
    -- ^ Combination of techniques
  deriving stock (Eq, Show, Generic)

instance ToJSON LightingStyle where
  toJSON LightingNatural = "natural"
  toJSON LightingStudio = "studio"
  toJSON LightingDramatic = "dramatic"
  toJSON LightingSoft = "soft"
  toJSON LightingMixed = "mixed"

instance FromJSON LightingStyle where
  parseJSON = withText "LightingStyle" $ \case
    "natural" -> pure LightingNatural
    "studio" -> pure LightingStudio
    "dramatic" -> pure LightingDramatic
    "soft" -> pure LightingSoft
    _ -> pure LightingMixed

-- | Convert to text
lightingStyleToText :: LightingStyle -> Text
lightingStyleToText LightingNatural = "natural"
lightingStyleToText LightingStudio = "studio"
lightingStyleToText LightingDramatic = "dramatic"
lightingStyleToText LightingSoft = "soft"
lightingStyleToText LightingMixed = "mixed"

-- | Subject matter focus
data SubjectFocus
  = FocusPeople
    -- ^ Human subjects
  | FocusProducts
    -- ^ Product shots
  | FocusEnvironments
    -- ^ Spaces and environments
  | FocusDetails
    -- ^ Close-up details
  | FocusMixed
    -- ^ Various subjects
  deriving stock (Eq, Show, Generic)

instance ToJSON SubjectFocus where
  toJSON FocusPeople = "people"
  toJSON FocusProducts = "products"
  toJSON FocusEnvironments = "environments"
  toJSON FocusDetails = "details"
  toJSON FocusMixed = "mixed"

instance FromJSON SubjectFocus where
  parseJSON = withText "SubjectFocus" $ \case
    "people" -> pure FocusPeople
    "products" -> pure FocusProducts
    "environments" -> pure FocusEnvironments
    "details" -> pure FocusDetails
    _ -> pure FocusMixed

-- | Convert to text
subjectFocusToText :: SubjectFocus -> Text
subjectFocusToText FocusPeople = "people"
subjectFocusToText FocusProducts = "products"
subjectFocusToText FocusEnvironments = "environments"
subjectFocusToText FocusDetails = "details"
subjectFocusToText FocusMixed = "mixed"

-- | Complete photography guidelines
data PhotographyGuidelines = PhotographyGuidelines
  { pgStyle    :: !PhotographyStyle
    -- ^ Overall style
  , pgLighting :: !LightingStyle
    -- ^ Lighting approach
  , pgFocus    :: !SubjectFocus
    -- ^ Subject matter
  , pgMoods    :: !(Vector Text)
    -- ^ Mood keywords (e.g., "authentic", "warm", "dynamic")
  , pgAvoid    :: !(Vector Text)
    -- ^ What to avoid (e.g., "stock-looking", "oversaturated")
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON PhotographyGuidelines where
  toJSON PhotographyGuidelines{..} = object
    [ "style"    .= pgStyle
    , "lighting" .= pgLighting
    , "focus"    .= pgFocus
    , "moods"    .= pgMoods
    , "avoid"    .= pgAvoid
    ]

instance FromJSON PhotographyGuidelines where
  parseJSON = withObject "PhotographyGuidelines" $ \v -> PhotographyGuidelines
    <$> v .: "style"
    <*> v .: "lighting"
    <*> v .: "focus"
    <*> v .: "moods"
    <*> v .: "avoid"

-- | Smart constructor
mkPhotographyGuidelines 
  :: PhotographyStyle 
  -> LightingStyle 
  -> SubjectFocus 
  -> Vector Text 
  -> Vector Text 
  -> PhotographyGuidelines
mkPhotographyGuidelines = PhotographyGuidelines

--------------------------------------------------------------------------------
-- Color Grading
--------------------------------------------------------------------------------

-- | Preset color grading styles
data GradingPreset
  = GradingNeutral
    -- ^ No color grading
  | GradingWarm
    -- ^ Warm tones
  | GradingCool
    -- ^ Cool tones
  | GradingVintage
    -- ^ Vintage/film look
  | GradingCinematic
    -- ^ Cinematic color grading
  | GradingHighContrast
    -- ^ High contrast B&W or color
  | GradingMuted
    -- ^ Desaturated, muted tones
  | GradingVibrant
    -- ^ Saturated, vibrant colors
  deriving stock (Eq, Show, Generic)

instance ToJSON GradingPreset where
  toJSON GradingNeutral = "neutral"
  toJSON GradingWarm = "warm"
  toJSON GradingCool = "cool"
  toJSON GradingVintage = "vintage"
  toJSON GradingCinematic = "cinematic"
  toJSON GradingHighContrast = "high-contrast"
  toJSON GradingMuted = "muted"
  toJSON GradingVibrant = "vibrant"

instance FromJSON GradingPreset where
  parseJSON = withText "GradingPreset" $ \case
    "neutral" -> pure GradingNeutral
    "warm" -> pure GradingWarm
    "cool" -> pure GradingCool
    "vintage" -> pure GradingVintage
    "cinematic" -> pure GradingCinematic
    "high-contrast" -> pure GradingHighContrast
    "muted" -> pure GradingMuted
    _ -> pure GradingVibrant

-- | Convert to text
gradingPresetToText :: GradingPreset -> Text
gradingPresetToText GradingNeutral = "neutral"
gradingPresetToText GradingWarm = "warm"
gradingPresetToText GradingCool = "cool"
gradingPresetToText GradingVintage = "vintage"
gradingPresetToText GradingCinematic = "cinematic"
gradingPresetToText GradingHighContrast = "high-contrast"
gradingPresetToText GradingMuted = "muted"
gradingPresetToText GradingVibrant = "vibrant"

-- | Color grading specification
data ColorGrading = ColorGrading
  { cgPreset      :: !GradingPreset
    -- ^ Base preset
  , cgSaturation  :: !Double
    -- ^ Saturation adjustment (-1 to 1)
  , cgContrast    :: !Double
    -- ^ Contrast adjustment (-1 to 1)
  , cgTemperature :: !Double
    -- ^ Temperature adjustment (-1 cool to 1 warm)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ColorGrading where
  toJSON ColorGrading{..} = object
    [ "preset"      .= cgPreset
    , "saturation"  .= cgSaturation
    , "contrast"    .= cgContrast
    , "temperature" .= cgTemperature
    ]

instance FromJSON ColorGrading where
  parseJSON = withObject "ColorGrading" $ \v -> ColorGrading
    <$> v .: "preset"
    <*> v .: "saturation"
    <*> v .: "contrast"
    <*> v .: "temperature"

-- | Smart constructor with clamping
mkColorGrading :: GradingPreset -> Double -> Double -> Double -> ColorGrading
mkColorGrading preset sat con temp = ColorGrading
  { cgPreset = preset
  , cgSaturation = clamp (-1) 1 sat
  , cgContrast = clamp (-1) 1 con
  , cgTemperature = clamp (-1) 1 temp
  }
  where
    clamp lo hi x = max lo (min hi x)

--------------------------------------------------------------------------------
-- Illustration Style
--------------------------------------------------------------------------------

-- | Illustration aesthetic
data IllustrationStyle
  = IllustrationFlat
    -- ^ Flat, 2D design
  | IllustrationLine
    -- ^ Line art/outline style
  | IllustrationIsometric
    -- ^ Isometric 3D
  | IllustrationHand
    -- ^ Hand-drawn appearance
  | IllustrationGeometric
    -- ^ Geometric shapes
  | Illustration3D
    -- ^ 3D rendered
  | IllustrationPhoto
    -- ^ Photo-realistic
  | IllustrationCustom !Text
    -- ^ Custom style
  deriving stock (Eq, Show, Generic)

instance ToJSON IllustrationStyle where
  toJSON IllustrationFlat = "flat"
  toJSON IllustrationLine = "line"
  toJSON IllustrationIsometric = "isometric"
  toJSON IllustrationHand = "hand-drawn"
  toJSON IllustrationGeometric = "geometric"
  toJSON Illustration3D = "3d"
  toJSON IllustrationPhoto = "photo-realistic"
  toJSON (IllustrationCustom t) = toJSON t

instance FromJSON IllustrationStyle where
  parseJSON = withText "IllustrationStyle" $ \t ->
    pure $ case t of
      "flat" -> IllustrationFlat
      "line" -> IllustrationLine
      "isometric" -> IllustrationIsometric
      "hand-drawn" -> IllustrationHand
      "geometric" -> IllustrationGeometric
      "3d" -> Illustration3D
      "photo-realistic" -> IllustrationPhoto
      custom -> IllustrationCustom custom

-- | Convert to text
illustrationStyleToText :: IllustrationStyle -> Text
illustrationStyleToText IllustrationFlat = "flat"
illustrationStyleToText IllustrationLine = "line"
illustrationStyleToText IllustrationIsometric = "isometric"
illustrationStyleToText IllustrationHand = "hand-drawn"
illustrationStyleToText IllustrationGeometric = "geometric"
illustrationStyleToText Illustration3D = "3d"
illustrationStyleToText IllustrationPhoto = "photo-realistic"
illustrationStyleToText (IllustrationCustom t) = t

-- | Line weight in pixels
newtype LineWeight = LineWeight Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkLineWeight :: Double -> Maybe LineWeight
mkLineWeight w
  | w > 0 && not (isNaN w) && not (isInfinite w) = Just $ LineWeight w
  | otherwise = Nothing

-- | Illustration guidelines
data IllustrationGuidelines = IllustrationGuidelines
  { igStyle      :: !IllustrationStyle
    -- ^ Primary style
  , igLineWeight :: !(Maybe LineWeight)
    -- ^ Line weight if applicable
  , igFillStyle  :: !Text
    -- ^ Fill approach (solid, gradient, pattern)
  , igCorners    :: !Text
    -- ^ Corner treatment (rounded, sharp, mixed)
  , igUseCases   :: !(Vector Text)
    -- ^ Where illustrations are used
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON IllustrationGuidelines where
  toJSON IllustrationGuidelines{..} = object
    [ "style"      .= igStyle
    , "lineWeight" .= igLineWeight
    , "fillStyle"  .= igFillStyle
    , "corners"    .= igCorners
    , "useCases"   .= igUseCases
    ]

instance FromJSON IllustrationGuidelines where
  parseJSON = withObject "IllustrationGuidelines" $ \v -> IllustrationGuidelines
    <$> v .: "style"
    <*> v .:? "lineWeight"
    <*> v .: "fillStyle"
    <*> v .: "corners"
    <*> v .: "useCases"

-- | Smart constructor
mkIllustrationGuidelines 
  :: IllustrationStyle 
  -> Maybe LineWeight 
  -> Text 
  -> Text 
  -> Vector Text 
  -> IllustrationGuidelines
mkIllustrationGuidelines = IllustrationGuidelines

--------------------------------------------------------------------------------
-- Image Treatment
--------------------------------------------------------------------------------

-- | How images are treated/displayed
data ImageTreatment
  = TreatmentNone
    -- ^ No treatment
  | TreatmentDuotone
    -- ^ Duotone color overlay
  | TreatmentGrayscale
    -- ^ Black and white
  | TreatmentOverlay
    -- ^ Color overlay
  | TreatmentBlur
    -- ^ Background blur
  | TreatmentVignette
    -- ^ Vignette effect
  deriving stock (Eq, Show, Generic)

instance ToJSON ImageTreatment where
  toJSON TreatmentNone = "none"
  toJSON TreatmentDuotone = "duotone"
  toJSON TreatmentGrayscale = "grayscale"
  toJSON TreatmentOverlay = "overlay"
  toJSON TreatmentBlur = "blur"
  toJSON TreatmentVignette = "vignette"

instance FromJSON ImageTreatment where
  parseJSON = withText "ImageTreatment" $ \case
    "none" -> pure TreatmentNone
    "duotone" -> pure TreatmentDuotone
    "grayscale" -> pure TreatmentGrayscale
    "overlay" -> pure TreatmentOverlay
    "blur" -> pure TreatmentBlur
    _ -> pure TreatmentVignette

-- | Convert to text
treatmentToText :: ImageTreatment -> Text
treatmentToText TreatmentNone = "none"
treatmentToText TreatmentDuotone = "duotone"
treatmentToText TreatmentGrayscale = "grayscale"
treatmentToText TreatmentOverlay = "overlay"
treatmentToText TreatmentBlur = "blur"
treatmentToText TreatmentVignette = "vignette"

-- | Corner radius in pixels
newtype CornerRadius = CornerRadius Double
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | Smart constructor
mkCornerRadius :: Double -> Maybe CornerRadius
mkCornerRadius r
  | r >= 0 && not (isNaN r) && not (isInfinite r) = Just $ CornerRadius r
  | otherwise = Nothing

-- | Image frame/container specification
data ImageFrame = ImageFrame
  { ifRadius    :: !CornerRadius
    -- ^ Corner radius
  , ifShadow    :: !Bool
    -- ^ Whether to show shadow
  , ifBorder    :: !Bool
    -- ^ Whether to show border
  , ifTreatment :: !ImageTreatment
    -- ^ Applied treatment
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ImageFrame where
  toJSON ImageFrame{..} = object
    [ "radius"    .= ifRadius
    , "shadow"    .= ifShadow
    , "border"    .= ifBorder
    , "treatment" .= ifTreatment
    ]

instance FromJSON ImageFrame where
  parseJSON = withObject "ImageFrame" $ \v -> ImageFrame
    <$> v .: "radius"
    <*> v .: "shadow"
    <*> v .: "border"
    <*> v .: "treatment"

-- | Smart constructor
mkImageFrame :: CornerRadius -> Bool -> Bool -> ImageTreatment -> ImageFrame
mkImageFrame = ImageFrame

--------------------------------------------------------------------------------
-- Aspect Ratios
--------------------------------------------------------------------------------

-- | Aspect ratio as width:height
data AspectRatio = AspectRatio
  { arWidth  :: !Int
  , arHeight :: !Int
  , arName   :: !Text
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON AspectRatio where
  toJSON AspectRatio{..} = object
    [ "width"  .= arWidth
    , "height" .= arHeight
    , "name"   .= arName
    ]

instance FromJSON AspectRatio where
  parseJSON = withObject "AspectRatio" $ \v -> AspectRatio
    <$> v .: "width"
    <*> v .: "height"
    <*> v .: "name"

-- | Smart constructor
mkAspectRatio :: Int -> Int -> Text -> Maybe AspectRatio
mkAspectRatio w h name
  | w > 0 && h > 0 = Just $ AspectRatio w h name
  | otherwise = Nothing

-- | Convert to display text
aspectRatioToText :: AspectRatio -> Text
aspectRatioToText AspectRatio{..} = 
  T.pack (show arWidth) <> ":" <> T.pack (show arHeight)

-- | Common aspect ratios
commonAspectRatios :: Vector AspectRatio
commonAspectRatios = V.fromList
  [ AspectRatio 1 1 "Square"
  , AspectRatio 4 3 "Standard"
  , AspectRatio 16 9 "Widescreen"
  , AspectRatio 21 9 "Ultrawide"
  , AspectRatio 9 16 "Portrait"
  , AspectRatio 3 2 "Classic"
  , AspectRatio 2 3 "Portrait Classic"
  ]

--------------------------------------------------------------------------------
-- Imagery System
--------------------------------------------------------------------------------

-- | Complete imagery guidelines
data ImageryGuidelines = ImageryGuidelines
  { imPhotography  :: !PhotographyGuidelines
    -- ^ Photography rules
  , imGrading      :: !ColorGrading
    -- ^ Color grading specification
  , imIllustration :: !(Maybe IllustrationGuidelines)
    -- ^ Illustration rules (if brand uses illustrations)
  , imFrame        :: !ImageFrame
    -- ^ Default image framing
  , imAspectRatios :: !(Vector AspectRatio)
    -- ^ Approved aspect ratios
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ImageryGuidelines where
  toJSON ImageryGuidelines{..} = object
    [ "photography"  .= imPhotography
    , "grading"      .= imGrading
    , "illustration" .= imIllustration
    , "frame"        .= imFrame
    , "aspectRatios" .= imAspectRatios
    ]

instance FromJSON ImageryGuidelines where
  parseJSON = withObject "ImageryGuidelines" $ \v -> ImageryGuidelines
    <$> v .: "photography"
    <*> v .: "grading"
    <*> v .:? "illustration"
    <*> v .: "frame"
    <*> v .: "aspectRatios"

-- | Smart constructor
mkImageryGuidelines 
  :: PhotographyGuidelines 
  -> ColorGrading 
  -> Maybe IllustrationGuidelines 
  -> ImageFrame 
  -> Vector AspectRatio 
  -> ImageryGuidelines
mkImageryGuidelines = ImageryGuidelines
