-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brand // modes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SMART Framework Modes Layer: Alternative styling, light/dark modes,
-- | corporate/expressive variations.
-- |
-- | STATUS: FOUNDATIONAL
-- |
-- | Many brands have dual visual identities for different contexts — often
-- | a formal/corporate mode and an expressive/creative mode. This module
-- | captures how the brand adapts while maintaining cohesion.
-- |
-- | SMART FRAMEWORK:
-- |   S - Story-driven: Each mode tells different facet of brand story
-- |   M - Memorable: Consistent modes create predictable identity
-- |   A - Agile: Modes allow adaptation to different contexts
-- |   R - Responsive: Maps to system light/dark preferences
-- |   T - Targeted: Trigger conditions define when to use each mode
-- |
-- | DEPENDENCIES:
-- |   - None (foundational module)
-- |
-- | DEPENDENTS:
-- |   - Hydrogen.Schema.Brand.Brand (compound Brand type)

module Hydrogen.Schema.Brand.Modes
  ( -- * Mode Type
    ModeType
      ( CorporateMode
      , ExpressiveMode
      , ProfessionalMode
      , PlayfulMode
      , FormalMode
      , CasualMode
      )
  , modeTypeToString
  , parseModeType
  
  -- * System Color Scheme
  , SystemColorScheme
      ( LightScheme
      , DarkScheme
      , SystemPreference
      )
  , systemColorSchemeToString
  , parseSystemColorScheme
  
  -- * Mode Priority
  , ModePriority
      ( DefaultMode
      , SecondaryMode
      , ContextualMode
      )
  , modePriorityToString
  , parseModePriority
  
  -- * Trigger Condition
  , TriggerCondition
  , mkTriggerCondition
  , triggerContext
  , triggerDescription
  
  -- * Visual Treatment
  , ModeVisualTreatment
  , mkModeVisualTreatment
  , treatmentBackground
  , treatmentLogoVariant
  , treatmentColorEmphasis
  , treatmentTexture
  
  -- * Brand Mode
  , BrandMode
  , mkBrandMode
  , modeName
  , modeType
  , modeVisualTreatment
  , modeApprovedContexts
  , modeColorScheme
  , modePriority
  , modeTriggerConditions
  
  -- * Mode Transition Rule
  , ModeTransitionRule
  , mkModeTransitionRule
  , transitionFromMode
  , transitionToMode
  , transitionCondition
  
  -- * Complete Modes Specification
  , ModesSpecification
  , mkModesSpecification
  , specModes
  , specDefaultMode
  , specTransitionRules
  , specDesignPrinciple
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>=)
  , (&&)
  , (<>)
  , show
  , compare
  )

import Data.Array (length) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, toLower) as String

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // mode type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of brand mode.
data ModeType
  = CorporateMode       -- Formal, professional contexts
  | ExpressiveMode      -- Creative, playful contexts
  | ProfessionalMode    -- Business-focused
  | PlayfulMode         -- Fun, engaging contexts
  | FormalMode          -- Official communications
  | CasualMode          -- Relaxed, friendly contexts

derive instance eqModeType :: Eq ModeType

instance ordModeType :: Ord ModeType where
  compare m1 m2 = compare (modeToInt m1) (modeToInt m2)
    where
      modeToInt :: ModeType -> Int
      modeToInt CorporateMode = 0
      modeToInt ExpressiveMode = 1
      modeToInt ProfessionalMode = 2
      modeToInt PlayfulMode = 3
      modeToInt FormalMode = 4
      modeToInt CasualMode = 5

instance showModeType :: Show ModeType where
  show = modeTypeToString

-- | Convert mode type to string.
modeTypeToString :: ModeType -> String
modeTypeToString CorporateMode = "corporate"
modeTypeToString ExpressiveMode = "expressive"
modeTypeToString ProfessionalMode = "professional"
modeTypeToString PlayfulMode = "playful"
modeTypeToString FormalMode = "formal"
modeTypeToString CasualMode = "casual"

-- | Parse mode type from string.
parseModeType :: String -> Maybe ModeType
parseModeType s = case String.toLower s of
  "corporate" -> Just CorporateMode
  "business" -> Just CorporateMode
  "expressive" -> Just ExpressiveMode
  "creative" -> Just ExpressiveMode
  "gamer" -> Just ExpressiveMode
  "professional" -> Just ProfessionalMode
  "playful" -> Just PlayfulMode
  "fun" -> Just PlayfulMode
  "formal" -> Just FormalMode
  "official" -> Just FormalMode
  "casual" -> Just CasualMode
  "relaxed" -> Just CasualMode
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // system color scheme
-- ═══════════════════════════════════════════════════════════════════════════════

-- | System color scheme mapping.
data SystemColorScheme
  = LightScheme         -- Light mode / light background
  | DarkScheme          -- Dark mode / dark background
  | SystemPreference    -- Follow system preference

derive instance eqSystemColorScheme :: Eq SystemColorScheme

instance ordSystemColorScheme :: Ord SystemColorScheme where
  compare s1 s2 = compare (schemeToInt s1) (schemeToInt s2)
    where
      schemeToInt :: SystemColorScheme -> Int
      schemeToInt LightScheme = 0
      schemeToInt DarkScheme = 1
      schemeToInt SystemPreference = 2

instance showSystemColorScheme :: Show SystemColorScheme where
  show = systemColorSchemeToString

-- | Convert system color scheme to string.
systemColorSchemeToString :: SystemColorScheme -> String
systemColorSchemeToString LightScheme = "light"
systemColorSchemeToString DarkScheme = "dark"
systemColorSchemeToString SystemPreference = "system"

-- | Parse system color scheme from string.
parseSystemColorScheme :: String -> Maybe SystemColorScheme
parseSystemColorScheme s = case String.toLower s of
  "light" -> Just LightScheme
  "light-mode" -> Just LightScheme
  "dark" -> Just DarkScheme
  "dark-mode" -> Just DarkScheme
  "system" -> Just SystemPreference
  "auto" -> Just SystemPreference
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // mode priority
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mode priority level.
data ModePriority
  = DefaultMode         -- Primary/default mode
  | SecondaryMode       -- Secondary, used when default doesn't fit
  | ContextualMode      -- Used only in specific contexts

derive instance eqModePriority :: Eq ModePriority

instance ordModePriority :: Ord ModePriority where
  compare p1 p2 = compare (prioToInt p1) (prioToInt p2)
    where
      prioToInt :: ModePriority -> Int
      prioToInt DefaultMode = 0
      prioToInt SecondaryMode = 1
      prioToInt ContextualMode = 2

instance showModePriority :: Show ModePriority where
  show = modePriorityToString

-- | Convert mode priority to string.
modePriorityToString :: ModePriority -> String
modePriorityToString DefaultMode = "default"
modePriorityToString SecondaryMode = "secondary"
modePriorityToString ContextualMode = "contextual"

-- | Parse mode priority from string.
parseModePriority :: String -> Maybe ModePriority
parseModePriority s = case String.toLower s of
  "default" -> Just DefaultMode
  "primary" -> Just DefaultMode
  "secondary" -> Just SecondaryMode
  "contextual" -> Just ContextualMode
  "specific" -> Just ContextualMode
  _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // trigger condition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Condition that triggers a mode.
type TriggerCondition =
  { context :: String           -- Context identifier
  , description :: String       -- Full description of when to use
  }

-- | Create trigger condition.
mkTriggerCondition :: String -> String -> Maybe TriggerCondition
mkTriggerCondition ctx desc =
  if String.length ctx >= 1 && String.length desc >= 1
    then Just { context: ctx, description: desc }
    else Nothing

-- | Get trigger context.
triggerContext :: TriggerCondition -> String
triggerContext tc = tc.context

-- | Get trigger description.
triggerDescription :: TriggerCondition -> String
triggerDescription tc = tc.description

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // mode visual treatment
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual treatment for a mode.
type ModeVisualTreatment =
  { background :: String        -- Background treatment (e.g., "light", "dark", "gradient")
  , logoVariant :: String       -- Which logo variant to use
  , colorEmphasis :: String     -- Which colors are emphasized
  , texture :: String           -- Texture/pattern treatment
  }

-- | Create mode visual treatment.
mkModeVisualTreatment
  :: String
  -> String
  -> String
  -> String
  -> Maybe ModeVisualTreatment
mkModeVisualTreatment bg logo color texture =
  if String.length bg >= 1 
     && String.length logo >= 1 
     && String.length color >= 1
    then Just
      { background: bg
      , logoVariant: logo
      , colorEmphasis: color
      , texture: texture
      }
    else Nothing

-- | Get background treatment.
treatmentBackground :: ModeVisualTreatment -> String
treatmentBackground mvt = mvt.background

-- | Get logo variant.
treatmentLogoVariant :: ModeVisualTreatment -> String
treatmentLogoVariant mvt = mvt.logoVariant

-- | Get color emphasis.
treatmentColorEmphasis :: ModeVisualTreatment -> String
treatmentColorEmphasis mvt = mvt.colorEmphasis

-- | Get texture treatment.
treatmentTexture :: ModeVisualTreatment -> String
treatmentTexture mvt = mvt.texture

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // brand mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A brand mode definition.
type BrandMode =
  { name :: String                           -- Mode identifier
  , mType :: ModeType
  , visualTreatment :: ModeVisualTreatment
  , approvedContexts :: Array String         -- Where this mode can be used
  , colorScheme :: SystemColorScheme
  , priority :: ModePriority
  , triggerConditions :: Array TriggerCondition
  }

-- | Create brand mode.
mkBrandMode
  :: String
  -> ModeType
  -> ModeVisualTreatment
  -> Array String
  -> SystemColorScheme
  -> ModePriority
  -> Array TriggerCondition
  -> Maybe BrandMode
mkBrandMode name mType visual contexts scheme priority triggers =
  if String.length name >= 1
    then Just
      { name: name
      , mType: mType
      , visualTreatment: visual
      , approvedContexts: contexts
      , colorScheme: scheme
      , priority: priority
      , triggerConditions: triggers
      }
    else Nothing

-- | Get mode name.
modeName :: BrandMode -> String
modeName bm = bm.name

-- | Get mode type.
modeType :: BrandMode -> ModeType
modeType bm = bm.mType

-- | Get visual treatment.
modeVisualTreatment :: BrandMode -> ModeVisualTreatment
modeVisualTreatment bm = bm.visualTreatment

-- | Get approved contexts.
modeApprovedContexts :: BrandMode -> Array String
modeApprovedContexts bm = bm.approvedContexts

-- | Get color scheme.
modeColorScheme :: BrandMode -> SystemColorScheme
modeColorScheme bm = bm.colorScheme

-- | Get priority.
modePriority :: BrandMode -> ModePriority
modePriority bm = bm.priority

-- | Get trigger conditions.
modeTriggerConditions :: BrandMode -> Array TriggerCondition
modeTriggerConditions bm = bm.triggerConditions

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // mode transition rule
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rule for transitioning between modes.
type ModeTransitionRule =
  { fromMode :: String         -- Source mode name
  , toMode :: String           -- Target mode name
  , condition :: String        -- When this transition is allowed
  }

-- | Create mode transition rule.
mkModeTransitionRule :: String -> String -> String -> Maybe ModeTransitionRule
mkModeTransitionRule from to condition =
  if String.length from >= 1 
     && String.length to >= 1 
     && String.length condition >= 1
    then Just
      { fromMode: from
      , toMode: to
      , condition: condition
      }
    else Nothing

-- | Get source mode.
transitionFromMode :: ModeTransitionRule -> String
transitionFromMode mtr = mtr.fromMode

-- | Get target mode.
transitionToMode :: ModeTransitionRule -> String
transitionToMode mtr = mtr.toMode

-- | Get transition condition.
transitionCondition :: ModeTransitionRule -> String
transitionCondition mtr = mtr.condition

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // modes specification
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete modes specification for a brand.
type ModesSpecification =
  { modes :: Array BrandMode
  , defaultModeName :: String       -- Name of the default mode
  , transitionRules :: Array ModeTransitionRule
  , designPrinciple :: String       -- Overarching design principle
  }

-- | Create modes specification.
mkModesSpecification
  :: Array BrandMode
  -> String
  -> Array ModeTransitionRule
  -> String
  -> Maybe ModesSpecification
mkModesSpecification modes defaultName transitions principle =
  if Array.length modes >= 1 
     && String.length defaultName >= 1 
     && String.length principle >= 1
    then Just
      { modes: modes
      , defaultModeName: defaultName
      , transitionRules: transitions
      , designPrinciple: principle
      }
    else Nothing

-- | Get all modes.
specModes :: ModesSpecification -> Array BrandMode
specModes ms = ms.modes

-- | Get default mode name.
specDefaultMode :: ModesSpecification -> String
specDefaultMode ms = ms.defaultModeName

-- | Get transition rules.
specTransitionRules :: ModesSpecification -> Array ModeTransitionRule
specTransitionRules ms = ms.transitionRules

-- | Get design principle.
specDesignPrinciple :: ModesSpecification -> String
specDesignPrinciple ms = ms.designPrinciple
