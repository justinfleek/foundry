{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                         // foundry // core // brand // agentcontext
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.AgentContext
Description : Brand context for MAESTRO agents
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the brand context that MAESTRO agents receive when executing tasks.
This provides a focused subset of brand data relevant to agent operations,
with capability-based access control.

== MAESTRO Integration

Each of MAESTRO's 64 agents receives an AgentBrandContext that:
- Contains only the brand data relevant to the agent's role
- Includes permission tokens for brand asset access
- Provides quick lookups for common operations
- Supports caching and invalidation

== Dependencies

Requires: vector, text, aeson, uuid
Required by: COMPASS, MAESTRO agents

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.AgentContext
  ( -- * Agent Roles
    AgentRole (..)
  , roleToText

    -- * Brand Access Level
  , BrandAccessLevel (..)
  , accessLevelToText

    -- * Brand Capability
  , BrandCapability (..)
  , capabilityToText
  , CapabilitySet (..)
  , hasCapability
  , grantCapability
  , revokeCapability
  , emptyCapabilities
  , allCapabilities

    -- * Quick Lookups
  , BrandQuickLookup (..)
  , mkQuickLookup

    -- * Agent Brand Context
  , AgentBrandContext (..)
  , mkAgentBrandContext
  , contextForRole

    -- * Context Operations
  , canAccessColors
  , canAccessTypography
  , canAccessLogo
  , canAccessVoice
  , canModifyBrand
  , getPrimaryColor
  , getHeadingFont
  , getTagline
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.=))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.Identity (BrandId, BrandName, Domain)
import Foundry.Core.Brand.Palette (OKLCH, ColorRole (..))

--------------------------------------------------------------------------------
-- Agent Roles
--------------------------------------------------------------------------------

-- | MAESTRO agent roles that interact with brand data
data AgentRole
  = RoleDesigner
    -- ^ Visual design agent (full brand access)
  | RoleCopywriter
    -- ^ Content/copy agent (voice, taglines, editorial)
  | RoleMarketer
    -- ^ Marketing agent (taglines, colors, customer segments)
  | RoleDeveloper
    -- ^ Development agent (tokens, technical specs)
  | RoleAnalyst
    -- ^ Analytics agent (read-only, metrics)
  | RoleAdmin
    -- ^ Administrative agent (full access)
  | RoleViewer
    -- ^ Read-only viewer
  | RoleCustom !Text
    -- ^ Custom role
  deriving stock (Eq, Ord, Show, Generic)

instance ToJSON AgentRole where
  toJSON RoleDesigner = "designer"
  toJSON RoleCopywriter = "copywriter"
  toJSON RoleMarketer = "marketer"
  toJSON RoleDeveloper = "developer"
  toJSON RoleAnalyst = "analyst"
  toJSON RoleAdmin = "admin"
  toJSON RoleViewer = "viewer"
  toJSON (RoleCustom t) = toJSON t

instance FromJSON AgentRole where
  parseJSON = withText "AgentRole" $ \t ->
    pure $ case t of
      "designer" -> RoleDesigner
      "copywriter" -> RoleCopywriter
      "marketer" -> RoleMarketer
      "developer" -> RoleDeveloper
      "analyst" -> RoleAnalyst
      "admin" -> RoleAdmin
      "viewer" -> RoleViewer
      custom -> RoleCustom custom

-- | Convert role to text
roleToText :: AgentRole -> Text
roleToText RoleDesigner = "designer"
roleToText RoleCopywriter = "copywriter"
roleToText RoleMarketer = "marketer"
roleToText RoleDeveloper = "developer"
roleToText RoleAnalyst = "analyst"
roleToText RoleAdmin = "admin"
roleToText RoleViewer = "viewer"
roleToText (RoleCustom t) = t

--------------------------------------------------------------------------------
-- Brand Access Level
--------------------------------------------------------------------------------

-- | Access level for brand data
data BrandAccessLevel
  = AccessNone
    -- ^ No access
  | AccessRead
    -- ^ Read-only access
  | AccessWrite
    -- ^ Read and write access
  | AccessAdmin
    -- ^ Full administrative access
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON BrandAccessLevel where
  toJSON AccessNone = "none"
  toJSON AccessRead = "read"
  toJSON AccessWrite = "write"
  toJSON AccessAdmin = "admin"

instance FromJSON BrandAccessLevel where
  parseJSON = withText "BrandAccessLevel" $ \case
    "none" -> pure AccessNone
    "read" -> pure AccessRead
    "write" -> pure AccessWrite
    "admin" -> pure AccessAdmin
    _ -> pure AccessNone

-- | Convert access level to text
accessLevelToText :: BrandAccessLevel -> Text
accessLevelToText AccessNone = "none"
accessLevelToText AccessRead = "read"
accessLevelToText AccessWrite = "write"
accessLevelToText AccessAdmin = "admin"

--------------------------------------------------------------------------------
-- Brand Capability
--------------------------------------------------------------------------------

-- | Individual brand capabilities
data BrandCapability
  = CapColors
    -- ^ Access color palette
  | CapTypography
    -- ^ Access typography settings
  | CapLogo
    -- ^ Access logo assets
  | CapVoice
    -- ^ Access voice guidelines
  | CapEditorial
    -- ^ Access editorial style
  | CapTaglines
    -- ^ Access taglines
  | CapStrategy
    -- ^ Access strategic layer
  | CapCustomers
    -- ^ Access customer segments
  | CapThemes
    -- ^ Access theme definitions
  | CapLayout
    -- ^ Access layout system
  | CapMaterial
    -- ^ Access material system
  | CapImagery
    -- ^ Access imagery guidelines
  | CapGradients
    -- ^ Access gradient specs
  | CapSpacing
    -- ^ Access spacing scale
  | CapModify
    -- ^ Can modify brand data
  | CapExport
    -- ^ Can export brand data
  | CapAdmin
    -- ^ Administrative capabilities
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON BrandCapability where
  toJSON = toJSON . capabilityToText

instance FromJSON BrandCapability where
  parseJSON = withText "BrandCapability" $ \t ->
    pure $ case t of
      "colors" -> CapColors
      "typography" -> CapTypography
      "logo" -> CapLogo
      "voice" -> CapVoice
      "editorial" -> CapEditorial
      "taglines" -> CapTaglines
      "strategy" -> CapStrategy
      "customers" -> CapCustomers
      "themes" -> CapThemes
      "layout" -> CapLayout
      "material" -> CapMaterial
      "imagery" -> CapImagery
      "gradients" -> CapGradients
      "spacing" -> CapSpacing
      "modify" -> CapModify
      "export" -> CapExport
      _ -> CapAdmin

-- | Convert capability to text
capabilityToText :: BrandCapability -> Text
capabilityToText CapColors = "colors"
capabilityToText CapTypography = "typography"
capabilityToText CapLogo = "logo"
capabilityToText CapVoice = "voice"
capabilityToText CapEditorial = "editorial"
capabilityToText CapTaglines = "taglines"
capabilityToText CapStrategy = "strategy"
capabilityToText CapCustomers = "customers"
capabilityToText CapThemes = "themes"
capabilityToText CapLayout = "layout"
capabilityToText CapMaterial = "material"
capabilityToText CapImagery = "imagery"
capabilityToText CapGradients = "gradients"
capabilityToText CapSpacing = "spacing"
capabilityToText CapModify = "modify"
capabilityToText CapExport = "export"
capabilityToText CapAdmin = "admin"

-- | Set of capabilities
newtype CapabilitySet = CapabilitySet (Set BrandCapability)
  deriving stock (Eq, Show, Generic)
  deriving newtype (Semigroup, Monoid)

instance ToJSON CapabilitySet where
  toJSON (CapabilitySet caps) = toJSON $ Set.toList caps

instance FromJSON CapabilitySet where
  parseJSON v = CapabilitySet . Set.fromList <$> parseJSON v

-- | Check if capability is present
hasCapability :: BrandCapability -> CapabilitySet -> Bool
hasCapability cap (CapabilitySet caps) = Set.member cap caps

-- | Grant a capability
grantCapability :: BrandCapability -> CapabilitySet -> CapabilitySet
grantCapability cap (CapabilitySet caps) = CapabilitySet (Set.insert cap caps)

-- | Revoke a capability
revokeCapability :: BrandCapability -> CapabilitySet -> CapabilitySet
revokeCapability cap (CapabilitySet caps) = CapabilitySet (Set.delete cap caps)

-- | Empty capability set
emptyCapabilities :: CapabilitySet
emptyCapabilities = CapabilitySet Set.empty

-- | All capabilities
allCapabilities :: CapabilitySet
allCapabilities = CapabilitySet $ Set.fromList [minBound .. maxBound]

--------------------------------------------------------------------------------
-- Quick Lookups
--------------------------------------------------------------------------------

-- | Pre-computed quick lookups for common brand queries
data BrandQuickLookup = BrandQuickLookup
  { qlPrimaryColor   :: !(Maybe OKLCH)
    -- ^ Primary brand color
  , qlAccentColor    :: !(Maybe OKLCH)
    -- ^ Accent color
  , qlBackgroundColor :: !(Maybe OKLCH)
    -- ^ Background color
  , qlHeadingFont    :: !(Maybe Text)
    -- ^ Heading font family name
  , qlBodyFont       :: !(Maybe Text)
    -- ^ Body font family name
  , qlPrimaryTagline :: !(Maybe Text)
    -- ^ Primary tagline text
  , qlBrandName      :: !BrandName
    -- ^ Brand name
  , qlDomain         :: !Domain
    -- ^ Brand domain
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandQuickLookup where
  toJSON BrandQuickLookup{..} = object
    [ "primaryColor"    .= qlPrimaryColor
    , "accentColor"     .= qlAccentColor
    , "backgroundColor" .= qlBackgroundColor
    , "headingFont"     .= qlHeadingFont
    , "bodyFont"        .= qlBodyFont
    , "primaryTagline"  .= qlPrimaryTagline
    , "brandName"       .= qlBrandName
    , "domain"          .= qlDomain
    ]

instance FromJSON BrandQuickLookup where
  parseJSON = withObject "BrandQuickLookup" $ \v -> BrandQuickLookup
    <$> v .: "primaryColor"
    <*> v .: "accentColor"
    <*> v .: "backgroundColor"
    <*> v .: "headingFont"
    <*> v .: "bodyFont"
    <*> v .: "primaryTagline"
    <*> v .: "brandName"
    <*> v .: "domain"

-- | Create quick lookup (simplified constructor)
mkQuickLookup :: BrandName -> Domain -> BrandQuickLookup
mkQuickLookup name domain = BrandQuickLookup
  { qlPrimaryColor = Nothing
  , qlAccentColor = Nothing
  , qlBackgroundColor = Nothing
  , qlHeadingFont = Nothing
  , qlBodyFont = Nothing
  , qlPrimaryTagline = Nothing
  , qlBrandName = name
  , qlDomain = domain
  }

--------------------------------------------------------------------------------
-- Agent Brand Context
--------------------------------------------------------------------------------

-- | Complete brand context for an agent
data AgentBrandContext = AgentBrandContext
  { abcBrandId      :: !BrandId
    -- ^ Brand identifier
  , abcRole         :: !AgentRole
    -- ^ Agent's role
  , abcAccessLevel  :: !BrandAccessLevel
    -- ^ Overall access level
  , abcCapabilities :: !CapabilitySet
    -- ^ Specific capabilities
  , abcQuickLookup  :: !BrandQuickLookup
    -- ^ Quick lookup cache
  , abcColorPalette :: !(Vector (ColorRole, OKLCH))
    -- ^ Accessible colors (if permitted)
  , abcFontFamilies :: !(Vector Text)
    -- ^ Accessible fonts (if permitted)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON AgentBrandContext where
  toJSON AgentBrandContext{..} = object
    [ "brandId"      .= abcBrandId
    , "role"         .= abcRole
    , "accessLevel"  .= abcAccessLevel
    , "capabilities" .= abcCapabilities
    , "quickLookup"  .= abcQuickLookup
    , "colorPalette" .= abcColorPalette
    , "fontFamilies" .= abcFontFamilies
    ]

instance FromJSON AgentBrandContext where
  parseJSON = withObject "AgentBrandContext" $ \v -> AgentBrandContext
    <$> v .: "brandId"
    <*> v .: "role"
    <*> v .: "accessLevel"
    <*> v .: "capabilities"
    <*> v .: "quickLookup"
    <*> v .: "colorPalette"
    <*> v .: "fontFamilies"

-- | Create agent brand context
mkAgentBrandContext
  :: BrandId
  -> AgentRole
  -> BrandAccessLevel
  -> CapabilitySet
  -> BrandQuickLookup
  -> AgentBrandContext
mkAgentBrandContext bid role access caps lookup' = AgentBrandContext
  { abcBrandId = bid
  , abcRole = role
  , abcAccessLevel = access
  , abcCapabilities = caps
  , abcQuickLookup = lookup'
  , abcColorPalette = V.empty
  , abcFontFamilies = V.empty
  }

-- | Get default context for a role
contextForRole :: AgentRole -> BrandId -> BrandQuickLookup -> AgentBrandContext
contextForRole role bid lookup' = AgentBrandContext
  { abcBrandId = bid
  , abcRole = role
  , abcAccessLevel = levelForRole role
  , abcCapabilities = capsForRole role
  , abcQuickLookup = lookup'
  , abcColorPalette = V.empty
  , abcFontFamilies = V.empty
  }
  where
    levelForRole :: AgentRole -> BrandAccessLevel
    levelForRole RoleAdmin = AccessAdmin
    levelForRole RoleDesigner = AccessWrite
    levelForRole RoleCopywriter = AccessWrite
    levelForRole RoleMarketer = AccessRead
    levelForRole RoleDeveloper = AccessRead
    levelForRole RoleAnalyst = AccessRead
    levelForRole RoleViewer = AccessRead
    levelForRole (RoleCustom _) = AccessRead
    
    capsForRole :: AgentRole -> CapabilitySet
    capsForRole RoleAdmin = allCapabilities
    capsForRole RoleDesigner = CapabilitySet $ Set.fromList
      [CapColors, CapTypography, CapLogo, CapThemes, CapLayout, CapMaterial, CapImagery, CapGradients, CapSpacing, CapModify]
    capsForRole RoleCopywriter = CapabilitySet $ Set.fromList
      [CapVoice, CapEditorial, CapTaglines, CapStrategy, CapModify]
    capsForRole RoleMarketer = CapabilitySet $ Set.fromList
      [CapColors, CapTaglines, CapCustomers, CapLogo, CapExport]
    capsForRole RoleDeveloper = CapabilitySet $ Set.fromList
      [CapColors, CapTypography, CapSpacing, CapThemes, CapExport]
    capsForRole RoleAnalyst = CapabilitySet $ Set.fromList
      [CapColors, CapTypography, CapCustomers]
    capsForRole RoleViewer = emptyCapabilities
    capsForRole (RoleCustom _) = emptyCapabilities

--------------------------------------------------------------------------------
-- Context Operations
--------------------------------------------------------------------------------

-- | Check if agent can access colors
canAccessColors :: AgentBrandContext -> Bool
canAccessColors ctx = hasCapability CapColors (abcCapabilities ctx)

-- | Check if agent can access typography
canAccessTypography :: AgentBrandContext -> Bool
canAccessTypography ctx = hasCapability CapTypography (abcCapabilities ctx)

-- | Check if agent can access logo
canAccessLogo :: AgentBrandContext -> Bool
canAccessLogo ctx = hasCapability CapLogo (abcCapabilities ctx)

-- | Check if agent can access voice
canAccessVoice :: AgentBrandContext -> Bool
canAccessVoice ctx = hasCapability CapVoice (abcCapabilities ctx)

-- | Check if agent can modify brand
canModifyBrand :: AgentBrandContext -> Bool
canModifyBrand ctx = 
  hasCapability CapModify (abcCapabilities ctx) &&
  abcAccessLevel ctx >= AccessWrite

-- | Get primary color from context
getPrimaryColor :: AgentBrandContext -> Maybe OKLCH
getPrimaryColor = qlPrimaryColor . abcQuickLookup

-- | Get heading font from context
getHeadingFont :: AgentBrandContext -> Maybe Text
getHeadingFont = qlHeadingFont . abcQuickLookup

-- | Get primary tagline from context
getTagline :: AgentBrandContext -> Maybe Text
getTagline = qlPrimaryTagline . abcQuickLookup
