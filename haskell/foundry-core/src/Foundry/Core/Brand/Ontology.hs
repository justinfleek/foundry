{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                             // foundry // core // brand // ontology
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Ontology
Description : Brand ontology for knowledge graph integration
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines the brand ontology schema for COMPASS knowledge graph export.
Maps brand components to entities, relationships, and properties
suitable for graph-based reasoning and agent queries.

== COMPASS Integration

This module enables export to COMPASS knowledge graph:
- Entities: Brand, Color, Font, Logo, etc.
- Relations: hasColor, usesFont, definedBy, etc.
- Properties: Strongly typed values

== Dependencies

Requires: vector, text, aeson, uuid
Required by: COMPASS export, MAESTRO agents

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Ontology
  ( -- * Entity Types
    EntityType (..)
  , entityTypeToText
  , textToEntityType

    -- * Relation Types
  , RelationType (..)
  , relationTypeToText

    -- * Property Types
  , PropertyType (..)
  , PropertyValue (..)

    -- * Entity Definition
  , EntityId (..)
  , Entity (..)
  , mkEntity

    -- * Relation Definition
  , Relation (..)
  , mkRelation

    -- * Ontology
  , BrandOntology (..)
  , mkBrandOntology
  , emptyOntology

    -- * Conversion
  , brandToOntology
  , ontologyToNDJSON
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.=))
import Data.Aeson qualified as Aeson
import Data.Aeson.Key qualified as Key
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Char8 qualified as LBS
import Data.Text (Text)
import Data.Text qualified as T
import Data.UUID (UUID)
import Data.UUID qualified
import Data.Set qualified as Set
import Data.Word qualified
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.Identity (BrandId (..), BrandName (..), brandIdToUUID)
import Foundry.Core.Brand.Complete (CompleteBrand (..))
import Foundry.Core.Brand.Palette (BrandPalette (..), BrandColor (..), ColorRole (..), OKLCH (..))
import Foundry.Core.Brand.Typography (Typography (..), FontFamily (..))
import Foundry.Core.Brand.Voice (BrandVoice (..), TraitSet (..), Trait (..))
import Foundry.Core.Brand.Tagline (TaglineSet (..), PrimaryTagline (..), Tagline (..), TaglineText (..))

--------------------------------------------------------------------------------
-- Entity Types
--------------------------------------------------------------------------------

-- | Types of entities in the brand ontology
data EntityType
  = EntityBrand
    -- ^ Top-level brand entity
  | EntityColor
    -- ^ Color definition
  | EntityFont
    -- ^ Font family
  | EntityLogo
    -- ^ Logo component
  | EntityTagline
    -- ^ Tagline text
  | EntityValue
    -- ^ Brand value
  | EntityTrait
    -- ^ Personality trait
  | EntityCustomer
    -- ^ Customer segment
  | EntityTheme
    -- ^ Theme definition
  | EntityGradient
    -- ^ Gradient definition
  | EntitySpacing
    -- ^ Spacing token
  | EntityBreakpoint
    -- ^ Responsive breakpoint
  | EntityShadow
    -- ^ Shadow definition
  | EntityAsset
    -- ^ Image/asset reference
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON EntityType where
  toJSON = toJSON . entityTypeToText

instance FromJSON EntityType where
  parseJSON = withText "EntityType" $ \t ->
    pure $ textToEntityType t

-- | Convert entity type to text
entityTypeToText :: EntityType -> Text
entityTypeToText EntityBrand = "Brand"
entityTypeToText EntityColor = "Color"
entityTypeToText EntityFont = "Font"
entityTypeToText EntityLogo = "Logo"
entityTypeToText EntityTagline = "Tagline"
entityTypeToText EntityValue = "Value"
entityTypeToText EntityTrait = "Trait"
entityTypeToText EntityCustomer = "Customer"
entityTypeToText EntityTheme = "Theme"
entityTypeToText EntityGradient = "Gradient"
entityTypeToText EntitySpacing = "Spacing"
entityTypeToText EntityBreakpoint = "Breakpoint"
entityTypeToText EntityShadow = "Shadow"
entityTypeToText EntityAsset = "Asset"

-- | Parse entity type from text
textToEntityType :: Text -> EntityType
textToEntityType "Brand" = EntityBrand
textToEntityType "Color" = EntityColor
textToEntityType "Font" = EntityFont
textToEntityType "Logo" = EntityLogo
textToEntityType "Tagline" = EntityTagline
textToEntityType "Value" = EntityValue
textToEntityType "Trait" = EntityTrait
textToEntityType "Customer" = EntityCustomer
textToEntityType "Theme" = EntityTheme
textToEntityType "Gradient" = EntityGradient
textToEntityType "Spacing" = EntitySpacing
textToEntityType "Breakpoint" = EntityBreakpoint
textToEntityType "Shadow" = EntityShadow
textToEntityType "Asset" = EntityAsset
textToEntityType _ = EntityBrand

--------------------------------------------------------------------------------
-- Relation Types
--------------------------------------------------------------------------------

-- | Types of relations between entities
data RelationType
  = HasColor
    -- ^ Brand has color
  | HasPrimaryColor
    -- ^ Brand has primary color
  | HasAccentColor
    -- ^ Brand has accent color
  | UsesFont
    -- ^ Brand uses font
  | UsesHeadingFont
    -- ^ Brand uses font for headings
  | UsesBodyFont
    -- ^ Brand uses font for body
  | HasLogo
    -- ^ Brand has logo
  | HasTagline
    -- ^ Brand has tagline
  | HasPrimaryTagline
    -- ^ Brand has primary tagline
  | HasValue
    -- ^ Brand has value
  | HasTrait
    -- ^ Brand has personality trait
  | TargetsCustomer
    -- ^ Brand targets customer segment
  | HasTheme
    -- ^ Brand has theme
  | HasGradient
    -- ^ Brand has gradient
  | ContrastsWith
    -- ^ Color contrasts with another
  | ComplementsColor
    -- ^ Color complements another
  | DerivedFrom
    -- ^ Entity derived from another
  | DefinedBy
    -- ^ Entity defined by source
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON RelationType where
  toJSON = toJSON . relationTypeToText

instance FromJSON RelationType where
  parseJSON = withText "RelationType" $ \t ->
    pure $ case t of
      "hasColor" -> HasColor
      "hasPrimaryColor" -> HasPrimaryColor
      "hasAccentColor" -> HasAccentColor
      "usesFont" -> UsesFont
      "usesHeadingFont" -> UsesHeadingFont
      "usesBodyFont" -> UsesBodyFont
      "hasLogo" -> HasLogo
      "hasTagline" -> HasTagline
      "hasPrimaryTagline" -> HasPrimaryTagline
      "hasValue" -> HasValue
      "hasTrait" -> HasTrait
      "targetsCustomer" -> TargetsCustomer
      "hasTheme" -> HasTheme
      "hasGradient" -> HasGradient
      "contrastsWith" -> ContrastsWith
      "complementsColor" -> ComplementsColor
      "derivedFrom" -> DerivedFrom
      _ -> DefinedBy

-- | Convert relation type to text
relationTypeToText :: RelationType -> Text
relationTypeToText HasColor = "hasColor"
relationTypeToText HasPrimaryColor = "hasPrimaryColor"
relationTypeToText HasAccentColor = "hasAccentColor"
relationTypeToText UsesFont = "usesFont"
relationTypeToText UsesHeadingFont = "usesHeadingFont"
relationTypeToText UsesBodyFont = "usesBodyFont"
relationTypeToText HasLogo = "hasLogo"
relationTypeToText HasTagline = "hasTagline"
relationTypeToText HasPrimaryTagline = "hasPrimaryTagline"
relationTypeToText HasValue = "hasValue"
relationTypeToText HasTrait = "hasTrait"
relationTypeToText TargetsCustomer = "targetsCustomer"
relationTypeToText HasTheme = "hasTheme"
relationTypeToText HasGradient = "hasGradient"
relationTypeToText ContrastsWith = "contrastsWith"
relationTypeToText ComplementsColor = "complementsColor"
relationTypeToText DerivedFrom = "derivedFrom"
relationTypeToText DefinedBy = "definedBy"

--------------------------------------------------------------------------------
-- Property Types
--------------------------------------------------------------------------------

-- | Property type definitions
data PropertyType
  = PropText
  | PropNumber
  | PropBoolean
  | PropColor
  | PropURL
  | PropTimestamp
  | PropJSON
  deriving stock (Eq, Show, Generic)

instance ToJSON PropertyType where
  toJSON PropText = "text"
  toJSON PropNumber = "number"
  toJSON PropBoolean = "boolean"
  toJSON PropColor = "color"
  toJSON PropURL = "url"
  toJSON PropTimestamp = "timestamp"
  toJSON PropJSON = "json"

-- | Property value (tagged union)
data PropertyValue
  = PVText !Text
  | PVNumber !Double
  | PVBoolean !Bool
  | PVJSON !Aeson.Value
  deriving stock (Eq, Show, Generic)

instance ToJSON PropertyValue where
  toJSON (PVText t) = toJSON t
  toJSON (PVNumber n) = toJSON n
  toJSON (PVBoolean b) = toJSON b
  toJSON (PVJSON v) = v

instance FromJSON PropertyValue where
  parseJSON v = case v of
    Aeson.String t -> pure $ PVText t
    Aeson.Number n -> pure $ PVNumber (realToFrac n)
    Aeson.Bool b -> pure $ PVBoolean b
    _ -> pure $ PVJSON v

--------------------------------------------------------------------------------
-- Entity Definition
--------------------------------------------------------------------------------

-- | Entity identifier (UUID5)
newtype EntityId = EntityId UUID
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (ToJSON, FromJSON)

-- | An entity in the ontology
data Entity = Entity
  { entityId         :: !EntityId
    -- ^ Unique identifier
  , entityType       :: !EntityType
    -- ^ Type of entity
  , entityLabel      :: !Text
    -- ^ Human-readable label
  , entityProperties :: !(Vector (Text, PropertyValue))
    -- ^ Key-value properties
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Entity where
  toJSON Entity{..} = object
    [ "id"         .= entityId
    , "type"       .= entityType
    , "label"      .= entityLabel
    , "properties" .= object (map (\(k, v) -> Key.fromText k .= v) (V.toList entityProperties))
    ]

instance FromJSON Entity where
  parseJSON = withObject "Entity" $ \v -> Entity
    <$> v .: "id"
    <*> v .: "type"
    <*> v .: "label"
    <*> pure V.empty  -- Simplified for now

-- | Smart constructor
mkEntity :: EntityId -> EntityType -> Text -> Vector (Text, PropertyValue) -> Entity
mkEntity = Entity

--------------------------------------------------------------------------------
-- Relation Definition
--------------------------------------------------------------------------------

-- | A relation between two entities
data Relation = Relation
  { relFrom       :: !EntityId
    -- ^ Source entity
  , relTo         :: !EntityId
    -- ^ Target entity
  , relType       :: !RelationType
    -- ^ Type of relation
  , relProperties :: !(Vector (Text, PropertyValue))
    -- ^ Additional properties
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON Relation where
  toJSON Relation{..} = object
    [ "from"       .= relFrom
    , "to"         .= relTo
    , "type"       .= relType
    , "properties" .= object (map (\(k, v) -> Key.fromText k .= v) (V.toList relProperties))
    ]

instance FromJSON Relation where
  parseJSON = withObject "Relation" $ \v -> Relation
    <$> v .: "from"
    <*> v .: "to"
    <*> v .: "type"
    <*> pure V.empty

-- | Smart constructor
mkRelation :: EntityId -> EntityId -> RelationType -> Vector (Text, PropertyValue) -> Relation
mkRelation = Relation

--------------------------------------------------------------------------------
-- Ontology
--------------------------------------------------------------------------------

-- | Complete brand ontology
data BrandOntology = BrandOntology
  { ontologyBrandId  :: !BrandId
    -- ^ Source brand ID
  , ontologyEntities :: !(Vector Entity)
    -- ^ All entities
  , ontologyRelations :: !(Vector Relation)
    -- ^ All relations
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandOntology where
  toJSON BrandOntology{..} = object
    [ "brandId"   .= ontologyBrandId
    , "entities"  .= ontologyEntities
    , "relations" .= ontologyRelations
    ]

instance FromJSON BrandOntology where
  parseJSON = withObject "BrandOntology" $ \v -> BrandOntology
    <$> v .: "brandId"
    <*> v .: "entities"
    <*> v .: "relations"

-- | Smart constructor
mkBrandOntology :: BrandId -> Vector Entity -> Vector Relation -> BrandOntology
mkBrandOntology = BrandOntology

-- | Empty ontology
emptyOntology :: BrandId -> BrandOntology
emptyOntology bid = BrandOntology bid V.empty V.empty

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert a CompleteBrand to an ontology
--
-- Creates entities for:
-- - Brand (root entity)
-- - Colors (from palette)
-- - Fonts (heading and body)
-- - Tagline (primary)
-- - Personality traits
--
-- Creates relations:
-- - Brand -> hasColor -> Color
-- - Brand -> usesFont -> Font
-- - Brand -> hasTagline -> Tagline
-- - Brand -> hasTrait -> Trait
brandToOntology :: CompleteBrand -> BrandOntology
brandToOntology brand = BrandOntology
  { ontologyBrandId = cbId brand
  , ontologyEntities = brandEntity `V.cons` (colorEntities V.++ fontEntities V.++ taglineEntities V.++ traitEntities)
  , ontologyRelations = colorRelations V.++ fontRelations V.++ taglineRelations V.++ traitRelations
  }
  where
    brandUUID = brandIdToUUID (cbId brand)
    brandEntityId = EntityId brandUUID
    
    -- Brand entity
    brandEntity = Entity
      { entityId = brandEntityId
      , entityType = EntityBrand
      , entityLabel = unBrandName (cbName brand)
      , entityProperties = V.empty
      }
    
    -- Color entities and relations
    colors = unBrandPalette (cbPalette brand)
    (colorEntities, colorRelations) = V.unzip $ V.imap makeColorPair (V.fromList colors)
    
    makeColorPair :: Int -> BrandColor -> (Entity, Relation)
    makeColorPair i (BrandColor oklch role) = (entity, relation)
      where
        colorId = EntityId $ makeUUID5 brandUUID ("color-" <> T.pack (show i))
        entity = Entity
          { entityId = colorId
          , entityType = EntityColor
          , entityLabel = colorRoleToText role
          , entityProperties = V.fromList
              [ ("oklch_l", PVNumber (oklchL oklch))
              , ("oklch_c", PVNumber (oklchC oklch))
              , ("oklch_h", PVNumber (oklchH oklch))
              , ("oklch_a", PVNumber (oklchA oklch))
              , ("role", PVText (colorRoleToText role))
              ]
          }
        relType = case role of
          Primary -> HasPrimaryColor
          Accent -> HasAccentColor
          _ -> HasColor
        relation = Relation
          { relFrom = brandEntityId
          , relTo = colorId
          , relType = relType
          , relProperties = V.empty
          }
    
    -- Font entities and relations
    typo = cbTypography brand
    fontEntities = V.fromList [headingFontEntity, bodyFontEntity]
    fontRelations = V.fromList [headingFontRel, bodyFontRel]
    
    headingFontId = EntityId $ makeUUID5 brandUUID "font-heading"
    headingFontEntity = Entity
      { entityId = headingFontId
      , entityType = EntityFont
      , entityLabel = fontFamilyName (typographyHeadingFamily typo)
      , entityProperties = V.fromList
          [ ("role", PVText "heading")
          , ("family", PVText (fontFamilyName (typographyHeadingFamily typo)))
          ]
      }
    headingFontRel = Relation
      { relFrom = brandEntityId
      , relTo = headingFontId
      , relType = UsesHeadingFont
      , relProperties = V.empty
      }
    
    bodyFontId = EntityId $ makeUUID5 brandUUID "font-body"
    bodyFontEntity = Entity
      { entityId = bodyFontId
      , entityType = EntityFont
      , entityLabel = fontFamilyName (typographyBodyFamily typo)
      , entityProperties = V.fromList
          [ ("role", PVText "body")
          , ("family", PVText (fontFamilyName (typographyBodyFamily typo)))
          ]
      }
    bodyFontRel = Relation
      { relFrom = brandEntityId
      , relTo = bodyFontId
      , relType = UsesBodyFont
      , relProperties = V.empty
      }
    
    -- Tagline entity and relation
    taglines = cbTaglines brand
    primaryTagline = taglineSetPrimary taglines
    primaryTaglineInner = unPrimaryTagline primaryTagline
    taglineTextValue = unTaglineText (Foundry.Core.Brand.Tagline.taglineText primaryTaglineInner)
    taglineId = EntityId $ makeUUID5 brandUUID "tagline-primary"
    
    taglineEntities = V.singleton Entity
      { entityId = taglineId
      , entityType = EntityTagline
      , entityLabel = taglineTextValue
      , entityProperties = V.fromList
          [ ("text", PVText taglineTextValue)
          , ("primary", PVBoolean True)
          ]
      }
    taglineRelations = V.singleton Relation
      { relFrom = brandEntityId
      , relTo = taglineId
      , relType = HasPrimaryTagline
      , relProperties = V.empty
      }
    
    -- Trait entities and relations
    voice = cbVoice brand
    traits = unTraitSet (brandVoiceTraits voice)
    (traitEntities, traitRelations) = V.unzip $ V.imap makeTraitPair (V.fromList (map unTrait (toList traits)))
    
    makeTraitPair :: Int -> Text -> (Entity, Relation)
    makeTraitPair i traitText = (entity, relation)
      where
        traitId = EntityId $ makeUUID5 brandUUID ("trait-" <> T.pack (show i))
        entity = Entity
          { entityId = traitId
          , entityType = EntityTrait
          , entityLabel = traitText
          , entityProperties = V.fromList
              [ ("trait", PVText traitText)
              ]
          }
        relation = Relation
          { relFrom = brandEntityId
          , relTo = traitId
          , relType = HasTrait
          , relProperties = V.empty
          }

-- | Helper to make deterministic UUID5 from brand UUID and a suffix
--
-- Uses a simple hash-based approach for deterministic UUID generation.
-- In production, should use proper UUID5 namespace generation.
makeUUID5 :: UUID -> Text -> UUID
makeUUID5 namespace name = 
  let combined = T.pack (show namespace) <> "-" <> name
      hash = abs (fromIntegral (T.foldl' (\acc c -> acc * 31 + fromEnum c) 0 combined) :: Int)
      w1 = fromIntegral hash :: Data.Word.Word32
      w2 = fromIntegral (hash `div` 2) :: Data.Word.Word32
      w3 = fromIntegral (hash `div` 3) :: Data.Word.Word32
      w4 = fromIntegral (hash `div` 5) :: Data.Word.Word32
  in Data.UUID.fromWords w1 w2 w3 w4

-- | Helper to convert Set to list
toList :: Set.Set a -> [a]
toList = Set.toList

-- | Convert color role to text
colorRoleToText :: ColorRole -> Text
colorRoleToText Primary = "primary"
colorRoleToText Secondary = "secondary"
colorRoleToText Tertiary = "tertiary"
colorRoleToText Accent = "accent"
colorRoleToText Neutral = "neutral"
colorRoleToText Background = "background"
colorRoleToText Surface = "surface"
colorRoleToText Error = "error"
colorRoleToText Warning = "warning"
colorRoleToText Success = "success"

-- | Export ontology to NDJSON format (one JSON object per line)
ontologyToNDJSON :: BrandOntology -> ByteString
ontologyToNDJSON BrandOntology{..} = 
  LBS.unlines $ entityLines <> relationLines
  where
    entityLines = V.toList $ V.map Aeson.encode ontologyEntities
    relationLines = V.toList $ V.map Aeson.encode ontologyRelations
