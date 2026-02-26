{-# LANGUAGE RecordWildCards #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                            // foundry // core // brand // hierarchy
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Brand.Hierarchy
Description : Brand hierarchy and sub-brand relationships
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Defines hierarchical brand structures for organizations with multiple
brands, sub-brands, product lines, or regional variations.

== Use Cases

- Parent company with multiple product brands
- Regional brand variations
- Brand extensions and sub-brands
- White-label brand derivatives

== Dependencies

Requires: vector, text, aeson
Required by: COMPASS, multi-brand systems

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Brand.Hierarchy
  ( -- * Hierarchy Types
    BrandRelation (..)
  , relationToText

    -- * Hierarchy Node
  , HierarchyNode (..)
  , mkHierarchyNode
  , isRoot
  , isLeaf

    -- * Brand Hierarchy
  , BrandHierarchy (..)
  , mkBrandHierarchy
  , emptyHierarchy
  , addNode
  , findNode
  , getChildren
  , getParent
  , getRoots
  , getLeaves
  , depth
  , flatten

    -- * Inheritance
  , InheritanceRule (..)
  , ComponentOverride (..)
  , resolveInheritance
  ) where

import Data.Aeson (FromJSON (..), ToJSON (..), object, withObject, withText, (.:), (.:?), (.=))
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Vector qualified as V
import GHC.Generics (Generic)

import Foundry.Core.Brand.Identity (BrandId)

--------------------------------------------------------------------------------
-- Hierarchy Types
--------------------------------------------------------------------------------

-- | Relationship types between brands
data BrandRelation
  = ParentBrand
    -- ^ Parent company/master brand
  | SubBrand
    -- ^ Sub-brand (endorsed)
  | ProductBrand
    -- ^ Product line brand
  | RegionalVariant
    -- ^ Regional/market variation
  | WhiteLabel
    -- ^ White-label derivative
  | Acquisition
    -- ^ Acquired brand
  | Partnership
    -- ^ Partner/co-brand
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

instance ToJSON BrandRelation where
  toJSON = toJSON . relationToText

instance FromJSON BrandRelation where
  parseJSON = withText "BrandRelation" $ \case
    "parent" -> pure ParentBrand
    "sub-brand" -> pure SubBrand
    "product" -> pure ProductBrand
    "regional" -> pure RegionalVariant
    "white-label" -> pure WhiteLabel
    "acquisition" -> pure Acquisition
    "partnership" -> pure Partnership
    _ -> pure SubBrand

-- | Convert relation to text
relationToText :: BrandRelation -> Text
relationToText ParentBrand = "parent"
relationToText SubBrand = "sub-brand"
relationToText ProductBrand = "product"
relationToText RegionalVariant = "regional"
relationToText WhiteLabel = "white-label"
relationToText Acquisition = "acquisition"
relationToText Partnership = "partnership"

--------------------------------------------------------------------------------
-- Hierarchy Node
--------------------------------------------------------------------------------

-- | A node in the brand hierarchy
data HierarchyNode = HierarchyNode
  { hnBrandId   :: !BrandId
    -- ^ Brand identifier
  , hnName      :: !Text
    -- ^ Display name
  , hnParent    :: !(Maybe BrandId)
    -- ^ Parent brand (Nothing for root)
  , hnRelation  :: !BrandRelation
    -- ^ Relationship to parent
  , hnChildren  :: !(Vector BrandId)
    -- ^ Child brand IDs
  , hnLevel     :: !Int
    -- ^ Depth in hierarchy (0 = root)
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON HierarchyNode where
  toJSON HierarchyNode{..} = object
    [ "brandId"  .= hnBrandId
    , "name"     .= hnName
    , "parent"   .= hnParent
    , "relation" .= hnRelation
    , "children" .= hnChildren
    , "level"    .= hnLevel
    ]

instance FromJSON HierarchyNode where
  parseJSON = withObject "HierarchyNode" $ \v -> HierarchyNode
    <$> v .: "brandId"
    <*> v .: "name"
    <*> v .:? "parent"
    <*> v .: "relation"
    <*> v .: "children"
    <*> v .: "level"

-- | Smart constructor
mkHierarchyNode 
  :: BrandId 
  -> Text 
  -> Maybe BrandId 
  -> BrandRelation 
  -> Vector BrandId 
  -> Int 
  -> HierarchyNode
mkHierarchyNode = HierarchyNode

-- | Check if node is a root (no parent)
isRoot :: HierarchyNode -> Bool
isRoot = (== Nothing) . hnParent

-- | Check if node is a leaf (no children)
isLeaf :: HierarchyNode -> Bool
isLeaf = V.null . hnChildren

--------------------------------------------------------------------------------
-- Brand Hierarchy
--------------------------------------------------------------------------------

-- | Complete brand hierarchy structure
data BrandHierarchy = BrandHierarchy
  { bhName     :: !Text
    -- ^ Hierarchy name (e.g., "Alphabet Inc.")
  , bhNodes    :: !(Vector HierarchyNode)
    -- ^ All nodes in hierarchy
  , bhMaxDepth :: !Int
    -- ^ Maximum depth of hierarchy
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON BrandHierarchy where
  toJSON BrandHierarchy{..} = object
    [ "name"     .= bhName
    , "nodes"    .= bhNodes
    , "maxDepth" .= bhMaxDepth
    ]

instance FromJSON BrandHierarchy where
  parseJSON = withObject "BrandHierarchy" $ \v -> BrandHierarchy
    <$> v .: "name"
    <*> v .: "nodes"
    <*> v .: "maxDepth"

-- | Smart constructor
mkBrandHierarchy :: Text -> Vector HierarchyNode -> BrandHierarchy
mkBrandHierarchy name nodes = BrandHierarchy
  { bhName = name
  , bhNodes = nodes
  , bhMaxDepth = computeMaxDepth nodes
  }
  where
    computeMaxDepth :: Vector HierarchyNode -> Int
    computeMaxDepth ns
      | V.null ns = 0
      | otherwise = V.maximum (V.map hnLevel ns)

-- | Empty hierarchy
emptyHierarchy :: Text -> BrandHierarchy
emptyHierarchy name = BrandHierarchy name V.empty 0

-- | Add a node to the hierarchy
addNode :: HierarchyNode -> BrandHierarchy -> BrandHierarchy
addNode node bh = bh
  { bhNodes = V.snoc (bhNodes bh) node
  , bhMaxDepth = max (bhMaxDepth bh) (hnLevel node)
  }

-- | Find a node by brand ID
findNode :: BrandId -> BrandHierarchy -> Maybe HierarchyNode
findNode bid = V.find (\n -> hnBrandId n == bid) . bhNodes

-- | Get children of a brand
getChildren :: BrandId -> BrandHierarchy -> Vector HierarchyNode
getChildren bid bh = case findNode bid bh of
  Nothing -> V.empty
  Just node -> V.mapMaybe (`findNode` bh) (hnChildren node)

-- | Get parent of a brand
getParent :: BrandId -> BrandHierarchy -> Maybe HierarchyNode
getParent bid bh = do
  node <- findNode bid bh
  parentId <- hnParent node
  findNode parentId bh

-- | Get all root nodes
getRoots :: BrandHierarchy -> Vector HierarchyNode
getRoots = V.filter isRoot . bhNodes

-- | Get all leaf nodes
getLeaves :: BrandHierarchy -> Vector HierarchyNode
getLeaves = V.filter isLeaf . bhNodes

-- | Get depth of a specific brand in hierarchy
depth :: BrandId -> BrandHierarchy -> Maybe Int
depth bid bh = hnLevel <$> findNode bid bh

-- | Flatten hierarchy to list (depth-first)
flatten :: BrandHierarchy -> Vector BrandId
flatten = V.map hnBrandId . bhNodes

--------------------------------------------------------------------------------
-- Inheritance
--------------------------------------------------------------------------------

-- | Rule for how components inherit from parent brands
data InheritanceRule
  = InheritAll
    -- ^ Inherit all parent values
  | InheritNone
    -- ^ Don't inherit (standalone)
  | InheritSelective !(Vector Text)
    -- ^ Inherit specific components only
  | InheritWithOverrides !(Vector ComponentOverride)
    -- ^ Inherit with specific overrides
  deriving stock (Eq, Show, Generic)

instance ToJSON InheritanceRule where
  toJSON InheritAll = object ["rule" .= ("all" :: Text)]
  toJSON InheritNone = object ["rule" .= ("none" :: Text)]
  toJSON (InheritSelective components) = object
    [ "rule" .= ("selective" :: Text)
    , "components" .= components
    ]
  toJSON (InheritWithOverrides overrides) = object
    [ "rule" .= ("overrides" :: Text)
    , "overrides" .= overrides
    ]

-- | Override for a specific component
data ComponentOverride = ComponentOverride
  { coComponent :: !Text
    -- ^ Component name (e.g., "palette", "typography")
  , coAction    :: !Text
    -- ^ Action: "replace", "merge", "extend"
  , coValue     :: !Text
    -- ^ Reference to override value
  }
  deriving stock (Eq, Show, Generic)

instance ToJSON ComponentOverride where
  toJSON ComponentOverride{..} = object
    [ "component" .= coComponent
    , "action"    .= coAction
    , "value"     .= coValue
    ]

instance FromJSON ComponentOverride where
  parseJSON = withObject "ComponentOverride" $ \v -> ComponentOverride
    <$> v .: "component"
    <*> v .: "action"
    <*> v .: "value"

-- | Resolve inheritance to get effective brand ID for a component
--
-- Returns the brand ID that should be used to look up the specified component,
-- walking up the hierarchy as needed based on the inheritance rule.
resolveInheritance :: BrandId -> Text -> InheritanceRule -> BrandHierarchy -> BrandId
resolveInheritance bid component rule hierarchy = case rule of
  InheritNone -> 
    -- No inheritance: always use own brand
    bid
  InheritAll -> 
    -- Full inheritance: walk up to root and return the root brand
    case walkToRoot bid hierarchy of
      Just rootId -> rootId
      Nothing -> bid
  InheritSelective components -> 
    -- Selective inheritance: use parent only if component is in the list
    if V.elem component components
      then case getParent bid hierarchy of
        Just parent -> hnBrandId parent
        Nothing -> bid
      else bid
  InheritWithOverrides overrides ->
    -- Override-based: check if component has an override, otherwise inherit
    case V.find (\o -> coComponent o == component) overrides of
      Just _ -> bid  -- Has override, use own brand
      Nothing -> case getParent bid hierarchy of
        Just parent -> hnBrandId parent
        Nothing -> bid
  where
    -- Walk up the hierarchy to find the root brand
    walkToRoot :: BrandId -> BrandHierarchy -> Maybe BrandId
    walkToRoot currentId bh = case findNode currentId bh of
      Nothing -> Nothing
      Just node -> case hnParent node of
        Nothing -> Just currentId  -- This is the root
        Just parentId -> walkToRoot parentId bh
