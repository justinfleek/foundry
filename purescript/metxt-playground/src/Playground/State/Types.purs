-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // playground // state // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure state types for the Brand Playground.
-- |
-- | The playground state is a pure value that represents:
-- | - Which atoms exist on the canvas
-- | - How atoms are composed into molecules
-- | - How molecules form compounds
-- | - Current selection and editing state
-- |
-- | No effects, no callbacks, no mutation — just data.

module Playground.State.Types
  ( -- * Canvas Position
    Position
  , mkPosition
  , posX
  , posY
  
  -- * Node Identity
  , NodeId
  , mkNodeId
  , unNodeId
  
  -- * Atom Nodes
  , AtomKind(..)
  , AtomNode
  , mkAtomNode
  , atomKind
  , atomPosition
  , atomValue
  
  -- * Connection
  , Connection
  , mkConnection
  , connectionFrom
  , connectionTo
  , connectionSlot
  
  -- * Molecule Nodes
  , MoleculeKind(..)
  , MoleculeNode
  , mkMoleculeNode
  
  -- * Compound Nodes
  , CompoundKind(..)
  , CompoundNode
  , mkCompoundNode
  
  -- * Canvas State
  , CanvasState
  , emptyCanvas
  , addAtom
  , addMolecule
  , addCompound
  , addConnection
  , removeNode
  , moveNode
  , selectNode
  , deselectAll
  
  -- * Playground State
  , PlaygroundState
  , initialState
  , canvasState
  , selectedPanel
  , zoomLevel
  ) where

import Prelude
  ( class Eq
  , class Show
  , (==)
  , (<>)
  , (&&)
  , (/=)
  , show
  , map
  )

import Data.Array (filter, snoc, (:))
import Data.Maybe (Maybe(Just, Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D position on canvas (in logical units, not pixels).
type Position =
  { x :: Number
  , y :: Number
  }

-- | Create a position.
mkPosition :: Number -> Number -> Position
mkPosition x y = { x, y }

-- | Get X coordinate.
posX :: Position -> Number
posX p = p.x

-- | Get Y coordinate.
posY :: Position -> Number
posY p = p.y

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // node id
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for canvas nodes.
-- |
-- | In production, these would be UUID5 from content.
-- | For the playground, we use incrementing integers for simplicity.
newtype NodeId = NodeId Int

derive instance eqNodeId :: Eq NodeId

instance showNodeId :: Show NodeId where
  show (NodeId n) = "node_" <> show n

-- | Create a node ID.
mkNodeId :: Int -> NodeId
mkNodeId = NodeId

-- | Unwrap node ID.
unNodeId :: NodeId -> Int
unNodeId (NodeId n) = n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // atom kinds
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All atom types in the brand schema.
-- |
-- | Each atom has defined bounds and validation.
data AtomKind
  -- Color atoms
  = LightnessAtom      -- 0 to 1
  | ChromaAtom         -- 0 to 0.5
  | HueAtom            -- 0 to 360 (wrapping)
  
  -- Typography atoms
  | FontWeightAtom     -- 100-900, multiples of 100
  | FontFamilyAtom     -- non-empty string
  | FontSizeAtom       -- > 0
  | ScaleRatioAtom     -- > 1
  
  -- Spacing atoms
  | BaseSpacingAtom    -- > 0
  | SpacingScaleAtom   -- > 1
  
  -- Identity atoms
  | DomainAtom         -- non-empty, contains dot
  | BrandNameAtom      -- 1-256 chars
  
  -- Voice atoms
  | ToneAtom           -- enum
  | TraitAtom          -- non-empty string

derive instance eqAtomKind :: Eq AtomKind

instance showAtomKind :: Show AtomKind where
  show LightnessAtom = "Lightness"
  show ChromaAtom = "Chroma"
  show HueAtom = "Hue"
  show FontWeightAtom = "FontWeight"
  show FontFamilyAtom = "FontFamily"
  show FontSizeAtom = "FontSize"
  show ScaleRatioAtom = "ScaleRatio"
  show BaseSpacingAtom = "BaseSpacing"
  show SpacingScaleAtom = "SpacingScale"
  show DomainAtom = "Domain"
  show BrandNameAtom = "BrandName"
  show ToneAtom = "Tone"
  show TraitAtom = "Trait"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // atom value
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Value held by an atom (dynamic but typed at runtime).
-- |
-- | Atoms on the canvas hold their current value.
-- | Validation happens when connecting to molecules.
data AtomValue
  = NumberValue Number
  | IntValue Int
  | StringValue String

derive instance eqAtomValue :: Eq AtomValue

instance showAtomValue :: Show AtomValue where
  show (NumberValue n) = show n
  show (IntValue i) = show i
  show (StringValue s) = "\"" <> s <> "\""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // atom node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | An atom on the canvas.
-- |
-- | Atoms are the fundamental building blocks.
-- | They have a kind, position, and current value.
type AtomNode =
  { id :: NodeId
  , kind :: AtomKind
  , position :: Position
  , value :: AtomValue
  , selected :: Boolean
  }

-- | Create an atom node.
mkAtomNode :: NodeId -> AtomKind -> Position -> AtomValue -> AtomNode
mkAtomNode id kind position value =
  { id
  , kind
  , position
  , value
  , selected: false
  }

-- | Get atom kind.
atomKind :: AtomNode -> AtomKind
atomKind a = a.kind

-- | Get atom position.
atomPosition :: AtomNode -> Position
atomPosition a = a.position

-- | Get atom value.
atomValue :: AtomNode -> AtomValue
atomValue a = a.value

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // connection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A connection between nodes.
-- |
-- | Connections are directed: from an output to an input slot.
type Connection =
  { from :: NodeId      -- Source node (atom or molecule)
  , to :: NodeId        -- Target node (molecule or compound)
  , slot :: String      -- Input slot name (e.g., "l", "c", "h" for OKLCH)
  }

-- | Create a connection.
mkConnection :: NodeId -> NodeId -> String -> Connection
mkConnection from to slot = { from, to, slot }

-- | Get source node.
connectionFrom :: Connection -> NodeId
connectionFrom c = c.from

-- | Get target node.
connectionTo :: Connection -> NodeId
connectionTo c = c.to

-- | Get input slot name.
connectionSlot :: Connection -> String
connectionSlot c = c.slot

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // molecule kinds
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Molecule types — compositions of atoms.
data MoleculeKind
  -- Color molecules
  = OKLCHMolecule          -- L + C + H → Color
  | PaletteEntryMolecule   -- Color + Role → Entry
  
  -- Typography molecules
  | TypeScaleMolecule      -- Base + Ratio → Scale
  
  -- Spacing molecules
  | SpacingScaleMolecule   -- Base + Ratio → Scale
  
  -- Identity molecules
  | IdentityMolecule       -- Name + Domain + UUID → Identity

derive instance eqMoleculeKind :: Eq MoleculeKind

instance showMoleculeKind :: Show MoleculeKind where
  show OKLCHMolecule = "OKLCH Color"
  show PaletteEntryMolecule = "Palette Entry"
  show TypeScaleMolecule = "Type Scale"
  show SpacingScaleMolecule = "Spacing Scale"
  show IdentityMolecule = "Identity"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // molecule node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A molecule on the canvas.
-- |
-- | Molecules accept atoms as inputs and produce composed values.
type MoleculeNode =
  { id :: NodeId
  , kind :: MoleculeKind
  , position :: Position
  , selected :: Boolean
  }

-- | Create a molecule node.
mkMoleculeNode :: NodeId -> MoleculeKind -> Position -> MoleculeNode
mkMoleculeNode id kind position =
  { id
  , kind
  , position
  , selected: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // compound kinds
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compound types — compositions of molecules.
data CompoundKind
  = BrandPaletteCmpd      -- Array of PaletteEntry → Palette
  | BrandTypographyCmpd   -- Families + Scale + Weights → Typography
  | BrandSpacingCmpd      -- Scale → Spacing
  | BrandVoiceCmpd        -- Tone + Traits → Voice
  | BrandIdentityCmpd     -- Identity → Identity (pass-through)
  | BrandCmpd             -- All layers → Brand

derive instance eqCompoundKind :: Eq CompoundKind

instance showCompoundKind :: Show CompoundKind where
  show BrandPaletteCmpd = "Brand Palette"
  show BrandTypographyCmpd = "Brand Typography"
  show BrandSpacingCmpd = "Brand Spacing"
  show BrandVoiceCmpd = "Brand Voice"
  show BrandIdentityCmpd = "Brand Identity"
  show BrandCmpd = "Brand"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // compound node
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A compound on the canvas.
type CompoundNode =
  { id :: NodeId
  , kind :: CompoundKind
  , position :: Position
  , selected :: Boolean
  }

-- | Create a compound node.
mkCompoundNode :: NodeId -> CompoundKind -> Position -> CompoundNode
mkCompoundNode id kind position =
  { id
  , kind
  , position
  , selected: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // canvas state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete canvas state.
-- |
-- | Pure data representing everything on the composition canvas.
type CanvasState =
  { atoms :: Array AtomNode
  , molecules :: Array MoleculeNode
  , compounds :: Array CompoundNode
  , connections :: Array Connection
  , nextId :: Int
  }

-- | Empty canvas.
emptyCanvas :: CanvasState
emptyCanvas =
  { atoms: []
  , molecules: []
  , compounds: []
  , connections: []
  , nextId: 1
  }

-- | Add an atom to the canvas.
addAtom :: AtomKind -> Position -> AtomValue -> CanvasState -> CanvasState
addAtom kind pos value canvas =
  let
    nodeId = NodeId canvas.nextId
    atom = mkAtomNode nodeId kind pos value
  in
    canvas
      { atoms = snoc canvas.atoms atom
      , nextId = canvas.nextId + 1
      }

-- | Add a molecule to the canvas.
addMolecule :: MoleculeKind -> Position -> CanvasState -> CanvasState
addMolecule kind pos canvas =
  let
    nodeId = NodeId canvas.nextId
    molecule = mkMoleculeNode nodeId kind pos
  in
    canvas
      { molecules = snoc canvas.molecules molecule
      , nextId = canvas.nextId + 1
      }

-- | Add a compound to the canvas.
addCompound :: CompoundKind -> Position -> CanvasState -> CanvasState
addCompound kind pos canvas =
  let
    nodeId = NodeId canvas.nextId
    compound = mkCompoundNode nodeId kind pos
  in
    canvas
      { compounds = snoc canvas.compounds compound
      , nextId = canvas.nextId + 1
      }

-- | Add a connection.
addConnection :: NodeId -> NodeId -> String -> CanvasState -> CanvasState
addConnection from to slot canvas =
  let conn = mkConnection from to slot
  in canvas { connections = snoc canvas.connections conn }

-- | Remove a node (atom, molecule, or compound) and its connections.
removeNode :: NodeId -> CanvasState -> CanvasState
removeNode nodeId canvas =
  canvas
    { atoms = filter (\a -> a.id /= nodeId) canvas.atoms
    , molecules = filter (\m -> m.id /= nodeId) canvas.molecules
    , compounds = filter (\c -> c.id /= nodeId) canvas.compounds
    , connections = filter (\c -> c.from /= nodeId && c.to /= nodeId) canvas.connections
    }

-- | Move a node to a new position.
moveNode :: NodeId -> Position -> CanvasState -> CanvasState
moveNode nodeId newPos canvas =
  canvas
    { atoms = map (\a -> if a.id == nodeId then a { position = newPos } else a) canvas.atoms
    , molecules = map (\m -> if m.id == nodeId then m { position = newPos } else m) canvas.molecules
    , compounds = map (\c -> if c.id == nodeId then c { position = newPos } else c) canvas.compounds
    }

-- | Select a node.
selectNode :: NodeId -> CanvasState -> CanvasState
selectNode nodeId canvas =
  canvas
    { atoms = map (\a -> a { selected = a.id == nodeId }) canvas.atoms
    , molecules = map (\m -> m { selected = m.id == nodeId }) canvas.molecules
    , compounds = map (\c -> c { selected = c.id == nodeId }) canvas.compounds
    }

-- | Deselect all nodes.
deselectAll :: CanvasState -> CanvasState
deselectAll canvas =
  canvas
    { atoms = map (\a -> a { selected = false }) canvas.atoms
    , molecules = map (\m -> m { selected = false }) canvas.molecules
    , compounds = map (\c -> c { selected = false }) canvas.compounds
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // playground state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Panel selection.
data Panel
  = AtomsPanel
  | MoleculesPanel
  | CompoundsPanel
  | PreviewPanel
  | ExportPanel

derive instance eqPanel :: Eq Panel

instance showPanel :: Show Panel where
  show AtomsPanel = "Atoms"
  show MoleculesPanel = "Molecules"
  show CompoundsPanel = "Compounds"
  show PreviewPanel = "Preview"
  show ExportPanel = "Export"

-- | Complete playground state.
type PlaygroundState =
  { canvas :: CanvasState
  , selectedPanel :: Panel
  , zoom :: Number          -- 0.25 to 4.0
  , panOffset :: Position   -- canvas pan offset
  }

-- | Initial playground state.
initialState :: PlaygroundState
initialState =
  { canvas: emptyCanvas
  , selectedPanel: AtomsPanel
  , zoom: 1.0
  , panOffset: mkPosition 0.0 0.0
  }

-- | Get canvas state.
canvasState :: PlaygroundState -> CanvasState
canvasState s = s.canvas

-- | Get selected panel.
selectedPanel :: PlaygroundState -> Panel
selectedPanel s = s.selectedPanel

-- | Get zoom level.
zoomLevel :: PlaygroundState -> Number
zoomLevel s = s.zoom
