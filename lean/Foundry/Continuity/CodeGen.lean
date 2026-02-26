/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                     CONTINUITY CODE GENERATION IR
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                 A Language-Agnostic Intermediate Representation
                      for Type-Safe Multi-Target Extraction

                          razorgirl / Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Power, in Case's world, meant corporate power. The zaibatsus, the
    multinationals... Cold as a wasp's nest, like the core of the matrix,
    the bright lattice of logic unfolding.
                                                        — Neuromancer

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This module defines a clean intermediate representation for code generation:

  Lean4 Types ─── toIR ───▶ IR.Module ─── emit ───▶ Target Source
       │                        │                        │
       │                        │                        ├─▶ Haskell
       │                        │                        ├─▶ C++23
       │                        │                        └─▶ Rust

The IR captures:
  - Type definitions (structs, enums, newtypes)
  - Function signatures
  - State machines (states, events, transitions)
  - Codec specifications (parse/serialize pairs)

Each target emitter is a pure function: IR.Module → String

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Foundry.Continuity.CodeGen

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 PRIMITIVE TYPES
-- ════════════════════════════════════════════════════════════════════════════════

/-- Primitive types with known representations across all targets -/
inductive Prim where
  | unit                          -- () / void / ()
  | bool                          -- Bool / bool / bool  
  | u8 | u16 | u32 | u64          -- Fixed-width unsigned
  | i8 | i16 | i32 | i64          -- Fixed-width signed
  | usize | isize                 -- Platform-sized
  | f32 | f64                     -- IEEE 754 floats
  | bytes                         -- ByteString / std::vector<uint8_t> / Vec<u8>
  | string                        -- Text / std::string / String
  deriving Repr, DecidableEq, Inhabited

/-- Endianness for wire formats -/
inductive Endian where
  | little | big | native
  deriving Repr, DecidableEq, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 TYPE EXPRESSIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Type expressions in the IR -/
inductive Ty where
  | prim : Prim → Ty                        -- Primitive type
  | named : String → Ty                      -- Reference to named type
  | array : Ty → Ty                          -- Variable-length array
  | fixedArray : Ty → Nat → Ty               -- Fixed-length array [T; N]
  | optional : Ty → Ty                       -- Option<T> / std::optional<T>
  | result : Ty → Ty → Ty                    -- Result<T, E> / Expected<T, E>
  | tuple : List Ty → Ty                     -- (T1, T2, ...)
  | func : List Ty → Ty → Ty                 -- Function type (args → ret)
  | generic : String → List Ty → Ty          -- Generic<T1, T2>
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 EXPRESSIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Binary operators -/
inductive BinOp where
  | add | sub | mul | div | rem             -- Arithmetic
  | and | or | xor                          -- Bitwise
  | land | lor                              -- Logical
  | eq | neq | lt | le | gt | ge            -- Comparison
  | shl | shr                               -- Shifts
  | concat                                  -- Array/string concatenation
  deriving Repr, DecidableEq, Inhabited

/-- Unary operators -/
inductive UnOp where
  | neg | not | bitnot
  deriving Repr, DecidableEq, Inhabited

/-- Literal values -/
abbrev Lit : Type := Bool ⊕ Nat ⊕ Int ⊕ String ⊕ Unit

/-- Pattern for matching: variable or constructor with bindings -/
abbrev Pattern : Type := String ⊕ (String × List String)

/-- Expressions -/
inductive Expr where
  | lit : Lit → Expr                         -- Literal value
  | var : String → Expr                      -- Variable reference
  | field : Expr → String → Expr             -- e.field
  | index : Expr → Expr → Expr               -- e[i]
  | call : String → List Expr → Expr         -- f(args)
  | methodCall : Expr → String → List Expr → Expr  -- e.method(args)
  | binop : BinOp → Expr → Expr → Expr       -- e1 op e2
  | unop : UnOp → Expr → Expr                -- op e
  | cond : Expr → Expr → Expr → Expr         -- if c then t else e
  | match_ : Expr → List (Pattern × Expr) → Expr  -- Pattern match
  | lambda : List String → Expr → Expr       -- \args -> body
  | construct : String → List (String × Expr) → Expr  -- Type { field = e, ... }
  | tuple : List Expr → Expr                 -- (e1, e2, ...)
  | cast : Expr → Ty → Expr                  -- e as T
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §3 STATEMENTS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Statements (for imperative targets like C++) -/
inductive Stmt where
  | letBind : String → Option Ty → Expr → Stmt       -- let x : T = e
  | mutBind : String → Option Ty → Expr → Stmt       -- var x : T = e (mutable)
  | assign : Expr → Expr → Stmt                      -- lhs = rhs
  | expr : Expr → Stmt                               -- e; (for side effects)
  | ret : Option Expr → Stmt                         -- return e
  | if_ : Expr → List Stmt → Option (List Stmt) → Stmt  -- if c { ... } else { ... }
  | match_ : Expr → List (Pattern × List Stmt) → Stmt
  | while_ : Expr → List Stmt → Stmt                 -- while c { ... }
  | for_ : String → Expr → List Stmt → Stmt          -- for x in e { ... }
  | block : List Stmt → Stmt                         -- { ... }
  | comment : String → Stmt                          -- // comment
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 TYPE DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- A field in a struct -/
structure Field where
  name : String
  ty : Ty
  doc : Option String := none
  deriving Repr, Inhabited

/-- A variant in an enum -/
structure Variant where
  name : String
  fields : List Field           -- Empty for unit variants
  doc : Option String := none
  deriving Repr, Inhabited

/-- Visibility modifiers -/
inductive Visibility where
  | public_ | private_ | internal
  deriving Repr, DecidableEq, Inhabited

/-- Type definition -/
inductive TypeDef where
  /-- Struct with named fields -/
  | struct : String → List String → List Field → TypeDef
  /-- Enum with variants -/
  | enum : String → List String → List Variant → TypeDef
  /-- Newtype wrapper -/
  | newtype : String → List String → Ty → TypeDef
  /-- Type alias -/
  | alias : String → List String → Ty → TypeDef
  deriving Repr, Inhabited

-- Helper to get type name
def TypeDef.name : TypeDef → String
  | .struct n _ _ => n
  | .enum n _ _ => n
  | .newtype n _ _ => n
  | .alias n _ _ => n

-- Helper to get type params
def TypeDef.params : TypeDef → List String
  | .struct _ ps _ => ps
  | .enum _ ps _ => ps
  | .newtype _ ps _ => ps
  | .alias _ ps _ => ps

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 FUNCTION DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- A function parameter -/
structure Param where
  name : String
  ty : Ty
  default : Option Expr := none
  deriving Repr, Inhabited

/-- Function body - either expression or statement block -/
inductive FuncBody where
  | expr : Expr → FuncBody
  | stmts : List Stmt → FuncBody
  deriving Repr, Inhabited

/-- Function definition -/
structure FuncDef where
  name : String
  typeParams : List String := []
  params : List Param
  returnTy : Ty
  body : FuncBody
  doc : Option String := none
  visibility : Visibility := .public_
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 STATE MACHINES
-- ════════════════════════════════════════════════════════════════════════════════

/-- A state in a state machine -/
structure State where
  name : String
  doc : Option String := none
  isInitial : Bool := false
  isTerminal : Bool := false
  deriving Repr, Inhabited

/-- An event that can trigger transitions -/
structure Event where
  name : String
  payload : List Field := []
  doc : Option String := none
  deriving Repr, Inhabited

/-- An action produced by a transition -/
structure Action where
  name : String
  payload : List Field := []
  doc : Option String := none
  deriving Repr, Inhabited

/-- A transition in the state machine -/
structure Transition where
  from_ : String
  event : String
  to : String
  actions : List String := []
  guard : Option Expr := none
  doc : Option String := none
  deriving Repr, Inhabited

/-- State machine definition -/
structure StateMachine where
  name : String
  states : List State
  events : List Event
  actions : List Action
  transitions : List Transition
  doc : Option String := none
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §7 CODEC SPECIFICATIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Wire format for a field -/
inductive WireFormat where
  | fixed : Prim → Endian → WireFormat           -- Fixed-size primitive
  | varInt : WireFormat                          -- Variable-length integer (LEB128)
  | lengthPrefixed : WireFormat → WireFormat     -- Length-prefixed data
  | nullTerminated : WireFormat                  -- Null-terminated string
  | padded : Nat → WireFormat → WireFormat       -- Padded to alignment
  | remaining : WireFormat                       -- Consume remaining bytes
  deriving Repr, Inhabited

/-- Codec specification -/
structure Codec where
  name : String
  ty : Ty
  wire : WireFormat
  doc : Option String := none
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §8 MODULE DEFINITION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Import statement -/
structure Import where
  module : String
  items : Option (List String) := none  -- None = import all
  qualified : Bool := false
  alias : Option String := none
  deriving Repr, Inhabited

/-- A complete module in the IR -/
structure Module where
  name : String
  doc : Option String := none
  imports : List Import := []
  types : List TypeDef := []
  functions : List FuncDef := []
  machines : List StateMachine := []
  codecs : List Codec := []
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §9 DERIVED INSTANCES
-- ════════════════════════════════════════════════════════════════════════════════

/-- What can be derived for a type -/
inductive Derivable where
  | eq | ord | hash                    -- Equality, ordering, hashing
  | show | debug                       -- String representation
  | default_                           -- Default value
  | clone | copy                       -- Cloning (Rust)
  | serialize | deserialize            -- Serde (Rust) / Aeson (Haskell)
  | arbitrary                          -- QuickCheck
  deriving Repr, DecidableEq, Inhabited

/-- Derive directives for a type -/
structure Derives where
  typeName : String
  derives : List Derivable
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §10 SMART CONSTRUCTORS
-- ════════════════════════════════════════════════════════════════════════════════

namespace Ty

def u8 : Ty := .prim .u8
def u16 : Ty := .prim .u16
def u32 : Ty := .prim .u32
def u64 : Ty := .prim .u64
def i8 : Ty := .prim .i8
def i16 : Ty := .prim .i16
def i32 : Ty := .prim .i32
def i64 : Ty := .prim .i64
def bool : Ty := .prim .bool
def bytes : Ty := .prim .bytes
def string : Ty := .prim .string
def unit : Ty := .prim .unit

def option (t : Ty) : Ty := .optional t
def vec (t : Ty) : Ty := .array t
def res (ok err : Ty) : Ty := .result ok err

end Ty

namespace Expr

-- Lit = Bool ⊕ Nat ⊕ Int ⊕ String ⊕ Unit
-- So: Bool is .inl b
--     Nat is .inr (.inl n)
--     Int is .inr (.inr (.inl n))
--     String is .inr (.inr (.inr (.inl s)))
--     Unit is .inr (.inr (.inr (.inr ())))
def int (n : Int) : Expr := .lit (Sum.inr (Sum.inr (Sum.inl n)))
def nat (n : Nat) : Expr := .lit (Sum.inr (Sum.inl n))
def str (s : String) : Expr := .lit (Sum.inr (Sum.inr (Sum.inr (Sum.inl s))))
def bool_ (b : Bool) : Expr := .lit (Sum.inl b)
def unit : Expr := .lit (Sum.inr (Sum.inr (Sum.inr (Sum.inr ()))))

def add (a b : Expr) : Expr := .binop .add a b
def sub (a b : Expr) : Expr := .binop .sub a b
def eq_ (a b : Expr) : Expr := .binop .eq a b
def lt (a b : Expr) : Expr := .binop .lt a b

end Expr

-- ════════════════════════════════════════════════════════════════════════════════
-- §11 PROPERTIES (commented out due to termination issues - not needed for codegen)
-- ════════════════════════════════════════════════════════════════════════════════

-- Well-formedness checks are useful for validation but not required for code generation.
-- The type system ensures structural correctness; semantic checks can be done at runtime
-- or in a separate verification pass.

end Foundry.Continuity.CodeGen
