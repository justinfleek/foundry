import Foundry.Foundry.Continuity.CodeGen

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // HASKELL // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                    IR.Module → Haskell Source Code

                         Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Generates idiomatic Haskell from the CodeGen IR:

  - Records with OverloadedRecordDot
  - GADTs for state machines
  - DerivingVia for instances
  - Strict ByteString for binary data
  - Megaparsec for parsing
  - Builder for serialization

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Foundry.Continuity.CodeGen.Haskell

open Foundry.Continuity.CodeGen

-- ════════════════════════════════════════════════════════════════════════════
-- §0 CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

/-- Haskell code generation options -/
structure Options where
  /-- Enable language extensions -/
  extensions : List String := [
    "OverloadedStrings",
    "DeriveGeneric",
    "DerivingStrategies",
    "DerivingVia",
    "DuplicateRecordFields",
    "OverloadedRecordDot",
    "StrictData",
    "LambdaCase",
    "GADTs",
    "TypeFamilies",
    "DataKinds",
    "KindSignatures"
  ]
  /-- Indentation width -/
  indent : Nat := 2
  /-- Generate Aeson instances -/
  aeson : Bool := true
  /-- Generate Binary instances -/
  binary : Bool := true
  /-- Generate QuickCheck Arbitrary instances -/
  quickcheck : Bool := false
  deriving Repr, Inhabited

def defaultOptions : Options := {}

-- ═════════════════════════════════════════════════════════════════════════════
-- §1 PRIMITIVE TYPE MAPPING
-- ═════════════════════════════════════════════════════════════════════════════

/-- Map IR primitive to Haskell type -/
def emitPrim : Prim → String
  | .unit => "()"
  | .bool => "Bool"
  | .u8 => "Word8"
  | .u16 => "Word16"
  | .u32 => "Word32"
  | .u64 => "Word64"
  | .i8 => "Int8"
  | .i16 => "Int16"
  | .i32 => "Int32"
  | .i64 => "Int64"
  | .usize => "Word"
  | .isize => "Int"
  | .f32 => "Float"
  | .f64 => "Double"
  | .bytes => "ByteString"
  | .string => "Text"

-- ════════════════════════════════════════════════════════════════════════════
-- §2 TYPE EMISSION
-- ════════════════════════════════════════════════════════════════════════════

/-- Emit a type expression -/
partial def emitTy : Ty → String
  | .prim p => emitPrim p
  | .named n => n
  | .array t => "[" ++ emitTy t ++ "]"
  | .fixedArray t n => s!"Vector {n} ({emitTy t})"
  | .optional t => "Maybe (" ++ emitTy t ++ ")"
  | .result ok err => s!"Either ({emitTy err}) ({emitTy ok})"
  | .tuple ts => "(" ++ ", ".intercalate (ts.map emitTy) ++ ")"
  | .func args ret => 
    let argTys := args.map emitTy
    let allTys := argTys ++ [emitTy ret]
    " -> ".intercalate allTys
  | .generic name args =>
    name ++ " " ++ " ".intercalate (args.map fun t => "(" ++ emitTy t ++ ")")

-- ════════════════════════════════════════════════════════════════════════════
-- §3 EXPRESSION EMISSION
-- ════════════════════════════════════════════════════════════════════════════

/-- Emit a binary operator -/
def emitBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "`div`"
  | .rem => "`mod`"
  | .and => ".&."
  | .or => ".|."
  | .xor => "`xor`"
  | .land => "&&"
  | .lor => "||"
  | .eq => "=="
  | .neq => "/="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .shl => "`shiftL`"
  | .shr => "`shiftR`"
  | .concat => "<>"

/-- Emit a unary operator -/
def emitUnOp : UnOp → String
  | .neg => "-"
  | .not => "not"
  | .bitnot => "complement"

/-- Emit a literal -/
def emitLit : Lit → String
  | .inl b => if b then "True" else "False"
  | .inr (.inl n) => toString n
  | .inr (.inr (.inl n)) => toString n  -- Int
  | .inr (.inr (.inr (.inl s))) => "\"" ++ s ++ "\""  -- TODO: escape
  | .inr (.inr (.inr (.inr ()))) => "()"

/-- Emit a pattern -/
def emitPattern : Pattern → String
  | .inl v => v  -- Variable
  | .inr (ctor, bindings) =>
    if bindings.isEmpty then ctor
    else ctor ++ " " ++ " ".intercalate bindings

/-- Emit an expression -/
partial def emitExpr : Expr → String
  | .lit l => emitLit l
  | .var v => v
  | .field e f => emitExpr e ++ "." ++ f
  | .index e i => emitExpr e ++ " !! " ++ emitExpr i
  | .call f args => f ++ " " ++ " ".intercalate (args.map (fun a => "(" ++ emitExpr a ++ ")"))
  | .methodCall e m args => 
    m ++ " " ++ emitExpr e ++ " " ++ " ".intercalate (args.map (fun a => "(" ++ emitExpr a ++ ")"))
  | .binop op l r => "(" ++ emitExpr l ++ " " ++ emitBinOp op ++ " " ++ emitExpr r ++ ")"
  | .unop op e => "(" ++ emitUnOp op ++ " " ++ emitExpr e ++ ")"
  | .cond c t f => "if " ++ emitExpr c ++ " then " ++ emitExpr t ++ " else " ++ emitExpr f
  | .match_ e cases =>
    let branches := cases.map fun (pat, body) =>
      "  " ++ emitPattern pat ++ " -> " ++ emitExpr body
    "case " ++ emitExpr e ++ " of\n" ++ "\n".intercalate branches
  | .lambda args body =>
    "\\" ++ " ".intercalate args ++ " -> " ++ emitExpr body
  | .construct name fields =>
    if fields.isEmpty then name
    else name ++ " { " ++ ", ".intercalate (fields.map fun (f, e) => f ++ " = " ++ emitExpr e) ++ " }"
  | .tuple es => "(" ++ ", ".intercalate (es.map emitExpr) ++ ")"
  | .cast e _ => emitExpr e  -- Haskell uses type annotations differently

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 STATEMENT EMISSION (for do-notation)
-- ════════════════════════════════════════════════════════════════════════════════

/-- Indentation helper -/
def spaces (n : Nat) : String := String.mk (List.replicate n ' ')

/-- Emit a statement (in do-notation context) -/
partial def emitStmt (indent : Nat) : Stmt → String
  | .letBind name ty e =>
    let tyAnnotation := match ty with
      | some t => " :: " ++ emitTy t
      | none => ""
    spaces indent ++ "let " ++ name ++ tyAnnotation ++ " = " ++ emitExpr e
  | .mutBind name ty e =>
    -- Haskell doesn't have mutable bindings, use IORef pattern
    let tyAnnotation := match ty with
      | some t => " :: IORef (" ++ emitTy t ++ ")"
      | none => ""
    spaces indent ++ name ++ tyAnnotation ++ " <- newIORef (" ++ emitExpr e ++ ")"
  | .assign lhs rhs =>
    spaces indent ++ "writeIORef " ++ emitExpr lhs ++ " (" ++ emitExpr rhs ++ ")"
  | .expr e =>
    spaces indent ++ emitExpr e
  | .ret (some e) =>
    spaces indent ++ "pure " ++ emitExpr e
  | .ret none =>
    spaces indent ++ "pure ()"
  | .if_ cond thenBody elseBody =>
    let thenStmts := thenBody.map (emitStmt (indent + 2))
    let elseStmts := match elseBody with
      | some stmts => "\n" ++ spaces indent ++ "else do\n" ++ "\n".intercalate (stmts.map (emitStmt (indent + 2)))
      | none => ""
    spaces indent ++ "if " ++ emitExpr cond ++ " then do\n" ++ "\n".intercalate thenStmts ++ elseStmts
  | .match_ e cases =>
    let branches := cases.map fun (pat, stmts) =>
      spaces (indent + 2) ++ emitPattern pat ++ " -> do\n" ++ "\n".intercalate (stmts.map (emitStmt (indent + 4)))
    spaces indent ++ "case " ++ emitExpr e ++ " of\n" ++ "\n".intercalate branches
  | .while_ cond body =>
    -- Use fix or a helper function for loops
    let bodyStmts := body.map (emitStmt (indent + 2))
    spaces indent ++ "fix $ \\loop -> when (" ++ emitExpr cond ++ ") $ do\n" ++
    "\n".intercalate bodyStmts ++ "\n" ++ spaces (indent + 2) ++ "loop"
  | .for_ var iter body =>
    let bodyStmts := body.map (emitStmt (indent + 2))
    spaces indent ++ "forM_ (" ++ emitExpr iter ++ ") $ \\" ++ var ++ " -> do\n" ++
    "\n".intercalate bodyStmts
  | .block stmts =>
    "\n".intercalate (stmts.map (emitStmt indent))
  | .comment c =>
    spaces indent ++ "-- " ++ c

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 TYPE DEFINITION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit deriving clause -/
def emitDerives (derives : List Derivable) : String :=
  if derives.isEmpty then ""
  else
    let mapped := derives.map fun
      | .eq => "Eq"
      | .ord => "Ord"
      | .hash => "Hashable"
      | .show => "Show"
      | .debug => "Show"
      | .default_ => "Default"
      | .clone => ""  -- Not needed in Haskell
      | .copy => ""
      | .serialize => "ToJSON"
      | .deserialize => "FromJSON"
      | .arbitrary => "Arbitrary"
    let filtered := mapped.filter (· != "")
    if filtered.isEmpty then ""
    else "\n  deriving stock (" ++ ", ".intercalate filtered ++ ")"

/-- Emit a field definition -/
def emitField (f : Field) : String :=
  let doc := match f.doc with
    | some d => "  -- ^ " ++ d ++ "\n"
    | none => ""
  doc ++ f.name ++ " :: " ++ emitTy f.ty

/-- Emit a struct as a record -/
def emitStruct (name : String) (params : List String) (fields : List Field) 
    (derives : List Derivable := [.eq, .show, .serialize, .deserialize]) : String :=
  let typeParams := if params.isEmpty then "" else " " ++ " ".intercalate params
  let fieldDefs := fields.map (fun f => "    " ++ emitField f)
  s!"data {name}{typeParams} = {name}\n  \{ " ++ 
  "\n  , ".intercalate fieldDefs ++ 
  "\n  }" ++ emitDerives derives

/-- Emit a variant definition -/
def emitVariant (v : Variant) : String :=
  let doc := match v.doc with
    | some d => "  -- | " ++ d ++ "\n  "
    | none => "  "
  if v.fields.isEmpty then
    doc ++ v.name
  else if v.fields.length == 1 && v.fields.head!.name == "0" then
    -- Single unnamed field = newtype-style
    doc ++ v.name ++ " " ++ emitTy v.fields.head!.ty
  else
    -- Named fields = record syntax
    let fieldDefs := v.fields.map (fun f => f.name ++ " :: " ++ emitTy f.ty)
    doc ++ v.name ++ " { " ++ ", ".intercalate fieldDefs ++ " }"

/-- Emit an enum as a sum type -/
def emitEnum (name : String) (params : List String) (variants : List Variant)
    (derives : List Derivable := [.eq, .show, .serialize, .deserialize]) : String :=
  let typeParams := if params.isEmpty then "" else " " ++ " ".intercalate params
  let variantDefs := variants.map emitVariant
  s!"data {name}{typeParams}\n  = " ++ "\n  | ".intercalate variantDefs ++ 
  emitDerives derives

/-- Emit a newtype -/
def emitNewtype (name : String) (params : List String) (inner : Ty)
    (derives : List Derivable := [.eq, .show]) : String :=
  let typeParams := if params.isEmpty then "" else " " ++ " ".intercalate params
  s!"newtype {name}{typeParams} = {name} \{ un{name} :: {emitTy inner} }" ++
  emitDerives derives

/-- Emit a type alias -/
def emitAlias (name : String) (params : List String) (ty : Ty) : String :=
  let typeParams := if params.isEmpty then "" else " " ++ " ".intercalate params
  s!"type {name}{typeParams} = {emitTy ty}"

/-- Emit a type definition -/
def emitTypeDef (td : TypeDef) (derives : List Derivable := [.eq, .show, .serialize, .deserialize]) : String :=
  match td with
  | .struct name params fields => emitStruct name params fields derives
  | .enum name params variants => emitEnum name params variants derives
  | .newtype name params ty => emitNewtype name params ty derives
  | .alias name params ty => emitAlias name params ty

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 FUNCTION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a function parameter -/
def emitParam (p : Param) : String := p.name

/-- Emit a function signature -/
def emitFuncSig (f : FuncDef) : String :=
  let paramTys := f.params.map (·.ty)
  let funcTy := Ty.func paramTys f.returnTy
  f.name ++ " :: " ++ emitTy funcTy

/-- Emit a function body -/
def emitFuncBody (name : String) (params : List Param) (body : FuncBody) : String :=
  let paramNames := params.map (·.name)
  let lhs := name ++ " " ++ " ".intercalate paramNames ++ " ="
  match body with
  | .expr e => lhs ++ " " ++ emitExpr e
  | .stmts stmts =>
    lhs ++ " do\n" ++ "\n".intercalate (stmts.map (emitStmt 2))

/-- Emit a complete function -/
def emitFunc (f : FuncDef) : String :=
  let doc := match f.doc with
    | some d => "-- | " ++ d ++ "\n"
    | none => ""
  doc ++ emitFuncSig f ++ "\n" ++ emitFuncBody f.name f.params f.body

-- ════════════════════════════════════════════════════════════════════════════════
-- §7 STATE MACHINE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit state machine as GADT with transition function -/
def emitStateMachine (sm : StateMachine) : String :=
  let doc := match sm.doc with
    | some d => "-- | " ++ d ++ "\n"
    | none => ""
  
  -- State type
  let stateType := s!"data {sm.name}State\n  = " ++
    "\n  | ".intercalate (sm.states.map (·.name)) ++
    "\n  deriving stock (Eq, Show, Enum, Bounded)"
  
  -- Event type
  let eventVariants := sm.events.map fun e =>
    if e.payload.isEmpty then e.name
    else e.name ++ " " ++ " ".intercalate (e.payload.map (fun f => emitTy f.ty))
  let eventType := s!"data {sm.name}Event\n  = " ++
    "\n  | ".intercalate eventVariants ++
    "\n  deriving stock (Eq, Show)"
  
  -- Action type  
  let actionVariants := sm.actions.map fun a =>
    if a.payload.isEmpty then a.name
    else a.name ++ " " ++ " ".intercalate (a.payload.map (fun f => emitTy f.ty))
  let actionType := s!"data {sm.name}Action\n  = " ++
    "\n  | ".intercalate actionVariants ++
    "\n  deriving stock (Eq, Show)"
  
  -- Transition function
  let transitionCases := sm.transitions.map fun t =>
    let actionList := if t.actions.isEmpty then "[]" 
                      else "[" ++ ", ".intercalate t.actions ++ "]"
    s!"  ({t.from_}, {t.event}) -> ({t.to}, {actionList})"
  let transitionFunc := s!"transition{sm.name} :: ({sm.name}State, {sm.name}Event) -> ({sm.name}State, [{sm.name}Action])\ntransition{sm.name} = \\case\n" ++
    "\n".intercalate transitionCases ++
    "\n  (s, _) -> (s, [])  -- Default: no transition"
  
  -- Initial state
  let initialState := sm.states.find? (·.isInitial) |>.map (·.name) |>.getD (sm.states.head!.name)
  let initialDef := s!"initial{sm.name}State :: {sm.name}State\ninitial{sm.name}State = {initialState}"
  
  doc ++ stateType ++ "\n\n" ++ eventType ++ "\n\n" ++ actionType ++ "\n\n" ++ transitionFunc ++ "\n\n" ++ initialDef

-- ════════════════════════════════════════════════════════════════════════════════
-- §8 MODULE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit language extensions pragma -/
def emitExtensions (exts : List String) : String :=
  exts.map (fun e => "{-# LANGUAGE " ++ e ++ " #-}") |> "\n".intercalate

/-- Emit imports -/
def emitImports (imports : List Import) (opts : Options) : String :=
  let standardImports := [
    "import Data.ByteString (ByteString)",
    "import Data.Text (Text)",
    "import Data.Word (Word8, Word16, Word32, Word64)",
    "import Data.Int (Int8, Int16, Int32, Int64)",
    "import GHC.Generics (Generic)"
  ]
  let aesonImports := if opts.aeson then [
    "import Data.Aeson (ToJSON, FromJSON)"
  ] else []
  let userImports := imports.map fun i =>
    let qual := if i.qualified then "qualified " else ""
    let alias := match i.alias with
      | some a => " as " ++ a
      | none => ""
    let items := match i.items with
      | some is => " (" ++ ", ".intercalate is ++ ")"
      | none => ""
    s!"import {qual}{i.module}{items}{alias}"
  "\n".intercalate (standardImports ++ aesonImports ++ userImports)

/-- Emit a complete module -/
def emitModule (m : Module) (opts : Options := defaultOptions) : String :=
  let extensions := emitExtensions opts.extensions
  let moduleDoc := match m.doc with
    | some d => "{-|\n" ++ d ++ "\n-}\n"
    | none => ""
  let moduleDecl := s!"module {m.name} where"
  let imports := emitImports m.imports opts
  let types := m.types.map (emitTypeDef · [.eq, .show, .serialize, .deserialize])
  let functions := m.functions.map emitFunc
  let machines := m.machines.map emitStateMachine
  
  extensions ++ "\n\n" ++
  moduleDoc ++
  moduleDecl ++ "\n\n" ++
  imports ++ "\n\n" ++
  "-- Types\n" ++ "\n\n".intercalate types ++ "\n\n" ++
  "-- Functions\n" ++ "\n\n".intercalate functions ++ "\n\n" ++
  "-- State Machines\n" ++ "\n\n".intercalate machines

end Foundry.Continuity.CodeGen.Haskell
