import Foundry.Continuity.CodeGen

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                // RUST // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                     IR.Module → Rust Source Code

                         straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Generates idiomatic Rust from the CodeGen IR:

  - #[derive(...)] for common traits
  - enum for sum types (native Rust ADTs)
  - Result<T, E> for fallible operations
  - &[u8] / Vec<u8> for binary data
  - serde for serialization
  - #[must_use] for pure functions

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/


namespace Foundry.Continuity.CodeGen.Rust

open Foundry.Continuity.CodeGen

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Rust code generation options -/
structure Options where
  /-- Generate serde derives -/
  serde : Bool := true
  /-- Use no_std -/
  noStd : Bool := false
  /-- Generate #[must_use] -/
  mustUse : Bool := true
  /-- Indentation width -/
  indent : Nat := 4
  /-- Crate edition -/
  edition : String := "2021"
  deriving Repr, Inhabited

def defaultOptions : Options := {}

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 PRIMITIVE TYPE MAPPING
-- ════════════════════════════════════════════════════════════════════════════════

/-- Map IR primitive to Rust type -/
def emitPrim : Prim → String
  | .unit => "()"
  | .bool => "bool"
  | .u8 => "u8"
  | .u16 => "u16"
  | .u32 => "u32"
  | .u64 => "u64"
  | .i8 => "i8"
  | .i16 => "i16"
  | .i32 => "i32"
  | .i64 => "i64"
  | .usize => "usize"
  | .isize => "isize"
  | .f32 => "f32"
  | .f64 => "f64"
  | .bytes => "Vec<u8>"
  | .string => "String"

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 TYPE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a type expression -/
partial def emitTy : Ty → String
  | .prim p => emitPrim p
  | .named n => n
  | .array t => s!"Vec<{emitTy t}>"
  | .fixedArray t n => s!"[{emitTy t}; {n}]"
  | .optional t => s!"Option<{emitTy t}>"
  | .result ok err => s!"Result<{emitTy ok}, {emitTy err}>"
  | .tuple ts => s!"({", ".intercalate (ts.map emitTy)})"
  | .func args ret =>
    let argTys := ", ".intercalate (args.map emitTy)
    s!"fn({argTys}) -> {emitTy ret}"
  | .generic name args =>
    s!"{name}<{", ".intercalate (args.map emitTy)}>"

/-- Emit type for borrowed parameter -/
def emitBorrowTy (t : Ty) : String :=
  match t with
  | .prim .bytes => "&[u8]"
  | .prim .string => "&str"
  | .array inner => s!"&[{emitTy inner}]"
  | .named n => s!"&{n}"
  | _ => emitTy t

-- ════════════════════════════════════════════════════════════════════════════════
-- §3 EXPRESSION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a binary operator -/
def emitBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .rem => "%"
  | .and => "&"
  | .or => "|"
  | .xor => "^"
  | .land => "&&"
  | .lor => "||"
  | .eq => "=="
  | .neq => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .shl => "<<"
  | .shr => ">>"
  | .concat => "+"  -- Not direct, needs method

/-- Emit a unary operator -/
def emitUnOp : UnOp → String
  | .neg => "-"
  | .not => "!"
  | .bitnot => "!"

/-- Emit a literal -/
def emitLit : Expr.Lit → String
  | .inl true => "true"
  | .inl false => "false"
  | .inr (.inl n) => s!"{n}_u64"
  | .inr (.inr (.inl (.inl n))) => s!"{n}_i64"
  | .inr (.inr (.inl (.inr n))) => s!"{n}_i64"
  | .inr (.inr (.inr (.inl s))) => "\"" ++ s ++ "\".to_string()"  -- TODO: escape
  | .inr (.inr (.inr (.inr ()))) => "()"

/-- Emit a pattern -/
def emitPattern : Expr.Pattern → String
  | .inl v => v
  | .inr (ctor, bindings) =>
    if bindings.isEmpty then ctor
    else s!"{ctor}({", ".intercalate bindings})"

/-- Emit an expression -/
partial def emitExpr : Expr → String
  | .lit l => emitLit l
  | .var v => v
  | .field e f => s!"{emitExpr e}.{f}"
  | .index e i => s!"{emitExpr e}[{emitExpr i}]"
  | .call f args => s!"{f}({", ".intercalate (args.map emitExpr)})"
  | .methodCall e m args => s!"{emitExpr e}.{m}({", ".intercalate (args.map emitExpr)})"
  | .binop op l r => s!"({emitExpr l} {emitBinOp op} {emitExpr r})"
  | .unop op e => s!"({emitUnOp op}{emitExpr e})"
  | .cond c t f => s!"if {emitExpr c} \{ {emitExpr t} \} else \{ {emitExpr f} \}"
  | .match_ e cases =>
    let arms := cases.map fun (pat, body) =>
      s!"    {emitPattern pat} => {emitExpr body},"
    s!"match {emitExpr e} \{\n" ++ "\n".intercalate arms ++ "\n}"
  | .lambda args body =>
    s!"|{", ".intercalate args}| {emitExpr body}"
  | .construct name fields =>
    if fields.isEmpty then name
    else s!"{name} \{ " ++ ", ".intercalate (fields.map fun (f, e) => s!"{f}: {emitExpr e}") ++ " }"
  | .tuple es => s!"({", ".intercalate (es.map emitExpr)})"
  | .cast e ty => s!"({emitExpr e} as {emitTy ty})"

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 STATEMENT EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Indentation helper -/
def spaces (n : Nat) : String := String.mk (List.replicate n ' ')

/-- Emit a statement -/
partial def emitStmt (indent : Nat) : Stmt → String
  | .letBind name ty e =>
    let tyAnnotation := match ty with
      | some t => s!": {emitTy t}"
      | none => ""
    spaces indent ++ s!"let {name}{tyAnnotation} = {emitExpr e};"
  | .mutBind name ty e =>
    let tyAnnotation := match ty with
      | some t => s!": {emitTy t}"
      | none => ""
    spaces indent ++ s!"let mut {name}{tyAnnotation} = {emitExpr e};"
  | .assign lhs rhs =>
    spaces indent ++ s!"{emitExpr lhs} = {emitExpr rhs};"
  | .expr e =>
    spaces indent ++ emitExpr e ++ ";"
  | .ret (some e) =>
    spaces indent ++ emitExpr e  -- Rust uses final expression, no semicolon
  | .ret none =>
    spaces indent ++ "return;"
  | .if_ cond thenBody elseBody =>
    let thenStmts := thenBody.map (emitStmt (indent + 4))
    let elseBlock := match elseBody with
      | some stmts => " else {\n" ++ "\n".intercalate (stmts.map (emitStmt (indent + 4))) ++ "\n" ++ spaces indent ++ "}"
      | none => ""
    spaces indent ++ s!"if {emitExpr cond} \{\n" ++ 
    "\n".intercalate thenStmts ++ "\n" ++ 
    spaces indent ++ "}" ++ elseBlock
  | .match_ e cases =>
    let arms := cases.map fun (pat, stmts) =>
      let body := if stmts.length == 1 then
        (emitStmt 0 stmts.head!).trim
      else
        "{\n" ++ "\n".intercalate (stmts.map (emitStmt (indent + 8))) ++ "\n" ++ spaces (indent + 4) ++ "}"
      spaces (indent + 4) ++ s!"{emitPattern pat} => {body},"
    spaces indent ++ s!"match {emitExpr e} \{\n" ++
    "\n".intercalate arms ++ "\n" ++
    spaces indent ++ "}"
  | .while_ cond body =>
    let bodyStmts := body.map (emitStmt (indent + 4))
    spaces indent ++ s!"while {emitExpr cond} \{\n" ++
    "\n".intercalate bodyStmts ++ "\n" ++
    spaces indent ++ "}"
  | .for_ var iter body =>
    let bodyStmts := body.map (emitStmt (indent + 4))
    spaces indent ++ s!"for {var} in {emitExpr iter} \{\n" ++
    "\n".intercalate bodyStmts ++ "\n" ++
    spaces indent ++ "}"
  | .block stmts =>
    spaces indent ++ "{\n" ++
    "\n".intercalate (stmts.map (emitStmt (indent + 4))) ++ "\n" ++
    spaces indent ++ "}"
  | .comment c =>
    spaces indent ++ "// " ++ c

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 TYPE DEFINITION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Map derivable trait to Rust derive name -/
def derivableToRust (opts : Options) : Derivable → Option String
  | .eq => some "PartialEq, Eq"
  | .ord => some "PartialOrd, Ord"
  | .hash => some "Hash"
  | .show => some "Debug"
  | .debug => some "Debug"
  | .default_ => some "Default"
  | .clone => some "Clone"
  | .copy => some "Copy"
  | .serialize => if opts.serde then some "serde::Serialize" else none
  | .deserialize => if opts.serde then some "serde::Deserialize" else none
  | .arbitrary => none  -- Would need proptest or quickcheck

/-- Emit derive attribute -/
def emitDerives (derives : List Derivable) (opts : Options) : String :=
  let mapped := derives.filterMap (derivableToRust opts)
  if mapped.isEmpty then ""
  else "#[derive(" ++ ", ".intercalate mapped ++ ")]\n"

/-- Default derives for types -/
def defaultDerives : List Derivable := 
  [.debug, .clone, .eq, .serialize, .deserialize]

/-- Emit a field definition -/
def emitField (f : Field) : String :=
  let doc := match f.doc with
    | some d => "    /// " ++ d ++ "\n"
    | none => ""
  doc ++ s!"    pub {f.name}: {emitTy f.ty},"

/-- Emit a struct -/
def emitStruct (name : String) (params : List String) (fields : List Field)
    (opts : Options) : String :=
  let derives := emitDerives defaultDerives opts
  let genericParams := if params.isEmpty then ""
    else s!"<{", ".intercalate params}>"
  let fieldDefs := fields.map emitField
  derives ++ s!"pub struct {name}{genericParams} \{\n" ++
  "\n".intercalate fieldDefs ++ "\n" ++
  "}"

/-- Emit a variant definition -/
def emitVariant (v : Variant) : String :=
  let doc := match v.doc with
    | some d => "    /// " ++ d ++ "\n    "
    | none => "    "
  if v.fields.isEmpty then
    doc ++ v.name ++ ","
  else if v.fields.length == 1 && v.fields.head!.name == "0" then
    -- Tuple variant
    doc ++ v.name ++ "(" ++ emitTy v.fields.head!.ty ++ "),"
  else
    -- Struct variant
    let fieldDefs := v.fields.map (fun f => s!"        {f.name}: {emitTy f.ty},")
    doc ++ v.name ++ " {\n" ++ "\n".intercalate fieldDefs ++ "\n    },"

/-- Emit an enum -/
def emitEnum (name : String) (params : List String) (variants : List Variant)
    (opts : Options) : String :=
  let derives := emitDerives defaultDerives opts
  let genericParams := if params.isEmpty then ""
    else s!"<{", ".intercalate params}>"
  let variantDefs := variants.map emitVariant
  derives ++ s!"pub enum {name}{genericParams} \{\n" ++
  "\n".intercalate variantDefs ++ "\n" ++
  "}"

/-- Emit a newtype -/
def emitNewtype (name : String) (params : List String) (inner : Ty)
    (opts : Options) : String :=
  let derives := emitDerives defaultDerives opts
  let genericParams := if params.isEmpty then ""
    else s!"<{", ".intercalate params}>"
  derives ++ s!"pub struct {name}{genericParams}(pub {emitTy inner});"

/-- Emit a type alias -/
def emitAlias (name : String) (params : List String) (ty : Ty) : String :=
  let genericParams := if params.isEmpty then ""
    else s!"<{", ".intercalate params}>"
  s!"pub type {name}{genericParams} = {emitTy ty};"

/-- Emit a type definition -/
def emitTypeDef (td : TypeDef) (opts : Options := defaultOptions) : String :=
  match td with
  | .struct name params fields => emitStruct name params fields opts
  | .enum name params variants => emitEnum name params variants opts
  | .newtype name params ty => emitNewtype name params ty opts
  | .alias name params ty => emitAlias name params ty

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 FUNCTION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a function signature -/
def emitFuncSig (f : FuncDef) (opts : Options) : String :=
  let mustUse := if opts.mustUse && f.returnTy != .prim .unit 
    then "#[must_use]\n" else ""
  let visibility := match f.visibility with
    | .public_ => "pub "
    | .private_ => ""
    | .internal => "pub(crate) "
  let genericParams := if f.typeParams.isEmpty then ""
    else s!"<{", ".intercalate f.typeParams}>"
  let params := f.params.map fun p => s!"{p.name}: {emitTy p.ty}"
  let retTy := if f.returnTy == .prim .unit then ""
    else s!" -> {emitTy f.returnTy}"
  mustUse ++ visibility ++ s!"fn {f.name}{genericParams}({", ".intercalate params}){retTy}"

/-- Emit a function body -/
def emitFuncBody (body : FuncBody) : String :=
  match body with
  | .expr e => s!" \{\n    {emitExpr e}\n\}"
  | .stmts stmts => " {\n" ++ "\n".intercalate (stmts.map (emitStmt 4)) ++ "\n}"

/-- Emit a complete function -/
def emitFunc (f : FuncDef) (opts : Options := defaultOptions) : String :=
  let doc := match f.doc with
    | some d => "/// " ++ d ++ "\n"
    | none => ""
  doc ++ emitFuncSig f opts ++ emitFuncBody f.body

-- ════════════════════════════════════════════════════════════════════════════════
-- §7 STATE MACHINE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit state machine as enums + impl -/
def emitStateMachine (sm : StateMachine) (opts : Options) : String :=
  let doc := match sm.doc with
    | some d => "/// " ++ d ++ "\n"
    | none => ""
  
  -- State enum
  let stateVariants := sm.states.map fun s =>
    let doc := match s.doc with
      | some d => "    /// " ++ d ++ "\n    "
      | none => "    "
    doc ++ s.name ++ ","
  let stateEnum := emitDerives [.debug, .clone, .copy, .eq] opts ++
    s!"pub enum {sm.name}State \{\n" ++ "\n".intercalate stateVariants ++ "\n}"
  
  -- Event enum
  let eventVariants := sm.events.map fun e =>
    let doc := match e.doc with
      | some d => "    /// " ++ d ++ "\n    "
      | none => "    "
    if e.payload.isEmpty then doc ++ e.name ++ ","
    else
      let fields := e.payload.map (fun f => s!"{f.name}: {emitTy f.ty}")
      doc ++ e.name ++ " { " ++ ", ".intercalate fields ++ " },"
  let eventEnum := emitDerives [.debug, .clone] opts ++
    s!"pub enum {sm.name}Event \{\n" ++ "\n".intercalate eventVariants ++ "\n}"
  
  -- Action enum
  let actionVariants := sm.actions.map fun a =>
    let doc := match a.doc with
      | some d => "    /// " ++ d ++ "\n    "
      | none => "    "
    if a.payload.isEmpty then doc ++ a.name ++ ","
    else
      let fields := a.payload.map (fun f => s!"{f.name}: {emitTy f.ty}")
      doc ++ a.name ++ " { " ++ ", ".intercalate fields ++ " },"
  let actionEnum := emitDerives [.debug, .clone] opts ++
    s!"pub enum {sm.name}Action \{\n" ++ "\n".intercalate actionVariants ++ "\n}"
  
  -- Impl block with transition function
  let transitionArms := sm.transitions.map fun t =>
    let actions := if t.actions.isEmpty then "vec![]"
      else s!"vec![{", ".intercalate (t.actions.map (s!"{sm.name}Action::" ++ ·))}]"
    s!"            ({sm.name}State::{t.from_}, {sm.name}Event::{t.event}) => \n                ({sm.name}State::{t.to}, {actions}),"
  let implBlock := s!"impl {sm.name}State \{\n" ++
    s!"    /// Transition from current state given an event\n" ++
    s!"    pub fn transition(self, event: {sm.name}Event) -> (Self, Vec<{sm.name}Action>) \{\n" ++
    s!"        match (self, event) \{\n" ++
    "\n".intercalate transitionArms ++ "\n" ++
    s!"            (state, _) => (state, vec![]),\n" ++
    s!"        \}\n" ++
    s!"    \}\n" ++
    s!"\}"
  
  -- Initial state
  let initialState := sm.states.find? (·.isInitial) |>.map (·.name) |>.getD (sm.states.head!.name)
  let defaultImpl := s!"impl Default for {sm.name}State \{\n" ++
    s!"    fn default() -> Self \{\n" ++
    s!"        {sm.name}State::{initialState}\n" ++
    s!"    \}\n" ++
    s!"\}"
  
  doc ++
  stateEnum ++ "\n\n" ++
  eventEnum ++ "\n\n" ++
  actionEnum ++ "\n\n" ++
  implBlock ++ "\n\n" ++
  defaultImpl

-- ════════════════════════════════════════════════════════════════════════════════
-- §8 MODULE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit module header -/
def emitModuleHeader (m : Module) (opts : Options) : String :=
  let doc := match m.doc with
    | some d => "//! " ++ d.replace "\n" "\n//! " ++ "\n\n"
    | none => ""
  let allow := "#![allow(dead_code)]\n"
  let serde := if opts.serde then "use serde::{Serialize, Deserialize};\n" else ""
  doc ++ allow ++ serde

/-- Emit a complete module -/
def emitModule (m : Module) (opts : Options := defaultOptions) : String :=
  let header := emitModuleHeader m opts
  let types := m.types.map (emitTypeDef · opts)
  let functions := m.functions.map (emitFunc · opts)
  let machines := m.machines.map (emitStateMachine · opts)
  
  header ++ "\n" ++
  "// Types\n" ++ "\n\n".intercalate types ++ "\n\n" ++
  "// Functions\n" ++ "\n\n".intercalate functions ++ "\n\n" ++
  "// State Machines\n" ++ "\n\n".intercalate machines

end Foundry.Continuity.CodeGen.Rust
