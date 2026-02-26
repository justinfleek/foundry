import Foundry.Foundry.Continuity.CodeGen

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // C++23 // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                    IR.Module → C++23 Source Code

                        / Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Generates modern C++23 from the CodeGen IR:

  - std::variant for sum types
  - std::expected for Result types
  - std::span for byte slices
  - Designated initializers for structs
  - Concepts for constraints
  - constexpr where possible
  - [[nodiscard]] for pure functions

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/


namespace Foundry.Continuity.CodeGen.Cpp

open Foundry.Continuity.CodeGen

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════════

/-- C++23 code generation options -/
structure Options where
  /-- Namespace for generated code -/
  namespace_ : String := "continuity"
  /-- Include guards style -/
  pragmaOnce : Bool := true
  /-- Generate constexpr where possible -/
  constexpr : Bool := true
  /-- Generate nodiscard attributes -/
  nodiscard : Bool := true
  /-- Generate span-based APIs -/
  spans : Bool := true
  /-- Indentation width -/
  indent : Nat := 4
  deriving Repr, Inhabited

def defaultOptions : Options := {}

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 PRIMITIVE TYPE MAPPING
-- ════════════════════════════════════════════════════════════════════════════════

/-- Map IR primitive to C++ type -/
def emitPrim : Prim → String
  | .unit => "void"
  | .bool => "bool"
  | .u8 => "std::uint8_t"
  | .u16 => "std::uint16_t"
  | .u32 => "std::uint32_t"
  | .u64 => "std::uint64_t"
  | .i8 => "std::int8_t"
  | .i16 => "std::int16_t"
  | .i32 => "std::int32_t"
  | .i64 => "std::int64_t"
  | .usize => "std::size_t"
  | .isize => "std::ptrdiff_t"
  | .f32 => "float"
  | .f64 => "double"
  | .bytes => "std::vector<std::uint8_t>"
  | .string => "std::string"

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 TYPE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a type expression -/
partial def emitTy : Ty → String
  | .prim p => emitPrim p
  | .named n => n
  | .array t => s!"std::vector<{emitTy t}>"
  | .fixedArray t n => s!"std::array<{emitTy t}, {n}>"
  | .optional t => s!"std::optional<{emitTy t}>"
  | .result ok err => s!"std::expected<{emitTy ok}, {emitTy err}>"
  | .tuple ts => s!"std::tuple<{", ".intercalate (ts.map emitTy)}>"
  | .func args ret =>
    let argTys := ", ".intercalate (args.map emitTy)
    s!"std::function<{emitTy ret}({argTys})>"
  | .generic name args =>
    s!"{name}<{", ".intercalate (args.map emitTy)}>"

/-- Emit type for function parameter (may use const ref) -/
def emitParamTy (t : Ty) : String :=
  match t with
  | .prim .bytes => "std::span<const std::uint8_t>"
  | .prim .string => "std::string_view"
  | .array _ => s!"const {emitTy t}&"
  | .named _ => s!"const {emitTy t}&"
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
  | .concat => "+"  -- Requires operator overloading

/-- Emit a unary operator -/
def emitUnOp : UnOp → String
  | .neg => "-"
  | .not => "!"
  | .bitnot => "~"

/-- Emit a literal -/
def emitLit : Lit → String
  | .inl true => "true"
  | .inl false => "false"
  | .inr (.inl n) => s!"{n}ULL"
  | .inr (.inr (.inl n)) => toString n  -- Int
  | .inr (.inr (.inr (.inl s))) => "\"" ++ s ++ "\""  -- TODO: escape
  | .inr (.inr (.inr (.inr ()))) => "{}"

/-- Emit a pattern for switch/variant visit -/
def emitPattern : Pattern → String
  | .inl v => v
  | .inr (ctor, bindings) =>
    if bindings.isEmpty then ctor
    else s!"{ctor}" ++ "{" ++ ", ".intercalate bindings ++ "}"

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
  | .cond c t f => s!"({emitExpr c} ? {emitExpr t} : {emitExpr f})"
  | .match_ e cases =>
    -- Use std::visit pattern
    let arms := cases.map fun (pat, body) =>
      s!"[](const {emitPattern pat}& v) \{ return {emitExpr body}; \}"
    s!"std::visit(overloaded\{{", ".intercalate arms}\}, {emitExpr e})"
  | .lambda args body =>
    s!"[&]({", ".intercalate (args.map (· ++ " auto"))})\{ return {emitExpr body}; \}"
  | .construct name fields =>
    if fields.isEmpty then s!"{name}\{\}"
    else s!"{name}\{" ++ ", ".intercalate (fields.map fun (f, e) => s!".{f} = {emitExpr e}") ++ "}"
  | .tuple es => s!"\{{", ".intercalate (es.map emitExpr)}\}"
  | .cast e ty => s!"static_cast<{emitTy ty}>({emitExpr e})"

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 STATEMENT EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Indentation helper -/
def spaces (n : Nat) : String := String.mk (List.replicate n ' ')

/-- Emit a statement -/
partial def emitStmt (indent : Nat) : Stmt → String
  | .letBind name ty e =>
    let tyStr := match ty with
      | some t => emitTy t
      | none => "auto"
    spaces indent ++ s!"{tyStr} {name} = {emitExpr e};"
  | .mutBind name ty e =>
    let tyStr := match ty with
      | some t => emitTy t
      | none => "auto"
    spaces indent ++ s!"{tyStr} {name} = {emitExpr e};"
  | .assign lhs rhs =>
    spaces indent ++ s!"{emitExpr lhs} = {emitExpr rhs};"
  | .expr e =>
    spaces indent ++ emitExpr e ++ ";"
  | .ret (some e) =>
    spaces indent ++ s!"return {emitExpr e};"
  | .ret none =>
    spaces indent ++ "return;"
  | .if_ cond thenBody elseBody =>
    let thenStmts := thenBody.map (emitStmt (indent + 4))
    let elseBlock := match elseBody with
      | some stmts => " else {\n" ++ "\n".intercalate (stmts.map (emitStmt (indent + 4))) ++ "\n" ++ spaces indent ++ "}"
      | none => ""
    spaces indent ++ s!"if ({emitExpr cond}) \{\n" ++ 
    "\n".intercalate thenStmts ++ "\n" ++ 
    spaces indent ++ "}" ++ elseBlock
  | .match_ e cases =>
    let arms := cases.map fun (pat, stmts) =>
      let body := "\n".intercalate (stmts.map (emitStmt (indent + 8)))
      spaces (indent + 4) ++ s!"[]({emitPattern pat}& v) \{\n{body}\n" ++ spaces (indent + 4) ++ "}"
    spaces indent ++ s!"std::visit(overloaded\{\n" ++
    ",\n".intercalate arms ++ "\n" ++
    spaces indent ++ s!"\}, {emitExpr e});"
  | .while_ cond body =>
    let bodyStmts := body.map (emitStmt (indent + 4))
    spaces indent ++ s!"while ({emitExpr cond}) \{\n" ++
    "\n".intercalate bodyStmts ++ "\n" ++
    spaces indent ++ "}"
  | .for_ var iter body =>
    let bodyStmts := body.map (emitStmt (indent + 4))
    spaces indent ++ s!"for (auto& {var} : {emitExpr iter}) \{\n" ++
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

/-- Emit a field definition -/
def emitField (f : Field) : String :=
  let doc := match f.doc with
    | some d => "    /// " ++ d ++ "\n"
    | none => ""
  doc ++ s!"    {emitTy f.ty} {f.name};"

/-- Emit comparison operators (C++20 style) -/
def emitComparison (name : String) : String :=
  s!"    auto operator<=>(const {name}&) const = default;"

/-- Emit a struct -/
def emitStruct (name : String) (params : List String) (fields : List Field) 
    (opts : Options) : String :=
  let templateDecl := if params.isEmpty then ""
    else s!"template<{", ".intercalate (params.map (s!"typename " ++ ·))}>\n"
  let fieldDefs := fields.map emitField
  let comparison := emitComparison name
  templateDecl ++ s!"struct {name} \{\n" ++
  "\n".intercalate fieldDefs ++ "\n\n" ++
  comparison ++ "\n" ++
  "};"

/-- Emit a variant case for std::variant -/
def emitVariantCase (v : Variant) : String :=
  let doc := match v.doc with
    | some d => "/// " ++ d ++ "\n"
    | none => ""
  if v.fields.isEmpty then
    doc ++ s!"struct {v.name} \{\n    auto operator<=>(const {v.name}&) const = default;\n\};"
  else
    let fieldDefs := v.fields.map emitField
    doc ++ s!"struct {v.name} \{\n" ++
    "\n".intercalate fieldDefs ++ "\n" ++
    s!"    auto operator<=>(const {v.name}&) const = default;\n\};"

/-- Emit an enum as std::variant -/
def emitEnum (name : String) (params : List String) (variants : List Variant)
    (opts : Options) : String :=
  let templateDecl := if params.isEmpty then ""
    else s!"template<{", ".intercalate (params.map (s!"typename " ++ ·))}>\n"
  
  -- First emit variant structs
  let variantStructs := variants.map emitVariantCase
  
  -- Then emit the variant alias
  let variantNames := variants.map (·.name)
  let variantType := s!"using {name} = std::variant<{", ".intercalate variantNames}>;"
  
  "// Variant cases for " ++ name ++ "\n" ++
  "\n\n".intercalate variantStructs ++ "\n\n" ++
  templateDecl ++ variantType

/-- Emit a newtype (C++ doesn't have newtypes, use struct wrapper) -/
def emitNewtype (name : String) (params : List String) (inner : Ty) : String :=
  let templateDecl := if params.isEmpty then ""
    else s!"template<{", ".intercalate (params.map (s!"typename " ++ ·))}>\n"
  templateDecl ++ s!"struct {name} \{\n    {emitTy inner} value;\n    auto operator<=>(const {name}&) const = default;\n\};"

/-- Emit a type alias -/
def emitAlias (name : String) (params : List String) (ty : Ty) : String :=
  let templateDecl := if params.isEmpty then ""
    else s!"template<{", ".intercalate (params.map (s!"typename " ++ ·))}>\n"
  templateDecl ++ s!"using {name} = {emitTy ty};"

/-- Emit a type definition -/
def emitTypeDef (td : TypeDef) (opts : Options := defaultOptions) : String :=
  match td with
  | .struct name params fields => emitStruct name params fields opts
  | .enum name params variants => emitEnum name params variants opts
  | .newtype name params ty => emitNewtype name params ty
  | .alias name params ty => emitAlias name params ty

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 FUNCTION EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a function signature -/
def emitFuncSig (f : FuncDef) (opts : Options) : String :=
  let nodiscard := if opts.nodiscard && f.returnTy != .prim .unit 
    then "[[nodiscard]] " else ""
  let constexpr_ := if opts.constexpr then "constexpr " else ""
  let templateDecl := if f.typeParams.isEmpty then ""
    else s!"template<{", ".intercalate (f.typeParams.map (s!"typename " ++ ·))}>\n"
  let params := f.params.map fun p => s!"{emitParamTy p.ty} {p.name}"
  templateDecl ++ nodiscard ++ constexpr_ ++ 
  s!"{emitTy f.returnTy} {f.name}({", ".intercalate params})"

/-- Emit a function body -/
def emitFuncBody (body : FuncBody) : String :=
  match body with
  | .expr e => s!" \{\n    return {emitExpr e};\n\}"
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

/-- Emit state machine as variant + transition function -/
def emitStateMachine (sm : StateMachine) (opts : Options) : String :=
  let doc := match sm.doc with
    | some d => "/// " ++ d ++ "\n"
    | none => ""
  
  -- State enum
  let stateEnum := s!"enum class {sm.name}State : std::uint8_t \{\n" ++
    ",\n".intercalate (sm.states.map (fun s => s!"    {s.name}")) ++
    "\n};"
  
  -- Event variant
  let eventStructs := sm.events.map fun e =>
    if e.payload.isEmpty then s!"struct {e.name}Event \{\};"
    else s!"struct {e.name}Event \{\n" ++
      "\n".intercalate (e.payload.map (fun f => s!"    {emitTy f.ty} {f.name};")) ++
      "\n};"
  let eventNames := sm.events.map (·.name ++ "Event")
  let eventVariant := s!"using {sm.name}Event = std::variant<{", ".intercalate eventNames}>;"
  
  -- Action variant
  let actionStructs := sm.actions.map fun a =>
    if a.payload.isEmpty then s!"struct {a.name}Action \{\};"
    else s!"struct {a.name}Action \{\n" ++
      "\n".intercalate (a.payload.map (fun f => s!"    {emitTy f.ty} {f.name};")) ++
      "\n};"
  let actionNames := sm.actions.map (·.name ++ "Action")
  let actionVariant := s!"using {sm.name}Action = std::variant<{", ".intercalate actionNames}>;"
  
  -- Transition function
  let transitionSig := s!"inline std::pair<{sm.name}State, std::vector<{sm.name}Action>> transition({sm.name}State state, const {sm.name}Event& event)"
  let defaultCase := s!"        return \{state, \{\}\};"
  let transitionBody := " {\n    return std::visit(overloaded{\n" ++
    ",\n".intercalate (sm.transitions.map fun t =>
      let actions := if t.actions.isEmpty then "{}"
        else s!"\{{", ".intercalate (t.actions.map (· ++ "Action{}"))}\}"
      s!"        [&](const {t.event}Event&) -> std::pair<{sm.name}State, std::vector<{sm.name}Action>> \{\n" ++
      s!"            if (state == {sm.name}State::{t.from_}) return \{{sm.name}State::{t.to}, {actions}\};\n" ++
      s!"            return \{state, \{\}\};\n" ++
      s!"        \}"
    ) ++
    "\n    }, event);\n}"
  
  -- Initial state
  let initialState := sm.states.find? (·.isInitial) |>.map (·.name) |>.getD (sm.states.head!.name)
  let initialDef := s!"constexpr {sm.name}State initial{sm.name}State = {sm.name}State::{initialState};"
  
  doc ++
  "// State enum\n" ++ stateEnum ++ "\n\n" ++
  "// Event types\n" ++ "\n".intercalate eventStructs ++ "\n" ++ eventVariant ++ "\n\n" ++
  "// Action types\n" ++ "\n".intercalate actionStructs ++ "\n" ++ actionVariant ++ "\n\n" ++
  "// Transition function\n" ++ transitionSig ++ transitionBody ++ "\n\n" ++
  "// Initial state\n" ++ initialDef

-- ════════════════════════════════════════════════════════════════════════════════
-- §8 HEADER EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

/-- Standard includes for generated code -/
def standardIncludes : String := String.intercalate "\n" [
  "#include " ++ "<" ++ "cstdint" ++ ">",
  "#include " ++ "<" ++ "cstddef" ++ ">",
  "#include " ++ "<" ++ "string" ++ ">",
  "#include " ++ "<" ++ "string_view" ++ ">",
  "#include " ++ "<" ++ "vector" ++ ">",
  "#include " ++ "<" ++ "array" ++ ">",
  "#include " ++ "<" ++ "span" ++ ">",
  "#include " ++ "<" ++ "optional" ++ ">",
  "#include " ++ "<" ++ "expected" ++ ">",
  "#include " ++ "<" ++ "variant" ++ ">",
  "#include " ++ "<" ++ "functional" ++ ">",
  "#include " ++ "<" ++ "utility" ++ ">"
]

/-- Overloaded helper for std::visit -/
def overloadedHelper : String :=
  "// Helper for std::visit with lambdas\n" ++
  "template" ++ "<" ++ "class... Ts" ++ ">" ++ " struct overloaded : Ts... " ++ "{" ++ " using Ts::operator()...; " ++ "}" ++ ";\n" ++
  "template" ++ "<" ++ "class... Ts" ++ ">" ++ " overloaded(Ts...) -" ++ ">" ++ " overloaded" ++ "<" ++ "Ts..." ++ ">" ++ ";"

/-- Emit a complete header file -/
def emitHeader (m : Module) (opts : Options := defaultOptions) : String :=
  let guard := if opts.pragmaOnce then "#pragma once\n" else
    let guardName := m.name.toUpper.map (fun c => if c == '.' then '_' else c)
    s!"#ifndef {guardName}_HPP\n#define {guardName}_HPP\n"
  
  let moduleDoc := match m.doc with
    | some d => "/**\n * " ++ d.replace "\n" "\n * " ++ "\n */\n"
    | none => ""
  
  let nsBegin := s!"namespace {opts.namespace_} \{\n"
  let nsEnd := s!"\} // namespace {opts.namespace_}"
  
  let types := m.types.map (emitTypeDef · opts)
  let functions := m.functions.map (emitFunc · opts)
  let machines := m.machines.map (emitStateMachine · opts)
  
  let guardEnd := if opts.pragmaOnce then "" else "\n#endif"
  
  guard ++ "\n" ++
  moduleDoc ++
  standardIncludes ++ "\n\n" ++
  overloadedHelper ++ "\n\n" ++
  nsBegin ++ "\n" ++
  "// Types\n" ++ "\n\n".intercalate types ++ "\n\n" ++
  "// Functions\n" ++ "\n\n".intercalate functions ++ "\n\n" ++
  "// State Machines\n" ++ "\n\n".intercalate machines ++ "\n\n" ++
  nsEnd ++ guardEnd

/-- Emit module (alias for header in C++) -/
def emitModule := emitHeader

end Foundry.Continuity.CodeGen.Cpp
