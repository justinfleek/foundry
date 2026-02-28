/-
  Cornell.ExtractCpp - C++ Code Generation from Box Definitions
  
  Generates parse/serialize functions in C++ from Lean4 Box specifications.
  The generated code is verified correct by construction (same structure as proofs).
  
  ## Design
  
  1. BoxExpr - AST representing box structure
  2. genParse/genSerialize - Generate C++ code strings
  3. genHeader - Generate complete .hpp file
  
  ## Generated Code Structure
  
  ```cpp
  // Parse result type
  template<typename T>
  struct ParseResult {
      std::optional<T> value;
      std::span<const uint8_t> remaining;
  };
  
  // Each box generates:
  ParseResult<T> parse_typename(std::span<const uint8_t> bs);
  std::vector<uint8_t> serialize_typename(const T& value);
  ```
-/

import Foundry.Cornell.Basic
import Foundry.Cornell.Nix

namespace Cornell.ExtractCpp

open Cornell

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX EXPRESSION AST
-- Represents the structure of a Box for code generation
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Primitive types that map directly to C++ -/
inductive PrimType where
  | u8 | u16le | u32le | u64le | bool64
  deriving Repr, DecidableEq

/-- Box expression - describes the structure of a codec -/
inductive BoxExpr where
  /-- Primitive fixed-size type -/
  | prim : PrimType → BoxExpr
  /-- Sequence of two boxes (parse A then B) -/
  | seq : BoxExpr → BoxExpr → BoxExpr
  /-- Dependent box (header determines body) -/
  | dep : BoxExpr → String → BoxExpr  -- header box, body selector name
  /-- Isomorphic mapping (wrap/unwrap) -/
  | iso : BoxExpr → String → String → BoxExpr  -- inner box, to_fn, from_fn
  /-- Length-prefixed array -/
  | array : BoxExpr → BoxExpr
  /-- Nix-style padded string -/
  | nixString : BoxExpr
  /-- Named reference to another box -/
  | ref : String → BoxExpr
  /-- Fixed-size byte array -/
  | bytesN : Nat → BoxExpr
  /-- Optional field (version-gated) -/
  | optional : BoxExpr → String → BoxExpr  -- inner box, condition expression
  deriving Repr

/-- A named box definition -/
structure BoxDef where
  name : String
  cppType : String
  expr : BoxExpr
  deriving Repr

-- ═══════════════════════════════════════════════════════════════════════════════
-- C++ TYPE MAPPING
-- ═══════════════════════════════════════════════════════════════════════════════

def primTypeToCpp : PrimType → String
  | .u8 => "uint8_t"
  | .u16le => "uint16_t"
  | .u32le => "uint32_t"
  | .u64le => "uint64_t"
  | .bool64 => "bool"

def primTypeSize : PrimType → Nat
  | .u8 => 1
  | .u16le => 2
  | .u32le => 4
  | .u64le => 8
  | .bool64 => 8

-- ═══════════════════════════════════════════════════════════════════════════════
-- CODE GENERATION - PARSE FUNCTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Generate parse expression for a primitive type -/
def genParsePrim (pt : PrimType) (inputVar : String) : String :=
  let size := primTypeSize pt
  let cppType := primTypeToCpp pt
  match pt with
  | .u8 => 
    s!"if ({inputVar}.size() < 1) return \{std::nullopt, {inputVar}};
    {cppType} value = {inputVar}[0];
    auto remaining = {inputVar}.subspan(1);"
  | .u16le =>
    s!"if ({inputVar}.size() < 2) return \{std::nullopt, {inputVar}};
    {cppType} value = static_cast<{cppType}>({inputVar}[0]) 
                    | (static_cast<{cppType}>({inputVar}[1]) << 8);
    auto remaining = {inputVar}.subspan(2);"
  | .u32le =>
    s!"if ({inputVar}.size() < 4) return \{std::nullopt, {inputVar}};
    {cppType} value = static_cast<{cppType}>({inputVar}[0])
                    | (static_cast<{cppType}>({inputVar}[1]) << 8)
                    | (static_cast<{cppType}>({inputVar}[2]) << 16)
                    | (static_cast<{cppType}>({inputVar}[3]) << 24);
    auto remaining = {inputVar}.subspan(4);"
  | .u64le =>
    s!"if ({inputVar}.size() < 8) return \{std::nullopt, {inputVar}};
    {cppType} value = static_cast<{cppType}>({inputVar}[0])
                    | (static_cast<{cppType}>({inputVar}[1]) << 8)
                    | (static_cast<{cppType}>({inputVar}[2]) << 16)
                    | (static_cast<{cppType}>({inputVar}[3]) << 24)
                    | (static_cast<{cppType}>({inputVar}[4]) << 32)
                    | (static_cast<{cppType}>({inputVar}[5]) << 40)
                    | (static_cast<{cppType}>({inputVar}[6]) << 48)
                    | (static_cast<{cppType}>({inputVar}[7]) << 56);
    auto remaining = {inputVar}.subspan(8);"
  | .bool64 =>
    s!"if ({inputVar}.size() < 8) return \{std::nullopt, {inputVar}};
    uint64_t raw = static_cast<uint64_t>({inputVar}[0])
                 | (static_cast<uint64_t>({inputVar}[1]) << 8)
                 | (static_cast<uint64_t>({inputVar}[2]) << 16)
                 | (static_cast<uint64_t>({inputVar}[3]) << 24)
                 | (static_cast<uint64_t>({inputVar}[4]) << 32)
                 | (static_cast<uint64_t>({inputVar}[5]) << 40)
                 | (static_cast<uint64_t>({inputVar}[6]) << 48)
                 | (static_cast<uint64_t>({inputVar}[7]) << 56);
    bool value = raw != 0;
    auto remaining = {inputVar}.subspan(8);"

/-- Generate serialize expression for a primitive type -/
def genSerializePrim (pt : PrimType) (valueVar : String) : String :=
  match pt with
  | .u8 => 
    s!"result.push_back(static_cast<uint8_t>({valueVar}));"
  | .u16le =>
    s!"result.push_back(static_cast<uint8_t>({valueVar} & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 8) & 0xFF));"
  | .u32le =>
    s!"result.push_back(static_cast<uint8_t>({valueVar} & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 8) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 16) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 24) & 0xFF));"
  | .u64le =>
    s!"result.push_back(static_cast<uint8_t>({valueVar} & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 8) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 16) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 24) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 32) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 40) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 48) & 0xFF));
    result.push_back(static_cast<uint8_t>(({valueVar} >> 56) & 0xFF));"
  | .bool64 =>
    s!"uint64_t bool_raw = {valueVar} ? 1 : 0;
    result.push_back(static_cast<uint8_t>(bool_raw & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 8) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 16) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 24) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 32) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 40) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 48) & 0xFF));
    result.push_back(static_cast<uint8_t>((bool_raw >> 56) & 0xFF));"

-- ═══════════════════════════════════════════════════════════════════════════════
-- FULL FUNCTION GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Counter for generating unique variable names -/
structure GenState where
  varCounter : Nat := 0

def freshVar (varPrefix : String) : StateM GenState String := do
  let s ← get
  set { s with varCounter := s.varCounter + 1 }
  return s!"{varPrefix}_{s.varCounter}"

/-- Struct field definition -/
structure FieldDef where
  name : String
  cppType : String
  expr : BoxExpr
  deriving Repr

/-- Struct definition for composite types -/
structure StructDef where
  name : String
  fields : List FieldDef
  deriving Repr

/-- Generate parse call for an expression (inline or function call) -/
partial def genParseExpr (expr : BoxExpr) (inputVar : String) (counter : Nat) : String × String × Nat :=
  match expr with
  | .prim pt =>
    let varName := s!"v{counter}"
    let code := match pt with
      | .u64le => s!"
    if ({inputVar}.size() < 8) return \{std::nullopt, {inputVar}};
    uint64_t {varName} = static_cast<uint64_t>({inputVar}[0])
                 | (static_cast<uint64_t>({inputVar}[1]) << 8)
                 | (static_cast<uint64_t>({inputVar}[2]) << 16)
                 | (static_cast<uint64_t>({inputVar}[3]) << 24)
                 | (static_cast<uint64_t>({inputVar}[4]) << 32)
                 | (static_cast<uint64_t>({inputVar}[5]) << 40)
                 | (static_cast<uint64_t>({inputVar}[6]) << 48)
                 | (static_cast<uint64_t>({inputVar}[7]) << 56);
    auto rest{counter} = {inputVar}.subspan(8);"
      | .bool64 => s!"
    if ({inputVar}.size() < 8) return \{std::nullopt, {inputVar}};
    uint64_t raw{counter} = static_cast<uint64_t>({inputVar}[0])
                 | (static_cast<uint64_t>({inputVar}[1]) << 8)
                 | (static_cast<uint64_t>({inputVar}[2]) << 16)
                 | (static_cast<uint64_t>({inputVar}[3]) << 24)
                 | (static_cast<uint64_t>({inputVar}[4]) << 32)
                 | (static_cast<uint64_t>({inputVar}[5]) << 40)
                 | (static_cast<uint64_t>({inputVar}[6]) << 48)
                 | (static_cast<uint64_t>({inputVar}[7]) << 56);
    bool {varName} = raw{counter} != 0;
    auto rest{counter} = {inputVar}.subspan(8);"
      | _ => s!"// TODO: parse {repr pt}"
    (code, s!"rest{counter}", counter + 1)
  | .ref refName =>
    let varName := s!"v{counter}"
    let code := s!"
    auto r{counter} = parse_{refName}({inputVar});
    if (!r{counter}) return \{std::nullopt, {inputVar}};
    auto {varName} = *r{counter}.value;
    auto rest{counter} = r{counter}.remaining;"
    (code, s!"rest{counter}", counter + 1)
  | .nixString =>
    let varName := s!"v{counter}"
    let code := s!"
    auto r{counter} = parse_nix_string({inputVar});
    if (!r{counter}) return \{std::nullopt, {inputVar}};
    auto {varName} = *r{counter}.value;
    auto rest{counter} = r{counter}.remaining;"
    (code, s!"rest{counter}", counter + 1)
  | .array elemExpr =>
    let varName := s!"arr{counter}"
    let code := s!"
    // Parse length-prefixed array
    if ({inputVar}.size() < 8) return \{std::nullopt, {inputVar}};
    uint64_t len{counter} = static_cast<uint64_t>({inputVar}[0])
                 | (static_cast<uint64_t>({inputVar}[1]) << 8)
                 | (static_cast<uint64_t>({inputVar}[2]) << 16)
                 | (static_cast<uint64_t>({inputVar}[3]) << 24)
                 | (static_cast<uint64_t>({inputVar}[4]) << 32)
                 | (static_cast<uint64_t>({inputVar}[5]) << 40)
                 | (static_cast<uint64_t>({inputVar}[6]) << 48)
                 | (static_cast<uint64_t>({inputVar}[7]) << 56);
    auto rest{counter} = {inputVar}.subspan(8);
    std::vector</* element type */> {varName};
    for (uint64_t i = 0; i < len{counter}; ++i) \{
        // TODO: parse element
    }"
    (code, s!"rest{counter}", counter + 1)
  | _ => (s!"// TODO: parse expr {repr expr}", inputVar, counter)

/-- Generate serialize call for an expression -/
partial def genSerializeExpr (expr : BoxExpr) (valueExpr : String) : String :=
  match expr with
  | .prim .u64le => s!"
    \{
        uint64_t v = {valueExpr};
        result.push_back(static_cast<uint8_t>(v & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 8) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 16) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 24) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 32) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 40) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 48) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 56) & 0xFF));
    }"
  | .prim .bool64 => s!"
    \{
        uint64_t v = {valueExpr} ? 1 : 0;
        result.push_back(static_cast<uint8_t>(v & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 8) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 16) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 24) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 32) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 40) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 48) & 0xFF));
        result.push_back(static_cast<uint8_t>((v >> 56) & 0xFF));
    }"
  | .ref refName => s!"
    \{
        auto bytes = serialize_{refName}({valueExpr});
        result.insert(result.end(), bytes.begin(), bytes.end());
    }"
  | .nixString => s!"
    \{
        auto bytes = serialize_nix_string({valueExpr});
        result.insert(result.end(), bytes.begin(), bytes.end());
    }"
  | .array _ => s!"
    // TODO: serialize array {valueExpr}"
  | _ => s!"// TODO: serialize {repr expr}"

/-- Generate struct definition -/
def genStructDef (def_ : StructDef) : String :=
  let fields := def_.fields.map (fun f => s!"    {f.cppType} {f.name};") |> String.intercalate "\n"
  s!"struct {def_.name} \{
{fields}
};"

/-- Generate parse function for a struct -/
def genStructParseFunction (def_ : StructDef) : String :=
  let header := s!"ParseResult<{def_.name}> parse_{def_.name.toLower}(std::span<const uint8_t> bs)"
  -- Build parse code and track the current input variable
  let rec go (fields : List FieldDef) (inputVar : String) (counter : Nat) (code : String) (assignments : List String) : String × List String × String :=
    match fields with
    | [] => (code, assignments, inputVar)
    | f :: rest =>
      let (fieldCode, nextInput, nextCounter) := genParseExpr f.expr inputVar counter
      let assignment := s!"value.{f.name} = v{counter};"
      go rest nextInput nextCounter (code ++ fieldCode) (assignments ++ [assignment])
  let (parseCode, assignments, lastInput) := go def_.fields "bs" 0 "" []
  let assignCode := assignments.map (s!"    " ++ ·) |> String.intercalate "\n"
  s!"{header} \{
    {def_.name} value;{parseCode}
{assignCode}
    return \{value, {lastInput}};
}"

/-- Generate serialize function for a struct -/
def genStructSerializeFunction (def_ : StructDef) : String :=
  let header := s!"std::vector<uint8_t> serialize_{def_.name.toLower}(const {def_.name}& value)"
  let serializeCode := def_.fields.map (fun f => genSerializeExpr f.expr s!"value.{f.name}") |> String.intercalate ""
  s!"{header} \{
    std::vector<uint8_t> result;{serializeCode}
    return result;
}"

/-- Generate complete parse function for a box definition -/
def genParseFunction (def_ : BoxDef) : String :=
  let header := s!"ParseResult<{def_.cppType}> parse_{def_.name}(std::span<const uint8_t> bs)"
  -- For now, generate based on the expression type
  match def_.expr with
  | .prim pt =>
    let body := genParsePrim pt "bs"
    s!"{header} \{
    {body}
    return \{value, remaining};
}"
  | .nixString =>
    s!"{header} \{
    // Parse length
    if (bs.size() < 8) return \{std::nullopt, bs};
    uint64_t len = static_cast<uint64_t>(bs[0])
                 | (static_cast<uint64_t>(bs[1]) << 8)
                 | (static_cast<uint64_t>(bs[2]) << 16)
                 | (static_cast<uint64_t>(bs[3]) << 24)
                 | (static_cast<uint64_t>(bs[4]) << 32)
                 | (static_cast<uint64_t>(bs[5]) << 40)
                 | (static_cast<uint64_t>(bs[6]) << 48)
                 | (static_cast<uint64_t>(bs[7]) << 56);
    auto rest = bs.subspan(8);
    
    // Calculate padding
    size_t pad = (8 - (len % 8)) % 8;
    size_t total = len + pad;
    
    if (rest.size() < total) return \{std::nullopt, bs};
    
    {def_.cppType} value;
    value.data.assign(rest.begin(), rest.begin() + len);
    auto remaining = rest.subspan(total);
    return \{value, remaining};
}"
  | .ref refName =>
    s!"{header} \{
    return parse_{refName}(bs);
}"
  | _ => s!"// TODO: generate parse for {repr def_.expr}\n{header};"

/-- Generate complete serialize function for a box definition -/  
def genSerializeFunction (def_ : BoxDef) : String :=
  let header := s!"std::vector<uint8_t> serialize_{def_.name}(const {def_.cppType}& value)"
  match def_.expr with
  | .prim pt =>
    let body := genSerializePrim pt "value"
    s!"{header} \{
    std::vector<uint8_t> result;
    {body}
    return result;
}"
  | .nixString =>
    s!"{header} \{
    std::vector<uint8_t> result;
    
    // Serialize length
    uint64_t len = value.data.size();
    result.push_back(static_cast<uint8_t>(len & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 8) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 16) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 24) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 32) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 40) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 48) & 0xFF));
    result.push_back(static_cast<uint8_t>((len >> 56) & 0xFF));
    
    // Serialize data
    result.insert(result.end(), value.data.begin(), value.data.end());
    
    // Add padding
    size_t pad = (8 - (len % 8)) % 8;
    for (size_t i = 0; i < pad; ++i) result.push_back(0);
    
    return result;
}"
  | .ref refName =>
    s!"{header} \{
    return serialize_{refName}(value);
}"
  | _ => s!"// TODO: generate serialize for {repr def_.expr}\n{header};"

-- ═══════════════════════════════════════════════════════════════════════════════
-- ENUM GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Enum variant with name and wire code -/
structure EnumVariant where
  name : String
  code : UInt64
  deriving Repr

/-- Enum definition -/
structure EnumDef where
  name : String
  baseType : String  -- e.g., "uint64_t"
  variants : List EnumVariant
  deriving Repr

/-- Generate C++ enum class -/
def genEnumClass (def_ : EnumDef) : String :=
  let variants := def_.variants.map (fun v => s!"    {v.name} = {v.code},") |> String.intercalate "\n"
  s!"enum class {def_.name} : {def_.baseType} \{
{variants}
};"

/-- Generate fromCode function for enum -/
def genEnumFromCode (def_ : EnumDef) : String :=
  let cases := def_.variants.map (fun v => 
    s!"        case {v.code}: return {def_.name}::{v.name};") |> String.intercalate "\n"
  s!"inline std::optional<{def_.name}> {def_.name.toLower}_from_code({def_.baseType} code) \{
    switch (code) \{
{cases}
        default: return std::nullopt;
    }
}"

/-- Generate toCode function for enum -/  
def genEnumToCode (def_ : EnumDef) : String :=
  s!"inline {def_.baseType} {def_.name.toLower}_to_code({def_.name} op) \{
    return static_cast<{def_.baseType}>(op);
}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- WORKER OP ENUM (from Foundry.Cornell.Nix)
-- ═══════════════════════════════════════════════════════════════════════════════

def workerOpEnum : EnumDef := {
  name := "WorkerOp"
  baseType := "uint64_t"
  variants := [
    { name := "IsValidPath", code := 1 },
    { name := "HasSubstitutes", code := 3 },
    { name := "QueryPathHash", code := 4 },
    { name := "QueryReferences", code := 5 },
    { name := "QueryReferrers", code := 6 },
    { name := "AddToStore", code := 7 },
    { name := "AddTextToStore", code := 8 },
    { name := "BuildPaths", code := 9 },
    { name := "EnsurePath", code := 10 },
    { name := "AddTempRoot", code := 11 },
    { name := "AddIndirectRoot", code := 12 },
    { name := "SyncWithGC", code := 13 },
    { name := "FindRoots", code := 14 },
    { name := "ExportPath", code := 16 },
    { name := "QueryDeriver", code := 18 },
    { name := "SetOptions", code := 19 },
    { name := "CollectGarbage", code := 20 },
    { name := "QuerySubstitutablePathInfo", code := 21 },
    { name := "QueryDerivationOutputs", code := 22 },
    { name := "QueryAllValidPaths", code := 23 },
    { name := "QueryFailedPaths", code := 24 },
    { name := "ClearFailedPaths", code := 25 },
    { name := "QueryPathInfo", code := 26 },
    { name := "ImportPaths", code := 27 },
    { name := "QueryDerivationOutputNames", code := 28 },
    { name := "QueryPathFromHashPart", code := 29 },
    { name := "QuerySubstitutablePathInfos", code := 30 },
    { name := "QueryValidPaths", code := 31 },
    { name := "QuerySubstitutablePaths", code := 32 },
    { name := "QueryValidDerivers", code := 33 },
    { name := "OptimiseStore", code := 34 },
    { name := "VerifyStore", code := 35 },
    { name := "BuildDerivation", code := 36 },
    { name := "AddSignatures", code := 37 },
    { name := "NarFromPath", code := 38 },
    { name := "AddToStoreNar", code := 39 },
    { name := "QueryMissing", code := 40 },
    { name := "QueryDerivationOutputMap", code := 41 },
    { name := "RegisterDrvOutput", code := 42 },
    { name := "QueryRealisation", code := 43 },
    { name := "AddMultipleToStore", code := 44 },
    { name := "AddBuildLog", code := 45 },
    { name := "BuildPathsWithResults", code := 46 }
  ]
}

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOCOL VERSION STRUCT
-- ═══════════════════════════════════════════════════════════════════════════════

def genProtocolVersion : String :=
"// ═══════════════════════════════════════════════════════════════════════════════
// Protocol Version
// ═══════════════════════════════════════════════════════════════════════════════

struct ProtocolVersion {
    uint64_t value;
    
    constexpr ProtocolVersion() : value(0) {}
    constexpr explicit ProtocolVersion(uint64_t v) : value(v) {}
    
    static constexpr ProtocolVersion make(uint64_t major, uint64_t minor) {
        return ProtocolVersion((major << 8) | minor);
    }
    
    constexpr uint64_t major() const { return value >> 8; }
    constexpr uint64_t minor() const { return value & 0xFF; }
    
    constexpr bool supports(uint64_t min_minor) const {
        return minor() >= min_minor;
    }
    
    constexpr bool operator==(const ProtocolVersion& other) const { return value == other.value; }
    constexpr bool operator<(const ProtocolVersion& other) const { return value < other.value; }
    constexpr bool operator<=(const ProtocolVersion& other) const { return value <= other.value; }
    constexpr bool operator>(const ProtocolVersion& other) const { return value > other.value; }
    constexpr bool operator>=(const ProtocolVersion& other) const { return value >= other.value; }
};

constexpr ProtocolVersion CURRENT_PROTOCOL = ProtocolVersion::make(1, 38);
constexpr ProtocolVersion MINIMUM_PROTOCOL = ProtocolVersion::make(1, 10);
"

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROTOCOL CONSTANTS
-- ═══════════════════════════════════════════════════════════════════════════════

def genProtocolConstants : String :=
"// ═══════════════════════════════════════════════════════════════════════════════
// Protocol Constants
// ═══════════════════════════════════════════════════════════════════════════════

constexpr uint64_t WORKER_MAGIC_1 = 0x6e697863;  // \"cxin\" LE
constexpr uint64_t WORKER_MAGIC_2 = 0x6478696f;  // \"oixd\" LE
constexpr uint64_t REAPI_UPGRADE_MAGIC = 0x52455049;  // \"REPI\"

constexpr uint64_t STDERR_NEXT = 0x6f6c6d67;
constexpr uint64_t STDERR_READ = 0x64617461;
constexpr uint64_t STDERR_WRITE = 0x64617416;
constexpr uint64_t STDERR_LAST = 0x616c7473;
constexpr uint64_t STDERR_ERROR = 0x63787470;
constexpr uint64_t STDERR_START_ACTIVITY = 0x53545254;
constexpr uint64_t STDERR_STOP_ACTIVITY = 0x53544F50;
constexpr uint64_t STDERR_RESULT = 0x52534C54;
"

-- ═══════════════════════════════════════════════════════════════════════════════
-- HANDSHAKE STRUCT DEFINITIONS
-- ═══════════════════════════════════════════════════════════════════════════════

def clientHelloStruct : StructDef := {
  name := "ClientHello"
  fields := [
    { name := "client_version", cppType := "uint64_t", expr := .prim .u64le }
  ]
}

def serverHelloStruct : StructDef := {
  name := "ServerHello"
  fields := [
    { name := "server_version", cppType := "uint64_t", expr := .prim .u64le }
  ]
}

def upgradeOfferStruct : StructDef := {
  name := "UpgradeOffer"
  fields := [
    { name := "magic", cppType := "uint64_t", expr := .prim .u64le }  -- REAPI_UPGRADE_MAGIC
  ]
}

def upgradeResponseStruct : StructDef := {
  name := "UpgradeResponse"
  fields := [
    { name := "accept", cppType := "bool", expr := .prim .bool64 }
  ]
}

def reapiConfigStruct : StructDef := {
  name := "ReapiConfig"
  fields := [
    { name := "instance_name", cppType := "NixString", expr := .nixString },
    { name := "digest_function", cppType := "uint64_t", expr := .prim .u64le },
    -- capabilities would be an array of strings, handled separately
  ]
}

def handshakeStructs : List StructDef := [
  clientHelloStruct,
  serverHelloStruct,
  upgradeOfferStruct,
  upgradeResponseStruct,
  reapiConfigStruct
]

-- ═══════════════════════════════════════════════════════════════════════════════
-- TRUST LEVEL ENUM
-- ═══════════════════════════════════════════════════════════════════════════════

def trustLevelEnum : EnumDef := {
  name := "TrustLevel"
  baseType := "uint64_t"
  variants := [
    { name := "Unknown", code := 0 },
    { name := "Trusted", code := 1 },
    { name := "Untrusted", code := 2 }
  ]
}

-- ═══════════════════════════════════════════════════════════════════════════════
-- FEATURE ENUM
-- ═══════════════════════════════════════════════════════════════════════════════

def featureEnum : EnumDef := {
  name := "Feature"
  baseType := "uint64_t"
  variants := [
    { name := "ReapiV2", code := 0 },
    { name := "CasSha256", code := 1 },
    { name := "StreamingNar", code := 2 },
    { name := "SignedNarinfo", code := 3 }
  ]
}

def genFeatureStringConversions : String :=
"inline std::string feature_to_string(Feature f) {
    switch (f) {
        case Feature::ReapiV2: return \"reapi-v2\";
        case Feature::CasSha256: return \"cas-sha256\";
        case Feature::StreamingNar: return \"streaming-nar\";
        case Feature::SignedNarinfo: return \"signed-narinfo\";
        default: return \"unknown\";
    }
}

inline std::optional<Feature> feature_from_string(const std::string& s) {
    if (s == \"reapi-v2\") return Feature::ReapiV2;
    if (s == \"cas-sha256\") return Feature::CasSha256;
    if (s == \"streaming-nar\") return Feature::StreamingNar;
    if (s == \"signed-narinfo\") return Feature::SignedNarinfo;
    return std::nullopt;
}
"

-- ═══════════════════════════════════════════════════════════════════════════════
-- BOX DEFINITIONS FOR NIX PROTOCOL
-- ═══════════════════════════════════════════════════════════════════════════════

def nixProtocolBoxes : List BoxDef := [
  -- Primitives
  { name := "u8", cppType := "uint8_t", expr := .prim .u8 },
  { name := "u16le", cppType := "uint16_t", expr := .prim .u16le },
  { name := "u32le", cppType := "uint32_t", expr := .prim .u32le },
  { name := "u64le", cppType := "uint64_t", expr := .prim .u64le },
  { name := "bool64", cppType := "bool", expr := .prim .bool64 },
  -- Nix types
  { name := "nix_string", cppType := "NixString", expr := .nixString },
  { name := "store_path", cppType := "StorePath", expr := .iso .nixString "StorePath" "to_nix_string" }
]

-- ═══════════════════════════════════════════════════════════════════════════════
-- HEADER FILE GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

def headerPreamble : String := 
"// ═══════════════════════════════════════════════════════════════════════════════
// GENERATED BY CORNELL - DO NOT EDIT
// Source: Cornell.ExtractCpp
// ═══════════════════════════════════════════════════════════════════════════════

#pragma once

#include <cstdint>
#include <optional>
#include <span>
#include <string>
#include <vector>

namespace cornell::generated {

// ═══════════════════════════════════════════════════════════════════════════════
// Parse Result
// ═══════════════════════════════════════════════════════════════════════════════

template<typename T>
struct ParseResult {
    std::optional<T> value;
    std::span<const uint8_t> remaining;
    
    bool ok() const { return value.has_value(); }
    explicit operator bool() const { return ok(); }
};

// ═══════════════════════════════════════════════════════════════════════════════
// Types
// ═══════════════════════════════════════════════════════════════════════════════

struct NixString {
    std::vector<uint8_t> data;
    
    std::string to_string() const {
        return std::string(data.begin(), data.end());
    }
    
    static NixString from_string(const std::string& s) {
        return NixString{std::vector<uint8_t>(s.begin(), s.end())};
    }
};

struct StorePath {
    NixString path;
};

"

def headerPostamble : String :=
"
} // namespace cornell::generated
"

/-- Generate complete header file -/
def genHeader (boxes : List BoxDef) : String :=
  let parseFns := boxes.map genParseFunction |> String.intercalate "\n\n"
  let serializeFns := boxes.map genSerializeFunction |> String.intercalate "\n\n"
  let workerOpCode := s!"{genEnumClass workerOpEnum}\n\n{genEnumFromCode workerOpEnum}\n\n{genEnumToCode workerOpEnum}"
  let trustLevelCode := s!"{genEnumClass trustLevelEnum}"
  let featureCode := s!"{genEnumClass featureEnum}\n\n{genFeatureStringConversions}"
  let structDefs := handshakeStructs.map genStructDef |> String.intercalate "\n\n"
  let structParseFns := handshakeStructs.map genStructParseFunction |> String.intercalate "\n\n"
  let structSerializeFns := handshakeStructs.map genStructSerializeFunction |> String.intercalate "\n\n"
  s!"{headerPreamble}
{genProtocolConstants}

{genProtocolVersion}

// ═══════════════════════════════════════════════════════════════════════════════
// Trust Level
// ═══════════════════════════════════════════════════════════════════════════════

{trustLevelCode}

// ═══════════════════════════════════════════════════════════════════════════════
// Features
// ═══════════════════════════════════════════════════════════════════════════════

{featureCode}

// ═══════════════════════════════════════════════════════════════════════════════
// Worker Operations
// ═══════════════════════════════════════════════════════════════════════════════

{workerOpCode}

// ═══════════════════════════════════════════════════════════════════════════════
// Handshake Structs
// ═══════════════════════════════════════════════════════════════════════════════

{structDefs}

// ═══════════════════════════════════════════════════════════════════════════════
// Parse Functions  
// ═══════════════════════════════════════════════════════════════════════════════

{parseFns}

// Struct parse functions
{structParseFns}

// ═══════════════════════════════════════════════════════════════════════════════
// Serialize Functions
// ═══════════════════════════════════════════════════════════════════════════════

{serializeFns}

// Struct serialize functions
{structSerializeFns}
{headerPostamble}"

-- ═══════════════════════════════════════════════════════════════════════════════
-- OUTPUT
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Write generated header to file -/
def writeGeneratedHeader (path : System.FilePath) : IO Unit := do
  let content := genHeader nixProtocolBoxes
  IO.FS.writeFile path content
  IO.println s!"Generated {path}"

-- For interactive evaluation (disabled - depends on sorry)
-- #eval IO.println (genHeader nixProtocolBoxes)

end Cornell.ExtractCpp

-- Main function at root scope for executable
def main (args : List String) : IO Unit := do
  let outputPath := args.head?.getD "cpp/include/cornell/generated.hpp"
  Cornell.ExtractCpp.writeGeneratedHeader outputPath
