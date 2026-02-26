import Foundry.Foundry.Continuity.CodeGen
import Foundry.Foundry.Continuity.CodeGen.Doc

/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                             // HASKELL // EMIT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                    IR.Module → Doc → Haskell Source

                        razorgirl / Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Generates idiomatic Haskell 2021 with:
  - GHC2021 language standard
  - OverloadedRecordDot for field access
  - StrictData for efficiency
  - DerivingStrategies for clean deriving

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Foundry.Continuity.CodeGen.Emit.Haskell

open Foundry.Continuity.CodeGen
open Foundry.Continuity.CodeGen.Doc

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════════

structure Config where
  extensions : List String := [
    "GHC2021", "OverloadedStrings", "StrictData", 
    "DuplicateRecordFields", "OverloadedRecordDot",
    "DerivingStrategies", "DeriveGeneric", "DeriveAnyClass"
  ]
  imports : List String := [
    "Data.ByteString (ByteString)",
    "Data.Text (Text)",
    "Data.Word",
    "Data.Int",
    "GHC.Generics (Generic)"
  ]
  deriving Repr, Inhabited

def defaultConfig : Config := {}

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 PRIMITIVE TYPES
-- ════════════════════════════════════════════════════════════════════════════════

def emitPrim : Prim → Doc
  | .unit => text "()"
  | .bool => text "Bool"
  | .u8 => text "Word8"
  | .u16 => text "Word16"
  | .u32 => text "Word32"
  | .u64 => text "Word64"
  | .i8 => text "Int8"
  | .i16 => text "Int16"
  | .i32 => text "Int32"
  | .i64 => text "Int64"
  | .usize => text "Word"
  | .isize => text "Int"
  | .f32 => text "Float"
  | .f64 => text "Double"
  | .bytes => text "ByteString"
  | .string => text "Text"

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 TYPE EXPRESSIONS
-- ════════════════════════════════════════════════════════════════════════════════

partial def emitTy : Ty → Doc
  | .prim p => emitPrim p
  | .named n => text n
  | .array t => brackets (emitTy t)
  | .fixedArray t n => text "Vector" ++ space ++ nat n ++ space ++ parens (emitTy t)
  | .optional t => text "Maybe" ++ space ++ parens (emitTy t)
  | .result ok err => text "Either" ++ space ++ parens (emitTy err) ++ space ++ parens (emitTy ok)
  | .tuple ts => parens (commas (ts.map emitTy))
  | .func args ret =>
    let allTys := args.map emitTy ++ [emitTy ret]
    intercalate (text " -> ") allTys
  | .generic name tyArgs =>
    text name ++ space ++ hsepList (tyArgs.map (fun t => parens (emitTy t)))

-- ════════════════════════════════════════════════════════════════════════════════
-- §3 LITERALS AND EXPRESSIONS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Emit a literal value -/
def emitLit : Lit → Doc
  | .inl b => if b then text "True" else text "False"
  | .inr (.inl n) => nat n
  | .inr (.inr (.inl i)) => int i
  | .inr (.inr (.inr (.inl s))) => string s
  | .inr (.inr (.inr (.inr ()))) => text "()"

def emitBinOp : BinOp → Doc
  | .add => text "+"
  | .sub => text "-"
  | .mul => text "*"
  | .div => text "`div`"
  | .rem => text "`mod`"
  | .and => text ".&."
  | .or => text ".|."
  | .xor => text "`xor`"
  | .land => text "&&"
  | .lor => text "||"
  | .eq => text "=="
  | .neq => text "/="
  | .lt => text "<"
  | .le => text "<="
  | .gt => text ">"
  | .ge => text ">="
  | .shl => text "`shiftL`"
  | .shr => text "`shiftR`"
  | .concat => text "<>"

def emitUnOp : UnOp → Doc
  | .neg => text "-"
  | .not => text "not"
  | .bitnot => text "complement"

def emitPattern : Pattern → Doc
  | .inl v => text v
  | .inr (ctor, bindings) =>
    if bindings.isEmpty then text ctor
    else text ctor ++ space ++ hsepList (bindings.map text)

partial def emitExpr : Expr → Doc
  | .lit l => emitLit l
  | .var v => text v
  | .field e f => emitExpr e ++ text "." ++ text f
  | .index e i => emitExpr e ++ text " !! " ++ emitExpr i
  | .call f args => 
    text f ++ space ++ hsepList (args.map (parens ∘ emitExpr))
  | .methodCall e m args =>
    text m ++ space ++ emitExpr e ++ space ++ hsepList (args.map (parens ∘ emitExpr))
  | .binop op l r => parens (emitExpr l ++ space ++ emitBinOp op ++ space ++ emitExpr r)
  | .unop op e => parens (emitUnOp op ++ space ++ emitExpr e)
  | .cond c t f => 
    text "if" ++ space ++ emitExpr c ++ 
    space ++ text "then" ++ space ++ emitExpr t ++
    space ++ text "else" ++ space ++ emitExpr f
  | .match_ e cases =>
    let branches := cases.map fun (pat, body) =>
      emitPattern pat ++ text " -> " ++ emitExpr body
    text "case" ++ space ++ emitExpr e ++ space ++ text "of" ++
    nest 2 (line ++ vsepList branches)
  | .lambda args body =>
    text "\\" ++ hsepList (args.map text) ++ text " -> " ++ emitExpr body
  | .construct name fields =>
    if fields.isEmpty then text name
    else text name ++ space ++ braces (
      commasSep (fields.map fun (f, e) => text f ++ text " = " ++ emitExpr e)
    )
  | .tuple es => parens (commas (es.map emitExpr))
  | .cast e _ty => emitExpr e

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 TYPE DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

def emitField (f : Field) : Doc :=
  text f.name ++ text " :: " ++ emitTy f.ty

def emitRecordFields (fields : List Field) : Doc :=
  braces (group (nest 2 (line ++ commasSep (fields.map emitField)) ++ line))

def emitVariant (v : Variant) : Doc :=
  if v.fields.isEmpty then
    text v.name
  else if v.fields.length == 1 && v.fields.head!.name == "_0" then
    -- Single unnamed field: positional
    text v.name ++ space ++ emitTy v.fields.head!.ty
  else
    -- Named fields: record syntax
    text v.name ++ space ++ emitRecordFields v.fields

def emitTypeParams (params : List String) : Doc :=
  if params.isEmpty then empty
  else space ++ hsepList (params.map text)

def emitDeriving : Doc :=
  line ++ text "deriving stock (Eq, Show, Generic)"

def emitTypeDef : TypeDef → Doc
  | .struct name params fields =>
    text "data" ++ space ++ text name ++ emitTypeParams params ++ text " = " ++
    text name ++ space ++ emitRecordFields fields ++
    emitDeriving
  | .enum name params variants =>
    let variantDocs := variants.map emitVariant
    text "data" ++ space ++ text name ++ emitTypeParams params ++
    nest 2 (line ++ text "= " ++ intercalate (line ++ text "| ") variantDocs) ++
    emitDeriving
  | .newtype name params inner =>
    text "newtype" ++ space ++ text name ++ emitTypeParams params ++ text " = " ++
    text name ++ space ++ braces (text "un" ++ text name ++ text " :: " ++ emitTy inner) ++
    emitDeriving
  | .alias name params target =>
    text "type" ++ space ++ text name ++ emitTypeParams params ++ text " = " ++ emitTy target

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 FUNCTION DEFINITIONS
-- ════════════════════════════════════════════════════════════════════════════════

def emitParam (p : Param) : Doc := text p.name

def emitFuncSig (f : FuncDef) : Doc :=
  let paramTys := f.params.map (fun p => emitTy p.ty)
  let allTys := paramTys ++ [emitTy f.returnTy]
  text f.name ++ text " :: " ++ intercalate (text " -> ") allTys

def emitFuncBody : FuncBody → Doc
  | .expr e => emitExpr e
  | .stmts _ => text "undefined"  -- TODO: do-notation

def emitFuncDef (f : FuncDef) : Doc :=
  let sig := emitFuncSig f
  let params := hsepList (f.params.map emitParam)
  let body := emitFuncBody f.body
  sig ++ line ++
  text f.name ++ space ++ params ++ text " = " ++ body

-- ════════════════════════════════════════════════════════════════════════════════
-- §6 STATE MACHINE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

def emitStateMachine (sm : StateMachine) : Doc :=
  -- State type
  let stateDoc := 
    text "data" ++ space ++ text sm.name ++ text "State" ++
    nest 2 (line ++ text "= " ++ intercalate (line ++ text "| ") 
      (sm.states.map (fun s => text (sm.name ++ "State" ++ s.name)))) ++
    emitDeriving
  -- Event type  
  let eventDoc :=
    text "data" ++ space ++ text sm.name ++ text "Event" ++
    nest 2 (line ++ text "= " ++ intercalate (line ++ text "| ")
      (sm.events.map (fun e => text (sm.name ++ "Event" ++ e.name)))) ++
    emitDeriving
  -- Action type
  let actionDoc :=
    text "data" ++ space ++ text sm.name ++ text "Action" ++
    nest 2 (line ++ text "= " ++ intercalate (line ++ text "| ")
      (sm.actions.map (fun a => text (sm.name ++ "Action" ++ a.name)))) ++
    emitDeriving
  stateDoc ++ line ++ line ++ eventDoc ++ line ++ line ++ actionDoc

-- ════════════════════════════════════════════════════════════════════════════════
-- §7 MODULE EMISSION
-- ════════════════════════════════════════════════════════════════════════════════

def emitExtensions (exts : List String) : Doc :=
  vsepList (exts.map (fun e => text "{-# LANGUAGE " ++ text e ++ text " #-}"))

def emitImports (imports : List String) : Doc :=
  vsepList (imports.map (fun i => text "import " ++ text i))

def emitModuleHeader (m : Module) : Doc :=
  text "module" ++ space ++ text m.name ++ space ++ text "where"

def emitModule (cfg : Config) (m : Module) : Doc :=
  let extensions := emitExtensions cfg.extensions
  let header := emitModuleHeader m
  let imports := emitImports cfg.imports
  let types := vsepList (m.types.map (fun t => emitTypeDef t ++ line))
  let machines := vsepList (m.machines.map (fun sm => emitStateMachine sm ++ line))
  let functions := vsepList (m.functions.map (fun f => emitFuncDef f ++ line))
  
  extensions ++ line ++ line ++
  header ++ line ++ line ++
  imports ++ line ++ line ++
  (match m.doc with | some d => hsDocComment d ++ line ++ line | none => empty) ++
  types ++
  machines ++
  functions

/-- Generate Haskell source code from a module -/
def generate (m : Module) : String :=
  pretty (emitModule defaultConfig m)

def generateWith (cfg : Config) (m : Module) : String :=
  pretty (emitModule cfg m)

end Foundry.Continuity.CodeGen.Emit.Haskell
