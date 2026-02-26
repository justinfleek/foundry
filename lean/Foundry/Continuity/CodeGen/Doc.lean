/-!
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // DOCUMENT // ALGEBRA
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

                   A Pretty-Printing Algebra for Code Generation

                           razorgirl / Straylight / 2026

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Based on Wadler's "A prettier printer" - a simple algebra for documents
that separates layout decisions from content:

  Doc = text s           -- literal text (no newlines)
      | line             -- newline or space (if flattened)
      | hardline         -- always newline
      | doc <> doc       -- concatenation
      | nest n doc       -- indent by n when broken
      | group doc        -- try to fit on one line

The renderer chooses between breaking groups or keeping them flat
based on available width.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

namespace Foundry.Continuity.CodeGen.Doc

-- ════════════════════════════════════════════════════════════════════════════════
-- §0 DOCUMENT TYPE
-- ════════════════════════════════════════════════════════════════════════════════

/-- A document for pretty-printing -/
inductive Doc where
  | nil                              -- Empty document
  | text : String → Doc              -- Literal text (must not contain newlines)
  | line : Bool → Doc                -- Newline; Bool = can flatten to space?
  | cat : Doc → Doc → Doc            -- Concatenation
  | nest : Nat → Doc → Doc           -- Increase indentation
  | group : Doc → Doc                -- Try to fit on one line
  | align : Doc → Doc                -- Align to current column
  deriving Repr, Inhabited

-- ════════════════════════════════════════════════════════════════════════════════
-- §1 CORE CONSTRUCTORS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Empty document -/
def empty : Doc := .nil

/-- Literal text (should not contain newlines) -/
def text (s : String) : Doc := if s.isEmpty then .nil else .text s

/-- Newline that can be flattened to a space -/
def line : Doc := .line true

/-- Newline that can be flattened to nothing -/
def linebreak : Doc := .line false

/-- Newline that cannot be flattened -/
def hardline : Doc := .cat (.line true) (.text "")  -- trick: text after prevents flattening

/-- Concatenate two documents -/
def append (a b : Doc) : Doc :=
  match a, b with
  | .nil, d => d
  | d, .nil => d
  | _, _ => .cat a b

instance : Append Doc where
  append := append

/-- Nest (indent) a document by n spaces -/
def nest (n : Nat) (d : Doc) : Doc := .nest n d

/-- Try to fit document on one line -/
def group (d : Doc) : Doc := .group d

/-- Align nested content to current column -/
def align (d : Doc) : Doc := .align d

-- ════════════════════════════════════════════════════════════════════════════════
-- §2 DERIVED COMBINATORS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Single space -/
def space : Doc := text " "

/-- Concatenate with a space between -/
def hsep (a b : Doc) : Doc := a ++ space ++ b

/-- Concatenate with a line between -/
def vsep (a b : Doc) : Doc := a ++ line ++ b

/-- Concatenate with a softline (space or newline) -/
def softline : Doc := group line

/-- Separator: line when broken, space when flat -/
def sep (a b : Doc) : Doc := a ++ softline ++ b

/-- Concatenate a list horizontally with spaces -/
def hsepList (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | [d] => d
  | d :: ds => ds.foldl hsep d

/-- Concatenate a list vertically with lines -/
def vsepList (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | [d] => d
  | d :: ds => ds.foldl vsep d

/-- Concatenate with a separator -/
def intercalate (sep : Doc) (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | [d] => d
  | d :: ds => ds.foldl (fun acc x => acc ++ sep ++ x) d

/-- Punctuate: add separator after each element except last -/
def punctuate (sep : Doc) (docs : List Doc) : List Doc :=
  match docs with
  | [] => []
  | [d] => [d]
  | d :: ds => (d ++ sep) :: punctuate sep ds

/-- Wrap in delimiters -/
def enclose (l r : Doc) (d : Doc) : Doc := l ++ d ++ r

/-- Parentheses -/
def parens (d : Doc) : Doc := enclose (text "(") (text ")") d

/-- Brackets -/
def brackets (d : Doc) : Doc := enclose (text "[") (text "]") d

/-- Braces -/
def braces (d : Doc) : Doc := enclose (text "{") (text "}") d

/-- Angles -/
def angles (d : Doc) : Doc := enclose (text "<") (text ">") d

/-- Double quotes -/
def dquotes (d : Doc) : Doc := enclose (text "\"") (text "\"") d

/-- Single quotes -/
def squotes (d : Doc) : Doc := enclose (text "'") (text "'") d

/-- Comma-separated list -/
def commas (docs : List Doc) : Doc := intercalate (text ", ") docs

/-- Comma-separated, with line breaks if needed -/
def commasSep (docs : List Doc) : Doc :=
  intercalate (text "," ++ line) docs

/-- Indented block -/
def indented (n : Nat) (d : Doc) : Doc := nest n (line ++ d)

/-- Block with braces -/
def block (d : Doc) : Doc := 
  text "{" ++ indented 2 d ++ line ++ text "}"

/-- Hanging indent: first line not indented -/
def hang (n : Nat) (d : Doc) : Doc := align (nest n d)

/-- Fill: try horizontal, break to vertical -/
def fillSep (docs : List Doc) : Doc :=
  match docs with
  | [] => empty
  | [d] => d
  | d :: ds => ds.foldl sep d

-- ════════════════════════════════════════════════════════════════════════════════
-- §3 RENDERING
-- ════════════════════════════════════════════════════════════════════════════════

/-- Rendering mode for a piece of document -/
inductive Mode where
  | flat    -- Render on single line
  | break_  -- Render with line breaks
  deriving Repr, DecidableEq

/-- Simplified document for rendering -/
inductive SimpleDoc where
  | nil
  | text : String → SimpleDoc → SimpleDoc
  | line : Nat → SimpleDoc → SimpleDoc  -- Nat = indentation
  deriving Repr, Inhabited

/-- Does this doc fit in the remaining width? -/
partial def fits (width : Int) (doc : SimpleDoc) : Bool :=
  if width < 0 then false
  else match doc with
    | .nil => true
    | .text s rest => fits (width - s.length) rest
    | .line _ _ => true  -- Always fits at line break

/-- Best layout: choose between flat and break based on width -/
partial def best (width : Int) (col : Int) 
    (docs : List (Nat × Mode × Doc)) : SimpleDoc :=
  match docs with
  | [] => .nil
  | (_, _, .nil) :: rest => best width col rest
  | (i, m, .text s) :: rest => 
    .text s (best width (col + s.length) rest)
  | (i, m, .line canFlatten) :: rest =>
    match m with
    | .flat => 
      if canFlatten 
      then .text " " (best width (col + 1) rest)
      else best width col rest
    | .break_ => .line i (best width i rest)
  | (i, m, .cat a b) :: rest =>
    best width col ((i, m, a) :: (i, m, b) :: rest)
  | (i, m, .nest j d) :: rest =>
    best width col ((i + j, m, d) :: rest)
  | (i, _, .group d) :: rest =>
    let flatDoc := best width col ((i, .flat, d) :: rest)
    if fits (width - col) flatDoc
    then flatDoc
    else best width col ((i, .break_, d) :: rest)
  | (i, m, .align d) :: rest =>
    best width col ((col.toNat, m, d) :: rest)

/-- Convert SimpleDoc to string -/
def layout : SimpleDoc → String
  | .nil => ""
  | .text s rest => s ++ layout rest
  | .line i rest => "\n" ++ String.ofList (List.replicate i ' ') ++ layout rest

/-- Render a document to a string with given width -/
def render (width : Nat) (doc : Doc) : String :=
  layout (best width 0 [(0, .break_, doc)])

/-- Render with default width of 80 -/
def pretty (doc : Doc) : String := render 80 doc

/-- Render compactly (minimal line breaks) -/
def compact (doc : Doc) : String := render 1000000 doc

-- ════════════════════════════════════════════════════════════════════════════════
-- §4 STRING UTILITIES
-- ════════════════════════════════════════════════════════════════════════════════

/-- Escape a string for code output -/
def escapeString (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ match c with
      | '\\' => "\\\\"
      | '"' => "\\\""
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | c => String.singleton c
  ) ""

/-- Quoted string -/
def string (s : String) : Doc := dquotes (text (escapeString s))

/-- Integer literal -/
def int (n : Int) : Doc := text (toString n)

/-- Natural literal -/
def nat (n : Nat) : Doc := text (toString n)

-- ════════════════════════════════════════════════════════════════════════════════
-- §5 COMMENTS
-- ════════════════════════════════════════════════════════════════════════════════

/-- Single-line comment (// style) -/
def lineComment (s : String) : Doc := text "// " ++ text s

/-- Single-line comment (-- style, Haskell) -/
def hsLineComment (s : String) : Doc := text "-- " ++ text s

/-- Single-line comment (# style) -/
def hashComment (s : String) : Doc := text "# " ++ text s

/-- Multi-line comment block -/
def blockComment (lines : List String) : Doc :=
  text "/*" ++ line ++ 
  vsepList (lines.map (fun l => text " * " ++ text l)) ++
  line ++ text " */"

/-- Doc comment (Haskell style) -/
def hsDocComment (s : String) : Doc := text "-- | " ++ text s

/-- Doc comment (Rust style) -/
def rustDocComment (s : String) : Doc := text "/// " ++ text s

end Foundry.Continuity.CodeGen.Doc
