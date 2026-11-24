/-
  DanaCore/Text.lean
  Canonical `(dana-core 0.1 ...)` S-expression wire codec (printer & parser)
  and canonical `(dana-report 0.1 ...)` formatter for Dana Core IR v0.1.
-/
import DanaCore.Syntax
import DanaCore.Check
import DanaCore.Eval

namespace DanaCore

local instance {α : Type} : Inhabited (Except String α) := ⟨.error ""⟩

/-! ## Canonical S-Expression AST -/

inductive SExp where
  | atom (s : String)
  | str (s : String)
  | list (items : List SExp)
  deriving BEq, Repr, Inhabited

/-! ## Canonical String Escaping & S-Expression Printer -/

def natToLowerHex (n : Nat) : String :=
  if n == 0 then "0"
  else
    let rec go (fuel : Nat) (v : Nat) (acc : List Char) : List Char :=
      match fuel with
      | 0 => acc
      | f + 1 =>
        if v == 0 then acc
        else
          let d := v % 16
          let c := if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)
          go f (v / 16) (c :: acc)
    String.ofList (go 16 n [])

def isControlChar (c : Char) : Bool :=
  c.toNat < 0x20 || c.toNat == 0x7F || (0x80 ≤ c.toNat && c.toNat ≤ 0x9F)

def escapeCanonicalChar (c : Char) : String :=
  if c == '"' then "\\\""
  else if c == '\\' then "\\\\"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if isControlChar c then
    "\\u{" ++ natToLowerHex c.toNat ++ "}"
  else
    String.singleton c

def escapeCanonicalString (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeCanonicalChar) ++ "\""

def printSExp : SExp → String
  | .atom s => s
  | .str s => escapeCanonicalString s
  | .list items => "(" ++ String.intercalate " " (printSExpList items) ++ ")"
where
  printSExpList : List SExp → List String
    | [] => []
    | x :: xs => printSExp x :: printSExpList xs

/-! ## Strict S-Expression Tokenizer & Parser -/

def isLowerHexDigitChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def hexCharVal (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else 10 + (c.toNat - 'a'.toNat)

def parseLowerHexNat (cs : List Char) : Option Nat :=
  if cs.isEmpty || cs.length > 6 || !cs.all isLowerHexDigitChar then none
  else some (cs.foldl (fun acc c => acc * 16 + hexCharVal c) 0)

def isAtomChar (c : Char) : Bool :=
  !isControlChar c && c != ' ' && c != '(' && c != ')' && c != '"' && c != '\\'

partial def parseEscapedStringChars : List Char → List Char → Except String (String × List Char)
  | [], _ => .error "unterminated string literal"
  | '"' :: rest, acc => .ok (String.ofList acc.reverse, rest)
  | '\\' :: esc :: rest, acc =>
    match esc with
    | '"' => parseEscapedStringChars rest ('"' :: acc)
    | '\\' => parseEscapedStringChars rest ('\\' :: acc)
    | 'n' => parseEscapedStringChars rest ('\n' :: acc)
    | 'r' => parseEscapedStringChars rest ('\r' :: acc)
    | 't' => parseEscapedStringChars rest ('\t' :: acc)
    | 'u' =>
      match rest with
      | '{' :: uRest =>
        let hexDigits := uRest.takeWhile (· != '}')
        let afterHex := uRest.dropWhile (· != '}')
        match afterHex with
        | '}' :: tail =>
          match parseLowerHexNat hexDigits with
          | none => .error "invalid or non-lowercase \\u{hex} escape in string"
          | some cp =>
            if (0xD800 ≤ cp && cp ≤ 0xDFFF) || cp > 0x10FFFF then
              .error "surrogate or out-of-range Unicode scalar in \\u{hex}"
            else
              let ch := Char.ofNat cp
              if !isControlChar ch || ch == '\n' || ch == '\r' || ch == '\t' ||
                 String.ofList hexDigits != natToLowerHex cp then
                .error "non-canonical \\u{hex} escape in string"
              else
                parseEscapedStringChars tail (ch :: acc)
        | _ => .error "unclosed \\u{...} escape"
      | _ => .error "expected '{' after \\u"
    | _ => .error s!"unknown string escape '\\{esc}'"
  | '\\' :: [], _ => .error "trailing backslash in string"
  | c :: rest, acc =>
    if isControlChar c then
      .error "raw control character inside string literal"
    else
      parseEscapedStringChars rest (c :: acc)

partial def parseSExpChars : List Char → Except String (SExp × List Char)
  | [] => .error "unexpected end of S-expression"
  | '(' :: rest => parseListItems rest []
  | '"' :: rest => do
    let (s, rem) ← parseEscapedStringChars rest []
    .ok (.str s, rem)
  | c :: rest =>
    if !isAtomChar c then
      .error "unexpected delimiter or control character in S-expression"
    else
      let tailAtoms := rest.takeWhile isAtomChar
      let rem := rest.dropWhile isAtomChar
      .ok (.atom (String.ofList (c :: tailAtoms)), rem)
where
  parseListItems (chars : List Char) (acc : List SExp) : Except String (SExp × List Char) :=
    match chars with
    | [] => .error "unclosed '(' in S-expression"
    | ')' :: rest => .ok (.list acc.reverse, rest)
    | ' ' :: ')' :: _ => .error "trailing space before ')' in canonical S-expression"
    | ' ' :: ' ' :: _ => .error "duplicate space in canonical S-expression"
    | ' ' :: rest =>
      if acc.isEmpty then .error "leading space after '(' in canonical S-expression"
      else do
        let (item, rem) ← parseSExpChars rest
        parseListItems rem (item :: acc)
    | _ =>
      if !acc.isEmpty then .error "missing single space separator between S-expression items"
      else do
        let (item, rem) ← parseSExpChars chars
        parseListItems rem (item :: acc)

/-- Parse a complete canonical single-line S-expression (requiring a single trailing LF). -/
def parseCanonicalSExp (input : String) : Except String SExp := do
  let raw := input.toList
  let bodyChars ←
    match raw.reverse with
    | '\n' :: revRest =>
      if revRest.contains '\n' || revRest.contains '\r' then
        .error "internal line breaks forbidden in canonical wire format"
      else .ok revRest.reverse
    | _ =>
      .error "canonical wire format requires single trailing LF"
  if bodyChars.any isControlChar then
    .error "raw control characters forbidden in canonical wire format"
  else do
    let (sexp, rem) ← parseSExpChars bodyChars
    if rem.isEmpty then .ok sexp
    else .error "trailing characters after top-level S-expression"

/-! ## Primitive Encoders & Decoders -/

def encodeBool : Bool → SExp
  | true => .atom "true"
  | false => .atom "false"

def decodeBool : SExp → Except String Bool
  | .atom "true" => .ok true
  | .atom "false" => .ok false
  | _ => .error "expected bool atom"

def encodeNat (n : Nat) : SExp := .atom (toString n)

def decodeNat : SExp → Except String Nat
  | .atom s =>
    match s.toNat? with
    | some n => .ok n
    | none => .error s!"expected Nat, got '{s}'"
  | _ => .error "expected Nat atom"

def encodeInt (n : Int) : SExp := .atom (toString n)

def decodeInt : SExp → Except String Int
  | .atom s =>
    match s.toInt? with
    | some n => .ok n
    | none => .error s!"expected Int, got '{s}'"
  | _ => .error "expected Int atom"

def encodeIdent (id : Ident) : SExp := .str id

def decodeIdent : SExp → Except String Ident
  | .str s => .ok s
  | .atom s => .ok s
  | _ => .error "expected identifier"

def encodeOpt {α : Type} (enc : α → SExp) : Option α → SExp
  | none => .list [.atom "none"]
  | some v => .list [.atom "some", enc v]

def decodeOpt {α : Type} (dec : SExp → Except String α) : SExp → Except String (Option α)
  | .list [.atom "none"] => .ok none
  | .list [.atom "some", x] => some <$> dec x
  | _ => .error "expected (none) or (some ...)"

def mapDecode {α : Type} (dec : SExp → Except String α) : List SExp → Except String (List α)
  | [] => .ok []
  | x :: xs => do
    let h ← dec x
    let t ← mapDecode dec xs
    .ok (h :: t)

/-! ## Sensitivity, Schema, and Type Wire Serialization -/

def encodeTagSet (ts : TagSet) : SExp :=
  .list (.atom "tags" :: ts.elems.map encodeIdent)

def decodeTagSet : SExp → Except String TagSet
  | .list (.atom "tags" :: items) => do
    let names ← mapDecode decodeIdent items
    let ts := TagSet.ofList names
    if ts.elems == names then .ok ts
    else .error "non-canonical unsorted or duplicate TagSet on wire"
  | _ => .error "expected (tags ...)"

def encodeAggKind : AggKind → SExp
  | .raw => .atom "raw"
  | .groupKey => .atom "group-key"
  | .blending => .atom "blending"
  | .nonBlending => .atom "non-blending"

def decodeAggKind : SExp → Except String AggKind
  | .atom "raw" => .ok .raw
  | .atom "group-key" => .ok .groupKey
  | .atom "blending" => .ok .blending
  | .atom "non-blending" => .ok .nonBlending
  | _ => .error "expected agg-kind"

def encodeScalarTy : ScalarTy → SExp
  | .unit => .list [.atom "unit"]
  | .bool => .list [.atom "bool"]
  | .int => .list [.atom "int"]
  | .decimal => .list [.atom "decimal"]
  | .float => .list [.atom "float"]
  | .text => .list [.atom "text"]
  | .bytes => .list [.atom "bytes"]
  | .date => .list [.atom "date"]
  | .timestamp => .list [.atom "timestamp"]
  | .duration => .list [.atom "duration"]
  | .data n => .list [.atom "data", encodeIdent n]
  | .option inner => .list [.atom "option", encodeScalarTy inner]

partial def decodeScalarTy : SExp → Except String ScalarTy
  | .list [.atom "unit"] => .ok .unit
  | .list [.atom "bool"] => .ok .bool
  | .list [.atom "int"] => .ok .int
  | .list [.atom "decimal"] => .ok .decimal
  | .list [.atom "float"] => .ok .float
  | .list [.atom "text"] => .ok .text
  | .list [.atom "bytes"] => .ok .bytes
  | .list [.atom "date"] => .ok .date
  | .list [.atom "timestamp"] => .ok .timestamp
  | .list [.atom "duration"] => .ok .duration
  | .list [.atom "data", n] => .data <$> decodeIdent n
  | .list [.atom "option", inner] => .option <$> decodeScalarTy inner
  | _ => .error "invalid scalar-ty"

def encodeColSpec (c : ColSpec) : SExp :=
  .list [
    .atom "col",
    encodeIdent c.name,
    encodeScalarTy c.ty,
    encodeTagSet c.tags,
    encodeBool c.bucketed,
    encodeAggKind c.aggKind
  ]

def decodeColSpec : SExp → Except String ColSpec
  | .list [.atom "col", n, t, ts, b, ak] => do
    let name ← decodeIdent n
    let ty ← decodeScalarTy t
    let tags ← decodeTagSet ts
    let bucketed ← decodeBool b
    let aggKind ← decodeAggKind ak
    .ok { name, ty, tags, bucketed, aggKind }
  | _ => .error "expected (col ...)"

def encodeTableTy (tt : TableTy) : SExp :=
  .list [
    .atom "table-ty",
    .list (tt.cols.map encodeColSpec),
    encodeTagSet tt.rowTags,
    encodeTagSet tt.orderTags,
    encodeOpt (fun ks => .list (ks.map encodeIdent)) tt.groupedBy,
    encodeBool tt.summarized,
    encodeOpt encodeIdent tt.distinctBy
  ]

def decodeTableTy : SExp → Except String TableTy
  | .list [.atom "table-ty", .list cs, rt, ot, gb, sumB, db] => do
    let cols ← mapDecode decodeColSpec cs
    let rowTags ← decodeTagSet rt
    let orderTags ← decodeTagSet ot
    let groupedBy ← decodeOpt (fun
      | .list xs => mapDecode decodeIdent xs
      | _ => .error "expected ident list") gb
    let summarized ← decodeBool sumB
    let distinctBy ← decodeOpt decodeIdent db
    .ok { cols, rowTags, orderTags, groupedBy, summarized, distinctBy }
  | _ => .error "expected (table-ty ...)"

def encodeTyList : List LTy → List SExp
  | [] => []
  | _ => [] -- replaced below

mutual
def encodeTy : Ty → SExp
  | .unit => .list [.atom "unit"]
  | .bool => .list [.atom "bool"]
  | .int => .list [.atom "int"]
  | .decimal => .list [.atom "decimal"]
  | .float => .list [.atom "float"]
  | .text => .list [.atom "text"]
  | .bytes => .list [.atom "bytes"]
  | .date => .list [.atom "date"]
  | .timestamp => .list [.atom "timestamp"]
  | .duration => .list [.atom "duration"]
  | .option t => .list [.atom "option", encodeTy t]
  | .result okT errT => .list [.atom "result", encodeTy okT, encodeTy errT]
  | .tuple es => .list [.atom "tuple", .list (encodeLTyList es)]
  | .list e => .list [.atom "list", encodeLTy e]
  | .map k v => .list [.atom "map", encodeLTy k, encodeLTy v]
  | .data n => .list [.atom "data", encodeIdent n]
  | .table tt => .list [.atom "table", encodeTableTy tt]
  | .dynamicTable ts => .list [.atom "dynamic-table", encodeTagSet ts]
  | .chart ts => .list [.atom "chart", encodeTagSet ts]
  | .report ts => .list [.atom "report-ty", encodeTagSet ts]
  | .profile ts => .list [.atom "profile", encodeTagSet ts]
  | .linearModel => .list [.atom "linear-model"]
  | .statTest => .list [.atom "stat-test"]
  | .fn ps pc ret => .list [.atom "fn-ty", .list (encodeLTyList ps), encodeTagSet pc, encodeLTy ret]
  | .args => .list [.atom "args"]
  | .clock => .list [.atom "clock"]
  | .console allows => .list [.atom "console", encodeTagSet allows]
  | .readFiles => .list [.atom "read-files"]
  | .writeFiles root allows => .list [.atom "write-files", .str root, encodeTagSet allows]
  | .readDB db => .list [.atom "read-db", encodeIdent db]
  | .writeTable db tbl cols rt allows =>
    .list [.atom "write-table", encodeIdent db, encodeIdent tbl,
      .list (cols.map encodeColSpec), encodeTagSet rt, encodeTagSet allows]
  | .rawReadDB db => .list [.atom "raw-read-db", encodeIdent db]
  | .httpsAllow host allows => .list [.atom "https-allow", .str host, encodeTagSet allows]
  | .secret name => .list [.atom "secret", .str name]
  | .declassify allows => .list [.atom "declassify", encodeTagSet allows]

def encodeLTy : LTy → SExp
  | .mk ty ts => .list [.atom "lty", encodeTy ty, encodeTagSet ts]

def encodeLTyList : List LTy → List SExp
  | [] => []
  | l :: ls => encodeLTy l :: encodeLTyList ls
end

mutual
partial def decodeTy : SExp → Except String Ty
  | .list [.atom "unit"] => .ok .unit
  | .list [.atom "bool"] => .ok .bool
  | .list [.atom "int"] => .ok .int
  | .list [.atom "decimal"] => .ok .decimal
  | .list [.atom "float"] => .ok .float
  | .list [.atom "text"] => .ok .text
  | .list [.atom "bytes"] => .ok .bytes
  | .list [.atom "date"] => .ok .date
  | .list [.atom "timestamp"] => .ok .timestamp
  | .list [.atom "duration"] => .ok .duration
  | .list [.atom "option", t] => .option <$> decodeTy t
  | .list [.atom "result", okT, errT] => .result <$> decodeTy okT <*> decodeTy errT
  | .list [.atom "tuple", .list es] => .tuple <$> mapDecode decodeLTy es
  | .list [.atom "list", e] => .list <$> decodeLTy e
  | .list [.atom "map", k, v] => .map <$> decodeLTy k <*> decodeLTy v
  | .list [.atom "data", n] => .data <$> decodeIdent n
  | .list [.atom "table", tt] => .table <$> decodeTableTy tt
  | .list [.atom "dynamic-table", ts] => .dynamicTable <$> decodeTagSet ts
  | .list [.atom "chart", ts] => .chart <$> decodeTagSet ts
  | .list [.atom "report-ty", ts] => .report <$> decodeTagSet ts
  | .list [.atom "profile", ts] => .profile <$> decodeTagSet ts
  | .list [.atom "linear-model"] => .ok .linearModel
  | .list [.atom "stat-test"] => .ok .statTest
  | .list [.atom "fn-ty", .list ps, pc, ret] =>
    .fn <$> mapDecode decodeLTy ps <*> decodeTagSet pc <*> decodeLTy ret
  | .list [.atom "args"] => .ok .args
  | .list [.atom "clock"] => .ok .clock
  | .list [.atom "console", allows] => .console <$> decodeTagSet allows
  | .list [.atom "read-files"] => .ok .readFiles
  | .list [.atom "write-files", .str root, allows] => .writeFiles root <$> decodeTagSet allows
  | .list [.atom "read-db", db] => .readDB <$> decodeIdent db
  | .list [.atom "write-table", db, tbl, .list cs, rt, allows] =>
    .writeTable <$> decodeIdent db <*> decodeIdent tbl <*>
      mapDecode decodeColSpec cs <*> decodeTagSet rt <*> decodeTagSet allows
  | .list [.atom "raw-read-db", db] => .rawReadDB <$> decodeIdent db
  | .list [.atom "https-allow", .str host, allows] => .httpsAllow host <$> decodeTagSet allows
  | .list [.atom "secret", .str name] => .ok (.secret name)
  | .list [.atom "declassify", allows] => .declassify <$> decodeTagSet allows
  | _ => .error "invalid Ty S-expression"

partial def decodeLTy : SExp → Except String LTy
  | .list [.atom "lty", t, ts] => .mk <$> decodeTy t <*> decodeTagSet ts
  | _ => .error "expected (lty ...)"
end

/-! ## Literals, PrimOps, HostOps, RowExpr, Expr, and Plan Serialization -/

def encodeLiteral : Literal → SExp
  | .unit => .list [.atom "lit-unit"]
  | .bool b => .list [.atom "lit-bool", encodeBool b]
  | .int n => .list [.atom "lit-int", encodeInt n]
  | .decimal d => .list [.atom "lit-decimal", encodeInt d]
  | .float f => .list [.atom "lit-float", encodeNat f.bits.toNat]
  | .text s => .list [.atom "lit-text", .str s]
  | .bytes bs => .list [.atom "lit-bytes", .list (bs.map (fun b => encodeNat b.toNat))]
  | .date d => .list [.atom "lit-date", encodeInt d]
  | .timestamp ts => .list [.atom "lit-timestamp", encodeInt ts]
  | .duration dur => .list [.atom "lit-duration", encodeInt dur]
  | .noneLit inner => .list [.atom "lit-none", encodeTy inner]

def decodeLiteral : SExp → Except String Literal
  | .list [.atom "lit-unit"] => .ok .unit
  | .list [.atom "lit-bool", b] => .bool <$> decodeBool b
  | .list [.atom "lit-int", n] => .int <$> decodeInt n
  | .list [.atom "lit-decimal", d] => .decimal <$> decodeInt d
  | .list [.atom "lit-float", b] => do
    let n ← decodeNat b
    .ok (.float ⟨n.toUInt64⟩)
  | .list [.atom "lit-text", .str s] => .ok (.text s)
  | .list [.atom "lit-bytes", .list bs] => do
    let ns ← mapDecode decodeNat bs
    if ns.all (· < 256) then .ok (.bytes (ns.map Nat.toUInt8))
    else .error "byte value out of 0..255 range"
  | .list [.atom "lit-date", d] => .date <$> decodeInt d
  | .list [.atom "lit-timestamp", ts] => .timestamp <$> decodeInt ts
  | .list [.atom "lit-duration", dur] => .duration <$> decodeInt dur
  | .list [.atom "lit-none", inner] => .noneLit <$> decodeTy inner
  | _ => .error "invalid Literal S-expression"

def encodeChartKind : ChartKind → SExp
  | .bar => .atom "bar"
  | .line => .atom "line"
  | .scatter => .atom "scatter"
  | .histogram => .atom "histogram"
  | .heatmap => .atom "heatmap"

def decodeChartKind : SExp → Except String ChartKind
  | .atom "bar" => .ok .bar
  | .atom "line" => .ok .line
  | .atom "scatter" => .ok .scatter
  | .atom "histogram" => .ok .histogram
  | .atom "heatmap" => .ok .heatmap
  | _ => .error "invalid chart kind"

def encodePrimOp : PrimOp → SExp
  | .someVal t => .list [.atom "some-val", encodeTy t]
  | .isSome => .atom "is-some"
  | .isNone => .atom "is-none"
  | .unwrapOr => .atom "unwrap-or"
  | .unwrapBang => .atom "unwrap-bang"
  | .okVal t => .list [.atom "ok-val", encodeTy t]
  | .errVal t => .list [.atom "err-val", encodeTy t]
  | .addInt => .atom "add-int"
  | .subInt => .atom "sub-int"
  | .mulInt => .atom "mul-int"
  | .divInt => .atom "div-int"
  | .modInt => .atom "mod-int"
  | .negInt => .atom "neg-int"
  | .addDec => .atom "add-dec"
  | .subDec => .atom "sub-dec"
  | .mulDec => .atom "mul-dec"
  | .divDec => .atom "div-dec"
  | .negDec => .atom "neg-dec"
  | .intToDec => .atom "int-to-dec"
  | .boolToDec => .atom "bool-to-dec"
  | .eq => .atom "eq"
  | .ne => .atom "ne"
  | .lt => .atom "lt"
  | .le => .atom "le"
  | .gt => .atom "gt"
  | .ge => .atom "ge"
  | .notBool => .atom "not-bool"
  | .andBool => .atom "and-bool"
  | .orBool => .atom "or-bool"
  | .concatText => .atom "concat-text"
  | .trimText => .atom "trim-text"
  | .lowerAsciiText => .atom "lower-ascii-text"
  | .containsText => .atom "contains-text"
  | .emptyText => .atom "empty-text"
  | .intToText => .atom "int-to-text"
  | .decToText => .atom "dec-to-text"
  | .dateTruncMonth => .atom "date-trunc-month"
  | .addDuration => .atom "add-duration"
  | .diffTimestamp => .atom "diff-timestamp"
  | .listLit el => .list [.atom "list-lit", encodeLTy el]
  | .listLen => .atom "list-len"
  | .listEmpty => .atom "list-empty"
  | .listAppend => .atom "list-append"
  | .listConcat => .atom "list-concat"
  | .mapLit k v => .list [.atom "map-lit", encodeLTy k, encodeLTy v]
  | .mapGet => .atom "map-get"
  | .tableCount => .atom "table-count"
  | .tableConcat s => .list [.atom "table-concat", encodeTableTy s]
  | .tableProfile => .atom "table-profile"
  | .statsCorr cx cy => .list [.atom "stats-corr", encodeIdent cx, encodeIdent cy]
  | .statsLinReg cx cy => .list [.atom "stats-linreg", encodeIdent cx, encodeIdent cy]
  | .statsTTest cx cy => .list [.atom "stats-ttest", encodeIdent cx, encodeIdent cy]
  | .chartMake k cs title =>
    .list [.atom "chart-make", encodeChartKind k, .list (cs.map encodeIdent), .str title]
  | .reportNew => .atom "report-new"
  | .reportAddSummary => .atom "report-add-summary"
  | .reportAddChart => .atom "report-add-chart"
  | .reportAddTable => .atom "report-add-table"

def decodePrimOp : SExp → Except String PrimOp
  | .list [.atom "some-val", t] => .someVal <$> decodeTy t
  | .atom "is-some" => .ok .isSome
  | .atom "is-none" => .ok .isNone
  | .atom "unwrap-or" => .ok .unwrapOr
  | .atom "unwrap-bang" => .ok .unwrapBang
  | .list [.atom "ok-val", t] => .okVal <$> decodeTy t
  | .list [.atom "err-val", t] => .errVal <$> decodeTy t
  | .atom "add-int" => .ok .addInt
  | .atom "sub-int" => .ok .subInt
  | .atom "mul-int" => .ok .mulInt
  | .atom "div-int" => .ok .divInt
  | .atom "mod-int" => .ok .modInt
  | .atom "neg-int" => .ok .negInt
  | .atom "add-dec" => .ok .addDec
  | .atom "sub-dec" => .ok .subDec
  | .atom "mul-dec" => .ok .mulDec
  | .atom "div-dec" => .ok .divDec
  | .atom "neg-dec" => .ok .negDec
  | .atom "int-to-dec" => .ok .intToDec
  | .atom "bool-to-dec" => .ok .boolToDec
  | .atom "eq" => .ok .eq
  | .atom "ne" => .ok .ne
  | .atom "lt" => .ok .lt
  | .atom "le" => .ok .le
  | .atom "gt" => .ok .gt
  | .atom "ge" => .ok .ge
  | .atom "not-bool" => .ok .notBool
  | .atom "and-bool" => .ok .andBool
  | .atom "or-bool" => .ok .orBool
  | .atom "concat-text" => .ok .concatText
  | .atom "trim-text" => .ok .trimText
  | .atom "lower-ascii-text" => .ok .lowerAsciiText
  | .atom "contains-text" => .ok .containsText
  | .atom "empty-text" => .ok .emptyText
  | .atom "int-to-text" => .ok .intToText
  | .atom "dec-to-text" => .ok .decToText
  | .atom "date-trunc-month" => .ok .dateTruncMonth
  | .atom "add-duration" => .ok .addDuration
  | .atom "diff-timestamp" => .ok .diffTimestamp
  | .list [.atom "list-lit", el] => .listLit <$> decodeLTy el
  | .atom "list-len" => .ok .listLen
  | .atom "list-empty" => .ok .listEmpty
  | .atom "list-append" => .ok .listAppend
  | .atom "list-concat" => .ok .listConcat
  | .list [.atom "map-lit", k, v] => .mapLit <$> decodeLTy k <*> decodeLTy v
  | .atom "map-get" => .ok .mapGet
  | .atom "table-count" => .ok .tableCount
  | .list [.atom "table-concat", s] => .tableConcat <$> decodeTableTy s
  | .atom "table-profile" => .ok .tableProfile
  | .list [.atom "stats-corr", cx, cy] => .statsCorr <$> decodeIdent cx <*> decodeIdent cy
  | .list [.atom "stats-linreg", cx, cy] => .statsLinReg <$> decodeIdent cx <*> decodeIdent cy
  | .list [.atom "stats-ttest", cx, cy] => .statsTTest <$> decodeIdent cx <*> decodeIdent cy
  | .list [.atom "chart-make", k, .list cs, .str title] =>
    .chartMake <$> decodeChartKind k <*> mapDecode decodeIdent cs <*> pure title
  | .atom "report-new" => .ok .reportNew
  | .atom "report-add-summary" => .ok .reportAddSummary
  | .atom "report-add-chart" => .ok .reportAddChart
  | .atom "report-add-table" => .ok .reportAddTable
  | _ => .error "invalid PrimOp"

def encodeHostOp : HostOp → SExp
  | .argsGet => .atom "args-get"
  | .clockNow => .atom "clock-now"
  | .consolePrint => .atom "console-print"
  | .consoleError => .atom "console-error"
  | .consolePrintTable => .atom "console-print-table"
  | .readCsv s => .list [.atom "read-csv", encodeIdent s]
  | .writeFile => .atom "write-file"
  | .writeReportHtml => .atom "write-report-html"
  | .writeTable => .atom "write-table-op"
  | .declassifyApprove ts => .list [.atom "declassify-approve", encodeTagSet ts]
  | .rawSqlQuery db s => .list [.atom "raw-sql-query", encodeIdent db, encodeTableTy s]
  | .httpsGetJson => .atom "https-get-json"
  | .readParquet s => .list [.atom "read-parquet", encodeTableTy s]
  | .writeParquet => .atom "write-parquet"
  | .writeXlsx => .atom "write-xlsx"
  | .fakeConsole allows => .list [.atom "fake-console", encodeTagSet allows]
  | .fakeFiles allows => .list [.atom "fake-files", encodeTagSet allows]
  | .fakeDB db => .list [.atom "fake-db", encodeIdent db]
  | .fakeHttps host allows => .list [.atom "fake-https", .str host, encodeTagSet allows]
  | .fakeSecret name => .list [.atom "fake-secret", .str name]

def decodeHostOp : SExp → Except String HostOp
  | .atom "args-get" => .ok .argsGet
  | .atom "clock-now" => .ok .clockNow
  | .atom "console-print" => .ok .consolePrint
  | .atom "console-error" => .ok .consoleError
  | .atom "console-print-table" => .ok .consolePrintTable
  | .list [.atom "read-csv", s] => .readCsv <$> decodeIdent s
  | .atom "write-file" => .ok .writeFile
  | .atom "write-report-html" => .ok .writeReportHtml
  | .atom "write-table-op" => .ok .writeTable
  | .list [.atom "declassify-approve", ts] => .declassifyApprove <$> decodeTagSet ts
  | .list [.atom "raw-sql-query", db, s] => .rawSqlQuery <$> decodeIdent db <*> decodeTableTy s
  | .atom "https-get-json" => .ok .httpsGetJson
  | .list [.atom "read-parquet", s] => .readParquet <$> decodeTableTy s
  | .atom "write-parquet" => .ok .writeParquet
  | .atom "write-xlsx" => .ok .writeXlsx
  | .list [.atom "fake-console", allows] => .fakeConsole <$> decodeTagSet allows
  | .list [.atom "fake-files", allows] => .fakeFiles <$> decodeTagSet allows
  | .list [.atom "fake-db", db] => .fakeDB <$> decodeIdent db
  | .list [.atom "fake-https", .str host, allows] => .fakeHttps host <$> decodeTagSet allows
  | .list [.atom "fake-secret", .str name] => .ok (.fakeSecret name)
  | _ => .error "invalid HostOp"

def encodeBugKind : BugKind → SExp
  | .intOverflow => .atom "int-overflow"
  | .decimalOverflow => .atom "decimal-overflow"
  | .divByZero => .atom "div-by-zero"
  | .unwrapNone => .atom "unwrap-none"
  | .joinCardinality => .atom "join-cardinality"
  | .promiseViolation => .atom "promise-violation"
  | .schemaConstraint => .atom "schema-constraint"
  | .exportGateDenied => .atom "export-gate-denied"
  | .outsideBoundary => .atom "outside-boundary"
  | .userStop => .atom "user-stop"

def decodeBugKind : SExp → Except String BugKind
  | .atom "int-overflow" => .ok .intOverflow
  | .atom "decimal-overflow" => .ok .decimalOverflow
  | .atom "div-by-zero" => .ok .divByZero
  | .atom "unwrap-none" => .ok .unwrapNone
  | .atom "join-cardinality" => .ok .joinCardinality
  | .atom "promise-violation" => .ok .promiseViolation
  | .atom "schema-constraint" => .ok .schemaConstraint
  | .atom "export-gate-denied" => .ok .exportGateDenied
  | .atom "outside-boundary" => .ok .outsideBoundary
  | .atom "user-stop" => .ok .userStop
  | _ => .error "invalid BugKind"

def encodeRowExpr : RowExpr → SExp
  | .lit v => .list [.atom "re-lit", encodeLiteral v]
  | .col n => .list [.atom "re-col", encodeIdent n]
  | .outerVar n => .list [.atom "re-outer", encodeIdent n]
  | .constRef n => .list [.atom "re-const", encodeIdent n]
  | .prim op args => .list [.atom "re-prim", encodePrimOp op, .list (encodeRowExprList args)]
  | .ifE c t e => .list [.atom "re-if", encodeRowExpr c, encodeRowExpr t, encodeRowExpr e]
  | .coalesce o d => .list [.atom "re-coalesce", encodeRowExpr o, encodeRowExpr d]
  | .callPure fn args => .list [.atom "re-call", encodeIdent fn, .list (encodeRowExprList args)]
where
  encodeRowExprList : List RowExpr → List SExp
    | [] => []
    | r :: rs => encodeRowExpr r :: encodeRowExprList rs

partial def decodeRowExpr : SExp → Except String RowExpr
  | .list [.atom "re-lit", v] => .lit <$> decodeLiteral v
  | .list [.atom "re-col", n] => .col <$> decodeIdent n
  | .list [.atom "re-outer", n] => .outerVar <$> decodeIdent n
  | .list [.atom "re-const", n] => .constRef <$> decodeIdent n
  | .list [.atom "re-prim", op, .list args] =>
    .prim <$> decodePrimOp op <*> mapDecode decodeRowExpr args
  | .list [.atom "re-if", c, t, e] =>
    .ifE <$> decodeRowExpr c <*> decodeRowExpr t <*> decodeRowExpr e
  | .list [.atom "re-coalesce", o, d] =>
    .coalesce <$> decodeRowExpr o <*> decodeRowExpr d
  | .list [.atom "re-call", fn, .list args] =>
    .callPure <$> decodeIdent fn <*> mapDecode decodeRowExpr args
  | _ => .error "invalid RowExpr"

def encodeDeriveItem : DeriveItem → SExp
  | .colExpr n re => .list [.atom "col-expr", encodeIdent n, encodeRowExpr re]
  | .bucketCol n src cuts lbls =>
    .list [.atom "bucket-col", encodeIdent n, encodeIdent src,
      .list (cuts.map encodeLiteral), .list (lbls.map SExp.str)]

def decodeDeriveItem : SExp → Except String DeriveItem
  | .list [.atom "col-expr", n, re] => .colExpr <$> decodeIdent n <*> decodeRowExpr re
  | .list [.atom "bucket-col", n, src, .list cuts, .list lbls] => do
    let name ← decodeIdent n
    let source ← decodeIdent src
    let cLits ← mapDecode decodeLiteral cuts
    let lStrs ← mapDecode (fun | .str s => .ok s | _ => .error "expected string label") lbls
    .ok (.bucketCol name source cLits lStrs)
  | _ => .error "invalid DeriveItem"

def encodeSortDir : SortDir → SExp
  | .asc => .atom "asc"
  | .desc => .atom "desc"

def decodeSortDir : SExp → Except String SortDir
  | .atom "asc" => .ok .asc
  | .atom "desc" => .ok .desc
  | _ => .error "invalid SortDir"

def encodeJoinKind : JoinKind → SExp
  | .innerOne => .atom "inner-one"
  | .innerManyToOne => .atom "inner-many-to-one"
  | .innerMany => .atom "inner-many"
  | .leftOne => .atom "left-one"
  | .leftManyToOne => .atom "left-many-to-one"
  | .semi => .atom "semi"
  | .anti => .atom "anti"

def decodeJoinKind : SExp → Except String JoinKind
  | .atom "inner-one" => .ok .innerOne
  | .atom "inner-many-to-one" => .ok .innerManyToOne
  | .atom "inner-many" => .ok .innerMany
  | .atom "left-one" => .ok .leftOne
  | .atom "left-many-to-one" => .ok .leftManyToOne
  | .atom "semi" => .ok .semi
  | .atom "anti" => .ok .anti
  | _ => .error "invalid JoinKind"

def encodeJoinOn : JoinOn → SExp
  | .sameKeys ks => .list [.atom "same-keys", .list (ks.map encodeIdent)]
  | .pairs ps => .list [.atom "key-pairs", .list (ps.map (fun (l, r) => .list [encodeIdent l, encodeIdent r]))]

def decodeJoinOn : SExp → Except String JoinOn
  | .list [.atom "same-keys", .list ks] => .sameKeys <$> mapDecode decodeIdent ks
  | .list [.atom "key-pairs", .list ps] =>
    .pairs <$> mapDecode (fun
      | .list [l, r] => Prod.mk <$> decodeIdent l <*> decodeIdent r
      | _ => .error "expected key pair") ps
  | _ => .error "invalid JoinOn"

def encodeAggOp : AggOp → SExp
  | .count => .atom "count"
  | .countDistinct => .atom "count-distinct"
  | .sum => .atom "sum"
  | .mean => .atom "mean"
  | .median => .atom "median"
  | .stddev => .atom "stddev"
  | .variance => .atom "variance"
  | .percentile p => .list [.atom "percentile", encodeNat p.bits.toNat]
  | .min => .atom "min"
  | .max => .atom "max"
  | .first => .atom "first"
  | .last => .atom "last"

def decodeAggOp : SExp → Except String AggOp
  | .atom "count" => .ok .count
  | .atom "count-distinct" => .ok .countDistinct
  | .atom "sum" => .ok .sum
  | .atom "mean" => .ok .mean
  | .atom "median" => .ok .median
  | .atom "stddev" => .ok .stddev
  | .atom "variance" => .ok .variance
  | .list [.atom "percentile", b] => (fun n => .percentile ⟨n.toUInt64⟩) <$> decodeNat b
  | .atom "min" => .ok .min
  | .atom "max" => .ok .max
  | .atom "first" => .ok .first
  | .atom "last" => .ok .last
  | _ => .error "invalid AggOp"

def encodeAggItem (a : AggItem) : SExp :=
  .list [.atom "agg", encodeIdent a.name, encodeAggOp a.op, encodeOpt encodeRowExpr a.arg]

def decodeAggItem : SExp → Except String AggItem
  | .list [.atom "agg", n, op, arg] =>
    AggItem.mk <$> decodeIdent n <*> decodeAggOp op <*> decodeOpt decodeRowExpr arg
  | _ => .error "invalid AggItem"

def encodeSuppressMode : SuppressMode → SExp
  | .drop => .atom "drop"
  | .maskComplementary => .atom "mask-complementary"

def decodeSuppressMode : SExp → Except String SuppressMode
  | .atom "drop" => .ok .drop
  | .atom "mask-complementary" => .ok .maskComplementary
  | _ => .error "invalid SuppressMode"

def encodeWindowFn : WindowFn → SExp
  | .lag c k => .list [.atom "lag", encodeIdent c, encodeNat k]
  | .lead c k => .list [.atom "lead", encodeIdent c, encodeNat k]
  | .rowNumber => .atom "row-number"
  | .rank c => .list [.atom "rank", encodeIdent c]
  | .runningSum c => .list [.atom "running-sum", encodeIdent c]
  | .rollingMean c w => .list [.atom "rolling-mean", encodeIdent c, encodeNat w]

def decodeWindowFn : SExp → Except String WindowFn
  | .list [.atom "lag", c, k] => .lag <$> decodeIdent c <*> decodeNat k
  | .list [.atom "lead", c, k] => .lead <$> decodeIdent c <*> decodeNat k
  | .atom "row-number" => .ok .rowNumber
  | .list [.atom "rank", c] => .rank <$> decodeIdent c
  | .list [.atom "running-sum", c] => .runningSum <$> decodeIdent c
  | .list [.atom "rolling-mean", c, w] => .rollingMean <$> decodeIdent c <*> decodeNat w
  | _ => .error "invalid WindowFn"

def encodeWindowItem (w : WindowItem) : SExp :=
  .list [.atom "win-item", encodeIdent w.name, encodeWindowFn w.fn,
    .list (w.over.map encodeIdent),
    .list (w.order.map (fun (c, d) => .list [encodeIdent c, encodeSortDir d]))]

def decodeWindowItem : SExp → Except String WindowItem
  | .list [.atom "win-item", n, fn, .list ov, .list ord] => do
    let name ← decodeIdent n
    let wFn ← decodeWindowFn fn
    let over ← mapDecode decodeIdent ov
    let order ← mapDecode (fun
      | .list [c, d] => Prod.mk <$> decodeIdent c <*> decodeSortDir d
      | _ => .error "expected (col dir)") ord
    .ok { name, fn := wFn, over, order }
  | _ => .error "invalid WindowItem"

mutual
def encodeExpr : Expr → SExp
  | .lit v => .list [.atom "lit", encodeLiteral v]
  | .var n => .list [.atom "var", encodeIdent n]
  | .constRef n => .list [.atom "const-ref", encodeIdent n]
  | .letE n lty b body => .list [.atom "let", encodeIdent n, encodeLTy lty, encodeExpr b, encodeExpr body]
  | .ifE c t e => .list [.atom "if", encodeExpr c, encodeExpr t, encodeExpr e]
  | .caseE s arms => .list [.atom "case", encodeExpr s, .list (encodeCaseArmList arms)]
  | .lam ps pc ret body =>
    .list [.atom "lam",
      .list (ps.map (fun (n, l) => .list [encodeIdent n, encodeLTy l])),
      encodeTagSet pc, encodeLTy ret, encodeExpr body]
  | .app f as1 => .list [.atom "app", encodeExpr f, .list (encodeExprList as1)]
  | .call fn as1 => .list [.atom "call", encodeIdent fn, .list (encodeExprList as1)]
  | .join lbl ps rhs body =>
    .list [.atom "join-pt", encodeIdent lbl,
      .list (ps.map (fun (n, l) => .list [encodeIdent n, encodeLTy l])),
      encodeExpr rhs, encodeExpr body]
  | .jump lbl as1 => .list [.atom "jump", encodeIdent lbl, .list (encodeExprList as1)]
  | .tuple es => .list [.atom "tuple-val", .list (encodeExprList es)]
  | .proj e i => .list [.atom "proj", encodeExpr e, encodeNat i]
  | .ctor tn cn as1 => .list [.atom "ctor", encodeIdent tn, encodeIdent cn, .list (encodeExprList as1)]
  | .tableLit s rows =>
    .list [.atom "table-lit", encodeTableTy s,
      .list (rows.map (fun r => .list (r.cells.map encodeLiteral)))]
  | .prim op as1 => .list [.atom "prim", encodePrimOp op, .list (encodeExprList as1)]
  | .rel p => .list [.atom "rel", encodePlan p]
  | .host op as1 => .list [.atom "host", encodeHostOp op, .list (encodeExprList as1)]
  | .stop k d =>
    let dSExp := match d with | none => .list [.atom "none"] | some e => .list [.atom "some", encodeExpr e]
    .list [.atom "stop", encodeBugKind k, dSExp]
  | .fail m => .list [.atom "fail", encodeExpr m]

def encodeExprList : List Expr → List SExp
  | [] => []
  | e :: es => encodeExpr e :: encodeExprList es

def encodeCaseArm : CaseArm → SExp
  | .mk cn bs body => .list [.atom "arm", encodeIdent cn, .list (bs.map encodeIdent), encodeExpr body]

def encodeCaseArmList : List CaseArm → List SExp
  | [] => []
  | a :: as1 => encodeCaseArm a :: encodeCaseArmList as1

def encodePlan : Plan → SExp
  | .sourceExpr e => .list [.atom "source-expr", encodeExpr e]
  | .sourceDB cap tbl s => .list [.atom "source-db", encodeExpr cap, encodeIdent tbl, encodeTableTy s]
  | .select p cs => .list [.atom "select", encodePlan p, .list (cs.map encodeIdent)]
  | .drop p cs => .list [.atom "drop", encodePlan p, .list (cs.map encodeIdent)]
  | .rename p ps =>
    .list [.atom "rename", encodePlan p,
      .list (ps.map (fun (nw, ol) => .list [encodeIdent nw, encodeIdent ol]))]
  | .derive p items => .list [.atom "derive", encodePlan p, .list (items.map encodeDeriveItem)]
  | .filter p re => .list [.atom "filter", encodePlan p, encodeRowExpr re]
  | .distinct p cs => .list [.atom "distinct", encodePlan p, .list (cs.map encodeIdent)]
  | .sort p ks =>
    .list [.atom "sort", encodePlan p,
      .list (ks.map (fun (c, d) => .list [encodeIdent c, encodeSortDir d]))]
  | .limit p n => .list [.atom "limit", encodePlan p, encodeNat n]
  | .join k l r on suf =>
    .list [.atom "join", encodeJoinKind k, encodePlan l, encodePlan r, encodeJoinOn on,
      encodeOpt (fun (sl, sr) => .list [.str sl, .str sr]) suf]
  | .union l r => .list [.atom "union", encodePlan l, encodePlan r]
  | .groupBy p ks => .list [.atom "group-by", encodePlan p, .list (ks.map encodeIdent)]
  | .summarize p aggs dk =>
    .list [.atom "summarize", encodePlan p, .list (aggs.map encodeAggItem), encodeOpt encodeIdent dk]
  | .suppressSmallGroups p k db m =>
    .list [.atom "suppress-small-groups", encodePlan p, encodeNat k,
      encodeOpt encodeIdent db, encodeSuppressMode m]
  | .window p items => .list [.atom "window", encodePlan p, .list (items.map encodeWindowItem)]
  | .fillGaps p col step ov fill =>
    .list [.atom "fill-gaps", encodePlan p, encodeIdent col, encodeInt step,
      .list (ov.map encodeIdent),
      .list (fill.map (fun (cn, lit) => .list [encodeIdent cn, encodeLiteral lit]))]
  | .pivotWider p nf vf scs fill =>
    .list [.atom "pivot-wider", encodePlan p, encodeIdent nf, encodeIdent vf,
      .list (scs.map encodeIdent), encodeLiteral fill]
  | .crosstab p r c v fill =>
    .list [.atom "crosstab", encodePlan p, encodeIdent r, encodeIdent c,
      encodeIdent v, encodeLiteral fill]
  | .redact p c rep => .list [.atom "redact", encodePlan p, encodeIdent c, .str rep]
  | .pseudonymize p c sec => .list [.atom "pseudonymize", encodePlan p, encodeIdent c, encodeExpr sec]
end

mutual
partial def decodeExpr : SExp → Except String Expr
  | .list [.atom "lit", v] => .lit <$> decodeLiteral v
  | .list [.atom "var", n] => .var <$> decodeIdent n
  | .list [.atom "const-ref", n] => .constRef <$> decodeIdent n
  | .list [.atom "let", n, lty, b, body] =>
    .letE <$> decodeIdent n <*> decodeLTy lty <*> decodeExpr b <*> decodeExpr body
  | .list [.atom "if", c, t, e] =>
    .ifE <$> decodeExpr c <*> decodeExpr t <*> decodeExpr e
  | .list [.atom "case", s, .list arms] =>
    .caseE <$> decodeExpr s <*> mapDecode decodeCaseArm arms
  | .list [.atom "lam", .list ps, pc, ret, body] => do
    let params ← mapDecode (fun
      | .list [n, l] => Prod.mk <$> decodeIdent n <*> decodeLTy l
      | _ => .error "expected param pair") ps
    .lam params <$> decodeTagSet pc <*> decodeLTy ret <*> decodeExpr body
  | .list [.atom "app", f, .list as1] => .app <$> decodeExpr f <*> mapDecode decodeExpr as1
  | .list [.atom "call", fn, .list as1] => .call <$> decodeIdent fn <*> mapDecode decodeExpr as1
  | .list [.atom "join-pt", lbl, .list ps, rhs, body] => do
    let label ← decodeIdent lbl
    let params ← mapDecode (fun
      | .list [n, l] => Prod.mk <$> decodeIdent n <*> decodeLTy l
      | _ => .error "expected join param") ps
    .join label params <$> decodeExpr rhs <*> decodeExpr body
  | .list [.atom "jump", lbl, .list as1] =>
    .jump <$> decodeIdent lbl <*> mapDecode decodeExpr as1
  | .list [.atom "tuple-val", .list es] => .tuple <$> mapDecode decodeExpr es
  | .list [.atom "proj", e, i] => .proj <$> decodeExpr e <*> decodeNat i
  | .list [.atom "ctor", tn, cn, .list as1] =>
    .ctor <$> decodeIdent tn <*> decodeIdent cn <*> mapDecode decodeExpr as1
  | .list [.atom "table-lit", s, .list rows] => do
    let schema ← decodeTableTy s
    let rLits ← mapDecode (fun
      | .list cs => RowLit.mk <$> mapDecode decodeLiteral cs
      | _ => .error "expected row cells") rows
    .ok (.tableLit schema rLits)
  | .list [.atom "prim", op, .list as1] =>
    .prim <$> decodePrimOp op <*> mapDecode decodeExpr as1
  | .list [.atom "rel", p] => .rel <$> decodePlan p
  | .list [.atom "host", op, .list as1] =>
    .host <$> decodeHostOp op <*> mapDecode decodeExpr as1
  | .list [.atom "stop", k, d] => .stop <$> decodeBugKind k <*> decodeOpt decodeExpr d
  | .list [.atom "fail", m] => .fail <$> decodeExpr m
  | _ => .error "invalid Expr S-expression"

partial def decodeCaseArm : SExp → Except String CaseArm
  | .list [.atom "arm", cn, .list bs, body] =>
    .mk <$> decodeIdent cn <*> mapDecode decodeIdent bs <*> decodeExpr body
  | _ => .error "invalid CaseArm"

partial def decodePlan : SExp → Except String Plan
  | .list [.atom "source-expr", e] => .sourceExpr <$> decodeExpr e
  | .list [.atom "source-db", cap, tbl, s] =>
    .sourceDB <$> decodeExpr cap <*> decodeIdent tbl <*> decodeTableTy s
  | .list [.atom "select", p, .list cs] =>
    .select <$> decodePlan p <*> mapDecode decodeIdent cs
  | .list [.atom "drop", p, .list cs] =>
    .drop <$> decodePlan p <*> mapDecode decodeIdent cs
  | .list [.atom "rename", p, .list ps] => do
    let plan ← decodePlan p
    let pairs ← mapDecode (fun
      | .list [nw, ol] => Prod.mk <$> decodeIdent nw <*> decodeIdent ol
      | _ => .error "expected rename pair") ps
    .ok (.rename plan pairs)
  | .list [.atom "derive", p, .list items] =>
    .derive <$> decodePlan p <*> mapDecode decodeDeriveItem items
  | .list [.atom "filter", p, re] =>
    .filter <$> decodePlan p <*> decodeRowExpr re
  | .list [.atom "distinct", p, .list cs] =>
    .distinct <$> decodePlan p <*> mapDecode decodeIdent cs
  | .list [.atom "sort", p, .list ks] => do
    let plan ← decodePlan p
    let keys ← mapDecode (fun
      | .list [c, d] => Prod.mk <$> decodeIdent c <*> decodeSortDir d
      | _ => .error "expected sort key") ks
    .ok (.sort plan keys)
  | .list [.atom "limit", p, n] => .limit <$> decodePlan p <*> decodeNat n
  | .list [.atom "join", k, l, r, on, suf] => do
    let kind ← decodeJoinKind k
    let lp ← decodePlan l
    let rp ← decodePlan r
    let jOn ← decodeJoinOn on
    let sf ← decodeOpt (fun
      | .list [.str sl, .str sr] => .ok (sl, sr)
      | _ => .error "expected suffix pair") suf
    .ok (.join kind lp rp jOn sf)
  | .list [.atom "union", l, r] => .union <$> decodePlan l <*> decodePlan r
  | .list [.atom "group-by", p, .list ks] =>
    .groupBy <$> decodePlan p <*> mapDecode decodeIdent ks
  | .list [.atom "summarize", p, .list aggs, dk] =>
    .summarize <$> decodePlan p <*> mapDecode decodeAggItem aggs <*> decodeOpt decodeIdent dk
  | .list [.atom "suppress-small-groups", p, k, db, m] =>
    .suppressSmallGroups <$> decodePlan p <*> decodeNat k <*>
      decodeOpt decodeIdent db <*> decodeSuppressMode m
  | .list [.atom "window", p, .list items] =>
    .window <$> decodePlan p <*> mapDecode decodeWindowItem items
  | .list [.atom "fill-gaps", p, col, step, .list ov, .list fill] => do
    let plan ← decodePlan p
    let c ← decodeIdent col
    let st ← decodeInt step
    let over ← mapDecode decodeIdent ov
    let fl ← mapDecode (fun
      | .list [cn, lit] => Prod.mk <$> decodeIdent cn <*> decodeLiteral lit
      | _ => .error "expected fill pair") fill
    .ok (.fillGaps plan c st over fl)
  | .list [.atom "pivot-wider", p, nf, vf, .list scs, fill] =>
    .pivotWider <$> decodePlan p <*> decodeIdent nf <*> decodeIdent vf <*>
      mapDecode decodeIdent scs <*> decodeLiteral fill
  | .list [.atom "crosstab", p, r, c, v, fill] =>
    .crosstab <$> decodePlan p <*> decodeIdent r <*> decodeIdent c <*>
      decodeIdent v <*> decodeLiteral fill
  | .list [.atom "redact", p, c, .str rep] =>
    .redact <$> decodePlan p <*> decodeIdent c <*> pure rep
  | .list [.atom "pseudonymize", p, c, sec] =>
    .pseudonymize <$> decodePlan p <*> decodeIdent c <*> decodeExpr sec
  | _ => .error "invalid Plan S-expression"
end

/-! ## Policy, Top-Level Declarations, Metadata Validation & `Program` Wire Codec -/

def encodePolicy (p : Policy) : SExp :=
  .list [
    .atom "policy",
    encodeNat p.minGroupSize,
    encodeBool p.forbidManualDeclassify,
    encodeBool p.forbidReplSensitive,
    encodeTagSet p.allowConsole,
    .list (p.allowExport.map (fun (r, ts) => .list [.str r, encodeTagSet ts])),
    .list (p.allowHttps.map (fun (h, ts) => .list [.str h, encodeTagSet ts])),
    .list (p.allowWrite.map (fun w => .list [encodeIdent w.db, encodeIdent w.table, encodeTagSet w.tags]))
  ]

def decodePolicy : SExp → Except String Policy
  | .list [.atom "policy", mg, fmd, frs, ac, .list ae, .list ah, .list aw] => do
    let minGroupSize ← decodeNat mg
    let forbidManualDeclassify ← decodeBool fmd
    let forbidReplSensitive ← decodeBool frs
    let allowConsole ← decodeTagSet ac
    let allowExport ← mapDecode (fun
      | .list [.str r, ts] => Prod.mk r <$> decodeTagSet ts
      | _ => .error "invalid allow-export rule") ae
    let allowHttps ← mapDecode (fun
      | .list [.str h, ts] => Prod.mk h <$> decodeTagSet ts
      | _ => .error "invalid allow-https rule") ah
    let allowWrite ← mapDecode (fun
      | .list [db, tbl, ts] => PolicyWriteRule.mk <$> decodeIdent db <*> decodeIdent tbl <*> decodeTagSet ts
      | _ => .error "invalid allow-write rule") aw
    .ok { minGroupSize, forbidManualDeclassify, forbidReplSensitive, allowConsole, allowExport, allowHttps, allowWrite }
  | _ => .error "expected (policy ...)"

def encodeDataDecl (d : DataDecl) : SExp :=
  .list [.atom "data-decl", encodeIdent d.name,
    .list (d.ctors.map (fun c => .list [.atom "ctor-decl", encodeIdent c.name, .list (c.fields.map encodeLTy)]))]

def decodeDataDecl : SExp → Except String DataDecl
  | .list [.atom "data-decl", n, .list cs] => do
    let name ← decodeIdent n
    let ctors ← mapDecode (fun
      | .list [.atom "ctor-decl", cn, .list fs] =>
        CtorDecl.mk <$> decodeIdent cn <*> mapDecode decodeLTy fs
      | _ => .error "expected ctor-decl") cs
    .ok { name, ctors }
  | _ => .error "expected data-decl"

def encodeSchemaDecl (s : SchemaDecl) : SExp :=
  .list [.atom "schema-decl", encodeIdent s.name, encodeTableTy s.schema]

def decodeSchemaDecl : SExp → Except String SchemaDecl
  | .list [.atom "schema-decl", n, tt] => SchemaDecl.mk <$> decodeIdent n <*> decodeTableTy tt
  | _ => .error "expected schema-decl"

def encodeConstDecl (c : ConstDecl) : SExp :=
  .list [.atom "const-decl", encodeIdent c.name, encodeLTy c.lty, encodeLiteral c.value]

def decodeConstDecl : SExp → Except String ConstDecl
  | .list [.atom "const-decl", n, l, v] =>
    ConstDecl.mk <$> decodeIdent n <*> decodeLTy l <*> decodeLiteral v
  | _ => .error "expected const-decl"

def encodeFunKind : FunKind → SExp
  | .function => .atom "fn"
  | .test => .atom "test"
  | .exampleDecl => .atom "example"
  | .promise => .atom "promise"

def decodeFunKind : SExp → Except String FunKind
  | .atom "fn" => .ok .function
  | .atom "test" => .ok .test
  | .atom "example" => .ok .exampleDecl
  | .atom "promise" => .ok .promise
  | _ => .error "invalid FunKind"

def encodeFunDecl (f : FunDecl) : SExp :=
  .list [
    .atom "fun-decl",
    encodeIdent f.name,
    encodeFunKind f.kind,
    encodeBool f.isPure,
    .list (f.params.map (fun (n, l) => .list [encodeIdent n, encodeLTy l])),
    encodeTagSet f.pc,
    encodeLTy f.ret,
    encodeExpr f.body
  ]

def decodeFunDecl : SExp → Except String FunDecl
  | .list [.atom "fun-decl", n, k, pB, .list ps, pc, ret, body] => do
    let name ← decodeIdent n
    let kind ← decodeFunKind k
    let isPure ← decodeBool pB
    let params ← mapDecode (fun
      | .list [pn, pl] => Prod.mk <$> decodeIdent pn <*> decodeLTy pl
      | _ => .error "expected param") ps
    let fPc ← decodeTagSet pc
    let fRet ← decodeLTy ret
    let fBody ← decodeExpr body
    .ok { name, kind, isPure, params, pc := fPc, ret := fRet, body := fBody }
  | _ => .error "expected fun-decl"

def validSourceSpanShape (sp : SourceSpan) : Bool :=
  !sp.file.isEmpty &&
  sp.startLine ≥ 1 &&
  sp.startCol ≥ 1 &&
  sp.startLine ≤ sp.endLine &&
  (if sp.startLine == sp.endLine then sp.startCol ≤ sp.endCol else sp.endCol ≥ 1)

def encodeSourceSpan (sp : SourceSpan) : SExp :=
  .list [.atom "span", .str sp.file, encodeNat sp.startLine, encodeNat sp.startCol,
    encodeNat sp.endLine, encodeNat sp.endCol]

def decodeSourceSpan : SExp → Except String SourceSpan
  | .list [.atom "span", .str file, sl, sc, el, ec] => do
    let sp : SourceSpan := {
      file := file
      startLine := ← decodeNat sl
      startCol := ← decodeNat sc
      endLine := ← decodeNat el
      endCol := ← decodeNat ec
    }
    if validSourceSpanShape sp then .ok sp
    else .error "invalid SourceSpan shape in CompilerMetadata"
  | _ => .error "expected (span ...)"

def encodeMetadata (m : CompilerMetadata) : SExp :=
  .list (.atom "meta" :: m.entries.map (fun e =>
    .list [.atom "meta-entry", encodeIdent e.nodeId,
      encodeOpt SExp.str e.origName,
      encodeOpt encodeSourceSpan e.span]))

def decodeMetadata : SExp → Except String CompilerMetadata
  | .list (.atom "meta" :: items) => do
    let entries ← mapDecode (fun
      | .list [.atom "meta-entry", nid, onm, sp] => do
        let nodeId ← decodeIdent nid
        if nodeId.isEmpty then .error "empty nodeId in CompilerMetadata"
        else do
          let origName ← decodeOpt (fun | .str s => .ok s | _ => .error "expected string") onm
          let span ← decodeOpt decodeSourceSpan sp
          .ok { nodeId, origName, span }
      | _ => .error "invalid meta-entry shape in CompilerMetadata") items
    .ok { entries }
  | _ => .error "expected (meta ...) in CompilerMetadata"

/-- Print a `Program` in canonical `(dana-core 0.1 ...)` S-expression wire format
    terminated by a single LF (`\n`). -/
def printProgram (prog : Program) : String :=
  let sexp : SExp := .list [
    .atom "dana-core",
    .atom s!"{prog.version.major}.{prog.version.minor}",
    .list (.atom "custom-tags" :: prog.tags.map encodeIdent),
    encodeOpt encodePolicy prog.policy,
    .list (.atom "datas" :: prog.datas.map encodeDataDecl),
    .list (.atom "schemas" :: prog.schemas.map encodeSchemaDecl),
    .list (.atom "consts" :: prog.consts.map encodeConstDecl),
    .list (.atom "funs" :: prog.funs.map encodeFunDecl),
    encodeOpt encodeIdent prog.entry,
    encodeMetadata prog.metadata
  ]
  printSExp sexp ++ "\n"

/-- Parse a canonical `(dana-core 0.1 ...)` wire document into a `Program`.
    Immediately rejects unknown versions, raw control characters, and malformed metadata. -/
def parseProgram (wire : String) : Except String Program := do
  let sexp ← parseCanonicalSExp wire
  match sexp with
  | .list [.atom "dana-core", .atom ver,
      .list (.atom "custom-tags" :: tagItems),
      polSExp,
      .list (.atom "datas" :: dataItems),
      .list (.atom "schemas" :: schemaItems),
      .list (.atom "consts" :: constItems),
      .list (.atom "funs" :: funItems),
      entrySExp,
      metaSExp] =>
    if ver != "0.1" then
      .error s!"unsupported dana-core wire version '{ver}' (expected 0.1)"
    else do
      let tags ← mapDecode decodeIdent tagItems
      let policy ← decodeOpt decodePolicy polSExp
      let datas ← mapDecode decodeDataDecl dataItems
      let schemas ← mapDecode decodeSchemaDecl schemaItems
      let consts ← mapDecode decodeConstDecl constItems
      let funs ← mapDecode decodeFunDecl funItems
      let entry ← decodeOpt decodeIdent entrySExp
      let metadata ← decodeMetadata metaSExp
      let prog : Program := {
        version := { major := 0, minor := 1 }
        tags, policy, datas, schemas, consts, funs, entry, metadata
      }
      if printProgram prog != wire then
        .error "non-canonical wire encoding (must match printProgram byte-for-byte)"
      else
        .ok prog
  | .list (.atom "dana-core" :: .atom ver :: _) =>
    if ver != "0.1" then
      .error s!"unsupported dana-core wire version '{ver}' (expected 0.1)"
    else .error "malformed (dana-core 0.1 ...) payload structure"
  | _ => .error "expected top-level (dana-core 0.1 ...)"

/-! ## Canonical Observable `Report` Wire Printer -/

def encodeExitStatus : ExitStatus → SExp
  | .ok => .atom "ok"
  | .stopped => .atom "stopped"
  | .failed => .atom "failed"

/-- Emit canonical `(dana-report 0.1 ...)\n` for differential verification against
    the Rust naive oracle (`src/oracle/`), vectorized VM, and SQL pushdown backends. -/
def printReport (rep : ExecReport) : String :=
  let sexp : SExp := .list [
    .atom "dana-report",
    .atom "0.1",
    .list [.atom "status", encodeExitStatus rep.status],
    .list [.atom "diagnostic", encodeOpt SExp.str rep.diagnostic],
    .list (.atom "stdout" :: rep.stdout.map SExp.str),
    .list (.atom "stderr" :: rep.stderr.map SExp.str),
    .list (.atom "written-files" :: rep.writtenFiles.map (fun (p, c) => .list [.str p, .str c])),
    .list (.atom "written-tables" :: rep.writtenTables.map (fun (db, tbl, cols, rows) =>
      .list [encodeIdent db, encodeIdent tbl,
        .list (cols.map encodeIdent),
        .list (rows.map (fun r => .list (r.map SExp.str)))])),
    .list (.atom "fake-consoles" :: rep.fakeConsoles.map (fun fc =>
      .list [.list (.atom "stdout" :: fc.stdout.map SExp.str),
             .list (.atom "stderr" :: fc.stderr.map SExp.str)])),
    .list (.atom "fake-files" :: rep.fakeFiles.map (fun ff =>
      .list (ff.files.map (fun (p, c) => .list [.str p, .str c]))))
  ]
  printSExp sexp ++ "\n"

end DanaCore
