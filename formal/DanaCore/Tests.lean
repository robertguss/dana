/-
  DanaCore/Tests.lean
  Compiled-evaluator `#guard` regression suite and `#print axioms` audit for
  Dana Core IR v0.1 (`Syntax`, `Check`, `Eval`, `Soundness`, `NonInterference`, `Text`).
-/
import DanaCore.Syntax
import DanaCore.Check
import DanaCore.Eval
import DanaCore.Soundness
import DanaCore.NonInterference
import DanaCore.Text

namespace DanaCore.Tests

open DanaCore

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

private def hasErrSubstr {α : Type} (res : Except String α) (sub : String) : Bool :=
  match res with
  | .error msg => (msg.splitOn sub).length > 1
  | .ok _ => false

private def ts (tags : List Tag) : TagSet := TagSet.ofList tags
private def pub : TagSet := TagSet.empty
private def pii : TagSet := ts ["pii"]
private def ferpa : TagSet := ts ["ferpa"]
private def sec : TagSet := ts ["secret"]

/-! ## Scenario 1: Public Zero-Friction Pipeline (`tags = []`) -/

private def publicSalesSchema : TableTy := {
  cols := [
    { name := "region", ty := .text, tags := pub },
    { name := "amount", ty := .int, tags := pub }
  ]
}

private def publicPipelineProg : Program := {
  schemas := [{ name := "Sales", schema := publicSalesSchema }]
  funs := [{
    name := "main"
    params := [("console", .mk (.console pub) pub)]
    ret := .mk .unit pub
    body := .letE "summary"
      (.mk (.table {
        cols := [
          { name := "region", ty := .text, tags := pub, aggKind := .groupKey },
          { name := "n", ty := .int, tags := pub, aggKind := .blending },
          { name := "total", ty := .int, tags := pub, aggKind := .blending }
        ]
        groupedBy := some ["region"]
        summarized := true
      }) pub)
      (.rel (
        .summarize
          (.groupBy
            (.sourceExpr (.tableLit publicSalesSchema [
              { cells := [.text "West", .int 100] },
              { cells := [.text "East", .int 250] },
              { cells := [.text "West", .int 150] }
            ]))
            ["region"])
          [
            { name := "n", op := .count, arg := none },
            { name := "total", op := .sum, arg := some (.col "amount") }
          ]
          none))
      (.host .consolePrintTable [.var "console", .var "summary"])
  }]
  entry := some "main"
}

#guard checkProgram publicPipelineProg == .ok ()
#guard (match runProgram 64 publicPipelineProg with
  | .ok rep => rep.status == .ok && rep.stdout == ["region | n | total\nEast | 1 | 250\nWest | 2 | 250"]
  | .error _ => false)

/-! ## Scenario 2: Caught Implicit-Flow FERPA Filter / Count Leak -/

private def studentSchema : TableTy := {
  cols := [
    { name := "id", ty := .int, tags := pii },
    { name := "email", ty := .text, tags := pii },
    { name := "program", ty := .text, tags := pub },
    { name := "credits", ty := .int, tags := ferpa },
    { name := "gpa", ty := .decimal, tags := ferpa }
  ]
}

private def implicitFlowLeakProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let leakedPlan : Plan :=
        .summarize
          (.groupBy
            (.select
              (.filter
                (.sourceDB (.var "db") "students" studentSchema)
                (.prim .lt [.col "gpa", .lit (.decimal (2 * decScale))]))
              ["program"])
            ["program"])
          [{ name := "probation_count", op := .count, arg := none }]
          none
      .host .consolePrintTable [.var "console", .rel leakedPlan]
  }]
  entry := some "main"
}

-- `filter(.gpa < 2.0)` taints `rowTags` with `[ferpa]`, which propagates into `count()`,
-- so printing to `Console(allows: [])` is statically rejected!
#guard hasErrSubstr (checkProgram implicitFlowLeakProg) "Console.printTable unauthorized for table sensitivity tags"

-- Scalar `if` implicit flow on `[ferpa]` condition to public `Console(allows: [])` is also rejected:
private def scalarImplicitFlowProg : Program := {
  funs := [{
    name := "leak_branch"
    params := [
      ("gpa", .mk .decimal ferpa),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body := .ifE
      (.prim .lt [.var "gpa", .lit (.decimal (2 * decScale))])
      (.host .consolePrint [.var "console", .lit (.text "academic_probation")])
      (.lit .unit)
  }]
}

#guard hasErrSubstr (checkProgram scalarImplicitFlowProg) "Console sink unauthorized for value or pc sensitivity tags"

/-! ## Scenario 3: `bucket` + `suppress_small_groups(min: 5, distinct_by: .id)` -/

private def kAnonCohortPlan : Plan :=
  .suppressSmallGroups
    (.summarize
      (.groupBy
        (.derive
          (.sourceDB (.var "db") "students" studentSchema)
          [.bucketCol "gpa_band" "gpa"
            [.decimal (2 * decScale), .decimal (3 * decScale)]
            ["<2.0", "2.0-3.0", ">=3.0"]])
        ["program", "gpa_band"])
      [
        { name := "n", op := .count, arg := none },
        { name := "total_credits", op := .sum, arg := some (.col "credits") }
      ]
      (some "id"))
    5
    (some "id")
    .drop

private def validKAnonProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body := .host .consolePrintTable [.var "console", .rel kAnonCohortPlan]
  }]
  entry := some "main"
}

#guard checkProgram validKAnonProg == .ok ()

-- Runtime check: CS `>=3.0` has 5 distinct students (kept); Math `>=3.0` has 6 rows
-- from only 3 distinct students (suppressed by `distinct_by: .id`!).
private def cohortTestWorld : World := {
  realDBTables := [{
    db := "registrar"
    tableName := "students"
    schema := studentSchema
    rows := [
      -- 5 distinct CS students with GPA >= 3.0
      [.int 1, .text "s1@u.edu", .text "CS", .int 15, .decimal (35 * (decScale / 10))],
      [.int 2, .text "s2@u.edu", .text "CS", .int 15, .decimal (36 * (decScale / 10))],
      [.int 3, .text "s3@u.edu", .text "CS", .int 15, .decimal (37 * (decScale / 10))],
      [.int 4, .text "s4@u.edu", .text "CS", .int 15, .decimal (38 * (decScale / 10))],
      [.int 5, .text "s5@u.edu", .text "CS", .int 15, .decimal (39 * (decScale / 10))],
      -- 6 rows in Math >= 3.0, but only 3 distinct student IDs (10, 11, 12)!
      [.int 10, .text "m1@u.edu", .text "Math", .int 12, .decimal (35 * (decScale / 10))],
      [.int 10, .text "m1@u.edu", .text "Math", .int 12, .decimal (35 * (decScale / 10))],
      [.int 11, .text "m2@u.edu", .text "Math", .int 12, .decimal (36 * (decScale / 10))],
      [.int 11, .text "m2@u.edu", .text "Math", .int 12, .decimal (36 * (decScale / 10))],
      [.int 12, .text "m3@u.edu", .text "Math", .int 12, .decimal (37 * (decScale / 10))],
      [.int 12, .text "m3@u.edu", .text "Math", .int 12, .decimal (37 * (decScale / 10))]
    ]
  }]
}

#guard (match runProgram 64 validKAnonProg cohortTestWorld with
  | .ok rep =>
    rep.status == .ok &&
    rep.stdout == ["program | gpa_band | n | total_credits\nCS | >=3.0 | 5 | 75"]
  | .error _ => false)

-- Non-bucketed raw `.email [pii]` group key is NEVER cleared by `suppress_small_groups`:
private def rawEmailGroupKeyProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let badPlan : Plan :=
        .suppressSmallGroups
          (.summarize
            (.groupBy (.sourceDB (.var "db") "students" studentSchema) ["email"])
            [{ name := "n", op := .count, arg := none }]
            none)
          5 none .drop
      .host .consolePrintTable [.var "console", .rel badPlan]
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram rawEmailGroupKeyProg) "Console.printTable unauthorized for table sensitivity tags"

-- Non-blending single-record extreme `max(.gpa) [ferpa]` is NEVER cleared by `suppress_small_groups`:
private def maxGpaExtremeProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let badPlan : Plan :=
        .suppressSmallGroups
          (.summarize
            (.groupBy (.sourceDB (.var "db") "students" studentSchema) ["program"])
            [{ name := "top_gpa", op := .max, arg := some (.col "gpa") }]
            none)
          5 none .drop
      .host .consolePrintTable [.var "console", .rel badPlan]
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram maxGpaExtremeProg) "Console.printTable unauthorized for table sensitivity tags"

/-! ## Scenario 4: `dana.policy` Repository Upper-Bound Enforcement -/

private def strictRepoPolicy : Policy := {
  minGroupSize := 10
  forbidManualDeclassify := true
  forbidReplSensitive := true
  allowConsole := pub
  allowExport := [("reports/", ferpa)]
  allowHttps := []
  allowWrite := []
}

-- 4a: Requesting `WriteFiles("tmp/", allows: [pii])` exceeds `dana.policy`
private def policyExceedWriteFilesProg : Program := {
  policy := some strictRepoPolicy
  funs := [{
    name := "main"
    params := [("out", .mk (.writeFiles "tmp/" pii) pub)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram policyExceedWriteFilesProg) "exceeds dana.policy"

-- 4b: `suppress_small_groups(min: 5)` is below `policy.minGroupSize = 10`
private def policySmallKProg : Program := { validKAnonProg with policy := some strictRepoPolicy }

#guard hasErrSubstr (checkProgram policySmallKProg) "below required minimum floor"

-- 4c: Manual `Declassify([ferpa])` is rejected under `forbidManualDeclassify = true`
private def policyManualDeclassifyProg : Program := {
  policy := some strictRepoPolicy
  funs := [{
    name := "main"
    params := [("dec", .mk (.declassify ferpa) pub)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram policyManualDeclassifyProg) "forbids manual Declassify"

/-! ## Scenario 5: Automatic `[REDACTED:pii]` Diagnostic Redaction on Duplicate Join Keys -/

private def ssnLeftSchema : TableTy := {
  cols := [
    { name := "ssn", ty := .text, tags := pii },
    { name := "dept", ty := .text, tags := pub }
  ]
}

private def ssnRightSchema : TableTy := {
  cols := [
    { name := "ssn", ty := .text, tags := pii },
    { name := "role", ty := .text, tags := pub }
  ]
}

private def dupJoinStopProg : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk .unit pub
    body := .letE "joined"
      (.mk (.table {
        cols := [
          { name := "ssn", ty := .text, tags := pii },
          { name := "dept", ty := .text, tags := pub },
          { name := "role", ty := .text, tags := pub }
        ]
        rowTags := pii
      }) pub)
      (.rel (.join .innerOne
        (.sourceExpr (.tableLit ssnLeftSchema [
          { cells := [.text "123-45-6789", .text "Physics"] }
        ]))
        (.sourceExpr (.tableLit ssnRightSchema [
          { cells := [.text "123-45-6789", .text "Faculty"] },
          { cells := [.text "123-45-6789", .text "Chair"] }
        ]))
        (.sameKeys ["ssn"])
        none))
      (.lit .unit)
  }]
  entry := some "main"
}

#guard checkProgram dupJoinStopProg == .ok ()
#guard (match runProgram 64 dupJoinStopProg with
  | .ok rep =>
    rep.status == .stopped &&
    rep.diagnostic == some "duplicate key [REDACTED:pii] (2 rows: 0, 1)"
  | .error _ => false)

/-! ## Scenario 6: Canonical `(dana-core 0.1 ...)` Wire Round-Trips & Strict Validation -/

private def richMetadataProg : Program := {
  tags := ["hipaa_custom"]
  policy := some {
    minGroupSize := 5
    forbidManualDeclassify := false
    forbidReplSensitive := true
    allowConsole := pub
    allowExport := [("exports/", ts ["hipaa_custom"])]
    allowWrite := [{ db := "warehouse", table := "cohorts", tags := ferpa }]
  }
  datas := [{
    name := "Status"
    ctors := [
      { name := "Active", fields := [.mk .int pub] },
      { name := "Inactive", fields := [] }
    ]
  }]
  schemas := [{ name := "Students", schema := studentSchema }]
  consts := [{ name := "THRESHOLD", lty := .mk .int pub, value := .int 42 }]
  funs := validKAnonProg.funs
  entry := some "main"
  metadata := {
    entries := [{
      nodeId := "fn_main_0"
      origName := some "cohort_report\t\"v1\""
      span := some { file := "src/cohort.dana", startLine := 1, startCol := 1, endLine := 24, endCol := 8 }
    }]
  }
}

#guard checkProgram richMetadataProg == .ok ()
#guard parseProgram (printProgram publicPipelineProg) == .ok publicPipelineProg
#guard parseProgram (printProgram richMetadataProg) == .ok richMetadataProg
#guard parseProgram (printProgram dupJoinStopProg) == .ok dupJoinStopProg

-- Reject unknown wire version `0.2`
#guard hasErrSubstr (parseProgram "(dana-core 0.2 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n") "unsupported dana-core wire version"

-- Reject raw control character (0x01) inside string literal
#guard hasErrSubstr (parseProgram ("(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"" ++ String.singleton (Char.ofNat 1) ++ "\") (meta))\n")) "raw control"

-- Reject UTF-16 surrogate escape `\u{d800}`
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{d800}\") (meta))\n") "surrogate"

-- Reject invalid metadata span (`startLine = 0`)
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" 0 1 1 1)))))\n") "invalid SourceSpan"

-- Reject invalid metadata span (`endLine < startLine`)
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" 5 1 4 1)))))\n") "invalid SourceSpan"

-- M7: Canonical wire format strictness (trailing LF, canonical \u{hex}, C1 controls 0x80..0x9F)
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))") "single trailing LF"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{41}\") (meta))\n") "non-canonical \\u{hex}"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{0A}\") (meta))\n") "non-lowercase \\u{hex}"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{01}\") (meta))\n") "non-canonical \\u{hex}"
#guard hasErrSubstr (parseProgram ("(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"" ++ String.singleton (Char.ofNat 0x85) ++ "\") (meta))\n")) "raw control"

private def c1ControlProg : Program := {
  metadata := {
    entries := [{
      nodeId := "c1_test"
      origName := some ("nel:" ++ String.singleton (Char.ofNat 0x85))
    }]
  }
}

#guard ((printProgram c1ControlProg).splitOn "\\u{85}").length > 1
#guard parseProgram (printProgram c1ControlProg) == .ok c1ControlProg

/-! ## Scenario 7: Real Floating-Point Aggregates, Window Rolling Mean, & Stats (B1) -/

private def mkF64 (x : Float) : Float64 := ⟨x.toBits⟩

private def floatMetricsSchema : TableTy := {
  cols := [
    { name := "grp", ty := .text, tags := pub },
    { name := "x", ty := .float, tags := pub },
    { name := "y", ty := .float, tags := pub }
  ]
}

private def floatAggsProg : Program := {
  funs := [{
    name := "main"
    params := [("console", .mk (.console pub) pub)]
    ret := .mk .unit pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 10.0), .float (mkF64 20.0)] },
        { cells := [.text "A", .float (mkF64 20.0), .float (mkF64 40.0)] },
        { cells := [.text "A", .float (mkF64 30.0), .float (mkF64 60.0)] }
      ]
      let p : Plan :=
        .summarize (.groupBy (.sourceExpr tbl) ["grp"])
          [
            { name := "s", op := .sum, arg := some (.col "x") },
            { name := "m", op := .mean, arg := some (.col "x") },
            { name := "med", op := .median, arg := some (.col "x") },
            { name := "v", op := .variance, arg := some (.col "x") },
            { name := "sd", op := .stddev, arg := some (.col "x") },
            { name := "p50", op := .percentile (mkF64 0.5), arg := some (.col "x") }
          ]
          none
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard checkProgram floatAggsProg == .ok ()
#guard (match runProgram 64 floatAggsProg with
  | .ok rep =>
    let expVar : Float := 200.0 / 3.0
    let expSd : Float := Float.sqrt expVar
    rep.status == .ok &&
    rep.stdout == [
      s!"grp | s | m | med | v | sd | p50\nA | float64({(60.0 : Float).toBits}) | some(float64({(20.0 : Float).toBits})) | some(float64({(20.0 : Float).toBits})) | some(float64({expVar.toBits})) | some(float64({expSd.toBits})) | some(float64({(20.0 : Float).toBits}))"
    ]
  | .error _ => false)

private def rollingMeanProg : Program := {
  funs := [{
    name := "main"
    params := [("console", .mk (.console pub) pub)]
    ret := .mk .unit pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 10.0), .float (mkF64 0.0)] },
        { cells := [.text "A", .float (mkF64 20.0), .float (mkF64 0.0)] },
        { cells := [.text "A", .float (mkF64 30.0), .float (mkF64 0.0)] }
      ]
      let p : Plan :=
        .window (.sourceExpr tbl) [{
          name := "rm2"
          fn := .rollingMean "x" 2
          over := ["grp"]
          order := [("x", .asc)]
        }]
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard checkProgram rollingMeanProg == .ok ()
#guard (match runProgram 64 rollingMeanProg with
  | .ok rep =>
    rep.status == .ok &&
    (match rep.stdout with
     | [out] =>
       (out.splitOn s!"float64({(15.0 : Float).toBits})").length > 1 &&
       (out.splitOn s!"float64({(25.0 : Float).toBits})").length > 1
     | _ => false)
  | .error _ => false)

-- `statsCorr` & `statsLinReg` compute real floating-point correlation and OLS regression;
-- `statsTTest` stops with `outsideBoundary`.
private def statsCorrTestProg : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk (.option .float) pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 1.0), .float (mkF64 3.0)] },
        { cells := [.text "A", .float (mkF64 2.0), .float (mkF64 5.0)] },
        { cells := [.text "A", .float (mkF64 3.0), .float (mkF64 7.0)] }
      ]
      .prim (.statsCorr "x" "y") [tbl]
  }]
  entry := some "main"
}

#guard checkProgram statsCorrTestProg == .ok ()
#guard (match eval 64 statsCorrTestProg [] pub {} (statsCorrTestProg.funs.head!.body) with
  | .ok (.optSome (.float f)) _ => Float.abs (Float.ofBits f.bits - 1.0) < 1e-9
  | _ => false)

private def statsLinRegTestProg : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk .linearModel pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 1.0), .float (mkF64 3.0)] },
        { cells := [.text "A", .float (mkF64 2.0), .float (mkF64 5.0)] },
        { cells := [.text "A", .float (mkF64 3.0), .float (mkF64 7.0)] }
      ]
      .prim (.statsLinReg "x" "y") [tbl]
  }]
  entry := some "main"
}

#guard checkProgram statsLinRegTestProg == .ok ()
#guard (match eval 64 statsLinRegTestProg [] pub {} (statsLinRegTestProg.funs.head!.body) with
  | .ok (.linearModel slope intercept r2) _ =>
    Float.abs (Float.ofBits slope.bits - 2.0) < 1e-9 &&
    Float.abs (Float.ofBits intercept.bits - 1.0) < 1e-9 &&
    Float.abs (Float.ofBits r2.bits - 1.0) < 1e-9
  | _ => false)

private def statsTTestBoundaryProg : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk .statTest pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 1.0), .float (mkF64 3.0)] }
      ]
      .prim (.statsTTest "x" "y") [tbl]
  }]
  entry := some "main"
}

#guard checkProgram statsTTestBoundaryProg == .ok ()
#guard (match runProgram 64 statsTTestBoundaryProg with
  | .ok rep =>
    rep.status == .stopped &&
    (match rep.diagnostic with
     | some msg => (msg.splitOn "outside boundary").length > 1
     | none => false)
  | .error _ => false)

/-! ## Scenario 8: Per-Column `WriteTable` Row-Tag Taint Check (B3 / Probe P2) -/

private def writeTableRowTagLeakProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("out", .mk (.writeTable "warehouse" "probation_summary"
        [
          { name := "program", ty := .text, tags := pub },
          { name := "probation_count", ty := .int, tags := ferpa }
        ]
        pub
        ferpa) pub)
    ]
    ret := .mk (.result .int .text) ferpa
    body :=
      let filteredSummary : Plan :=
        .summarize
          (.groupBy
            (.select
              (.filter
                (.sourceDB (.var "db") "students" studentSchema)
                (.prim .lt [.col "gpa", .lit (.decimal (2 * decScale))]))
              ["program"])
            ["program"])
          [{ name := "probation_count", op := .count, arg := none }]
          none
      .host .writeTable [.var "out", .rel filteredSummary]
  }]
  entry := some "main"
}

-- Probe P2: `program` is public (`[]`) while `effRow` carries `[ferpa]` and `destRowTags = []`.
-- Must be statically rejected so row presence cannot leak through the public `program` column!
#guard hasErrSubstr (checkProgram writeTableRowTagLeakProg) "column-by-column schema or tag mismatch"

/-! ## Scenario 9: `median` / `percentile` Stay Tagged vs. `stddev` / `variance` Clear (B4) -/

private def medianAfterSuppressProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let p : Plan :=
        .suppressSmallGroups
          (.summarize
            (.groupBy (.sourceDB (.var "db") "students" studentSchema) ["program"])
            [{ name := "med_gpa", op := .median, arg := some (.col "gpa") }]
            none)
          5 none .drop
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

private def percentileAfterSuppressProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let p : Plan :=
        .suppressSmallGroups
          (.summarize
            (.groupBy (.sourceDB (.var "db") "students" studentSchema) ["program"])
            [{ name := "p50_gpa", op := .percentile (mkF64 0.5), arg := some (.col "gpa") }]
            none)
          5 none .drop
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

private def stddevVarianceAfterSuppressProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let p : Plan :=
        .suppressSmallGroups
          (.summarize
            (.groupBy (.sourceDB (.var "db") "students" studentSchema) ["program"])
            [
              { name := "sd_gpa", op := .stddev, arg := some (.col "gpa") },
              { name := "var_gpa", op := .variance, arg := some (.col "gpa") }
            ]
            none)
          5 none .drop
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram medianAfterSuppressProg) "Console.printTable unauthorized for table sensitivity tags"
#guard hasErrSubstr (checkProgram percentileAfterSuppressProg) "Console.printTable unauthorized for table sensitivity tags"
#guard checkProgram stddevVarianceAfterSuppressProg == .ok ()

/-! ## Scenario 10: `progSafeForNI` Non-Vacuity (M1) -/

private def progWithSpecAndSensitiveDataAndPublicSuppress : Program := {
  datas := [{
    name := "PatientRef"
    ctors := [{ name := "PatientRef", fields := [.mk .text pii] }]
  }]
  schemas := [{ name := "Sales", schema := publicSalesSchema }]
  funs := [
    {
      name := "main"
      params := [("console", .mk (.console pub) pub)]
      ret := .mk .unit pub
      body :=
        let p : Plan :=
          .suppressSmallGroups
            (.summarize
              (.groupBy
                (.sourceExpr (.tableLit publicSalesSchema [
                  { cells := [.text "West", .int 100] }
                ]))
                ["region"])
              [{ name := "n", op := .count, arg := none }]
              none)
            5 none .drop
        .host .consolePrintTable [.var "console", .rel p]
    },
    {
      name := "unused_spec_test"
      kind := .test
      params := []
      ret := .mk .unit pub
      body := .letE "fc" (.mk (.console pii) pub)
        (.host (.fakeConsole pii) [])
        (.host .consolePrint [.var "fc", .lit (.text "test")])
    }
  ]
  entry := some "main"
}

#guard checkProgram progWithSpecAndSensitiveDataAndPublicSuppress == .ok ()
#guard progSafeForNI progWithSpecAndSensitiveDataAndPublicSuppress TagSet.empty == true

/-! ## Scenario 11: Multi-Group Complementary Suppression in `:mask` Mode (M3) -/

private def maskCompSchema : TableTy := {
  cols := [
    { name := "dept", ty := .text, tags := pub },
    { name := "score", ty := .int, tags := ferpa }
  ]
}

private def maskCompProg : Program := {
  funs := [{
    name := "main"
    params := [("console", .mk (.console pub) pub)]
    ret := .mk .unit pub
    body :=
      let tbl : Expr := .tableLit maskCompSchema [
        -- Dept A: 1 row (< 5)
        { cells := [.text "A", .int 10] },
        -- Dept B: 1 row (< 5); total suppressed = 1 + 1 = 2 < 5 -> triggers complementary suppression!
        { cells := [.text "B", .int 20] },
        -- Dept C: 5 rows (>= 5, smallest valid group -> masked by complementary suppression!)
        { cells := [.text "C", .int 1] },
        { cells := [.text "C", .int 1] },
        { cells := [.text "C", .int 1] },
        { cells := [.text "C", .int 1] },
        { cells := [.text "C", .int 1] },
        -- Dept D: 8 rows (>= 5, remains unmasked as `some 8`!)
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] },
        { cells := [.text "D", .int 2] }
      ]
      let p : Plan :=
        .suppressSmallGroups
          (.summarize (.groupBy (.sourceExpr tbl) ["dept"])
            [{ name := "n", op := .count, arg := none }]
            none)
          5 none .maskComplementary
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard checkProgram maskCompProg == .ok ()
#guard (match runProgram 64 maskCompProg with
  | .ok rep =>
    rep.status == .ok &&
    rep.stdout == ["dept | n\nA | none\nB | none\nC | none\nD | some(8)"]
  | .error _ => false)

/-! ## Scenario 12: Upfront `--allow-export` Runtime Gate (M4) -/

private def exportGateProg : Program := {
  funs := [{
    name := "main"
    params := [
      ("console", .mk (.console pub) pub),
      ("out", .mk (.writeFiles "exports/" pii) pub)
    ]
    ret := .mk .unit pub
    body := .host .consolePrint [.var "console", .lit (.text "before")]
  }]
  entry := some "main"
}

#guard checkProgram exportGateProg == .ok ()
-- Denied upfront: zero partial stdout!
#guard (match runProgram 64 exportGateProg {} with
  | .ok rep =>
    rep.status == .stopped &&
    rep.stdout == [] &&
    (match rep.diagnostic with
     | some msg => (msg.splitOn "--allow-export").length > 1
     | none => false)
  | .error _ => false)
-- Authorized via `runtimeAllowExport`: runs normally and emits stdout!
#guard (match runProgram 64 exportGateProg { runtimeAllowExport := pii } with
  | .ok rep => rep.status == .ok && rep.stdout == ["before"]
  | .error _ => false)

/-! ## Scenario 13: Public `WriteFiles` & Safe Subpath Matching Under `dana.policy` (M5) -/

private def policyPublicWriteFilesProg : Program := {
  policy := some strictRepoPolicy
  funs := [{
    name := "main"
    params := [("out", .mk (.writeFiles "out/" pub) pub)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

private def policySubpathWriteFilesProg : Program := {
  policy := some strictRepoPolicy
  funs := [{
    name := "main"
    params := [("out", .mk (.writeFiles "reports/q1/" ferpa) pub)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

private def policyTraversalWriteFilesProg : Program := {
  policy := some strictRepoPolicy
  funs := [{
    name := "main"
    params := [("out", .mk (.writeFiles "reports/../tmp/" ferpa) pub)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

#guard checkProgram policyPublicWriteFilesProg == .ok ()
#guard checkProgram policySubpathWriteFilesProg == .ok ()
#guard hasErrSubstr (checkProgram policyTraversalWriteFilesProg) "exceeds dana.policy"

/-! ## Scenario 14: `redact` & `pseudonymize` Relational Plans (M10) -/

private def redactPlanProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let p : Plan :=
        .select
          (.redact (.sourceDB (.var "db") "students" studentSchema) "email" "[MASKED]")
          ["program", "email"]
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard checkProgram redactPlanProg == .ok ()
#guard (match runProgram 64 redactPlanProg {
    realDBTables := [{
      db := "registrar", tableName := "students", schema := studentSchema,
      rows := [[.int 1, .text "alice@u.edu", .text "CS", .int 15, .decimal (35 * (decScale / 10))]]
    }]
  } with
  | .ok rep => rep.status == .ok && rep.stdout == ["program | email\nCS | [MASKED]"]
  | .error _ => false)

private def pseudonymizePlanProg : Program := {
  schemas := [{ name := "Students", schema := studentSchema }]
  funs := [{
    name := "main"
    params := [
      ("db", .mk (.readDB "registrar") pub),
      ("salt", .mk (.secret "student_hmac") sec),
      ("console", .mk (.console pub) pub)
    ]
    ret := .mk .unit pub
    body :=
      let p : Plan :=
        .select
          (.pseudonymize (.sourceDB (.var "db") "students" studentSchema) "email" (.var "salt"))
          ["program", "email"]
      .host .consolePrintTable [.var "console", .rel p]
  }]
  entry := some "main"
}

#guard checkProgram pseudonymizePlanProg == .ok ()
#guard (match runProgram 64 pseudonymizePlanProg {
    realDBTables := [{
      db := "registrar", tableName := "students", schema := studentSchema,
      rows := [[.int 1, .text "alice@u.edu", .text "CS", .int 15, .decimal (35 * (decScale / 10))]]
    }]
    realSecrets := [("student_hmac", "k_secret_42")]
  } with
  | .ok rep =>
    rep.status == .ok &&
    (match rep.stdout with
     | [out] => (out.splitOn "ps_").length > 1 && (out.splitOn "alice@u.edu").length == 1
     | _ => false)
  | .error _ => false)

/-! ## Scenario 15: Entry `Secret ""` Non-`"secret"` Tag Rejection (M11) -/

private def badEmptySecretTagProg : Program := {
  funs := [{
    name := "main"
    params := [("s", .mk (.secret "") pii)]
    ret := .mk .unit pub
    body := .lit .unit
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram badEmptySecretTagProg) "program entry parameters must be top-level capabilities"

/-! ## Scenario 16: Re-Review Hardening (Runtime Path Confinement, Canonical Wire, Numeric & Percentile Validation) -/

-- Blocking 2 / M9: runtime `writeFile` rejects traversal, absolute, empty, and backslash paths,
-- and joins root + relPath with exactly one `/` (preventing `out` + `_evil/x` -> `out_evil/x`).
private def mkWriteFileProg (root relPath : String) : Program := {
  funs := [{
    name := "main"
    params := [("out", .mk (.writeFiles root pub) pub)]
    ret := .mk (.result .unit .text) pub
    body := .host .writeFile [.var "out", .lit (.text relPath), .lit (.text "payload")]
  }]
  entry := some "main"
}

#guard (match runProgram 32 (mkWriteFileProg "reports/" "../public_www/leak.csv") with
  | .ok rep => rep.status == .ok && rep.writtenFiles.isEmpty
  | .error _ => false)
#guard (match runProgram 32 (mkWriteFileProg "reports/" "/etc/passwd") with
  | .ok rep => rep.status == .ok && rep.writtenFiles.isEmpty
  | .error _ => false)
#guard (match runProgram 32 (mkWriteFileProg "reports/" "sub\\..\\leak.csv") with
  | .ok rep => rep.status == .ok && rep.writtenFiles.isEmpty
  | .error _ => false)
#guard (match runProgram 32 (mkWriteFileProg "out" "_evil/x.csv") with
  | .ok rep => rep.status == .ok && rep.writtenFiles == [("out/_evil/x.csv", "payload")]
  | .error _ => false)
#guard (match runProgram 32 (mkWriteFileProg "reports/" "q1.csv") with
  | .ok rep => rep.status == .ok && rep.writtenFiles == [("reports/q1.csv", "payload")]
  | .error _ => false)
#guard !pathMatchesExportPrefix "out/" "out/..\\secret"

-- Minor 1 (M7): strict byte-for-byte wire canonicality rejects unquoted idents, non-canonical ints, and overflowing float bits.
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some main) (meta))\n") "non-canonical wire encoding"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int 007)))) (some \"main\") (meta))\n") "non-canonical wire encoding"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int -0)))) (some \"main\") (meta))\n") "non-canonical wire encoding"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int 1_000)))) (some \"main\") (meta))\n") "non-canonical wire encoding"
#guard hasErrSubstr (parseProgram "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (float) (tags)) (lit (lit-float 18446744073709551616)))) (some \"main\") (meta))\n") "non-canonical wire encoding"

-- Minor 3 & 4 (B1): degenerate `statsLinReg` stops cleanly; extreme magnitudes resist overflow/underflow.
private def degenerateLinRegProg : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk .linearModel pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 5.0), .float (mkF64 1.0)] },
        { cells := [.text "A", .float (mkF64 5.0), .float (mkF64 2.0)] }
      ]
      .prim (.statsLinReg "x" "y") [tbl]
  }]
  entry := some "main"
}

#guard checkProgram degenerateLinRegProg == .ok ()
#guard (match runProgram 64 degenerateLinRegProg with
  | .ok rep =>
    rep.status == .stopped &&
    (match rep.diagnostic with
     | some msg => (msg.splitOn "degenerate linear regression").length > 1
     | none => false)
  | .error _ => false)

#guard (match computeStatsCorr [[.float (mkF64 1e80), .float (mkF64 2e80)], [.float (mkF64 2e80), .float (mkF64 4e80)], [.float (mkF64 3e80), .float (mkF64 6e80)]] with
  | some r => Float.abs (Float.ofBits r.bits - 1.0) < 1e-9
  | none => false)
#guard (match computeStatsCorr [[.float (mkF64 1e-82), .float (mkF64 2e-82)], [.float (mkF64 2e-82), .float (mkF64 4e-82)], [.float (mkF64 3e-82), .float (mkF64 6e-82)]] with
  | some r => Float.abs (Float.ofBits r.bits - 1.0) < 1e-9
  | none => false)
#guard (match computeStatsLinReg [[.float (mkF64 1e-170), .float (mkF64 2e-170)], [.float (mkF64 2e-170), .float (mkF64 4e-170)], [.float (mkF64 3e-170), .float (mkF64 6e-170)]] with
  | some (slope, _, r2) => Float.abs (Float.ofBits slope.bits - 2.0) < 1e-9 && Float.abs (Float.ofBits r2.bits - 1.0) < 1e-9
  | none => false)
#guard (let med := Float.ofBits (medianSortedFloats [.float (mkF64 1e308), .float (mkF64 1.7e308)]).bits
  !med.isInf && Float.abs (med - 1.35e308) < 1e300)

-- R1 & N1: NaN / Inf in `statsLinReg` & `statsCorr` are rejected (never return spurious perfect fit),
-- and extreme-magnitude `mean`, `stddev`, and `percentile` resist overflow/underflow.
private def nanF64 : Float64 := { bits := 0x7ff8000000000000 }
private def posInfF64 : Float64 := { bits := 0x7ff0000000000000 }

#guard (computeStatsLinReg [[.float (mkF64 1.0), .float (mkF64 1.0)], [.float (mkF64 2.0), .float nanF64], [.float (mkF64 3.0), .float (mkF64 3.0)]]).isNone
#guard (computeStatsLinReg [[.float (mkF64 1.0), .float posInfF64], [.float (mkF64 2.0), .float posInfF64]]).isNone
#guard (computeStatsCorr [[.float (mkF64 1.0), .float (mkF64 1.0)], [.float (mkF64 2.0), .float nanF64], [.float (mkF64 3.0), .float (mkF64 3.0)]]).isNone
#guard (let m := Float.ofBits (meanSortedFloats [.float (mkF64 1.7e308), .float (mkF64 1.7e308)]).bits
  !m.isInf && Float.abs (m - 1.7e308) < 1e300)
#guard (let s := Float.ofBits (stddevSortedFloats [.float (mkF64 0.0), .float (mkF64 2e200)]).bits
  !s.isInf && Float.abs (s - 1e200) < 1e192)
#guard (let s := Float.ofBits (stddevSortedFloats [.float (mkF64 0.0), .float (mkF64 2e-170)]).bits
  s > 0.0 && Float.abs (s - 1e-170) < 1e-178)
#guard (let p := Float.ofBits (percentileSortedFloats (mkF64 0.5) [.float (mkF64 (-1.7e308)), .float (mkF64 1.7e308)]).bits
  !p.isInf && Float.abs p < 1e-9)

-- Minor 5 (B1): out-of-range or NaN `percentile` parameter `p` is statically rejected.
private def mkBadPercentileProg (p : Float64) : Program := {
  funs := [{
    name := "main"
    params := []
    ret := .mk .int pub
    body :=
      let tbl : Expr := .tableLit floatMetricsSchema [
        { cells := [.text "A", .float (mkF64 1.0), .float (mkF64 2.0)] }
      ]
      let pPlan : Plan := .summarize (.groupBy (.sourceExpr tbl) ["grp"])
        [{ name := "p_bad", op := .percentile p, arg := some (.col "x") }] none
      .prim .tableCount [.rel pPlan]
  }]
  entry := some "main"
}

#guard hasErrSubstr (checkProgram (mkBadPercentileProg (mkF64 1.5))) "percentile parameter p must be finite in [0.0, 1.0]"
#guard hasErrSubstr (checkProgram (mkBadPercentileProg (mkF64 (-0.1)))) "percentile parameter p must be finite in [0.0, 1.0]"
#guard hasErrSubstr (checkProgram (mkBadPercentileProg { bits := 0x7ff8000000000000 })) "percentile parameter p must be finite in [0.0, 1.0]"

/-! ## Axiom Footprint Audit (Theorem 1 & Theorem 2) -/

#print axioms theorem1_expr_soundness
#print axioms theorem1_plan_soundness
#print axioms theorem1_program_soundness
#print axioms theorem1_suppress_small_groups_invariant
#print axioms theorem2_expr_noninterference_ok
#print axioms theorem2_plan_noninterference_ok
#print axioms theorem2_program_noninterference_ok
#print axioms theorem2_public_noninterference
#print axioms theorem2_redacted_stop_noninterference

end DanaCore.Tests
