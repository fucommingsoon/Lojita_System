import Lean
import LojitaCtx

open Lean Elab Command

/- Audit the compiled environment, including dependencies defined in Init and Std. -/
private def audit (env : Environment) (isProject : Name → Bool)
    (initial : Array (Name × List Name)) (auditCompiler : Bool) : CommandElabM Unit := do
  let label := if auditCompiler then "G1 compiler" else "G1"
  let rewrites := (Compiler.CSimp.ext.getState env).map
  let mut rewriteCount := 0
  let mut todo := initial
  let mut projectViolations : Array Name := #[]
  let roots := todo.size
  let mut seen : NameSet := {}
  let mut violations := 0
  let mut counters : Std.TreeMap String Nat := {}
  let mut examples : Array String := #[]
  let mut queueIndex := 0
  let mut names : Std.TreeMap String (List Name) := {}
  while let some (n, parents) := todo[queueIndex]? do
    queueIndex := queueIndex + 1
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | throwError "missing declaration {n}"
    let badAx := (info matches .axiomInfo _) && ![``propext, ``Quot.sound, ``Classical.choice].contains n
    let reason := if n == ``sorryAx then "sorry" else if badAx then "axiom"
      else if isExtern env n then "extern" else if info.isUnsafe then "unsafe" else ""
    if !reason.isEmpty then
      violations := violations + 1
      if isProject n then projectViolations := projectViolations.push n
      counters := counters.insert reason (counters[reason]?.getD 0 + 1)
      names := names.insert reason (n :: names[reason]?.getD [])
      if reason != "extern" || counters[reason]?.getD 0 ≤ 8 then
        examples := examples.push (reason ++ "  " ++ String.intercalate " -> " ((n :: parents).reverse.map toString))
    let mut deps := info.getUsedConstantsAsSet
    if let some impl := Compiler.getImplementedBy? env n then deps := deps.insert impl
    if auditCompiler then
      if let some rewrite := rewrites.find? n then
        rewriteCount := rewriteCount + 1
        deps := (deps.insert rewrite.toDeclName).insert rewrite.thmName
    for dep in deps do
      unless seen.contains dep do todo := todo.push (dep, n :: parents)
  if auditCompiler then
    logInfo m!"G1 compiler audit followed {rewriteCount} registered csimp substitutions"
  logInfo m!"{label} audited {roots} project declarations, {seen.size} reachable constants"
  logInfo m!"Forbidden declarations defined in audited project modules: {projectViolations.size} {projectViolations}"
  for (kind, ns) in names.toList do logInfo m!"{kind}: {ns}"
  unless violations == 0 do
    logError m!"{label} strict purity failed at {violations} constants {counters.toList}\n{String.intercalate "\n" examples.toList}"

run_cmd do
  let env ← getEnv
  for dir in ["LojitaCtx/Posix","LojitaCtx/Io"] do
    for file in ← (System.FilePath.mk dir).walkDir do
      if file.extension == some "lean" then
        let mod := ((file.withExtension "").components).foldl Name.str Name.anonymous
        unless env.header.moduleNames.contains mod do throwError "G1 module missing from environment: {mod}"
  let isProject := fun n =>
    match env.getModuleIdxFor? n with
    | none => false
    | some idx => [`LojitaCtx.Io, `LojitaCtx.Posix].any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
  -- Report a dependency forced by the required regular-file representation when present.
  let payload := `LojitaCtx.Posix.InodePayload.reg
  if (env.find? payload).any (·.getUsedConstantsAsSet.contains `ByteArray) &&
      (env.find? `ByteArray).any (·.getUsedConstantsAsSet.contains `ByteArray.mk) &&
      isExtern env `ByteArray.mk then
    logInfo m!"G1 required field: {payload} -> ByteArray -> ByteArray.mk [extern]"
  let mut todo : Array (Name × List Name) := #[]
  for (n, _) in env.constants.toList do
    if isProject n then
      todo := todo.push (n, [])
  if todo.isEmpty then throwError "no audited constants"
  audit env isProject todo false
  audit env isProject todo true
