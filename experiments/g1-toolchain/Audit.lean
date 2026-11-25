import Lean

open Lean Elab Command

/-- The walk uses the same constant dependencies, implementation edges, and
    standard axioms as Test/PosixPurity.lean. The roots here are explicit. -/
private def forbidden (env : Environment) (roots : Array Name) : IO (Nat × List String) := do
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut bad : List String := []
  let mut i := 0
  while let some name := todo[i]? do
    i := i + 1
    if seen.contains name then continue
    seen := seen.insert name
    let some decl := env.find? name | throw <| IO.userError s!"missing declaration {name}"
    if name == ``sorryAx || ((decl matches .axiomInfo _) &&
        ![``propext, ``Quot.sound, ``Classical.choice].contains name) ||
        isExtern env name || decl.isUnsafe then bad := toString name :: bad
    let mut deps := decl.getUsedConstantsAsSet
    if let some impl := Compiler.getImplementedBy? env name then deps := deps.insert impl
    todo := todo ++ deps.toList.toArray
  return (seen.size, bad.mergeSort)

/-- Load the target's environments from disk while running the auditor with the release compiler. -/
unsafe def main (paths : List String) : IO Unit := do
  searchPathRef.set (paths.map System.FilePath.mk)
  enableInitializersExecution
  let env ← importModules #[{module := `Native}] {} (loadExts := true)
  let root := `G1Probe.Payload.reg
  let (reachable, bad) ← forbidden env #[root]
  IO.println s!"payload: reachable={reachable}, forbidden={bad.length} {bad}"
  let replacements := Compiler.CSimp.ext.getState env
  let targets := [`Nat.succ, `UInt8.ofBitVec, `Array.mk, `ByteArray.mk]
  let mut impls := #[]
  for n in targets do
    if let some e := replacements.map.find? n then
      IO.println s!"compiler rewrite: {n} -> {e.toDeclName} ({e.thmName})"
      impls := impls.push e.toDeclName
  if !impls.isEmpty then
    let (n, deps) ← forbidden env impls
    IO.println s!"replacement bodies: reachable={n}, forbidden={deps.length} {deps}"
