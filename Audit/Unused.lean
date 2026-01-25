import Lean
import ImportGraph.RequiredModules
import Collatz.MainEntry

open Lean
open Lean.Elab Command

def projectRoot : Name := `Collatz

def roots : List Name :=
  [`Collatz.collatz_conjecture_universal
  , `Collatz.collatz_conjecture_odd_universal
  , `Collatz.no_nontrivial_cycles
  ]

def namesToJson (xs : Array Name) : Json :=
  Json.arr <| xs.map (fun n => Json.str n.toString)

elab "#dump_unused" : command => do
  let env ← getEnv

  -- CoreM -> CommandElabM
  let used : NameSet ←
    Lean.Elab.Command.liftCoreM <|
      (NameSet.ofList roots).transitivelyUsedConstants

  let mut all : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some m := env.getModuleFor? n then
      if projectRoot.isPrefixOf m then
        all := all.push n

  let mut usedArr : Array Name := #[]
  let mut unusedArr : Array Name := #[]
  for n in all do
    if used.contains n then usedArr := usedArr.push n
    else unusedArr := unusedArr.push n

  liftIO <| IO.FS.writeFile "used.json"   (toString (namesToJson usedArr))
  liftIO <| IO.FS.writeFile "unused.json" (toString (namesToJson unusedArr))

#dump_unused