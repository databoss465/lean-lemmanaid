import Lean
import LeanLemmanaid.Template
import LeanLemmanaid.TypedAbstraction
import LeanLemmanaid.Elaboration

open Lean Environment Elab Term Meta Command

initialize templateExt : PersistentEnvExtension (Name × Template) (Name × Template) (NameMap Template) ← do
  registerPersistentEnvExtension {
    mkInitial := return {}

    addImportedFn imported := do
      let mut s : (NameMap Template) := {}
      for (name, temp) in imported.flatten do
        s := s.insert name temp
      pure s

    addEntryFn map temp := map.insert temp.1 temp.2

    exportEntriesFn map := map.toArray
  }
