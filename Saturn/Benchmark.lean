import Lean

section
open Lean Elab Command

syntax (name := timeCmd)  "#time " command : command

@[commandElab timeCmd] def elabTimeCmd : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end

set_option maxRecDepth 100000 in
#time example : (List.range 500).length = 500 := rfl
