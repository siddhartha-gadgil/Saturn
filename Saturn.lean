import Saturn.Examples
import Saturn.DPLL
import Saturn.NQueens
open Nat

/-
Running the elementary examples as well as the N-Queens problem for `N` a command line
argument.
-/
def printSolution {n dom : Nat}: (clauses : Vector (Clause n) dom) → Nat →  IO Unit :=
  match n with
  | zero => fun _ _ => pure ()
  | l + 1 => 
    fun clauses q => 
      do
        IO.println ""
        IO.println (s!"Solving the {q}-Queens problem (may take a while):")
        IO.println (solveSAT clauses).toString
        return ()

def main (args: List String) : IO UInt32 := do
  let n : Nat := 
    match args.head? with
    | none => 0 
    | some s =>
      match s.toNat? with
      | some n => n 
      | none => 0  
  IO.println ""
  IO.println "SATurn: A SAT solver-prover in lean"
  IO.println ""
  IO.println "Solving the sat problem with clauses {P ∨ Q}, {P} and {¬Q}:"
  IO.println (solveSAT eg1Statement).toString
  IO.println ""
  IO.println "Solving the sat problem with clauses {P ∨ Q} and {¬Q}:"
  IO.println (solveSAT eg2Statement).toString
  let problem := (queensClauses n)
  printSolution problem n

  return 0
