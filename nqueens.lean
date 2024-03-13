import Saturn.Examples
import Saturn.DPLL
import Saturn.NQueens
open Nat

/-
Running the elementary examples as well as the N-Queens problem for `N` a command line
argument.
-/
def printSolution {n num_clauses : Nat}: (clauses : Vector (Clause (n * n)) num_clauses) → Nat →  IO Unit :=
  match n with
  | zero => fun _ _ => pure ()
  | m + 1 =>
    fun clauses q =>
      do
        IO.println ""
        IO.println (s!"Solving the {q}-Queens problem (may take a while):")
        let soln := solveSAT clauses
        match soln with
        | .unsat .. =>
          IO.println soln.toString
        | .sat model .. =>
          IO.println "\nSAT\n"
          IO.println (showQueens  (m + 1) model)
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
  IO.println "Solving the sat problem with clauses {P ∨ Q}, {¬P} and {¬Q}:"
  IO.println (solveSAT eg1Statement).toString
  IO.println ""
  IO.println "Solving the sat problem with clauses {P ∨ Q} and {¬Q}:"
  IO.println (solveSAT eg2Statement).toString
  let problem := (queensClauses n)
  printSolution problem n

  return 0
