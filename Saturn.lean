import Saturn.Examples
import Saturn.DPLL
import Saturn.NQueens
open Nat

def printSolution {n dom : Nat}: (clauses : Vector (Clause n) dom) →  IO Unit :=
  match n with
  | zero => fun _ => pure ()
  | l + 1 => 
    fun clauses => 
      do
        IO.println ("solving problem")
        IO.println (solve clauses).toString
        return ()

def main (args: List String) : IO UInt32 := do
  let n := Option.getD (bind (args.head?) (String.toNat?)) zero
  IO.println "Hello from SATurn!"
  IO.println (solve eg1Statement).toString
  IO.println (solve eg2Statement).toString
  let problem := (queensClauses n)
  printSolution problem

  return 0
