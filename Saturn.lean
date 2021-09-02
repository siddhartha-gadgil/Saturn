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
  IO.println "Hello from SATurn!"
  IO.println (solveSAT eg1Statement).toString
  IO.println (solveSAT eg2Statement).toString
  let problem := (queensClauses n)
  printSolution problem

  return 0
