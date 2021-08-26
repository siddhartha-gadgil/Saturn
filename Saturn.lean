import Saturn.Examples
import Saturn.DPLL
import Saturn.NQueens

def printSolution {n dom : Nat}: (clauses : FinSeq dom (Clause n)) →  IO Unit :=
  match n with
  | 0 => fun _ => pure ()
  | l + 1 => 
    fun clauses => 
      do
        IO.println ("solving problem")
        IO.println (solve clauses).toString
        return ()

def main (args: List String) : IO UInt32 := do
  let n := Option.getD (bind (args.head?) (String.toNat?)) 0
  IO.println "Hello from SATurn!"
  IO.println (solve eg1Statement).toString
  IO.println (solve eg2Statement).toString
  let problem := (queensClauses n)
  printSolution problem

  return 0
