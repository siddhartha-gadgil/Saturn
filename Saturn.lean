import Saturn.Examples
import Saturn.DPLL
import Saturn.NQueens

def main : IO UInt32 := do
  IO.println "Hello, SATurn!"
  IO.println (solve eg1Statement).toString
  IO.println (solve eg2Statement).toString
  IO.println (solve (queensClauses 5)).toString
  return 0
