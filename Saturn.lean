import Saturn.Examples
import Saturn.DPLL

def main : IO UInt32 := do
  IO.println "Hello, SATurn!"
  IO.println (solve eg1Statement).toString
  IO.println (solve eg2Statement).toString
  return 0
