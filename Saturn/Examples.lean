import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
open Nat

/-
Simple examples of solving SAT problems with proofs to be run in the interpreter.
-/
def cl1 : Clause 2 := (some true) +: (some true) +: Vector.nil -- P ∨ Q
def cl2 : Clause 2 := (some false) +: (none) +: Vector.nil -- ¬P
def cl3 : Clause 2 := (none) +: (some false) +: Vector.nil -- ¬Q

def eg1Statement := cl1 +: cl2 +: cl3 +: Vector.nil -- all three clauses
def eg2Statement := cl1 +: cl3 +: Vector.nil -- clauses 1 and 3 only

#eval decide (isSat eg2Statement)  -- true
#eval decide (isSat eg1Statement)   -- false
#eval decide (isUnSat eg1Statement)  -- true

-- structured solutions

def eg1Soln : SatSolution eg1Statement := solveSAT (eg1Statement)
def eg2Soln : SatSolution eg2Statement := solveSAT (eg2Statement)

#eval eg1Soln.toString
#eval eg2Soln.toString

def eg1Untyped  := getProof eg1Soln

def eg1 : isUnSat eg1Statement := by
  have lem : decide (isUnSat eg1Statement) = true := by nativeDecide
  exact of_decide_eq_true lem 

set_option maxHeartbeats 500000
def eg2 : isSat eg2Statement := getProof eg2Soln 

#check eg1 -- isUnSat eg1Statement
#check eg2 -- isSat eg2Statement
