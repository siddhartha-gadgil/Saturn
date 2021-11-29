import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
import Lean.Meta
open Lean Meta Elab Term
open Nat

/-
Simple examples of solving SAT problems with proofs to be run in the interpreter.
-/

def cl1 : Clause 2 :=   -- P ∨ Q
  (some true) +: (some true) +: Vector.nil

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cl3 : Clause 2 := -- ¬Q
  (none) +: (some false) +: Vector.nil

def eg1Statement : Vector (Clause 2) 3 := cl1 +: cl2 +: cl3 +: Vector.nil -- all three clauses
def eg2Statement := cl1 +: cl3 +: Vector.nil -- clauses 1 and 3 only

#eval decide (isSat eg2Statement)
#eval decide (isSat eg1Statement)
#eval decide (isUnSat eg1Statement)



-- structured solutions

def eg1Soln := solveSAT (eg1Statement)
def eg2Soln := solveSAT (eg2Statement)

#eval eg1Soln.toString
#eval eg2Soln.toString


def eg1Untyped  := getProof eg1Soln

set_option maxHeartbeats 500000

def eg1 : isUnSat eg1Statement := by
  have lem : decide (isUnSat eg1Statement) = true := by nativeDecide
  exact of_decide_eq_true lem 

def eg2 : isSat eg2Statement := getProof eg2Soln 

#check eg1
#check eg2
