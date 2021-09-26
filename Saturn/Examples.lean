import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
import Lean.Meta

open Nat

def cl1 : Clause 2 :=   -- P ∨ Q
  (some true) +: (some true) +: Vector.nil

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cl3 : Clause 2 := -- ¬Q
  (none) +: (some false) +: Vector.nil

def eg1Statement : Vector (Clause 2) 3 := cl2 +: cl1 +: cl3 +: Vector.nil -- all three clauses
def eg2Statement := FinSeq.vec (eg1Statement.coords.tail) -- clauses 1 and 3 only

set_option maxHeartbeats 500000

-- structured solutions

def eg1Soln := solveSAT (eg1Statement)
def eg2Soln := solveSAT (eg2Statement)


def eg1IsFalse : Bool := eg1Soln.isSat
#eval eg1IsFalse
-- example : eg1IsFalse = false := by  rfl

#eval eg1Soln.toString
#eval eg2Soln.toString

def eg1 := getProof eg1Soln
def eg2 := getProof eg2Soln 

#eval Decidable.decide (isSat eg2Statement)

#check eg1
#check eg2

example : Not (cl1 ⊇  cl2) := by decide