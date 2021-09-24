import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL

open Nat

def cl1 : Clause 2 :=   -- P ∨ Q
  (some true) +: (some true) +: Vector.Nil

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.Nil

def cl3 : Clause 2 := -- ¬Q
  (none) +: (some false) +: Vector.Nil

def eg1Statement : Vector (Clause 2) 3 := cl2 +: cl1 +: cl3 +: Vector.Nil -- all three clauses
def eg2Statement := FinSeq.vec (eg1Statement.at.tail) -- clauses 1 and 3 only

set_option maxHeartbeats 500000

-- structured solutions

def eg1Soln := solveSAT (eg1Statement)
def eg2Soln := solveSAT (eg2Statement)

#eval eg1Soln.toString
#eval eg2Soln.toString

-- theorems: can directly use `proveOrDisprove`; we are avoiding computing twice
-- note that a refined type is specified, the opposite will give an error

def eg1 : unsat eg1Statement := getProof eg1Soln -- should be unsat, sat is a compiler error
def eg2 : sat eg2Statement := getProof eg2Soln -- should be sat, unsat is a compiler error

#check eg1
#check eg2