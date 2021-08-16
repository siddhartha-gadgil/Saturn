import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.Resolution
import Saturn.DPLL

open Nat

def cl1 : Clause 2 :=   -- P ∨ Q
  (some true) +: (some true) +: FinSeq.empty

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: FinSeq.empty

def cl3 : Clause 2 := -- ¬Q
  (none) +: (some false) +: FinSeq.empty

def eg1Statement : FinSeq 3 (Clause 2) := cl2 +: cl1 +: cl3 +: FinSeq.empty
def eg2Statement := tail eg1Statement

set_option maxHeartbeats 500000

-- structured solutions

def eg1Soln := solve (eg1Statement)
def eg2Soln := solve (eg2Statement)

#eval eg1Soln.toString
#eval eg2Soln.toString

-- theorems: can directly use `proveOrDisprove`; we are avoiding computing twice
-- note that a refined type is specified, the opposite will give an error

def eg1 : unsat eg1Statement := getProof eg1Soln -- should be unsat
def eg2 : sat eg2Statement := getProof eg2Soln -- should be sat

#check eg1
#check eg2