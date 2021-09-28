import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
import Lean.Meta
open Nat

/-
Simple examples of solving SAT problems with proofs to be run in the interpreter.
-/

def cl0 : Clause 1 := (some true) +: Vector.nil
def cl00 : Clause 1 := (some false) +: Vector.nil

def cl1 : Clause 2 :=   -- P ∨ Q
  (some true) +: (some true) +: Vector.nil

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cl3 : Clause 2 := -- ¬Q
  (none) +: (some false) +: Vector.nil

def cl4 : Clause 2 := (some true) +: none +: Vector.nil  -- P

def eg0Statement := cl0 +: cl00 +: Vector.nil
def eg1Statement : Vector (Clause 2) 3 := cl2 +: cl1 +: cl3 +: Vector.nil -- all three clauses
def eg2Statement := cl1 +: cl3  +: Vector.nil -- clauses 1 and 3 only
def eg3Statement : Vector (Clause 2) 0 :=  Vector.nil
def eg4Statement := cl2 +: cl4 +: Vector.nil

set_option maxHeartbeats 500000

-- structured solutions

def eg0Soln := solveSAT (eg0Statement)
def eg1Soln := solveSAT (eg1Statement)
def eg2Soln := solveSAT (eg2Statement)
def eg3Soln := solveSAT (eg3Statement)
def eg4Soln := solveSAT (eg4Statement)

def eg1IsFalse : Bool := eg1Soln.isSat
def eg2IsTrue : Bool := eg2Soln.isSat
#eval eg1IsFalse
#reduce eg1IsFalse
#eval eg2IsTrue
#eval eg4Soln.isSat

open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

syntax (name:= normalform)"whnf!" term : term
@[termElab normalform] def normalformImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(whnf! $s) => 
      do
        let t ← elabTerm s none 
        let e ← whnf t
        return e
  | _ => Lean.Elab.throwIllFormedSyntax

def eg1isFalseNormal := whnf! eg1IsFalse
#eval eg1isFalseNormal
#print eg1IsFalse
#print eg1isFalseNormal
#print eg1Soln
#print eg2IsTrue

/-
-- def eg3SolnNorm := whnf! eg3Soln
def eg2SolnNorm := whnf! eg2Soln
def eg4SolnNorm := whnf! eg4Soln
#print eg4SolnNorm

/- (in working version)
def eg4SolnNorm : SatSolution eg4Statement :=
SatSolution.unsat
  (mergeUnitTrees zero (_ : 0 < succ (0 + 1))
    (Eq.mpr eg4SolnNorm.proof_1
      (pullBackTree true zero (_ : 0 < succ (0 + 1)) eg4Statement
          (restrictionData true zero (_ : 0 < succ (0 + 1)) eg4Statement).restrictionClauses
          (restrictionData true zero (_ : 0 < succ (0 + 1)) eg4Statement).nonPosReverse
          (restrictionData true zero (_ : 0 < succ (0 + 1)) eg4Statement).reverseRelation (_root_.contradiction (0 + 1))
          (ResolutionTree.assumption zero (_ : 0 < succ 0) (_root_.contradiction (0 + 1))
            eg4SolnNorm.proof_2)).provedTree)
    (Eq.mpr eg4SolnNorm.proof_3
      (pullBackTree false zero (_ : 0 < succ (0 + 1)) eg4Statement
          (restrictionData false zero (_ : 0 < succ (0 + 1)) eg4Statement).restrictionClauses
          (restrictionData false zero (_ : 0 < succ (0 + 1)) eg4Statement).nonPosReverse
          (restrictionData false zero (_ : 0 < succ (0 + 1)) eg4Statement).reverseRelation
          (_root_.contradiction (0 + 1))
          (ResolutionTree.assumption zero (_ : 0 < succ 0) (_root_.contradiction (0 + 1))
            eg4SolnNorm.proof_4)).provedTree))
-/


-- def eg1 : isUnSat eg1Statement := getProof eg1Soln
def eg4 : isUnSat eg4Statement := getProof eg4Soln -- the minimal non-type-checking example
def eg2 : isSat eg2Statement := getProof eg2Soln 
def eg3 : isSat eg3Statement := getProof eg3Soln 


/-
def eg1SolnNorm := whnf! eg1Soln


example : eg1IsFalse = false := by  rfl


#eval eg1Soln.toString
#eval eg2Soln.toString

def eg1 : isUnSat eg1Statement := getProof eg1Soln
def eg2 : isSat eg2Statement := getProof eg2Soln 

#eval Decidable.decide (isSat eg2Statement)

#check eg1
#check eg2

example : Not (cl1 ⊇  cl2) := by decide
-/
-/