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
def eg2IsTrue : Bool := eg2Soln.isSat
#eval eg1IsFalse
#reduce eg1IsFalse
#eval eg2IsTrue

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

def eg2SolnNorm := whnf! eg2Soln
def eg1SolnNorm := whnf! eg1Soln

/-
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