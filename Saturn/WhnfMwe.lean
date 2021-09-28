import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
import Lean.Meta
open Nat

open Lean.Meta
open Lean.Elab.Term

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

open Nat
open FinSeq


def clauses : Vector (Clause 2) 0 :=  Vector.nil

def egSoln:  SatSolution clauses := solveSAT  clauses

def directSoln:  SatSolution clauses := 
      let cls := clauses 
      let index := zero
      let bd := zero_lt_succ 1
      let rd : RestrictionData false zero bd cls := 
            restrictionData false zero bd cls
      let subCls : Vector (Clause 1) 0 := Vector.nil 
      let valuation := true +: Vector.nil
      let pf : ((k : Nat) → (kw : k < zero) 
        → ClauseSat (subCls.coords k kw) valuation) := fun k kw => nomatch kw
      let pb :=  pullBackSolution false index bd cls 
              rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
      let valuationN := insert false _ index bd valuation.coords
      SatSolution.sat valuationN.vec pb


def directSolnBranched:  SatSolution clauses := 
    let n := 1
    match c:n with
    | zero =>  False.elim (Nat.succ_ne_zero  _ c)
    | m + 1 =>
      let cls := clauses 
      let index := zero
      let bd := zero_lt_succ 1
      let rd : RestrictionData false zero bd cls := 
            restrictionData false index bd cls
      let subCls := rd.restrictionClauses.restClauses
      let subSol: SatSolution subCls := solveSAT subCls
      match subSol with
        | SatSolution.sat valuation pf => 
          let pb :=  pullBackSolution false index bd cls 
              rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
          let valuationN := insert false _ index bd valuation.coords
          SatSolution.sat valuationN.vec pb
        | SatSolution.unsat tree => 
            let liftedProof : LiftedResPf false zero bd cls :=
              pullBackResPf  false index bd cls 
                  rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                  tree
            match liftedProof with
            | LiftedResPf.contra pf => 
                treeToUnsat pf
            | LiftedResPf.unit rpf1 => 
                let rd : RestrictionData true zero bd cls 
                    := restrictionData true index bd cls
                let subCls := rd.restrictionClauses.restClauses
                let subSol := solveSAT subCls
                match subSol with
                | SatSolution.sat valuation pf => 
                  let pb :=  pullBackSolution true index bd cls 
                      rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                  let valuationN := insert true _ index bd valuation.coords
                  SatSolution.sat valuationN.vec pb
                | SatSolution.unsat tree  => 
                    let liftedProof :=
                      pullBackResPf  true index bd cls 
                          rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                          tree
                    match liftedProof with
                    | LiftedResPf.contra pf => 
                        treeToUnsat pf
                    | LiftedResPf.unit rpf2 => 
                        let merged := mergeUnitTrees index bd rpf2 rpf1
                        treeToUnsat merged


def egSolnNorm := whnf! egSoln
def directSolnNorm := whnf! directSoln
def directSolnBranchedNorm := whnf! directSolnBranched

#print directSoln 
#print egSoln