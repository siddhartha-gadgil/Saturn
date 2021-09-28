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

def cl2 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cl4 : Clause 2 := (some true) +: none +: Vector.nil  -- P

def eg4Statement := cl2 +: cl4 +: Vector.nil

def solveSATOuter{n dom : Nat}: (clauses : Vector (Clause (n + 1)) dom) →  SatSolution clauses :=
      match n with
      | zero => fun clauses => lengthOneSolution clauses
      | m + 1 =>
        fun clauses =>
        let cls := clauses 
        let index := zero
        let bd := zero_lt_succ (m + 1)
        let rd : RestrictionData false zero bd cls := 
            restrictionData false index bd cls
        let subCls := rd.restrictionClauses.restClauses
        let subSol: SatSolution subCls := solveSAT subCls
        match subSol with
        | SatSolution.sat valuation pf => 
          let pb :=  pullBackSolution false index bd cls 
              rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
          let valuationN := insert false (m + 1) index bd valuation.coords
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
                let subSol : SatSolution subCls := solveSAT subCls
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

def eg4CallSoln := solveSATOuter eg4Statement

def eg4Soln :=  
    let clauses := eg4Statement
    let cls :  Vector (Clause 2) 2 := clauses 
    let index := zero
    let bd := zero_lt_succ 1
    let rd : RestrictionData false zero bd cls := 
        restrictionData false zero bd cls
    let subCls   := 
            rd.restrictionClauses.restClauses
    let subSol: SatSolution subCls := solveSAT subCls
    match subSol with
    | SatSolution.sat valuation pf => 
      let pb :=  pullBackSolution false zero bd cls 
          rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
      let valuationN := insert false 1 index bd valuation.coords
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
              let pb :=  pullBackSolution  true index bd cls 
                  rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
              let valuationN := insert true _ index bd valuation.coords
              SatSolution.sat valuationN.vec pb
            | SatSolution.unsat tree  => 
                let liftedProof : LiftedResPf true index bd cls :=
                  pullBackResPf  true index bd cls 
                      rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                      tree
                match liftedProof with
                | LiftedResPf.contra pf => 
                    treeToUnsat pf
                | LiftedResPf.unit rpf2 => 
                    let merged := mergeUnitTrees index bd rpf2 rpf1
                    treeToUnsat merged



def eg4SolnNorm := whnf! eg4Soln

#print eg4SolnNorm

def eg4CallSolnNorm := whnf! eg4CallSoln

#print eg4CallSolnNorm

def eg4SolnVal := eg4Soln.isSat

#eval eg4Soln.isSat

def eg4 : isUnSat eg4Statement := getProof eg4Soln
def eg4Call : isUnSat eg4Statement := getProof eg4CallSoln