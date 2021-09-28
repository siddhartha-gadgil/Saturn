import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.DPLL
import Lean.Meta
open Nat

open Lean.Meta
open Lean.Elab.Term

syntax (name:= nrmlform)"whnf!" term : term
@[termElab nrmlform] def normalformImpl : TermElab :=
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

def cls1 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cls2 : Clause 2 := (some true) +: none +: Vector.nil  -- P

def egStatement := cls1 +: cls2 +: Vector.nil

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

def egCallSoln := solveSATOuter egStatement

def egSoln :=  
    let clauses := egStatement
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



def egSolnNorm := whnf! egSoln

#print egSolnNorm

def egCallSolnNorm := whnf! egCallSoln

#print egCallSolnNorm

def egSolnVal := egSoln.isSat

#eval egSoln.isSat

def eg : isUnSat egStatement := getProof egSoln
def egCall : isUnSat egStatement := getProof egCallSoln

inductive SatAnswer{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) where
  | unsat : SatAnswer clauses
  | sat : (valuation : Valuation (n + 1)) → SatAnswer clauses 

structure SimpleRestrictionClauses{dom n: Nat}
    (clauses: Vector (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector  (Clause n) codom

def prependRes{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (rd : SimpleRestrictionClauses clauses) → 
           (head : Clause (n + 1)) → 
        SimpleRestrictionClauses (head +: clauses) := 
        fun rd  head => 
          if c : head.coords focus focusLt = some branch then
            ⟨rd.codom, rd.restClauses⟩
          else
            ⟨rd.codom + 1, (FinSeq.vec (delete focus focusLt head.coords)) +: rd.restClauses⟩

def restClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)  
        (clauses: Vector (Clause (n + 1)) dom) :
         SimpleRestrictionClauses clauses :=
            match dom, clauses with
            | 0, _ =>  ⟨0, Vector.nil⟩
            | m + 1, Vector.cons head clauses =>
                prependRes branch focus focusLt clauses 
                            (restClauses branch focus focusLt clauses) head           

def answerSAT{n dom : Nat}: (clauses : Vector (Clause (n + 1)) dom) →  SatAnswer clauses :=
      match n with
      | zero => fun clauses => 
           match lengthOneSolution clauses with
           | SatSolution.sat valuation pf => SatAnswer.sat valuation
           | SatSolution.unsat tree => SatAnswer.unsat         
      | m + 1 =>
        fun clauses =>
        let cls := clauses 
        let bd := zero_lt_succ (m + 1)
        let rd  := 
            restClauses false zero bd clauses
        let subCls := rd.restClauses
        let subSol: SatAnswer subCls := answerSAT subCls
        match subSol with
        | SatAnswer.sat valuation  => 
          let valuationN := insert false (m + 1) zero bd valuation.coords
          SatAnswer.sat valuationN.vec 
        | SatAnswer.unsat  => 
            let rd 
                := restClauses true zero bd cls
            let subCls := rd.restClauses
            let subSol : SatAnswer subCls := answerSAT subCls
            match subSol with
            | SatAnswer.sat valuation  => 
                let valuationN := insert true _ zero bd valuation.coords
                SatAnswer.sat valuationN.vec 
            | SatAnswer.unsat   => 
                SatAnswer.unsat

def egAnswer : SatAnswer egStatement := answerSAT egStatement

def egAnswerNorm : SatAnswer egStatement := whnf! egAnswer