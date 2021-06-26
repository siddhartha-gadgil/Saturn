import Saturn.FinSeq 
import Saturn.Solverstep
import Saturn.Resolution
import Saturn.PosRestClause
import Saturn.PrependClause
import Saturn.ExistingClause
-- set_option trace.Elab.definition true
-- set_option pp.all true

open Nat
open leaner

instance {n: Nat} : DecidableEq (Clause n) := fun c1 c2 => deqSeq n c1 c2

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
        fun rd  head => 
        match findElem? (rd.restrictionClauses.restClauses) (delete focus focusLt head) with
        | some ⟨p, pLt, peqn⟩ =>
            ExistingClauses.prependResData branch focus focusLt clauses rd head p pLt peqn
        | none => 
          if c : head focus focusLt = some branch then
            PosResClause.prependResData branch focus focusLt clauses head c rd
          else
            PrependClause.prependResData branch focus focusLt clauses head c rd
         
def restrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1):
    (clauses: FinSeq dom (Clause (n + 1))) →   
        RestrictionData branch focus focusLt clauses := 
      match dom with 
      | 0 => fun clauses =>  
        let eqn : clauses = FinSeq.empty := funext (fun j => funext (fun w => nomatch w))
        match clauses, eqn with
        | .(FinSeq.empty), rfl =>
          let rc : RestrictionClauses branch focus focusLt FinSeq.empty := 
              ⟨0, FinSeq.empty, 
                fun k w => nomatch w, 
                fun k w => nomatch w, fun k w => nomatch w, fun k w => nomatch w⟩
          ⟨rc,
          ⟨fun k w => nomatch w⟩,
          ⟨fun k w => nomatch w⟩,
          ⟨fun k w => nomatch w⟩, 
          ⟨fun k w => nomatch w⟩⟩
      | l + 1 => fun clauses => 
        let res := prependResData branch focus focusLt (tail clauses) 
          (restrictionData branch focus focusLt (tail clauses))
          (head clauses)
        let lem := headTail clauses
        by
          rw (Eq.symm lem)
          exact res

def containmentLift{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(cntn : Containment clauses):
          SatSolution (cntn.imageSeq) → SatSolution clauses := 
          fun sol =>
          match sol with
          | SatSolution.sat val pf => 
              SatSolution.sat val (
                fun k kw => 
                        let ⟨ind, bd, w⟩ := cntn.forward k kw
                        let ev := pf ind bd
                        let lem := containsSat (clauses k kw) (cntn.imageSeq ind bd) w val
                        lem ev)
              
          | SatSolution.unsat tree chk chkTop => 
                let rpf := 
                  transportResPf cntn.imageSeq clauses cntn.reverse (contrad (n + 1))
                    tree chk chkTop
                SatSolution.unsat rpf.tree rpf.check rpf.checkTop

def lengthOneEqual{cl1 cl2 : Clause 1}(eql : cl1 0 (zeroLtSucc 0) = cl2 0 (zeroLtSucc 0)) : 
                          cl1 = cl2 :=
                            funext (fun j =>
                                    match j with
                                    | 0 => funext (fun jw => eql)
                                    | i + 1 => funext (fun jw => nomatch jw)
                                    )

def lengthOneUnit{cl: Clause 1}{b : Bool}(eql : cl 0 (zeroLtSucc 0) = some b):
                                cl = unitClause 0 b 0 (zeroLtSucc 0) := 
                                let lem1 : unitClause 0 b 0 (zeroLtSucc 0) 0 (zeroLtSucc 0) = some b :=
                                          by
                                            apply unitDiag
                                let lem2 : cl 0 (zeroLtSucc 0) = 
                                    unitClause 0 b 0 (zeroLtSucc 0) 0 (zeroLtSucc 0) := 
                                          by
                                            rw eql
                                            exact Eq.symm lem1
                                            done  
                                lengthOneEqual lem2

def lengthOneContra{cl: Clause 1}(eql : cl 0 (zeroLtSucc 0) = none):
                              cl = leaner.contrad 1 := lengthOneEqual eql

def contraSol{n dom: Nat}{clauses : FinSeq dom (Clause (n + 1))}{j : Nat}{jw : j < dom}
                (eqn : clauses j jw = leaner.contrad (n + 1)): SatSolution clauses :=
                  SatSolution.unsat (ResolutionTree.assumption j jw) eqn eqn 
                
def emptySol{n: Nat}(clauses : FinSeq 0 (Clause (n + 1))) : SatSolution clauses :=
        SatSolution.sat (fun k kw => true)  (fun k kw => nomatch kw)

def lengthOneSolution{dom : Nat}: (clauses : FinSeq dom (Clause 1)) →  SatSolution clauses :=
    match dom with
    | 0 => fun cls => emptySol cls
    | l + 1 =>
      fun cls =>
      match searchElem cls (contrad 1) with
      | ExistsElem.exsts index bound eqn => contraSol eqn
      | ExistsElem.notExst noContra =>
        let head := cls (0) (zeroLtSucc l) 
        if c : head 0 (zeroLtSucc 0) = none then   
          let eqn := lengthOneContra c     
          contraSol eqn
        else 
          if ct : head 0 (zeroLtSucc 0) = some true then
              match searchElem cls (unitClause 0 false 0 (zeroLtSucc 0)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionProof cls (unitClause 0 true 0 (zeroLtSucc 0)) :=
                    ⟨ResolutionTree.assumption 0 (zeroLtSucc l), lengthOneUnit ct,
                    lengthOneUnit ct⟩
                  let rpf := mergeAlignUnitTrees treePf1 treePf2
                  treeToUnsat rpf
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (fun _ _ => true) 
                    fun k kw =>
                      let lem1 : Not (cls k kw 0 (zeroLtSucc 0) = some false) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not (cls k kw 0 (zeroLtSucc 0) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : cls k kw 0 (zeroLtSucc 0) = some true :=
                        match cls k kw 0 (zeroLtSucc 0), lem1, lem2 with
                        | some true, l1, l2 => rfl
                        | some false, l1, l2 => absurd (l1 rfl) id
                        | none, l1, l2 => absurd (l2 rfl) id 
                      ⟨0, zeroLtSucc _, lem⟩                      
          else 
            if cf : head 0 (zeroLtSucc 0) = some false then
              match searchElem cls (unitClause 0 true 0 (zeroLtSucc 0)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionProof cls (unitClause 0 false 0 (zeroLtSucc 0)) :=
                    ⟨ResolutionTree.assumption 0 (zeroLtSucc l), lengthOneUnit cf,
                    lengthOneUnit cf⟩
                  let rpf := mergeAlignUnitTrees treePf1 treePf2
                  treeToUnsat rpf
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (fun _ _ => false) 
                    fun k kw =>
                      let lem1 : Not (cls k kw 0 (zeroLtSucc 0) = some true) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not (cls k kw 0 (zeroLtSucc 0) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : cls k kw 0 (zeroLtSucc 0) = some false :=
                        match cls k kw 0 (zeroLtSucc 0), lem1, lem2 with
                        | some false, l1, l2 => rfl
                        | some true, l1, l2 => False.elim (l1 rfl) 
                        | none, l1, l2 => False.elim (l2 rfl)  
                      ⟨0, zeroLtSucc _, lem⟩
            else 
                match head 0 (zeroLtSucc 0), c, ct, cf with
                | some true, l1, l2, l3 => False.elim (l2 rfl)
                | some false, l1, l2, l3 => False.elim (l3 rfl)
                | none, l1, l2, l3 => False.elim (l1 rfl)

