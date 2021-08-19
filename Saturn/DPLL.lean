import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
import Saturn.Resolution
import Saturn.PosRestClause
import Saturn.PrependClause
import Saturn.ExistingClause
-- set_option trace.Elab.definition true
-- set_option pp.all true

open Nat

instance {n: Nat} : DecidableEq (Clause n) := fun c1 c2 => deqSeq n c1 c2

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
        fun rd  head => 
        -- match findElem? (rd.restrictionClauses.restClauses) (delete focus focusLt head) with
        -- | some ⟨p, pLt, peqn⟩ =>
        --     ExistingClauses.prependResData branch focus focusLt clauses rd head p pLt peqn
        -- | none => 
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
                  transportResPf cntn.imageSeq clauses cntn.reverse (contradiction (n + 1))
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
                              cl = contradiction 1 := lengthOneEqual eql

def contraSol{n dom: Nat}{clauses : FinSeq dom (Clause (n + 1))}{j : Nat}{jw : j < dom}
                (eqn : clauses j jw = contradiction (n + 1)): SatSolution clauses :=
                  SatSolution.unsat (ResolutionTree.assumption j jw) eqn eqn 
                
def emptySol{n: Nat}(clauses : FinSeq 0 (Clause (n + 1))) : SatSolution clauses :=
        SatSolution.sat (fun k kw => true)  (fun k kw => nomatch kw)

def lengthOneSolution{dom : Nat}: (clauses : FinSeq dom (Clause 1)) →  SatSolution clauses :=
    match dom with
    | 0 => fun cls => emptySol cls
    | l + 1 =>
      fun cls =>
      match searchElem cls (contradiction 1) with
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

def pureNot(b: Bool): (x : Option Bool) → x = none ∨  x = some b  → Not (x = some (not b)) :=
  fun x eqn  =>
     match b, eqn  with
     | true, Or.inr pf => 
            fun hyp =>
              let lem1 : some true = some false := by
                rw (Eq.symm pf)
                rw hyp
                rfl
                done
              let lem2 : true = false := by 
                  injection lem1
                  assumption
              Bool.noConfusion lem2
     | false, Or.inr pf => 
              fun hyp =>
              let lem1 : some true = some false := by
                rw (Eq.symm pf)
                rw hyp
                rfl
                done
              let lem2 : true = false := by 
                  injection lem1
                  assumption
              Bool.noConfusion lem2
     | _ , Or.inl pf => fun hyp =>
        let w := Eq.trans (Eq.symm pf) hyp
        Option.noConfusion w

def solve{n dom : Nat}: (clauses : FinSeq dom (Clause (n + 1))) →  SatSolution clauses :=
      match n with
      | 0 => fun clauses => lengthOneSolution clauses
      | m + 1 =>
        fun clauses =>
        match findElem? clauses (contradiction (m + 2)) with
        | some z => contraSol z.equation 
        | none =>     
          -- let cntn := simplifiedContainment clauses
          let cls := clauses -- cntn.imageSeq
          let solution : SatSolution cls :=
              match someUnitClause cls with
              | some ⟨i, iw, index, bd, par, eql⟩ => 
                  let rd := restrictionData par index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solve subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution par index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert par _ index bd valuation
                    SatSolution.sat valuationN pb
                  | SatSolution.unsat tree treeCheck treeTop => 
                      let liftedProof :=
                        pullBackResPf  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            ⟨tree, treeCheck, treeTop⟩
                      match liftedProof with
                      | LiftedResPf.contra pf => 
                          treeToUnsat pf
                      | LiftedResPf.unit rpf => 
                          let tree1 := unitProof eql
                          let merged := mergeAlignUnitTrees tree1 rpf
                          treeToUnsat merged 
              | none => 
                match hasPure cls with 
                | some ⟨index, bd, par, evid⟩=> 
                  let rd := restrictionData par index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solve subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution par index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert par _ index bd valuation
                    SatSolution.sat valuationN pb
                  | SatSolution.unsat tree treeCheck treeTop => 
                      let liftedProof :=
                        pullBackResPf  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            ⟨tree, treeCheck, treeTop⟩
                      match liftedProof with
                      | LiftedResPf.contra pf => 
                          treeToUnsat pf
                      | LiftedResPf.unit rpf => 
                          let base : (j : Nat) → (lt : j < dom) → 
                              Not (cls j lt index bd = some (not par)) := 
                                fun j jw => pureNot par (cls j jw index bd) (evid j jw)
                          let pure :=
                            proofsPreverveNonPos (not par) index bd base
                                   (unitClause (m + 1) (!par) index bd)
                                   rpf.tree rpf.check rpf.checkTop
                          let impure := unitDiag (m + 1) (not par) index bd 
                          absurd impure pure
                | none =>  
                  let index := 0
                  let bd := zeroLtSucc (m + 1)
                  let rd := restrictionData false index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solve subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution false index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert false _ index bd valuation
                    SatSolution.sat valuationN pb
                  | SatSolution.unsat tree treeCheck treeTop => 
                      let liftedProof :=
                        pullBackResPf  false index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            ⟨tree, treeCheck, treeTop⟩
                      match liftedProof with
                      | LiftedResPf.contra pf => 
                          treeToUnsat pf
                      | LiftedResPf.unit rpf1 => 
                          let rd := restrictionData true index bd cls
                          let subCls := rd.restrictionClauses.restClauses
                          let subSol := solve subCls
                          match subSol with
                          | SatSolution.sat valuation pf => 
                            let pb :=  pullBackSolution true index bd cls 
                                rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                            let valuationN := insert true _ index bd valuation
                            SatSolution.sat valuationN pb
                          | SatSolution.unsat tree treeCheck treeTop => 
                              let liftedProof :=
                                pullBackResPf  true index bd cls 
                                    rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                                    ⟨tree, treeCheck, treeTop⟩
                              match liftedProof with
                              | LiftedResPf.contra pf => 
                                  treeToUnsat pf
                              | LiftedResPf.unit rpf2 => 
                                  let merged := mergeUnitTrees index bd rpf2 rpf1
                                  treeToUnsat merged
        -- containmentLift clauses cntn solution
        solution

instance {dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                 : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def proveOrDisprove{n dom : Nat}(clauses : FinSeq dom (Clause (n + 1))) :=
            getProof (solve clauses)

#check proveOrDisprove


def sat{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1))) :=
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuation k kw)

def unsat{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1))) :=
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuation k kw))

