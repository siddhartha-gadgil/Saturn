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

instance {n: Nat} : DecidableEq (Clause n) := 
  fun c1 c2 =>
  match decEq c1.at c2.at with
  | isTrue pf => isTrue (equalCoords pf)
  | isFalse contra => isFalse (
      fun hyp =>
        contra (congrArg Vector.at hyp)
  )

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
        fun rd  head => 
        -- match findElem? (rd.restrictionClauses.restClauses) (delete focus focusLt head) with
        -- | some ⟨p, pLt, peqn⟩ =>
        --     ExistingClauses.prependResData branch focus focusLt clauses rd head p pLt peqn
        -- | none => 
          if c : head.at focus focusLt = some branch then
            PosResClause.prependResData branch focus focusLt clauses head c rd
          else
            PrependClause.prependResData branch focus focusLt clauses head c rd

def restrictionDataAux{domHead domAccum dom n: Nat}(branch: Bool)
    (focus: Nat)(focusLt : focus < n + 1):
    (clausesHead: Vector (Clause (n + 1)) domHead) → 
    (clausesAccum: Vector (Clause (n + 1)) domAccum) → 
    (s : domHead + domAccum = dom) → 
    (restAcum : RestrictionData branch focus focusLt clausesAccum) → 
    (clauses: Vector (Clause (n + 1)) dom) →
    (clsEq : concatSeqAux s clausesHead.at clausesAccum.at = clauses.at) →    
        RestrictionData branch focus focusLt clauses := 
         match domHead with
    | zero => fun clausesHead clausesAccum s restAccum clauses clsEq =>
      by
        have ss : dom = domAccum by 
          rw ← s
          apply Nat.zero_add
          done
        have sf : FinSeq dom (Clause (n + 1))  = FinSeq domAccum (Clause (n + 1)) by
          rw ss
        have sff : Vector (Clause (n + 1)) dom  = Vector (Clause (n + 1)) domAccum by
          rw ss
        have resolve : concatSeqAux s clausesHead.at clausesAccum.at = 
            Eq.mpr sf clausesAccum.at by rfl
        have clSeq : clauses = FinSeq.vec (clauses.at) by 
          apply equalCoords
          rw seqAt
          done
        rw clSeq
        rw ← clsEq
        rw resolve 
        let clausesTrans: RestrictionData branch focus focusLt 
              (FinSeq.vec (Eq.mpr sf clausesAccum.at))  :=
          match dom , domAccum, ss, sf, clausesAccum, restAccum with
          | d, .(d), rfl, rfl, cls,  ra => by
            have sm : FinSeq.vec (Eq.mpr rfl (Vector.at cls)) = cls by 
              apply equalCoords
              rw seqAt
              rfl
              done
            rw sm
            exact ra
            done
        exact clausesTrans
        done
    | k + 1 => fun clausesHead clausesAccum s restAccum clauses clsEq => 
      let ss : k + (domAccum + 1)  = dom := 
        by
          rw ← s
          rw (Nat.add_comm domAccum 1)
          rw (Nat.add_assoc k 1 domAccum)
          done
      let resolve : concatSeqAux s clausesHead.at clausesAccum.at = 
        concatSeqAux ss (init clausesHead.at) ((last clausesHead.at) +| clausesAccum.at) := rfl
      let recRestAccum := 
        prependResData branch focus focusLt clausesAccum restAccum (last clausesHead.at)
      restrictionDataAux branch focus focusLt (FinSeq.vec (init clausesHead.at)) 
          ((last clausesHead.at) +: clausesAccum) ss recRestAccum clauses 
          (by 
            have sm : Vector.at (FinSeq.vec (init (Vector.at clausesHead))) =
                init (Vector.at clausesHead) by rw seqAt
            rw sm
            rw (consCommutes (last (Vector.at clausesHead)) clausesAccum)
            rw ← resolve
            rw clsEq
            done)

def restrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1):
    (clauses: Vector (Clause (n + 1)) dom) →   
        RestrictionData branch focus focusLt clauses := 
        fun clauses =>
          let rc : RestrictionClauses branch focus focusLt Vector.Nil := 
              ⟨zero, Vector.Nil, Vector.Nil,
                fun k w => nomatch w, 
                Vector.Nil, fun k w => nomatch w⟩
          let rd : RestrictionData branch focus focusLt Vector.Nil := ⟨rc,
            ⟨fun k w => nomatch w⟩,
            ⟨fun k w => nomatch w⟩,
            ⟨fun k w => nomatch w⟩, 
            ⟨fun k w => nomatch w⟩⟩
          restrictionDataAux branch focus focusLt clauses Vector.Nil 
              (Nat.add_zero dom) rd clauses (concatEmptySeq clauses.at)

def containmentLift{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom)
    (cntn : Containment clauses):
          SatSolution (cntn.imageSeq) → SatSolution clauses := 
          fun sol =>
          match sol with
          | SatSolution.sat val pf => 
              SatSolution.sat val (
                fun k kw => 
                        let ⟨ind, bd, w⟩ := cntn.forward k kw
                        let ev := pf ind bd
                        let lem := containsSat (clauses.at k kw) (cntn.imageSeq.at ind bd) w val
                        lem ev)
              
          | SatSolution.unsat tree => 
                let rpf := 
                  transportResPf cntn.imageSeq clauses cntn.reverse (contradiction (n + 1))
                    tree 
                SatSolution.unsat rpf 

def lengthOneEqual{cl1 cl2 : Clause 1}(eql : cl1.at zero (zeroLtSucc zero) = cl2.at zero (zeroLtSucc zero)) : 
                          cl1 = cl2 :=
                            equalCoords 
                            (funext (fun j =>
                                    match j with
                                    | zero => funext (fun jw => eql)
                                    | i + 1 => funext (fun jw => nomatch jw)
                                    ))

def lengthOneUnit{cl: Clause 1}{b : Bool}(eql : cl.at zero (zeroLtSucc zero) = some b):
                                cl = unitClause zero b zero (zeroLtSucc zero) := 
                                let lem1 : Vector.at (unitClause zero b zero (zeroLtSucc zero)) zero (zeroLtSucc zero) = 
                                  some b :=
                                          by
                                            apply unitDiag
                                let lem2 : cl.at zero (zeroLtSucc zero) = 
                                    Vector.at (unitClause zero b zero (zeroLtSucc zero)) zero (zeroLtSucc zero) 
                                      := 
                                          by
                                            rw eql
                                            exact Eq.symm lem1
                                            done  
                                lengthOneEqual lem2

def lengthOneContra{cl: Clause 1}(eql : cl.at zero (zeroLtSucc zero) = none):
                              cl = contradiction 1 := lengthOneEqual eql

def contraSol{n dom: Nat}{clauses : Vector (Clause (n + 1)) dom}{j : Nat}{jw : j < dom}
                (eqn : clauses.at j jw = contradiction (n + 1)): SatSolution clauses :=
                  SatSolution.unsat (ResolutionTree.assumption j jw _ eqn) 
                
def emptySol{n: Nat}(clauses : Vector (Clause (n + 1)) zero) : SatSolution clauses :=
        SatSolution.sat (FinSeq.vec (fun k kw => true))  (fun k kw => nomatch kw)

def lengthOneSolution{dom : Nat}: (clauses : Vector (Clause 1) dom) →  SatSolution clauses :=
    match dom with
    | zero => fun cls => emptySol cls
    | l + 1 =>
      fun cls =>
      match searchElem cls.at (contradiction 1) with
      | ExistsElem.exsts index bound eqn => contraSol eqn
      | ExistsElem.notExst noContra =>
        let head := cls.at (zero) (zeroLtSucc l) 
        if c : head.at zero (zeroLtSucc zero) = none then   
          let eqn := lengthOneContra c     
          contraSol eqn
        else 
          if ct : head.at zero (zeroLtSucc zero) = some true then
              match searchElem cls.at (unitClause zero false zero (zeroLtSucc zero)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionTree cls (unitClause zero true zero (zeroLtSucc zero)) :=
                    ResolutionTree.assumption zero (zeroLtSucc l) _ (lengthOneUnit ct)
                  let rpf := mergeAlignUnitTrees treePf1 treePf2
                  treeToUnsat rpf
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (FinSeq.vec (fun _ _ => true)) 
                    fun k kw =>
                      let lem1 : Not (Vector.at (cls.at k kw) zero (zeroLtSucc zero) = some false) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not (Vector.at (cls.at k kw) zero (zeroLtSucc zero) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : Vector.at (cls.at k kw) zero (zeroLtSucc zero) = some true :=
                        match Vector.at (cls.at k kw) zero (zeroLtSucc zero), lem1, lem2 with
                        | some true, l1, l2 => rfl
                        | some false, l1, l2 => absurd (l1 rfl) id
                        | none, l1, l2 => absurd (l2 rfl) id 
                      ⟨zero, zeroLtSucc _, lem⟩                      
          else 
            if cf : head.at zero (zeroLtSucc zero) = some false then
              match searchElem cls.at (unitClause zero true zero (zeroLtSucc zero)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionTree cls (unitClause zero false zero (zeroLtSucc zero)) :=
                    ResolutionTree.assumption zero (zeroLtSucc l) _ (lengthOneUnit cf)
                  let rpf := mergeAlignUnitTrees treePf1 treePf2
                  treeToUnsat rpf
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (FinSeq.vec (fun _ _ => false)) 
                    fun k kw =>
                      let lem1 : Not (Vector.at (cls.at k kw) zero (zeroLtSucc zero) = some true) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not (Vector.at (cls.at k kw) zero (zeroLtSucc zero) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : Vector.at (cls.at k kw) zero (zeroLtSucc zero) = some false :=
                        match Vector.at (cls.at k kw) zero (zeroLtSucc zero), lem1, lem2 with
                        | some false, l1, l2 => rfl
                        | some true, l1, l2 => False.elim (l1 rfl) 
                        | none, l1, l2 => False.elim (l2 rfl)  
                      ⟨zero, zeroLtSucc _, lem⟩
            else 
                match head.at zero (zeroLtSucc zero), c, ct, cf with
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

def solve{n dom : Nat}: (clauses : Vector (Clause (n + 1)) dom) →  SatSolution clauses :=
      match n with
      | zero => fun clauses => lengthOneSolution clauses
      | m + 1 =>
        fun clauses =>
        match findElem? clauses.at (contradiction (m + 2)) with
        | some z => contraSol z.equation 
        | none =>     
          let cntn := simplifiedContainment clauses
          let cls := cntn.imageSeq
          let solution : SatSolution cls :=
              match someUnitClause cls.at with
              | some ⟨i, iw, index, bd, par, eql⟩ => 
                  let rd := restrictionData par index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solve subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution par index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert par _ index bd valuation.at
                    SatSolution.sat valuationN.vec pb
                  | SatSolution.unsat tree  => 
                      let liftedProof :=
                        pullBackResPf  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
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
                    let valuationN := insert par _ index bd valuation.at
                    SatSolution.sat valuationN.vec pb
                  | SatSolution.unsat tree => 
                      let liftedProof :=
                        pullBackResPf  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
                      match liftedProof with
                      | LiftedResPf.contra pf => 
                          treeToUnsat pf
                      | LiftedResPf.unit rpf => 
                          let base : (j : Nat) → (lt : j < cntn.codom) → 
                              Not (Vector.at (cls.at j lt) index bd = some (not par)) := 
                                fun j jw => 
                                  pureNot par (Vector.at (cls.at j jw) index bd) (evid j jw)
                          let pure :=
                            proofsPreverveNonPos (not par) index bd base
                                   (unitClause (m + 1) (!par) index bd)
                                   rpf
                          let impure := unitDiag (m + 1) (not par) index bd 
                          absurd impure pure
                | none =>  
                  let index := zero
                  let bd := zeroLtSucc (m + 1)
                  let rd := restrictionData false index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solve subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution false index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert false _ index bd valuation.at
                    SatSolution.sat valuationN.vec pb
                  | SatSolution.unsat tree => 
                      let liftedProof :=
                        pullBackResPf  false index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
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
                            let valuationN := insert true _ index bd valuation.at
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
        containmentLift clauses cntn solution

instance {dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                 : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def proveOrDisprove{n dom : Nat}(clauses : Vector (Clause (n + 1)) dom) :=
            getProof (solve clauses)

#check proveOrDisprove


def sat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), (Vector.at (clauses.at p pw) k kw) = some (valuation.at k kw)

def unsat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), (Vector.at (clauses.at p pw) k kw) = some (valuation.at k kw))

