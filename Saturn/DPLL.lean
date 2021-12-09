import Saturn.Prover
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Containment
import Saturn.Solverstep
import Saturn.Resolution
import Saturn.PosRestClause
import Saturn.PrependClause
import Saturn.SatSolution
import Saturn.LiftSolution
open Nat
open FinSeq

/-
The DPLL algorithm with proofs. Here we implement:
  - restricting to a branch.
  - the simple cases of having contradictions or no clauses.
  - the base case: length one clauses in our implementation
  - lifting of proofs from branches and combining them if necessary
-/

instance {n: Nat} : DecidableEq (Clause n) := 
  fun c1 c2 =>
  match decEq c1.coords c2.coords with
  | isTrue pf => isTrue (coords_eq_implies_vec_eq pf)
  | isFalse contra => isFalse (
      fun hyp =>
        contra (congrArg Vector.coords hyp)
  )

/-
We map to branches inductively. The main work is done earlier.
-/
def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (rd : ReductionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → 
        ReductionData branch focus focusLt (head +: clauses) := 
        fun rd  head => 
          if c : head.coords focus focusLt = some branch then
            PosResClause.prependResData branch focus focusLt clauses head c rd
          else
            PrependClause.prependResData branch focus focusLt clauses head c rd

def restrictionDataAux{domHead domAccum dom n: Nat}(branch: Bool)
    (focus: Nat)(focusLt : focus < n + 1):
    (clausesHead: Vector (Clause (n + 1)) domHead) → 
    (clausesAccum: Vector (Clause (n + 1)) domAccum) → 
    (s : domHead + domAccum = dom) → 
    (restAcum : ReductionData branch focus focusLt clausesAccum) → 
    (clauses: Vector (Clause (n + 1)) dom) →
    (clsEq : concatSeqAux s clausesHead.coords clausesAccum.coords = clauses.coords) →    
        ReductionData branch focus focusLt clauses := 
    match domHead with
    | zero =>  
      by
        intro clausesHead clausesAccum s restAccum clauses clsEq
        have ss : dom = domAccum := by 
          rw [← s]
          apply Nat.zero_add
          done
        have sf : FinSeq dom (Clause (n + 1))  = FinSeq domAccum (Clause (n + 1)):= by
          rw [ss]
        have clSeq : clauses = clauses.coords.vec := by 
          apply coords_eq_implies_vec_eq
          rw [seq_to_vec_coords]
        have resolve : concatSeqAux s clausesHead.coords clausesAccum.coords = 
            Eq.mpr sf clausesAccum.coords := by rfl        
        rw [clSeq]
        rw [← clsEq]
        rw [resolve] 
        match dom , domAccum, ss, sf, clausesAccum, restAccum with
        | d, .(d), rfl, rfl, cls,  ra => 
          have sm : FinSeq.vec (cls.coords) = cls := by 
            apply coords_eq_implies_vec_eq
            rw [seq_to_vec_coords]
          rw [← sm] at ra
          exact ra
    | k + 1 => fun clausesHead clausesAccum s restAccum clauses clsEq => 
      let ss : k + (domAccum + 1)  = dom := 
        by
          rw [← s]
          rw [(Nat.add_comm domAccum 1)]
          rw [(Nat.add_assoc k 1 domAccum)]
          done
      let resolve : concatSeqAux s clausesHead.coords clausesAccum.coords = 
        concatSeqAux ss (clausesHead.coords.init) ((clausesHead.coords.last) +| clausesAccum.coords) := rfl
      let recRestAccum := 
        prependResData branch focus focusLt clausesAccum restAccum (last clausesHead.coords)
      restrictionDataAux branch focus focusLt (FinSeq.vec (init clausesHead.coords)) 
          ((last clausesHead.coords) +: clausesAccum) ss recRestAccum clauses 
          (by 
            have sm : (FinSeq.vec (init clausesHead.coords)).coords =
                init (clausesHead.coords) := by rw [seq_to_vec_coords]
            rw [sm,
               (cons_commutes (last (clausesHead.coords)) clausesAccum),
               ← resolve,
               clsEq]
            done)
    

def restrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1):
    (clauses: Vector (Clause (n + 1)) dom) →   
        ReductionData branch focus focusLt clauses := 
        fun clauses =>
          let rc : ReductionClauses branch focus focusLt Vector.nil := 
              ⟨0, Vector.nil, Vector.nil,
                fun k w => nomatch w, 
                Vector.nil, fun k w => nomatch w⟩
          let rd : ReductionData branch focus focusLt Vector.nil := ⟨rc,
            ⟨fun k w => nomatch w⟩,
            ⟨fun k w => nomatch w⟩,
            ⟨fun k w => nomatch w⟩, 
            ⟨(by
                intro k kw
                have eq0 : rc.codom = 0 := by rfl
                rw [eq0] at kw
                have contra := not_lt_zero _ kw
                exact False.elim contra
            )⟩⟩
          restrictionDataAux branch focus focusLt clauses Vector.nil 
              (Nat.add_zero dom) rd clauses (concat_empty_seq_id clauses.coords)

/-
The simple cases: having a contradiction or having no clauses.
-/

def contraSol{n dom: Nat}{clauses : Vector (Clause (n + 1)) dom}{j : Nat}{jw : j < dom}
                (eqn : clauses.coords j jw = contradiction (n + 1)): SatSolution clauses :=
                  SatSolution.unsat (ResolutionTree.assumption j jw _ eqn) 
                
def emptySol{n: Nat}(clauses : Vector (Clause (n + 1)) zero) : SatSolution clauses :=
        SatSolution.sat (FinSeq.vec (fun k kw => true))  (fun k kw => nomatch kw)

/-
Solution for length one clauses
-/
def lengthOneEqual{cl1 cl2 : Clause 1}(eql : cl1.coords zero (zero_lt_succ zero) = cl2.coords zero (zero_lt_succ zero)) : 
                          cl1 = cl2 :=
                            coords_eq_implies_vec_eq 
                            (funext (fun j =>
                                    match j with
                                    | zero => funext (fun jw => eql)
                                    | i + 1 => funext (fun jw => nomatch jw)
                                    ))

def lengthOneUnit{cl: Clause 1}{b : Bool}(eql : cl.coords zero (zero_lt_succ zero) = some b):
                                cl = unitClause zero b zero (zero_lt_succ zero) := 
                                let lem1 :  
                                  (unitClause zero b zero (zero_lt_succ zero)).coords zero (zero_lt_succ zero) = 
                                    some b :=
                                          by
                                            apply unitDiag
                                let lem2 : cl.coords zero (zero_lt_succ zero) = 
                                    (unitClause zero b zero (zero_lt_succ zero)).coords 
                                      zero (zero_lt_succ zero) 
                                      := 
                                          by
                                            rw [eql]
                                            exact Eq.symm lem1
                                            done  
                                lengthOneEqual lem2

def lengthOneContra{cl: Clause 1}(eql : cl.coords zero (zero_lt_succ zero) = none):
                              cl = contradiction 1 := lengthOneEqual eql

def lengthOneSolution{dom : Nat}: (clauses : Vector (Clause 1) dom) →  SatSolution clauses :=
    match dom with
    | zero => fun cls => emptySol cls
    | l + 1 =>
      fun cls =>
      match searchElem cls.coords (contradiction 1) with
      | ExistsElem.exsts index bound eqn => contraSol eqn
      | ExistsElem.notExst noContra =>
        let head := cls.coords (zero) (zero_lt_succ l) 
        if c : head.coords zero (zero_lt_succ zero) = none then   
          let eqn := lengthOneContra c     
          contraSol eqn
        else 
          if ct : head.coords zero (zero_lt_succ zero) = some true then
              match searchElem cls.coords (unitClause zero false zero (zero_lt_succ zero)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionTree cls (unitClause zero true zero (zero_lt_succ zero)) :=
                    ResolutionTree.assumption zero (zero_lt_succ l) _ (lengthOneUnit ct)
                  let tree := mergeAlignUnitTrees treePf1 treePf2
                  SatSolution.unsat tree
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (FinSeq.vec (fun _ _ => true)) 
                    fun k kw =>
                      let lem1 : Not ((cls.coords k kw).coords zero (zero_lt_succ zero) = some false) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not ((cls.coords k kw).coords zero (zero_lt_succ zero) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : (cls.coords k kw).coords zero (zero_lt_succ zero) = some true :=
                        match (cls.coords k kw).coords zero (zero_lt_succ zero), lem1, lem2 with
                        | some true, l1, l2 => rfl
                        | some false, l1, l2 => absurd (l1 rfl) id
                        | none, l1, l2 => absurd (l2 rfl) id 
                      ⟨zero, zero_lt_succ _, lem⟩                      
          else 
            if cf : head.coords zero (zero_lt_succ zero) = some false then
              match searchElem cls.coords (unitClause zero true zero (zero_lt_succ zero)) with
              | ExistsElem.exsts index bound eqn => 
                  let treePf2 := unitProof eqn 
                  let treePf1 : 
                    ResolutionTree cls (unitClause zero false zero (zero_lt_succ zero)) :=
                    ResolutionTree.assumption zero (zero_lt_succ l) _ (lengthOneUnit cf)
                  let tree := mergeAlignUnitTrees treePf1 treePf2
                  SatSolution.unsat tree
              | ExistsElem.notExst noNeg => 
                 SatSolution.sat (FinSeq.vec (fun _ _ => false)) 
                    fun k kw =>
                      let lem1 : Not ((cls.coords k kw).coords zero (zero_lt_succ zero) = some true) :=
                        fun hyp => noNeg k kw (lengthOneUnit hyp)
                      let lem2 : Not ((cls.coords k kw).coords zero (zero_lt_succ zero) = none) :=
                        fun hyp => noContra k kw (lengthOneContra hyp)
                      let lem : (cls.coords k kw).coords zero (zero_lt_succ zero) = some false :=
                        match (cls.coords k kw).coords zero (zero_lt_succ zero), lem1, lem2 with
                        | some false, l1, l2 => rfl
                        | some true, l1, l2 => False.elim (l1 rfl) 
                        | none, l1, l2 => False.elim (l2 rfl)  
                      ⟨zero, zero_lt_succ _, lem⟩
            else 
                match head.coords zero (zero_lt_succ zero), c, ct, cf with
                | some true, l1, l2, l3 => False.elim (l2 rfl)
                | some false, l1, l2, l3 => False.elim (l3 rfl)
                | none, l1, l2, l3 => False.elim (l1 rfl)

-- a helper
theorem notpure_cases(b: Bool): (x : Option Bool) → x = none ∨  x = some b  → 
        Not (x = some (not b)) :=
  fun x eqn  =>
     match b, eqn  with
     | true, Or.inr pf => 
            fun hyp =>
              let lem1 : some true = some false := by
                rw [← pf]
                rw [hyp]
                rfl
                done
              let lem2 : true = false := by 
                  injection lem1
                  assumption
              Bool.noConfusion lem2
     | false, Or.inr pf => 
              fun hyp =>
              let lem1 : some true = some false := by
                rw [← pf]
                rw [hyp]
                rfl
                done
              let lem2 : true = false := by 
                  injection lem1
                  assumption
              Bool.noConfusion lem2
     | _ , Or.inl pf => fun hyp =>
        let w := Eq.trans (Eq.symm pf) hyp
        Option.noConfusion w

/-
Lifting under containment and from branches and putting together lifts
-/
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
                        let lem := containsSat (clauses.coords k kw) (cntn.imageSeq.coords ind bd) w val
                        lem ev)
              
          | SatSolution.unsat tree => 
                let tree := 
                  transportResTree cntn.imageSeq clauses cntn.reverse (contradiction (n + 1))
                    tree 
                SatSolution.unsat tree 


def solveSAT{n dom : Nat}: (clauses : Vector (Clause (n + 1)) dom) →  SatSolution clauses :=
      match n with
      | zero => fun clauses => lengthOneSolution clauses
      | m + 1 =>
        fun clauses =>
        let posCount  := clauses.map (parityCount true)
        let negCount  := clauses.map (parityCount false)
        match findElem? clauses.coords (contradiction (m + 2)) with
        | some z => contraSol z.equation 
        | none =>     
          let cntn := simplifiedContainment clauses posCount negCount
          let cls := cntn.imageSeq
          let posCount  := cls.map (parityCount true)
          let negCount  := cls.map (parityCount false)
          let solution : SatSolution cls :=
              match someUnitClause cls.coords posCount negCount with
              | some ⟨i, iw, index, bd, par, eql⟩ => 
                  let rd := restrictionData par index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solveSAT subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution par index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert par _ index bd valuation.coords
                    SatSolution.sat valuationN.vec pb
                  | SatSolution.unsat tree  => 
                      let liftedProof :=
                        pullBackResTree  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
                      match liftedProof with
                      | LiftedResTree.contra pf => 
                          SatSolution.unsat pf
                      | LiftedResTree.unit tree => 
                          let tree1 := unitProof eql
                          let merged := mergeAlignUnitTrees tree1 tree
                          SatSolution.unsat merged 
              | none => 
                match hasPure cls with 
                | some ⟨index, bd, par, evid⟩=> 
                  let rd := restrictionData par index bd cls
                  let subCls := rd.restrictionClauses.restClauses
                  let subSol := solveSAT subCls
                  match subSol with
                  | SatSolution.sat valuation pf => 
                    let pb :=  pullBackSolution par index bd cls 
                        rd.restrictionClauses rd.droppedProof rd.forwardRelation valuation pf
                    let valuationN := insert par _ index bd valuation.coords
                    SatSolution.sat valuationN.vec pb
                  | SatSolution.unsat tree => 
                      let liftedProof :=
                        pullBackResTree  par index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
                      match liftedProof with
                      | LiftedResTree.contra pf => 
                          SatSolution.unsat pf
                      | LiftedResTree.unit tree => 
                          let base : (j : Nat) → (lt : j < cntn.codom) → 
                              Not ((cls.coords j lt).coords index bd = some (not par)) := 
                                fun j jw => 
                                  notpure_cases par ((cls.coords j jw).coords index bd) (evid j jw)
                          let pure :=
                            trees_preserve_notsomebranch (not par) index bd base
                                   (unitClause (m + 1) (!par) index bd)
                                   tree
                          let impure := unitDiag (m + 1) (not par) index bd 
                          absurd impure pure
                | none =>  
                  let index := zero
                  let bd := zero_lt_succ (m + 1)
                  let rd : ReductionData false zero bd cls := 
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
                      let liftedProof : LiftedResTree false zero bd cls :=
                        pullBackResTree  false index bd cls 
                            rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                            tree
                      match liftedProof with
                      | LiftedResTree.contra pf => 
                          SatSolution.unsat pf
                      | LiftedResTree.unit tree1 => 
                          let rd : ReductionData true zero bd cls 
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
                                pullBackResTree  true index bd cls 
                                    rd.restrictionClauses rd.nonPosReverse rd.reverseRelation 
                                    tree
                              match liftedProof with
                              | LiftedResTree.contra pf => 
                                  SatSolution.unsat pf
                              | LiftedResTree.unit tree2 => 
                                  let merged := mergeUnitTrees index bd tree2 tree1
                                  SatSolution.unsat merged
        containmentLift clauses cntn solution

/-
Decidability and convenience functions.
-/
instance {dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                 : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def proveOrDisprove{n dom : Nat}(clauses : Vector (Clause (n + 1)) dom) :=
            getProof (solveSAT clauses)

instance {n dom : Nat}{clauses : Vector (Clause (n + 1)) dom} :
    Decidable (isSat clauses) := 
    match solveSAT clauses with
      | SatSolution.sat valuation evidence =>
          isTrue ⟨valuation, evidence⟩
      | SatSolution.unsat tree => isFalse $ fun hyp => 
            not_sat_and_unsat clauses hyp $ tree_unsat clauses tree

instance {n dom : Nat}{clauses : Vector (Clause (n + 1)) dom} :
    Decidable (isUnSat clauses) := 
    match solveSAT clauses with
      | SatSolution.sat valuation evidence => isFalse $ fun hyp => 
        not_sat_and_unsat clauses ⟨valuation, evidence⟩ hyp    
      | SatSolution.unsat tree =>
        isTrue $ tree_unsat clauses tree
