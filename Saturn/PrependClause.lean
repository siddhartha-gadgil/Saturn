import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
open Nat
open Vector
open FinSeq

/-
The inductive step for adding a new clause when it is not dropped. The new clauses and maps 
are defined. All the witnesses for the relations between the old and new clauses are also
constructed.
-/
def prependClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) → 
            ReductionClauses branch focus focusLt (head +: clauses) := 
          fun rc head neg =>
            let headImage := (delete focus focusLt head.coords).vec
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := head +: clauses
            let restClausesN := headImage +: rc.restClauses
            let forwardVecN := (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) )
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | zero => fun _ => some zero
              | l + 1 => 
                fun w : l + 1 < domN   =>  (rc.forward l (le_of_succ_le_succ w)).map (. + 1)
            have forwardNEq : forwardVecN.coords = forwardN := by
                  apply funext
                  intro j
                  cases j with
                  | zero => 
                    apply funext
                    intro jw
                    rfl
                  | succ i =>
                    apply funext
                    intro jw
                    have tl :forwardVecN.coords (succ i) jw = 
                        forwardVecN.coords.tail i (Nat.le_of_succ_le_succ jw) := by rfl
                    rw [tl,
                      tail_commutes (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1))),
                      map_coords_commute]
            have forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | zero => fun w => 
                let lem1 : forwardN zero w = some zero := by rfl
                by
                  rw [lem1]
                  apply zero_lt_succ
                  done
              | l + 1 => 
                fun w : l + 1 < domN   => 
                  let lem : forwardN (l + 1) w = 
                    (rc.forward l (le_of_succ_le_succ w)).map (. + 1) := by rfl 
                  let lem2 := boundOptSucc rc.codom 
                            (rc.forward l (le_of_succ_le_succ w))
                            (rc.forwardWit l (le_of_succ_le_succ w))
                  by
                    rw [lem]
                    exact lem2
                    done
            let reverseVecN := zero +: (rc.reverseVec.map (. + 1))
            let reverseN : (k : Nat) →  k < codomN → Nat :=             
              fun k =>
              match k with
              | zero => fun _ => zero
              | l + 1 => fun w => (rc.reverse l (Nat.le_of_succ_le_succ w)) + 1
            have reverseNEq : reverseVecN.coords = reverseN := by
                  apply funext
                  intro j
                  cases j with
                  | zero =>
                    apply funext
                    intro jw
                    rfl
                  | succ i =>
                    apply funext
                    intro jw
                    have tl :reverseVecN.coords (succ i) jw =
                        reverseVecN.coords.tail i (Nat.le_of_succ_le_succ jw) := by rfl
                    rw [tl,
                       tail_commutes zero (rc.reverseVec.map (. + 1)),
                        map_coords_commute]
            have reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
              fun k =>
              match k with
              | zero => fun _ => zero_lt_succ _ 
              | l + 1 => fun w => by 
                  apply succ_le_succ
                  exact rc.reverseWit l (le_of_succ_le_succ w)
                  done
            ReductionClauses.mk codomN restClausesN 
                    forwardVecN 
                    (forwardNEq ▸ forwardWitN) 
                    reverseVecN
                    (reverseNEq ▸ reverseWitN)


theorem none_mapsto_none{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none 
  | none, rfl => by rfl

theorem map_plusone_not_somezero{n: Option Nat} : Not (n.map (. + 1) = some zero) :=
  match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some zero =>
    let lem : j + 1 = zero := by
      injection hyp
      assumption
    Nat.noConfusion lem

theorem map_plusone_pred{n : Option Nat}{m : Nat} : n.map (. + 1) = some (m + 1) → 
  n = some m :=
    match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some (m + 1) => 
      let lem1 : j + 1 = m + 1 := by
        injection hyp
        assumption
      let lem2 : j = m := by
        injection lem1
        assumption 
    congrArg some lem2


namespace PrependClause

theorem forwardResolve{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
        (l: Nat) → (w : l + 1 < dom + 1) → 
          (prependClause  branch focus focusLt clauses rc head neg).forward (l + 1) w = 
            (rc.forward l (le_of_succ_le_succ w)).map (. + 1) := by
                  intro rc head neg l w  
                  let rcN := prependClause  branch focus focusLt clauses rc head neg 
                  have res1 : rcN.forward (l + 1) w = 
                      rcN.forwardVec.coords (l + 1) w := by rfl
                  have res2 : rc.forward l (le_of_succ_le_succ w) =
                      rc.forwardVec.coords l (le_of_succ_le_succ w) := by rfl
                  rw [res1]
                  rw [res2]
                  have res3 :rcN.forwardVec = 
                    (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) ) 
                      := by rfl
                  rw [res3]
                  have res4 :
                      ((some zero) +: 
                        (rc.forwardVec.map (fun nop => nop.map (. + 1)) )).coords 
                          (l + 1) w =
                      (
                        ((some zero) +: 
                        (rc.forwardVec.map (fun nop => nop.map (. + 1)) )).coords.tail 
                      ) l (Nat.le_of_succ_le_succ w) := by rfl
                  rw [res4]
                  rw [(tail_commutes 
                      (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) ))]
                  rw [map_coords_commute]


def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
          DroppedProof rc → 
          DroppedProof (prependClause  branch focus focusLt clauses rc head neg) := 
          fun rc head neg drc =>
            let rcN := prependClause  branch focus focusLt clauses rc head neg 
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := head +: clauses
            let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  (clausesN.coords k w).coords focus focusLt = some branch :=
                by
                intro k
                  match k with
                  | zero => 
                    intro w wf  
                    exact Option.noConfusion wf
                  | l + 1 => 
                    intro w nw 
                    have clres: clausesN.coords (l + 1) w = 
                        clauses.coords l (le_of_succ_le_succ w) := by rfl
                    rw [clres]
                    have prev := drc.dropped l (le_of_succ_le_succ w)
                    apply prev
                    rw [forwardResolve] at nw
                    apply none_mapsto_none (. + 1)
                    exact nw
            ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
          ForwardRelation rc → 
          ForwardRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg frc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg 
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt ((clausesN.coords k w).coords) = 
                (rcN.restClauses.coords j jw).coords := by
                intro k 
                match k with
                | zero => 
                    intro w j sw 
                    let lem1 : rcN.forward zero w = some zero := by rfl 
                    let lem2 : some j = some zero := Eq.trans (Eq.symm sw) lem1
                    let lem3 : j = zero := by 
                      injection lem2
                      assumption
                    rw [lem3]
                    intro jw
                    have hl1 : clausesN.coords zero w = head := by rfl
                    rw [hl1]
                    have hl2 : rcN.restClauses.coords zero jw = 
                         (delete focus focusLt (head.coords)).vec := by rfl
                    rw [hl2]
                    apply Eq.symm
                    apply seq_to_vec_coords
                | l + 1 => 
                    intro w
                    match c:rcN.forward (l + 1) w with                    
                    | none =>
                      intro j sw jw 
                      exact Option.noConfusion sw
                    | some zero => 
                      rw [forwardResolve] at c
                      let contra:= map_plusone_not_somezero c
                      exact False.elim contra
                    | some (j + 1) =>   
                      intro j1 eq1
                      have eq2 : j + 1 = j1 := by 
                        injection eq1
                        assumption 
                      rw [← eq2]
                      intro jw
                      have clres: clausesN.coords (l + 1) w = 
                        clauses.coords l (le_of_succ_le_succ w) := by rfl
                      rw [clres]
                      rw [forwardResolve] at c
                      let cc:= map_plusone_pred c
                      have prev := 
                          frc.forwardRelation l (le_of_succ_le_succ w) j cc 
                            (le_of_succ_le_succ jw)
                      rw [prev]
                      rfl
          ⟨forwardRelationN⟩


theorem reverseResolve{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
        (l: Nat) → (w : l + 1 < rc.codom + 1) → 
          (prependClause  branch focus focusLt clauses rc head neg).reverse (l + 1) w = 
            (rc.reverse l (le_of_succ_le_succ w)) + 1 := by
            intro rc head neg l w 
            let rcN := prependClause  branch focus focusLt clauses rc head neg 
            have res1 : rcN.reverse (l + 1) w = 
                                      rcN.reverseVec.coords (l + 1) w := by rfl
            have res2 : rc.reverse l (le_of_succ_le_succ w) =
                    rc.reverseVec.coords l (le_of_succ_le_succ w) := by rfl
            rw [res1]
            rw [res2]
            have res3 :rcN.reverseVec = 
              zero +: (rc.reverseVec.map (. + 1)) := by rfl
            rw [res3]
            have res4 :
                (zero +: 
                  (rc.reverseVec.map (. + 1)) ).coords (l + 1) w =
                  (zero +: 
                  (rc.reverseVec.map (. + 1)) ).coords.tail 
                  l (Nat.le_of_succ_le_succ w) := by rfl
            rw [res4]
            rw [(tail_commutes 
                zero (rc.reverseVec.map (. + 1)))]
            rw [map_coords_commute]  

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
          ReverseRelation rc → 
          ReverseRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head pos rrc =>
          let rcN := prependClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rcN.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) → 
                 (rcN.restClauses.coords k w).coords = 
                  delete focus focusLt 
                      (clausesN.coords (rcN.reverse k w) (rcN.reverseWit k w)).coords := 
                    by
                    intro k 
                    match k with
                    | zero => 
                      intro w  
                      have resRHS : rcN.restClauses.coords zero w 
                                = (delete focus focusLt head.coords).vec := by rfl
                      rw [resRHS]
                      rw [seq_to_vec_coords]
                      rfl
                    | l + 1 => 
                      intro w 
                      let lem1 : rcN.restClauses.coords (l + 1) w = 
                              rc.restClauses.coords l (le_of_succ_le_succ w) := by rfl
                      let lem2 := rrc.relation l (le_of_succ_le_succ w)                     
                      rw [lem1]                          
                      rw [lem2]
                      have rs0 : clausesN.coords (rcN.reverse (l + 1) w) 
                                (rcN.reverseWit (l + 1) w) =
                                  clausesN.coords 
                                    (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l (Nat.le_of_succ_le_succ w))) := by 
                                    apply witness_independent
                                    apply reverseResolve
                      rw [rs0]
                      rfl
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
          NonPosReverse rc → 
          NonPosReverse (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg prc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg  
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  (clausesN.coords (rcN.reverse k w) (rcN.reverseWit k w)).coords  
                    (focus) focusLt = some branch) := by
                intro k 
                match k with
                | zero => 
                      intro w hyp
                      apply neg 
                      let lem : 
                         (clausesN.coords (rcN.reverse zero w) (rcN.reverseWit zero w)).coords 
                          focus focusLt = head.coords focus focusLt := by rfl
                      rw [← lem] 
                      exact hyp
                | l + 1 => 
                    intro w hyp 
                    have rs0 : clausesN.coords (rcN.reverse (l + 1) w) 
                                (rcN.reverseWit (l + 1) w) =
                                  clausesN.coords 
                                    (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l (Nat.le_of_succ_le_succ w))) := by 
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0] at hyp
                    have rs1 : clausesN.coords 
                                    (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l (Nat.le_of_succ_le_succ w))) =
                                        clauses.coords (rc.reverse l (Nat.le_of_succ_le_succ w))
                                        (rc.reverseWit l (Nat.le_of_succ_le_succ w)) := by rfl
                    rw [rs1] at hyp
                    let prev := prc.nonPosRev l (Nat.le_of_succ_le_succ w)
                    exact absurd hyp prev
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (head : Clause (n + 1)) → (neg : Not (head.coords focus focusLt = some branch)) →
        (rd : ReductionData branch focus focusLt clauses) → 
        ReductionData branch focus focusLt (head +: clauses) := 
          fun head neg rd =>
          let rc := prependClause branch focus focusLt clauses rd.restrictionClauses head neg
          ⟨rc, 
          droppedProof branch focus focusLt clauses rd.restrictionClauses head neg rd.droppedProof,
          forwardRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.forwardRelation,
          reverseRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.reverseRelation,
          pureReverse branch focus focusLt clauses rd.restrictionClauses head neg rd.nonPosReverse⟩

end PrependClause

