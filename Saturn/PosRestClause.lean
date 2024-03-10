import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.Solverstep
open Nat
open FinSeq

/-
The inductive step for adding a new clause when it should be dropped. The new clauses and maps
are defined. All the witnesses for the relations between the old and new clauses are also
constructed.
-/
def addPositiveClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
            ReductionClauses branch focus focusLt (head +: clauses) :=
          fun rc head _ =>
          let domN := dom + 1
          let codomN := rc.codom
          let forwardVecN := none +: rc.forwardVec
          let forwardN: (k : Nat) →  k < domN → Option Nat  :=
            fun k  =>
            match k with
            | zero => fun _ => none
            | l + 1 =>
              fun w : l + 1 < domN   =>  rc.forward l (le_of_succ_le_succ w)
          have forwardNEq : forwardVecN.get' = forwardN := by
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
                    rw [get'_cons_succ none rc.forwardVec]
          have forwardWitN : (k: Fin domN) →
              boundOpt rc.codom (forwardN k.val k.isLt) := by
            intro ⟨k, w⟩
            match k with
            | zero =>
                intros
                simp [forwardN, boundOpt]
            | l + 1 =>
                apply rc.forwardWit ⟨l, Nat.le_of_succ_le_succ w⟩
          let reverseVecN := rc.reverseVec.map (. + 1)
          let reverseN : (k : Nat) →  k < codomN → Nat :=
            fun k w => (rc.reverse k w) + 1
          have reverseNEq : reverseVecN.get' = reverseN := by
                  apply funext
                  intro j
                  apply funext
                  intro jw
                  apply get'_map
          have reverseWitN : (k : Fin codomN) →
            reverseN k.val k.isLt < domN :=
              fun ⟨k, w⟩  => succ_le_succ (rc.reverseWit ⟨k,  w⟩)
          ReductionClauses.mk codomN rc.restClauses
                    (forwardVecN)
                    (forwardNEq ▸ forwardWitN)
                    reverseVecN
                    (reverseNEq ▸ reverseWitN)

namespace PosResClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
          DroppedProof rc →
          DroppedProof (addPositiveClause  branch focus focusLt clauses rc head pos) :=
        fun rc head pos drc =>
          ⟨by
            intro k
            match k with
            | zero =>
              intros
              exact pos
            | l + 1 =>
                intro w nw
                exact drc.dropped l (le_of_succ_le_succ w) nw
          ⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
          ForwardRelation rc →
          ForwardRelation (addPositiveClause  branch focus focusLt clauses rc head pos) :=
        fun rc head pos frc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt ((clausesN.get' k w).get') =
                (rcN.restClauses.get' j jw).get' := by
                intro k
                match k with
                | zero =>
                  intro w j sw
                  exact Option.noConfusion sw
                | l + 1 =>
                  intro w j sw
                  exact frc.forwardRelation l (le_of_succ_le_succ w) j sw
          ⟨forwardRelationN⟩

theorem reverseResolve{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : (head.get' focus focusLt = some branch)) →
        (l: Nat) → (w : l  < rc.codom ) →
          (addPositiveClause  branch focus focusLt clauses rc head pos).reverse l w =
            (rc.reverse l w) + 1 := by
            intro rc head neg l w
            let rcN := addPositiveClause  branch focus focusLt clauses rc head neg
            have res1 : rcN.reverse l w =
                                      rcN.reverseVec.get' l w := by rfl
            have res2 : rc.reverse l w =
                    rc.reverseVec.get' l w := by rfl
            rw [res1]
            rw [res2]
            have res3 :rcN.reverseVec =
              (rc.reverseVec.map (. + 1)) := by rfl
            rw [res3]
            have res4 :
                ( (rc.reverseVec.map (. + 1)) ).get' l w =
                  (zero +:
                  (rc.reverseVec.map (. + 1)) ).get'
                  (l + 1) (Nat.succ_le_succ w) := by rfl
            rw [res4]
            rw [(get'_cons_succ
                zero (rc.reverseVec.map (. + 1)))]
            rw [get'_map]

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
          ReverseRelation rc →
          ReverseRelation (addPositiveClause  branch focus focusLt clauses rc head pos) :=
        fun rc head pos rrc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos
          let codomN := rc.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) →
                 (rcN.restClauses.get' k w).get' =
                  delete focus focusLt
                    (clausesN.get' (rcN.reverse k w) (rcN.reverseWit ⟨k, w⟩ )).get' :=
                  by
                    intro l
                    intro w
                    let lem1 : rcN.restClauses.get' l w =
                              rc.restClauses.get' l w := by rfl
                    let lem2 := rrc.relation l w
                    rw [lem1]
                    rw [lem2]
                    have rs0 : clausesN.get' (rcN.reverse l w)
                                (rcN.reverseWit ⟨l, w⟩) =
                                  clausesN.get'
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit ⟨l, w⟩)) := by
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0]
                    rfl
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
          NonPosReverse rc →
          NonPosReverse (addPositiveClause  branch focus focusLt clauses rc head pos) :=
        fun rc head pos prc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos
          let codomN := rc.codom
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  →
                Not (
                  (clausesN.get' (rcN.reverse k w) (rcN.reverseWit ⟨k, w⟩ )).get'
                     focus focusLt = some branch) :=
                  by
                    intro l w hyp
                    have rs0 : clausesN.get' (rcN.reverse l w)
                                (rcN.reverseWit ⟨l, w⟩) =
                                  clausesN.get'
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit ⟨l, w⟩)) := by
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0] at hyp
                    have rs1 : clausesN.get'
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit ⟨l, w⟩)) =
                                        clauses.get' (rc.reverse l w)
                                        (rc.reverseWit ⟨l, w⟩) := by rfl
                    rw [rs1] at hyp
                    let prev := prc.nonPosRev l w
                    exact absurd hyp prev
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
        (head : Clause (n + 1)) → (pos : head.get' focus focusLt = some branch) →
        (rd : ReductionData branch focus focusLt clauses) →
        ReductionData branch focus focusLt (head +: clauses) :=
          fun head pos rd =>
          let rc := addPositiveClause branch focus focusLt clauses rd.restrictionClauses head pos
          ⟨rc,
          droppedProof branch focus focusLt clauses rd.restrictionClauses head pos rd.droppedProof,
          forwardRelation branch focus focusLt clauses rd.restrictionClauses head pos rd.forwardRelation,
          reverseRelation branch focus focusLt clauses rd.restrictionClauses head pos rd.reverseRelation,
          pureReverse branch focus focusLt clauses rd.restrictionClauses head pos rd.nonPosReverse⟩


end PosResClause
