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
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) → 
            ReductionClauses branch focus focusLt (head +: clauses) := 
          fun rc head pos => 
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          let forwardVecN := none +: rc.forwardVec
          let forwardN: (k : Nat) →  k < domN → Option Nat  := 
            fun k  => 
            match k with 
            | zero => fun _ => none
            | l + 1 => 
              fun w : l + 1 < domN   =>  rc.forward l (le_of_succ_le_succ w)
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
                    rw [tl]
                    rw [tail_commutes none rc.forwardVec]
          have forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
            fun k  => 
            match k with 
            | zero => fun w => 
              let resolve : forwardN zero w = none := by rfl
              by
                rw [resolve]
                exact True.intro
                done
            | l + 1 => 
              fun w : l + 1 < domN   => 
                let lem : forwardN (l + 1) w = rc.forward l (le_of_succ_le_succ w) := by rfl 
                by
                  rw [lem]
                  exact (rc.forwardWit l (le_of_succ_le_succ w))
                  done
          let reverseVecN := rc.reverseVec.map (. + 1)
          let reverseN : (k : Nat) →  k < codomN → Nat := 
            fun k w => (rc.reverse k w) + 1
          have reverseNEq : reverseVecN.coords = reverseN := by
                  apply funext
                  intro j
                  apply funext
                  intro jw
                  apply map_coords_commute
                  done
          have reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
            fun k w => succ_le_succ (rc.reverseWit k  w)
          ReductionClauses.mk codomN rc.restClauses 
                    (forwardVecN) 
                    (forwardNEq ▸ forwardWitN) 
                    reverseVecN
                    (reverseNEq ▸ reverseWitN)

namespace PosResClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) →
          DroppedProof rc → 
          DroppedProof (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos drc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  (clausesN.coords k w).coords focus focusLt = some branch := by
                  intro k 
                  match k with
                  | zero => 
                    intro _ _ 
                    exact pos
                  | l + 1 => 
                      intro w nw 
                      let resolve : rcN.forward (l + 1) w = 
                        rc.forward l (le_of_succ_le_succ w) := by rfl
                      rw [resolve] at nw
                      let lem3 := drc.dropped l (le_of_succ_le_succ w) nw
                      exact lem3                      
          ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) →
          ForwardRelation rc → 
          ForwardRelation (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos frc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt ((clausesN.coords k w).coords) = 
                (rcN.restClauses.coords j jw).coords := by
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
        (head : Clause (n + 1)) → (pos : (head.coords focus focusLt = some branch)) →
        (l: Nat) → (w : l  < rc.codom ) → 
          (addPositiveClause  branch focus focusLt clauses rc head pos).reverse l w = 
            (rc.reverse l w) + 1 := by
            intro rc head neg l w 
            let rcN := addPositiveClause  branch focus focusLt clauses rc head neg 
            have res1 : rcN.reverse l w = 
                                      rcN.reverseVec.coords l w := by rfl
            have res2 : rc.reverse l w =
                    rc.reverseVec.coords l w := by rfl
            rw [res1]
            rw [res2]
            have res3 :rcN.reverseVec = 
              (rc.reverseVec.map (. + 1)) := by rfl
            rw [res3]
            have res4 :
                ( (rc.reverseVec.map (. + 1)) ).coords l w =
                  (zero +: 
                  (rc.reverseVec.map (. + 1)) ).coords.tail 
                  l w := by rfl
            rw [res4]
            rw [(tail_commutes 
                zero (rc.reverseVec.map (. + 1)))]
            rw [map_coords_commute]  

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) →
          ReverseRelation rc → 
          ReverseRelation (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos rrc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) → 
                 (rcN.restClauses.coords k w).coords = 
                  delete focus focusLt 
                    (clausesN.coords (rcN.reverse k w) (rcN.reverseWit k w)).coords := 
                  by
                    intro l
                    intro w 
                    let lem1 : rcN.restClauses.coords l w = 
                              rc.restClauses.coords l w := by rfl
                    let lem2 := rrc.relation l w               
                    rw [lem1]                          
                    rw [lem2]
                    have rs0 : clausesN.coords (rcN.reverse l w) 
                                (rcN.reverseWit l w) =
                                  clausesN.coords 
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l w)) := by 
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0]
                    rfl
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: ReductionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) →
          NonPosReverse rc → 
          NonPosReverse (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos prc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  (clausesN.coords (rcN.reverse k w) (rcN.reverseWit k w)).coords 
                     focus focusLt = some branch) :=
                  by
                    intro l w hyp 
                    have rs0 : clausesN.coords (rcN.reverse l w) 
                                (rcN.reverseWit l w) =
                                  clausesN.coords 
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l w)) := by 
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0] at hyp
                    have rs1 : clausesN.coords 
                                    (rc.reverse l w + 1)
                                    (succ_le_succ
                                      (rc.reverseWit l w)) =
                                        clauses.coords (rc.reverse l w)
                                        (rc.reverseWit l w) := by rfl
                    rw [rs1] at hyp
                    let prev := prc.nonPosRev l w
                    exact absurd hyp prev
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (head : Clause (n + 1)) → (pos : head.coords focus focusLt = some branch) →
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

