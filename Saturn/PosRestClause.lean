import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat

 

def addPositiveClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) → 
            RestrictionClauses branch focus focusLt (head +: clauses) := 
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
          have forwardNEq : forwardVecN.at = forwardN := by
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
                    have tl :forwardVecN.at (succ i) jw = 
                        tail forwardVecN.at i (Nat.le_of_succ_le_succ jw) := by rfl
                    rw [tl]
                    rw [tailCommutes none rc.forwardVec]
                    have fr : forwardN (succ i) jw = 
                            rc.forward i (le_of_succ_le_succ jw) :=
                        by rfl
                    rw [fr]
                    rfl
                    done
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
          have reverseNEq : reverseVecN.at = reverseN := by
                  apply funext
                  intro j
                  apply funext
                  intro jw
                  apply mapAt
                  done
          have reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
            fun k w => succ_le_succ (rc.reverseWit k  w)
          RestrictionClauses.mk codomN rc.restClauses 
                    (forwardVecN) 
                    (forwardNEq ▸ forwardWitN) 
                    reverseVecN
                    (reverseNEq ▸ reverseWitN)

namespace PosResClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) →
          DroppedProof rc → 
          DroppedProof (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos drc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  Vector.at (clausesN.at k w) focus focusLt = some branch :=
                fun k =>
                  match k with
                  | zero => fun _ _ => pos
                  | l + 1 => 
                    fun w nw =>
                      let resolve : rcN.forward (l + 1) w = 
                        rc.forward l (le_of_succ_le_succ w) := by rfl
                      let lem2 := Eq.trans (Eq.symm resolve) nw
                      let lem3 := drc.dropped l (le_of_succ_le_succ w) lem2
                      by
                        exact lem3
                        done
          ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) →
          ForwardRelation rc → 
          ForwardRelation (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos frc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (Vector.at (clausesN.at k w)) = 
                Vector.at (rcN.restClauses.at j jw) := 
                fun k =>
                match k with
                | zero => fun w j => 
                  fun sw =>
                    Option.noConfusion sw
                | l + 1 => 
                  fun w j => 
                    fun sw =>
                      frc.forwardRelation l (le_of_succ_le_succ w) j sw
          ⟨forwardRelationN⟩

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) →
          ReverseRelation rc → 
          ReverseRelation (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos rrc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) → 
                 Vector.at (rcN.restClauses.at k w) = 
                  delete focus focusLt 
                    (Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))) := 
                  fun k w =>
                  let resolve : (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w)) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  
                      by 
                        have res0:  rcN.reverse k w = rc.reverse k w  + 1 :=
                          by
                            have res1 : rcN.reverse k w = 
                                      rcN.reverseVec.at k w := by rfl 
                            have res2 : rc.reverse k w =
                                    rc.reverseVec.at k w := by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.reverseVec = 
                              rc.reverseVec.map (. + 1) := by rfl
                            rw [res3]
                            rw [mapAt]                                  
                            done
                            done
                        have res00 : clausesN.at (rcN.reverse k w) 
                                  (rcN.reverseWit k w) =
                              clauses.at (rc.reverse k w )
                                (rc.reverseWit k w) := by 
                                  have rs0 : clausesN.at (rcN.reverse k w) 
                                    (rcN.reverseWit k w) =
                                      clausesN.at (rc.reverse k w + 1)
                                        (succ_le_succ (rc.reverseWit k w)) := by 
                                        apply witnessIndependent
                                        exact res0
                                        done
                                  rw [rs0]
                                  have dfn : clausesN = head +: clauses := by rfl
                                  rw [dfn] 
                                  have td :
                                    Vector.at (head +: clauses) 
                                       (rc.reverse k w + 1) 
                                       (succ_le_succ (rc.reverseWit k w)) =
                                        clauses.at (rc.reverse k w)
                                          (rc.reverseWit k w) := by rfl
                                  rw [td]
                                  done
                        rw [res00]
                        done
                  resolve ▸ rrc.relation k w                      
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) →
          NonPosReverse rc → 
          NonPosReverse (addPositiveClause  branch focus focusLt clauses rc head pos) := 
        fun rc head pos prc =>
          let rcN := addPositiveClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))
                     focus focusLt = some branch) :=
                  fun k w =>
                  let resolve : clausesN.at (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  
                    by
                      have res0:  rcN.reverse k w = rc.reverse k w  + 1 :=
                          by
                            have res1 : rcN.reverse k w = 
                                      rcN.reverseVec.at k w := by rfl 
                            have res2 : rc.reverse k w =
                                    rc.reverseVec.at k w := by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.reverseVec = 
                              rc.reverseVec.map (. + 1) :=  by rfl
                            rw [res3]
                            rw [mapAt]                                  
                            done
                      have rs0 : clausesN.at (rcN.reverse k w) 
                          (rcN.reverseWit k w) =
                            clausesN.at (rc.reverse k w + 1)
                             (succ_le_succ (rc.reverseWit k w)) := by 
                              apply witnessIndependent
                              exact res0
                              done
                        rw [rs0]
                        have dfn : clausesN = head +: clauses := by rfl
                        rw [dfn] 
                        have td :
                          Vector.at (head +: clauses) 
                              (rc.reverse k w + 1) 
                              (succ_le_succ (rc.reverseWit k w)) =
                              clauses.at (rc.reverse k w)
                                (rc.reverseWit k w) := by rfl
                      rw [td]
                      done
                  resolve ▸ prc.nonPosRev k w
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (head : Clause (n + 1)) → (pos : head.at focus focusLt = some branch) →
        (rd : RestrictionData branch focus focusLt clauses) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
          fun head pos rd =>
          let rc := addPositiveClause branch focus focusLt clauses rd.restrictionClauses head pos
          ⟨rc, 
          droppedProof branch focus focusLt clauses rd.restrictionClauses head pos rd.droppedProof,
          forwardRelation branch focus focusLt clauses rd.restrictionClauses head pos rd.forwardRelation,
          reverseRelation branch focus focusLt clauses rd.restrictionClauses head pos rd.reverseRelation,
          pureReverse branch focus focusLt clauses rd.restrictionClauses head pos rd.nonPosReverse⟩
          

end PosResClause

