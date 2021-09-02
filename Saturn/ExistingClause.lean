import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat



def addExistingPositiveClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (Vector.at (rc.restClauses.at p pw) = delete focus focusLt head.at) → 
            RestrictionClauses branch focus focusLt (head +: clauses) := 
          fun rc head p pw peqn =>
            let domN := dom + 1
            let codomN := rc.codom
            let clausesN := head +: clauses
            let forwardVecN := (some p) +: rc.forwardVec
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | zero => fun _ => some p
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
                    rw tl
                    rw tailCommutes (some p) rc.forwardVec
                    have fr : forwardN (succ i) jw = 
                            rc.forward i (le_of_succ_le_succ jw)
                        by rfl
                    rw fr
                    rfl
                    done
            have forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | zero => fun w => 
                let resolve : forwardN zero w = some p := by rfl
                resolve ▸ pw
              | l + 1 => 
                fun w : l + 1 < domN   => 
                  let lem : forwardN (l + 1) w = rc.forward l (le_of_succ_le_succ w) := 
                      by rfl 
                  lem ▸ (rc.forwardWit l (le_of_succ_le_succ w))
                    
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
              fun k w => (rc.reverseWit k w)

            RestrictionClauses.mk codomN rc.restClauses 
                  (forwardVecN) 
                  (forwardNEq ▸ forwardWitN) 
                  reverseVecN
                  (reverseNEq ▸ reverseWitN)
                  
namespace ExistingClauses

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : Vector.at (rc.restClauses.at p pw) = delete focus focusLt head.at) →
          DroppedProof rc → 
          DroppedProof (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf drc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  Vector.at (clausesN.at k w) focus focusLt = some branch :=
                fun k =>
                  match k with
                  | zero => fun x y => 
                    let lem : rcN.forward zero x = some p := by rfl
                    let lem2 := (Eq.trans (Eq.symm lem) y)
                    Option.noConfusion lem2
                  | l + 1 => 
                    fun w nw =>
                      let resolve : rcN.forward (l + 1) w = 
                        rc.forward l (le_of_succ_le_succ w) := by rfl
                      let lem2 := Eq.trans (Eq.symm resolve) nw
                      drc.dropped l (le_of_succ_le_succ w) lem2
          ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1))  → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : Vector.at (rc.restClauses.at p pw) = delete focus focusLt head.at)  →
          ForwardRelation rc → 
          ForwardRelation (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf frc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf 
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (Vector.at (clausesN.at k w )) = 
                Vector.at (rcN.restClauses.at j jw) := 
                fun k =>
                match k with
                | zero => fun w j => 
                  fun sw jw =>
                    let resolve : rcN.forward zero w = some p := by rfl 
                    let lem2 : some j = some p := Eq.trans (Eq.symm sw) resolve
                    let lem3 : j = p := by 
                      injection lem2
                      assumption
                      done
                    let lem4 : rc.restClauses.at p = rcN.restClauses.at p := by rfl
                    let lem5 : clausesN.at zero w = head := by rfl
                    by
                      rw (congrArg (
                          fun s => delete focus focusLt (Vector.at s)) lem5)
                      rw ← eqf
                      rw lem4
                      apply congrArg Vector.at  
                      rw (witnessIndependent rcN.restClauses.at)
                      rw [lem3]
                      done
                | l + 1 => 
                  fun w j => 
                    fun sw =>
                      frc.forwardRelation l (le_of_succ_le_succ w) j sw
          ⟨forwardRelationN⟩

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : Vector.at (rc.restClauses.at p pw) = 
            delete focus focusLt head.at) →
          ReverseRelation rc → 
          ReverseRelation (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf rrc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) → 
                 Vector.at (rcN.restClauses.at k w) = 
                  delete focus focusLt 
                    (Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))) := 
                  fun k w =>
                  let resolve : clausesN.at (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  
                    by 
                    have res0:  rcN.reverse k w = rc.reverse k w  + 1 
                          by
                            have res1 : rcN.reverse k w = 
                                      rcN.reverseVec.at k w by rfl 
                            have res2 : rc.reverse k w =
                                    rc.reverseVec.at k w by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.reverseVec = 
                              rc.reverseVec.map (. + 1)  by rfl
                            rw res3
                            rw mapAt                                  
                            done
                            done
                    have res00 : clausesN.at (rcN.reverse k w) 
                              (rcN.reverseWit k w) =
                          clauses.at (rc.reverse k w )
                            (rc.reverseWit k w) by 
                              have rs0 : clausesN.at (rcN.reverse k w) 
                                (rcN.reverseWit k w) =
                                  clausesN.at (rc.reverse k w + 1)
                                    (rc.reverseWit k w) by 
                                    apply witnessIndependent
                                    exact res0
                                    done
                              rw rs0
                              have dfn : clausesN = head +: clauses by rfl
                              rw dfn 
                              have td :
                                Vector.at (head +: clauses) 
                                    (rc.reverse k w + 1) 
                                    (rc.reverseWit k w) =
                                    clauses.at (rc.reverse k w)
                                      (rc.reverseWit k w) by rfl
                              rw td
                              done
                    rw res00
                    done
                  resolve ▸ rrc.relation k w
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : Vector.at (rc.restClauses.at p pw) = delete focus focusLt head.at) →
          NonPosReverse rc → 
          NonPosReverse (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf prc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))
                     (focus) focusLt = some branch) :=
                  fun k w =>
                  let resolve : clausesN.at (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  
                    by 
                      have res0:  rcN.reverse k w = rc.reverse k w  + 1 
                          by
                            have res1 : rcN.reverse k w = 
                                      rcN.reverseVec.at k w by rfl 
                            have res2 : rc.reverse k w =
                                    rc.reverseVec.at k w by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.reverseVec = 
                              rc.reverseVec.map (. + 1)  by rfl
                            rw res3
                            rw mapAt                                  
                            done
                      have rs0 : clausesN.at (rcN.reverse k w) 
                          (rcN.reverseWit k w) =
                            clausesN.at (rc.reverse k w + 1)
                              (rc.reverseWit k w) by 
                              apply witnessIndependent
                              exact res0
                              done
                        rw rs0
                        have dfn : clausesN = head +: clauses by rfl
                        rw dfn 
                        have td :
                          Vector.at (head +: clauses) 
                              (rc.reverse k w + 1) 
                              (rc.reverseWit k w) =
                              clauses.at (rc.reverse k w)
                                (rc.reverseWit k w) by rfl
                      rw td
                      done
                  resolve ▸ prc.nonPosRev k w
          ⟨pureN⟩

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → (p : Nat) → 
          (pw : p < rd.restrictionClauses.codom) → 
          (
            Vector.at (rd.restrictionClauses.restClauses.at p pw) = 
              delete focus focusLt head.at) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
      fun rd head p pw peqn =>
      let rc := addExistingPositiveClause branch focus focusLt clauses rd.restrictionClauses 
                    head p pw peqn
      ⟨rc, 
      droppedProof branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.droppedProof,
      forwardRelation branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.forwardRelation,
      reverseRelation branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.reverseRelation,
      pureReverse branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.nonPosReverse⟩

end ExistingClauses


