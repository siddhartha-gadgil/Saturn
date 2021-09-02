import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat
open Vector



def prependClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) → 
            RestrictionClauses branch focus focusLt (head +: clauses) := 
          fun rc head neg =>
            let headImage := (delete focus focusLt head.at).vec
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
                    rw tailCommutes (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) )
                    rw mapAt
                    have fr : forwardN (succ i) jw = 
                            (rc.forward i (le_of_succ_le_succ jw)).map (. + 1)
                        by rfl
                    rw fr
                    rfl
                    done
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
                    rw lem
                    exact lem2
                    done
            let reverseVecN := zero +: (rc.reverseVec.map (. + 1))
            let reverseN : (k : Nat) →  k < codomN → Nat :=             
              fun k =>
              match k with
              | zero => fun _ => zero
              | l + 1 => fun w => (rc.reverse l w) + 1
            have reverseNEq : reverseVecN.at = reverseN := by
                  apply funext
                  intro j
                  cases j with
                  | zero =>
                    apply funext
                    intro jw
                    rfl
                    done
                  | succ i =>
                    apply funext
                    intro jw
                    have tl :reverseVecN.at (succ i) jw =
                        tail reverseVecN.at i (Nat.le_of_succ_le_succ jw) := by rfl
                    rw tl
                    rw tailCommutes zero (rc.reverseVec.map (. + 1))
                    rw mapAt
                    rfl
                    done
            have reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
              fun k =>
              match k with
              | zero => fun _ => zero_lt_succ _ 
              | l + 1 => fun w => 
                rc.reverseWit l w
            RestrictionClauses.mk codomN restClausesN 
                    (forwardVecN) 
                    ( forwardNEq ▸ forwardWitN) 
                    reverseVecN
                    (reverseNEq ▸ reverseWitN)

namespace PrependClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) →
          DroppedProof rc → 
          DroppedProof (prependClause  branch focus focusLt clauses rc head neg) := 
          fun rc head neg drc =>
            let rcN := prependClause  branch focus focusLt clauses rc head neg 
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := head +: clauses
            let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  Vector.at (clausesN.at k w) focus focusLt = some branch :=
                fun k =>
                  match k with
                  | zero => fun w wf => 
                    Option.noConfusion wf
                  | l + 1 => 
                    fun w nw =>
                      let lem1 : rcN.forward (l + 1) w = 
                        (rc.forward l (le_of_succ_le_succ w)).map (. + 1)  := 
                          by 
                            have res1 : rcN.forward (l + 1) w = 
                                rcN.forwardVec.at (l + 1) w by rfl
                            have res2 : rc.forward l (le_of_succ_le_succ w) =
                                rc.forwardVec.at l (le_of_succ_le_succ w) by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.forwardVec = 
                              (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) ) by rfl
                            rw res3
                            have res4 :
                                Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) (l + 1) w =
                                tail (
                                 Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) 
                                ) l (Nat.le_of_succ_le_succ w) by rfl
                            rw res4
                            rw (tailCommutes 
                                (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) ))
                            rw mapAt
                            done
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := mapNoneIsNone _ _ lem2
                      let lem4 := drc.dropped l (le_of_succ_le_succ w) lem3
                      lem4
            ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) →
          ForwardRelation rc → 
          ForwardRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg frc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg 
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (Vector.at (clausesN.at k w)) = 
                Vector.at (rcN.restClauses.at j jw) := 
                fun k =>
                match k with
                | zero => fun w j => 
                  fun sw jw =>
                    let lem1 : rcN.forward zero w = some zero := by rfl 
                    let lem2 : some j = some zero := Eq.trans (Eq.symm sw) lem1
                    let lem3 : j = zero := by 
                      injection lem2
                      assumption
                      done
                    let lem4 : delete focus focusLt (Vector.at (clausesN.at zero w )) = 
                        Vector.at (rcN.restClauses.at zero (zero_lt_succ rc.codom)) := 
                          by
                            have resLHS : clausesN.at zero w  = head by rfl
                            rw resLHS
                            have resRHS : rcN.restClauses.at zero (zero_lt_succ rc.codom) 
                                = (delete focus focusLt head.at).vec by rfl
                            rw resRHS
                            rw [seqAt]
                            done
                    by
                      rw lem4
                      apply congrArg   
                      apply (witnessIndependent rcN.restClauses.at)
                      exact Eq.symm lem3
                      done
                | l + 1 => 
                  fun w  => 
                    let lem1 : rcN.forward (l + 1) w = 
                      (rc.forward l (le_of_succ_le_succ w)).map (. + 1) := 
                        by 
                        have res1 : rcN.forward (l + 1) w = 
                                rcN.forwardVec.at (l + 1) w by rfl
                        have res2 : rc.forward l (le_of_succ_le_succ w) =
                                rc.forwardVec.at l (le_of_succ_le_succ w) by rfl
                        rw [res1]
                        rw [res2]
                        have res3 :rcN.forwardVec = 
                          (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) ) by rfl
                        rw res3
                        have res4 :
                            Vector.at ((some zero) +: 
                              (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) (l + 1) w =
                            tail (
                              Vector.at ((some zero) +: 
                              (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) 
                            ) l (Nat.le_of_succ_le_succ w) by rfl
                        rw res4
                        rw (tailCommutes 
                            (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) ))
                        rw mapAt
                        done
                    if c : Option.isNone (rcN.forward (l + 1) w) then 
                      fun j sw jw => 
                        let lem2 : Option.isNone (rcN.forward (l + 1) w) = false 
                          := congrArg Option.isNone sw
                        let lem3 := Eq.trans (Eq.symm c) lem2 
                        Bool.noConfusion lem3
                    else   
                      fun j =>
                      match j with
                      | zero =>
                        fun sw jw =>
                          let lem2 : (rc.forward l (le_of_succ_le_succ w)).map (. + 1) =
                            some zero := by
                            rw [← s]w
                            apply Eq.symm
                            have res1 : rcN.forward (l + 1) w = 
                                rcN.forwardVec.at (l + 1) w by rfl
                            have res2 : rc.forward l (le_of_succ_le_succ w) =
                                    rc.forwardVec.at l (le_of_succ_le_succ w) by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.forwardVec = 
                              (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) ) by rfl
                            rw res3
                            have res4 :
                                Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) (l + 1) w =
                                tail (
                                  Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) 
                                ) l (Nat.le_of_succ_le_succ w) by rfl
                            rw res4
                            rw (tailCommutes 
                                (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) ))
                            rw mapAt
                            done
                         let lem2  : False := mapPlusOneZero lem2
                         absurd lem2 (fun x => x)
                      | i + 1 =>
                        by
                          intros sw jw
                          let lem2 : (rc.forward l (le_of_succ_le_succ w)).map (. + 1) =
                            some (i + 1) := by
                            rw [← s]w              
                            have res1 : rcN.forward (l + 1) w = 
                                rcN.forwardVec.at (l + 1) w by rfl
                            have res2 : rc.forward l (le_of_succ_le_succ w) =
                                    rc.forwardVec.at l (le_of_succ_le_succ w) by rfl
                            rw [res1]
                            rw [res2]
                            have res3 :rcN.forwardVec = 
                              (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) ) by rfl
                            rw res3
                            have res4 :
                                Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) (l + 1) w =
                                tail (
                                  Vector.at ((some zero) +: 
                                  (rc.forwardVec.map (fun nop => nop.map (. + 1)) )) 
                                ) l (Nat.le_of_succ_le_succ w) by rfl
                            rw res4
                            rw (tailCommutes 
                                (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1)) ))
                            rw mapAt
                            done
                          let lem3 : rc.forward l (le_of_succ_le_succ w) = some i 
                            := mapPlusOneShift lem2
                          let lem4 := 
                            frc.forwardRelation l (le_of_succ_le_succ w) i lem3 (le_of_succ_le_succ jw)
                          have ll1 : 
                            clausesN.at (l + 1) w = clauses.at l (le_of_succ_le_succ w) by rfl 
                          have ll2 : rcN.restClauses.at (i + 1) jw
                             = rc.restClauses.at i (le_of_succ_le_succ jw) by rfl
                          rw ll1
                          rw ll2
                          rw lem4
                          done
          ⟨forwardRelationN⟩


def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) →
          ReverseRelation rc → 
          ReverseRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head pos rrc =>
          let rcN := prependClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rcN.codom
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) → 
                 Vector.at (rcN.restClauses.at k w) = 
                  delete focus focusLt 
                      (Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))) := 
                    fun k =>
                    match k with
                    | zero => 
                      fun w  => by 
                        have resRHS : rcN.restClauses.at zero w 
                                = (delete focus focusLt head.at).vec by rfl
                        rw resRHS
                        have lll : 
                          Vector.at (FinSeq.vec (delete focus focusLt (Vector.at head))) =
                              delete focus focusLt (Vector.at head) by 
                                rw [seqAt]
                        rw lll
                        apply (congrArg)
                        apply congrArg
                        rfl
                        done
                    | l + 1 => 
                      fun w =>
                        let lem1 : rcN.restClauses.at (l + 1) w = 
                              rc.restClauses.at l (le_of_succ_le_succ w) := by rfl
                        let lem2 := rrc.relation l (le_of_succ_le_succ w) 
                        by
                          rw [lem1]                          
                          rw [lem2]
                          have res0 : rcN.reverse (l + 1) w =
                               rc.reverse l (Nat.le_of_succ_le_succ w) + 1 := 
                                by                                  
                                  have res1 : rcN.reverse (l + 1) w = 
                                      rcN.reverseVec.at (l + 1) w by rfl
                                  have res2 : rc.reverse l (le_of_succ_le_succ w) =
                                          rc.reverseVec.at l (le_of_succ_le_succ w) by rfl
                                  rw [res1]
                                  rw [res2]
                                  have res3 :rcN.reverseVec = 
                                    zero +: (rc.reverseVec.map (. + 1))  by rfl
                                  rw res3
                                  have res4 :
                                      Vector.at (zero +: 
                                        (rc.reverseVec.map (. + 1)) ) (l + 1) w =
                                      tail (
                                        Vector.at (zero +: 
                                        (rc.reverseVec.map (. + 1)) ) 
                                      ) l (Nat.le_of_succ_le_succ w) by rfl
                                  rw res4
                                  rw (tailCommutes 
                                      zero (rc.reverseVec.map (. + 1)))
                                  rw mapAt                                  
                                  done
                          have res00 : clausesN.at (rcN.reverse (l + 1) w) 
                                  (rcN.reverseWit (l + 1) w) =
                              clauses.at (rc.reverse l 
                                (Nat.le_of_succ_le_succ w))
                                (rc.reverseWit l 
                                (Nat.le_of_succ_le_succ w)) by 
                                  have rs0 : clausesN.at (rcN.reverse (l + 1) w) 
                                    (rcN.reverseWit (l + 1) w) =
                                      clausesN.at (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                        (rc.reverseWit l (Nat.le_of_succ_le_succ w)) by 
                                        apply witnessIndependent
                                        exact res0
                                        done
                                  rw rs0
                                  have dfn : clausesN = head +: clauses by rfl
                                  rw dfn 
                                  have td :
                                    Vector.at (head +: clauses) 
                                       (rc.reverse l (Nat.le_of_succ_le_succ w) + 1) 
                                       (rc.reverseWit l (Nat.le_of_succ_le_succ w)) =
                                        clauses.at (rc.reverse l (Nat.le_of_succ_le_succ w))
                                          (rc.reverseWit l (Nat.le_of_succ_le_succ w)) by rfl
                                  rw td
                                  done
                          rw res00                                
                          done
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) →
          NonPosReverse rc → 
          NonPosReverse (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg prc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg  
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w)) 
                    (focus) focusLt = some branch) :=
                fun k =>
                match k with
                | zero => 
                  fun w  => 
                    fun hyp =>
                      let lem : 
                        Vector.at  (clausesN.at (rcN.reverse zero w) (rcN.reverseWit zero w)) 
                          focus focusLt = head.at focus focusLt := by rfl
                      let lem2 := Eq.trans (Eq.symm lem) hyp
                      neg lem2
                | l + 1 => 
                  fun w hyp =>
                    let lem : 
                        Vector.at (clausesN.at (rcN.reverse (l + 1) w) (rcN.reverseWit (l + 1) w)) 
                          focus focusLt =
                          Vector.at (clauses.at (rc.reverse l (le_of_succ_le_succ w)) 
                            (rc.reverseWit l (le_of_succ_le_succ w))) focus focusLt := 
                              by 
                                have res0 : rcN.reverse (l + 1) w =
                                  rc.reverse l (Nat.le_of_succ_le_succ w) + 1 := 
                                    by                                  
                                      have res1 : rcN.reverse (l + 1) w = 
                                          rcN.reverseVec.at (l + 1) w by rfl
                                      have res2 : rc.reverse l (le_of_succ_le_succ w) =
                                              rc.reverseVec.at l (le_of_succ_le_succ w) by rfl
                                      rw [res1]
                                      rw [res2]
                                      have res3 :rcN.reverseVec = 
                                        zero +: (rc.reverseVec.map (. + 1))  by rfl
                                      rw res3
                                      have res4 :
                                          Vector.at (zero +: 
                                            (rc.reverseVec.map (. + 1)) ) (l + 1) w =
                                          tail (
                                            Vector.at (zero +: 
                                            (rc.reverseVec.map (. + 1)) ) 
                                          ) l (Nat.le_of_succ_le_succ w) by rfl
                                      rw res4
                                      rw (tailCommutes 
                                          zero (rc.reverseVec.map (. + 1)))
                                      rw mapAt                                  
                                      done
                                have res00 : clausesN.at (rcN.reverse (l + 1) w) 
                                  (rcN.reverseWit (l + 1) w) =
                                    clauses.at (rc.reverse l 
                                      (Nat.le_of_succ_le_succ w))
                                      (rc.reverseWit l 
                                      (Nat.le_of_succ_le_succ w)) by 
                                        have rs0 : clausesN.at (rcN.reverse (l + 1) w) 
                                          (rcN.reverseWit (l + 1) w) =
                                            clausesN.at (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                              (rc.reverseWit l (Nat.le_of_succ_le_succ w)) by 
                                              apply witnessIndependent
                                              exact res0
                                              done
                                        rw rs0
                                        have dfn : clausesN = head +: clauses by rfl
                                        rw dfn 
                                        have td :
                                          Vector.at (head +: clauses) 
                                            (rc.reverse l (Nat.le_of_succ_le_succ w) + 1) 
                                            (rc.reverseWit l (Nat.le_of_succ_le_succ w)) =
                                              clauses.at (rc.reverse l (Nat.le_of_succ_le_succ w))
                                                (rc.reverseWit l (Nat.le_of_succ_le_succ w)) by rfl
                                        rw td
                                        done
                                rw res00
                                done
                    let lem2 := Eq.trans (Eq.symm lem) hyp
                    prc.nonPosRev l (le_of_succ_le_succ w) lem2
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (head : Clause (n + 1)) → (neg : Not (head.at focus focusLt = some branch)) →
        (rd : RestrictionData branch focus focusLt clauses) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
          fun head neg rd =>
          let rc := prependClause branch focus focusLt clauses rd.restrictionClauses head neg
          ⟨rc, 
          droppedProof branch focus focusLt clauses rd.restrictionClauses head neg rd.droppedProof,
          forwardRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.forwardRelation,
          reverseRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.reverseRelation,
          pureReverse branch focus focusLt clauses rd.restrictionClauses head neg rd.nonPosReverse⟩

end PrependClause

