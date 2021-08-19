import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat



def prependClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) → 
            RestrictionClauses branch focus focusLt (head +: clauses) := 
          fun rc head neg =>
            let headImage := delete focus focusLt head
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := head +: clauses
            let restClausesN := headImage +: rc.restClauses
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | 0 => fun _ => some 0
              | l + 1 => 
                fun w : l + 1 < domN   =>  (rc.forward l (leOfSuccLeSucc w)).map (. + 1)
            let forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | 0 => fun w => 
                let lem1 : forwardN 0 w = some 0 := by rfl
                by
                  rw lem1
                  apply zeroLtSucc
                  done
              | l + 1 => 
                fun w : l + 1 < domN   => 
                  let lem : forwardN (l + 1) w = 
                    (rc.forward l (leOfSuccLeSucc w)).map (. + 1) := by rfl 
                  let lem2 := boundOptSucc rc.codom 
                            (rc.forward l (leOfSuccLeSucc w))
                            (rc.forwardWit l (leOfSuccLeSucc w))
                  by
                    rw lem
                    exact lem2
                    done
            let reverseN : (k : Nat) →  k < codomN → Nat :=             
              fun k =>
              match k with
              | 0 => fun _ => 0
              | l + 1 => fun w => (rc.reverse l w) + 1
            let reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
              fun k =>
              match k with
              | 0 => fun _ => zeroLtSucc _ 
              | l + 1 => fun w => 
                rc.reverseWit l w
            ⟨codomN, restClausesN, forwardN, forwardWitN, reverseN, reverseWitN⟩

namespace PrependClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) →
          DroppedProof rc → 
          DroppedProof (prependClause  branch focus focusLt clauses rc head neg) := 
          fun rc head neg drc =>
            let rcN := prependClause  branch focus focusLt clauses rc head neg 
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := head +: clauses
            let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  clausesN k w focus focusLt = some branch :=
                fun k =>
                  match k with
                  | 0 => fun w wf => 
                    Option.noConfusion wf
                  | l + 1 => 
                    fun w nw =>
                      let lem1 : rcN.forward (l + 1) w = 
                        (rc.forward l (leOfSuccLeSucc w)).map (. + 1)  := by rfl
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := mapNoneIsNone _ _ lem2
                      let lem4 := drc.dropped l (leOfSuccLeSucc w) lem3
                      lem4
            ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) →
          ForwardRelation rc → 
          ForwardRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg frc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg 
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          let forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (clausesN k w ) = 
                rcN.restClauses j jw := 
                fun k =>
                match k with
                | 0 => fun w j => 
                  fun sw jw =>
                    let lem1 : rcN.forward 0 w = some 0 := by rfl 
                    let lem2 : some j = some 0 := Eq.trans (Eq.symm sw) lem1
                    let lem3 : j = 0 := by 
                      injection lem2
                      assumption
                      done
                    let lem4 : delete focus focusLt (clausesN 0 w ) = 
                        rcN.restClauses 0 (zeroLtSucc rc.codom) := by rfl
                    by
                      rw lem4
                      apply (witnessIndependent rcN.restClauses)
                      exact Eq.symm lem3
                      done
                | l + 1 => 
                  fun w  => 
                    let lem1 : rcN.forward (l + 1) w = 
                      (rc.forward l (leOfSuccLeSucc w)).map (. + 1) := by rfl
                    if c : Option.isNone (rcN.forward (l + 1) w) then 
                      fun j sw jw => 
                        let lem2 : Option.isNone (rcN.forward (l + 1) w) = false 
                          := congrArg Option.isNone sw
                        let lem3 := Eq.trans (Eq.symm c) lem2 
                        Bool.noConfusion lem3
                    else   
                      fun j =>
                      match j with
                      | 0 =>
                        fun sw jw =>
                          let lem2 : (rc.forward l (leOfSuccLeSucc w)).map (. + 1) =
                            some 0 := sw
                         let lem2  : False := mapPlusOneZero lem2
                         absurd lem2 (fun x => x)
                      | i + 1 =>
                        fun sw jw =>
                          let lem2 : (rc.forward l (leOfSuccLeSucc w)).map (. + 1) =
                            some (i + 1) := sw
                          let lem3 : rc.forward l (leOfSuccLeSucc w) = some i 
                            := mapPlusOneShift lem2
                          let lem4 := 
                            frc.forwardRelation l (leOfSuccLeSucc w) i lem3 (leOfSuccLeSucc jw)
                          lem4
          ⟨forwardRelationN⟩


def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) →
          ReverseRelation rc → 
          ReverseRelation (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head pos rrc =>
          let rcN := prependClause  branch focus focusLt clauses rc head pos  
          let domN := dom + 1
          let codomN := rcN.codom
          let clausesN := head +: clauses
          let relationN : (k : Nat) → (w: k < codomN) → 
                 rcN.restClauses k w = 
                  delete focus focusLt (clausesN (rcN.reverse k w) (rcN.reverseWit k w)) := 
                    fun k =>
                    match k with
                    | 0 => 
                      fun w  => by rfl
                    | l + 1 => 
                      fun w =>
                        let lem1 : rcN.restClauses (l + 1) w = 
                              rc.restClauses l (leOfSuccLeSucc w) := by rfl
                        let lem2 := rrc.relation l (leOfSuccLeSucc w) 
                        by
                          rw lem1
                          exact lem2
                          done
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) →
          NonPosReverse rc → 
          NonPosReverse (prependClause  branch focus focusLt clauses rc head neg) := 
        fun rc head neg prc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg  
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := head +: clauses
          let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (rcN.reverse k w) (rcN.reverseWit k w) (focus) focusLt = some branch) :=
                fun k =>
                match k with
                | 0 => 
                  fun w  => 
                    fun hyp =>
                      let lem : 
                        clausesN (rcN.reverse 0 w) (rcN.reverseWit 0 w) 
                          focus focusLt = head focus focusLt := by rfl
                      let lem2 := Eq.trans (Eq.symm lem) hyp
                      neg lem2
                | l + 1 => 
                  fun w hyp =>
                    let lem : 
                        clausesN (rcN.reverse (l + 1) w) (rcN.reverseWit (l + 1) w) focus focusLt =
                          clauses (rc.reverse l (leOfSuccLeSucc w)) 
                            (rc.reverseWit l (leOfSuccLeSucc w)) focus focusLt := by rfl
                    let lem2 := Eq.trans (Eq.symm lem) hyp
                    prc.nonPosRev l (leOfSuccLeSucc w) lem2
          ⟨pureN⟩


def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))): 
        (head : Clause (n + 1)) → (neg : Not (head focus focusLt = some branch)) →
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

