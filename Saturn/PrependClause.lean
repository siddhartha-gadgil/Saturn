import Saturn.Basic
import Saturn.FinSeq 
import Saturn.Solverstep
open Nat

def prependClause{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus = some branch)) → 
            RestrictionClauses branch focus (prepend _ head clauses) := 
          fun rc head neg =>
            let headImage := dropAt _ focus.val focus.isLt head
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := prepend _ head clauses
            let restClausesN := prepend _ headImage rc.restClauses
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
            RestrictionClauses.mk codomN restClausesN forwardN forwardWitN reverseN reverseWitN

namespace PrependClause

theorem mapPlusOneZero{n: Option Nat} : Not (n.map (. + 1) = some 0) :=
  match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some 0 =>
    let lem : j + 1 = 0 := by
      injection hyp
      assumption
    Nat.noConfusion lem

theorem mapPlusOneShift{n : Option Nat}{m : Nat} : n.map (. + 1) = some (m + 1) → 
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

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus = some branch)) →
          ForwardRelation rc → 
          ForwardRelation (prependClause  branch focus clauses rc head neg) := 
        fun rc head pos frc =>
          let rcN := prependClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := prepend _ head clauses
          let forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  dropAt _ focus.val focus.isLt (clausesN (⟨k, w⟩) ) = 
                rcN.restClauses ⟨j, jw⟩ := 
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
                    let lem4 : dropAt _ focus.val focus.isLt (clausesN (⟨0, w⟩) ) = 
                        rcN.restClauses ⟨0, zeroLtSucc _⟩ := by rfl
                    by
                      rw lem4
                      apply (congrArg rcN.restClauses)
                      apply Fin.eqOfVeq
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

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus = some branch)) →
          ReverseRelation rc → 
          ReverseRelation (prependClause  branch focus clauses rc head neg) := 
        fun rc head pos rrc =>
          let rcN := prependClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rcN.codom
          let clausesN := prepend _ head clauses
          let relationN : (k : Nat) → (w: k < codomN) → 
                 rcN.restClauses ⟨k, w⟩ = 
                  dropAt _ focus.val focus.isLt (clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩)) := 
                    fun k =>
                    match k with
                    | 0 => 
                      fun w  => by rfl
                    | l + 1 => 
                      fun w =>
                        let lem1 : rcN.restClauses ⟨l + 1, w⟩ = 
                              rc.restClauses ⟨l, leOfSuccLeSucc w ⟩ := by rfl
                        let lem2 := rrc.relation l (leOfSuccLeSucc w) 
                        let lem3 : clausesN ⟨rcN.reverse (l + 1) w, rcN.reverseWit (l + 1) w⟩ = 
                          clauses ⟨rc.reverse l w, rc.reverseWit l w⟩ := by rfl
                        let lem4 := congrArg (dropAt n focus.val focus.isLt)
                          lem3
                        by
                          rw lem1
                          rw lem4
                          exact lem2
                          done
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus = some branch)) →
          NonPosReverse rc → 
          NonPosReverse (prependClause  branch focus clauses rc head neg) := 
        fun rc head neg prc =>
          let rcN := prependClause  branch focus clauses rc head neg  
          let domN := dom + 1
          let codomN := rc.codom + 1
          let clausesN := prepend _ head clauses
          let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩) (focus) = some branch) :=
                fun k =>
                match k with
                | 0 => 
                  fun w  => 
                    fun hyp =>
                      let lem : 
                        clausesN (⟨rcN.reverse 0 w, rcN.reverseWit 0 w⟩) focus = head focus := by rfl
                      let lem2 := Eq.trans (Eq.symm lem) hyp
                      neg lem2
                | l + 1 => 
                  fun w hyp =>
                    let lem : 
                        clausesN (⟨rcN.reverse (l + 1) w, rcN.reverseWit (l + 1) w⟩) focus =
                          clauses ⟨rc.reverse l (leOfSuccLeSucc w), 
                            rc.reverseWit l (leOfSuccLeSucc w)⟩ focus := by rfl
                    let lem2 := Eq.trans (Eq.symm lem) hyp
                    prc.nonPosRev l (leOfSuccLeSucc w) lem2
          ⟨pureN⟩