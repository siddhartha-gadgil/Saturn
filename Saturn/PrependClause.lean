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
                  fun w j => 
                    fun sw jw =>
                      sorry
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
          PureReverse rc → 
          PureReverse (prependClause  branch focus clauses rc head neg) := 
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
                    prc.pure l (leOfSuccLeSucc w) lem2
          ⟨pureN⟩
