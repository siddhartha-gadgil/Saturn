import Saturn.Basic
import Saturn.FinSeq 
import Saturn.Solverstep
open Nat

def addPositiveClause{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) → 
            RestrictionClauses branch focus (prepend _ head clauses) := 
          fun rc head pos => 
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := prepend _ head clauses
          let forwardN: (k : Nat) →  k < domN → Option Nat  := 
            fun k  => 
            match k with 
            | 0 => fun _ => none
            | l + 1 => 
              fun w : l + 1 < domN   =>  rc.forward l (leOfSuccLeSucc w)
          let forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
            fun k  => 
            match k with 
            | 0 => fun w => 
              let lem1 : forwardN 0 w = none := by rfl
              by
                rw lem1
                exact True.intro
                done
            | l + 1 => 
              fun w : l + 1 < domN   => 
                let lem : forwardN (l + 1) w = rc.forward l (leOfSuccLeSucc w) := by rfl 
                by
                  rw lem
                  exact (rc.forwardWit l (leOfSuccLeSucc w))
                  done
          let reverseN : (k : Nat) →  k < codomN → Nat := 
            fun k w => (rc.reverse k w) + 1
          let reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
            fun k w => (rc.reverseWit k w)
          RestrictionClauses.mk codomN rc.restClauses forwardN forwardWitN reverseN reverseWitN

namespace PosResClause

def droppedProof{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) →
          DroppedProof rc → 
          DroppedProof (addPositiveClause  branch focus clauses rc head pos) := 
        fun rc head pos drc =>
          let rcN := addPositiveClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := prepend _ head clauses
          let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  clausesN ⟨k, w⟩ focus = some branch :=
                fun k =>
                  match k with
                  | 0 => fun _ _ => pos
                  | l + 1 => 
                    fun w nw =>
                      let lem1 : rcN.forward (l + 1) w = 
                        rc.forward l (leOfSuccLeSucc w) := by rfl
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := drc.dropped l (leOfSuccLeSucc w) lem2
                      by
                        exact lem3
                        done
          ⟨droppedN⟩

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) →
          ForwardRelation rc → 
          ForwardRelation (addPositiveClause  branch focus clauses rc head pos) := 
        fun rc head pos frc =>
          let rcN := addPositiveClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := prepend _ head clauses
          let forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  dropAt _ focus.val focus.isLt (clausesN (⟨k, w⟩) ) = 
                rcN.restClauses ⟨j, jw⟩ := 
                fun k =>
                match k with
                | 0 => fun w j => 
                  fun sw =>
                    Option.noConfusion sw
                | l + 1 => 
                  fun w j => 
                    fun sw =>
                      frc.forwardRelation l (leOfSuccLeSucc w) j sw
          ⟨forwardRelationN⟩

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) →
          ReverseRelation rc → 
          ReverseRelation (addPositiveClause  branch focus clauses rc head pos) := 
        fun rc head pos rrc =>
          let rcN := addPositiveClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := prepend _ head clauses
          let relationN : (k : Nat) → (w: k < codomN) → 
                 rcN.restClauses ⟨k, w⟩ = 
                  dropAt _ focus.val focus.isLt (clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩)) := 
                  fun k w =>
                  let lem1 : clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩) =
                    clauses (⟨rc.reverse k w, rc.reverseWit k w⟩ ) :=  by rfl
                    by
                      rw lem1
                      exact rrc.relation k w
                      done
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) →
          NonPosReverse rc → 
          NonPosReverse (addPositiveClause  branch focus clauses rc head pos) := 
        fun rc head pos prc =>
          let rcN := addPositiveClause  branch focus clauses rc head pos  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := prepend _ head clauses
          let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩) (focus) = some branch) :=
                  fun k w =>
                  let lem1 : clausesN (⟨rcN.reverse k w, rcN.reverseWit k w⟩) =
                    clauses (⟨rc.reverse k w, rc.reverseWit k w⟩) :=  by rfl
                    by
                      rw lem1
                      exact prc.nonPosRev k w
                      done
          ⟨pureN⟩
