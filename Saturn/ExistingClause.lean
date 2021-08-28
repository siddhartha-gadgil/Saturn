import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat



def addExistingPositiveClause{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (rc.restClauses p pw = delete focus focusLt head) → 
            RestrictionClauses branch focus focusLt (head +| clauses) := 
          fun rc head p pw peqn =>
            let domN := dom + 1
            let codomN := rc.codom
            let clausesN := head +| clauses
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | 0 => fun _ => some p
              | l + 1 => 
                fun w : l + 1 < domN   =>  rc.forward l (leOfSuccLeSucc w)
            let forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | 0 => fun w => 
                let lem1 : forwardN 0 w = some p := by rfl
                by
                  rw lem1
                  exact pw
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

namespace ExistingClauses

def droppedProof{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : rc.restClauses p pw = delete focus focusLt head) →
          DroppedProof rc → 
          DroppedProof (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf drc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +| clauses
          let droppedN : 
              (k : Nat) → (w: k < domN) → rcN.forward k w = none → 
                  clausesN k w focus focusLt = some branch :=
                fun k =>
                  match k with
                  | 0 => fun x y => 
                    let lem : rcN.forward 0 x = some p := by rfl
                    let lem2 := (Eq.trans (Eq.symm lem) y)
                    Option.noConfusion lem2
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

def forwardRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1))  → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : rc.restClauses p pw = delete focus focusLt head)  →
          ForwardRelation rc → 
          ForwardRelation (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf frc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf 
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +| clauses
          let forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (clausesN k w ) = 
                rcN.restClauses j jw := 
                fun k =>
                match k with
                | 0 => fun w j => 
                  fun sw jw =>
                    let lem1 : rcN.forward 0 w = some p := by rfl 
                    let lem2 : some j = some p := Eq.trans (Eq.symm sw) lem1
                    let lem3 : j = p := by 
                      injection lem2
                      assumption
                      done
                    let lem4 : rc.restClauses p = rcN.restClauses p := by rfl
                    let lem5 : clausesN 0 w = head := by rfl
                    by
                      rw (congrArg (delete focus focusLt) lem5)
                      rw (Eq.symm eqf)
                      rw lem4
                      apply (witnessIndependent rcN.restClauses)
                      exact Eq.symm lem3
                      done
                | l + 1 => 
                  fun w j => 
                    fun sw =>
                      frc.forwardRelation l (leOfSuccLeSucc w) j sw
          ⟨forwardRelationN⟩

def reverseRelation{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : rc.restClauses p pw = delete focus focusLt head) →
          ReverseRelation rc → 
          ReverseRelation (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf rrc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +| clauses
          let relationN : (k : Nat) → (w: k < codomN) → 
                 rcN.restClauses k w = 
                  delete focus focusLt 
                    (clausesN (rcN.reverse k w) (rcN.reverseWit k w)) := 
                  fun k w =>
                  let lem1 : clausesN (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses (rc.reverse k w) (rc.reverseWit k w) :=  by rfl
                    by
                      rw lem1
                      exact rrc.relation k w
                      done
          ⟨relationN⟩

def pureReverse{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))):
      (rc: RestrictionClauses branch focus focusLt clauses) → 
        (head : Clause (n + 1)) → (p : Nat) → (pw : p < rc.codom) → 
          (eqf : rc.restClauses p pw = delete focus focusLt head) →
          NonPosReverse rc → 
          NonPosReverse (addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf) := 
        fun rc head p pw eqf prc =>
          let rcN := addExistingPositiveClause  branch focus focusLt clauses rc head p pw eqf  
          let domN := dom + 1
          let codomN := rc.codom
          let clausesN := head +| clauses
          let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (rcN.reverse k w) (rcN.reverseWit k w) (focus) focusLt = some branch) :=
                  fun k w =>
                  let lem1 : clausesN (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses (rc.reverse k w) (rc.reverseWit k w) :=  by rfl
                    by
                      rw lem1
                      exact prc.nonPosRev k w
                      done 
          ⟨pureN⟩

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → (p : Nat) → 
          (pw : p < rd.restrictionClauses.codom) → 
          (rd.restrictionClauses.restClauses p pw = delete focus focusLt head) → 
        RestrictionData branch focus focusLt (head +| clauses) := 
      fun rd head p pw peqn =>
      let rc := addExistingPositiveClause branch focus focusLt clauses rd.restrictionClauses 
                    head p pw peqn
      ⟨rc, 
      droppedProof branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.droppedProof,
      forwardRelation branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.forwardRelation,
      reverseRelation branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.reverseRelation,
      pureReverse branch focus focusLt clauses rd.restrictionClauses head p pw peqn rd.nonPosReverse⟩

end ExistingClauses


