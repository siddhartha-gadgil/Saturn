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
          let forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt (Vector.at (clausesN.at k w)) = 
                Vector.at (rcN.restClauses.at j jw) := 
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
          let relationN : (k : Nat) → (w: k < codomN) → 
                 Vector.at (rcN.restClauses.at k w) = 
                  delete focus focusLt 
                    (Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))) := 
                  fun k w =>
                  let lem1 : (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w)) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  by rfl
                    by
                      rw lem1
                      exact rrc.relation k w
                      done
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
          let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (
                  Vector.at (clausesN.at (rcN.reverse k w) (rcN.reverseWit k w))
                     focus focusLt = some branch) :=
                  fun k w =>
                  let lem1 : clausesN.at (rcN.reverse k w) (rcN.reverseWit k w) =
                    clauses.at (rc.reverse k w) (rc.reverseWit k w) :=  by rfl
                    by
                      rw lem1
                      exact prc.nonPosRev k w
                      done
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

