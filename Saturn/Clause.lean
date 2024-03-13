import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Prover
open Nat
open Vector
open FinSeq

/-!
## Clauses

A **SAT problem** is determined by a set of clauses. Here we define structures corresponding to clauses, and prove their basic properties.

Variables are assumed to correspond to integers.
Literals correspond to associating to each variable a term of type `Option Bool`, with `none` meaning absence of the variable in the clause, and
`some b` meaning its presence with `b` a boolean indicating whether the variable or its negation is part of the clause. Thus, clauses correspond to `Vector (Option Bool) n`, with `n` the number of variables.
Similarly a valuation (assignment of `true` or `false` to each variable) is a term of type `Vector Bool n`.

We also define *unit clauses*, which are clauses that have only one literal, and *pure clauses* and define functions to find these.
These allow simplification of the SAT problem.
-/


/--
### Contradiction

These are clauses that are always false, i.e., they have no satisfying valuation. They are the empty clauses.
-/
def contradiction(n: Nat) : Clause n :=
  Vector.ofFn' (fun _ _ => none)


theorem get'_contradiction(n: Nat)(k: Nat)(w: k < n) : (contradiction n).get' k w = none :=
  by rw [contradiction, Vector.get'_of_Fn']

theorem get_contradiction (n : Nat) (kw : Fin n) : (contradiction n).get kw = none :=
  by rw [contradiction, Vector.ofFn', Vector.get_ofFn]

theorem contradiction_is_false (n: Nat) : ∀ valuation : Valuation n,
          Not (clauseSat (contradiction n) valuation) := by
    intro valuation ⟨k, ⟨b, p⟩⟩
    simp [get_contradiction, varSat] at p


theorem contradiction_insert_none{n : Nat} (focus: Nat)(focusLt : focus < n + 1) :
      insert none n focus focusLt ((contradiction n).get') =
                          (contradiction (n + 1)).get' := by
    apply funext
    intro j
    apply funext
    intro jw
    rw [get'_contradiction]
    exact if c : j = focus then
      match focus, c, focusLt with
      | .(j), rfl, .(jw) =>
        by
          rw [insert_at_focus]
    else by
      let i := skipInverse focus j c
      let eqn : skip focus i = j := skipInverse_eq focus j c
      let iw := skip_preimage_lt focusLt jw eqn
      match j, eqn, jw with
      | .(skip focus i), rfl, .(skip_le_succ iw) =>
        rw [insert_at_image
            none n focus focusLt ((contradiction n).get')
            i iw, get'_contradiction]


instance {n: Nat} : Repr (Clause n) :=
  ⟨fun (cls : Clause n) => fun n => reprPrec (cls.toList) n⟩

/-!
### Unit clauses

These are clauses that have only one literal. They are useful in simplifying the SAT problem. Given a unit clause, the variable in the clause must be assigned the value that makes the clause true. This lets us consider only one branch of the search tree in the DPLL algorithm.
-/
def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  Vector.ofFn' (insert (some b) n k w ((contradiction n).get'))

theorem unitClause_at_literal(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):
          (unitClause n b k w).get' k w = b := by
            rw [unitClause, Vector.of_Fn'_get']
            apply insert_at_focus

theorem unitClause_skipping_literal(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):
          (i: Nat) → (iw : i < n) → (unitClause n b k w).get' (skip k i)
                  (skip_le_succ iw) = none := by
                  intro i iw
                  rw [unitClause, Vector.of_Fn'_get']
                  let ins := insert_at_image (some b) n k w ((contradiction n).get') i iw
                  rw [ins, get'_contradiction]

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1))(parity: Bool) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) :=
    fun ⟨k, w⟩ =>
      if pf:clause = (unitClause n parity k w)
      then
        some ⟨k, w, parity, pf⟩
      else none
  let seq : FinSeq (n + 1) (Fin (n + 1)) := fun k w => ⟨k, w⟩
  findSome? f seq

structure SomeUnitClause{l n : Nat}(clauses : Vector (Clause (n + 1)) l) where
  pos: Nat
  posBound : pos < l
  index: Nat
  bound : index < n + 1
  parity: Bool
  equality : clauses.get' pos posBound = unitClause n parity index bound

def someUnitClauseAux {l : Nat} {n : Nat}: (clauses : Vector (Clause (n + 1)) l) →
  Vector Nat l →  Vector Nat l →
  (cb: Nat) → (cbBound : cb ≤  l) → Option (SomeUnitClause clauses) →
  Option (SomeUnitClause clauses)  :=
    fun clauses posCount negCount cb =>
    match cb with
    | zero => fun _ optCl => optCl
    | m + 1 =>
      fun cbBound optCl =>
      match optCl with
      | some scl => some scl
      | none =>
        if (posCount.get' m cbBound) + (negCount.get' m cbBound) = 1 then
        let parity := (posCount.get' m cbBound) == 1
        match clauseUnit (clauses.get' m cbBound) parity with
        | some u =>
            some ⟨m, cbBound, u.index, u.bound, u.parity, u.equality⟩
        | none =>
          someUnitClauseAux clauses
            posCount negCount m (Nat.le_trans (Nat.le_succ m) cbBound) none
        else none


def someUnitClause? {l : Nat} {n : Nat}: (clauses : Vector  (Clause (n + 1)) l) →
  Vector Nat l →
  Vector Nat l →
  Option (SomeUnitClause clauses)  :=
    fun clauses posCount negCount =>
     someUnitClauseAux clauses posCount negCount l (Nat.le_refl l) none

/-!
### Pure variables

A variable is pure in a set of clauses if it appears only with the same polarity in all the clauses. This means that the variable can be assigned a value that makes all the clauses true. This is useful in simplifying the SAT problem as if there
-/

structure HasPureVar{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < num_clauses) →
          ((clauses.get' k lt).get' index bound = none) ∨
            ((clauses.get' k lt).get' index bound = some parity)

structure IsPureVar{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < num_clauses) → ((clauses.get' k lt).get' index bound = none) ∨
                                ((clauses.get' k lt).get' index bound = some parity)

def IsPure {num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
                  (index: Nat)(bound : index < n)(parity : Bool): Prop :=
                  (k : Nat) → (lt : k < num_clauses) →
          ((clauses.get' k lt).get' index bound = none) ∨
          ((clauses.get' k lt).get' index bound = some parity)

def HasPureTail{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
                  (index: Nat)(bound : index < n)(parity : Bool)(m: Nat): Prop :=
                  (k : Nat) → (lt : k < num_clauses) → (m ≤ k) →
          ((clauses.get' k lt).get' index bound = none) ∨
          ((clauses.get' k lt).get' index bound = some parity)

theorem isPure_of_PureTail_at_zero{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
                (index: Nat)(bound : index < n)(parity : Bool) :
                  HasPureTail clauses index bound parity zero →
                  IsPure clauses index bound parity := by
                    intro hyp
                    intro k
                    intro kw
                    exact hyp k kw  (Nat.zero_le k)
                    done

theorem pureTail_at_end{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
            (index: Nat)(bound : index < n)(parity : Bool)(m: Nat)(le: num_clauses ≤ m):
            HasPureTail clauses index bound parity m := by
                  intro k
                  intro kw
                  intro ineq
                  let inq := Nat.le_trans le ineq
                  let inq2 := Nat.lt_of_lt_of_le kw inq
                  exact (False.elim (Nat.lt_irrefl k inq2))
                  done

structure PureVarTail{num_clauses n : Nat}(clauses : Vector  (Clause n) num_clauses)
                      (index: Nat)(bound : index < n)(parity : Bool)(m: Nat) where
  evidence : HasPureTail clauses index bound parity m

def varIsPureRec{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) :
  (num_clauses: Nat) →  (clauses : Vector  (Clause n) num_clauses) →
    (m: Nat) → Option (PureVarTail clauses index bound parity m) →
    Option (IsPureVar clauses index bound parity) :=
    fun num_clauses clauses m =>
    match m with
    | zero => fun opt =>
        opt.map (fun pb => ⟨isPure_of_PureTail_at_zero clauses index bound parity pb.evidence⟩)
    | p + 1 =>
      fun opt =>
        match opt with
        | none => none
        | some pureBeyondEv =>
          if pw : p < num_clauses then
            let head := (clauses.get' p pw).get' index bound
              if pf : (head = none) ∨  (head = some parity) then
                let evidence : HasPureTail clauses index bound parity p :=
                  by
                    intro k
                    intro kw
                    intro ineq
                    cases Nat.eq_or_lt_of_le ineq with
                    | inl eql =>
                      let lem1 : clauses.get' p pw = clauses.get' k kw := by
                        apply witness_independent
                        exact eql
                      rw [← lem1]
                      exact pf
                    | inr l2 =>
                      exact pureBeyondEv.evidence k kw l2
                varIsPureRec index bound parity num_clauses clauses p (some ⟨evidence⟩)
              else none
          else
            none -- can recurse here but never called so making TCO easy

def varIsPure?{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) :
  (num_clauses: Nat) →  (clauses : Vector  (Clause n) num_clauses) →
    Option (IsPureVar clauses index bound parity) :=
    fun num_clauses clauses =>
      varIsPureRec index bound parity num_clauses clauses num_clauses
        (some ⟨pureTail_at_end clauses index bound parity num_clauses (Nat.le_refl _)⟩)

def findPureAux{n : Nat} : (num_clauses: Nat) →  (clauses : Vector  (Clause (n +1)) num_clauses) →
  (ub: Nat) → (lt : ub < n + 1) →
      Option (HasPureVar clauses) :=
      fun num_clauses clauses ub =>
        match ub with
        | zero =>
          fun lt =>
           match (varIsPure? zero lt true num_clauses clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk zero lt true evidence
              ) with
              | none =>
                (varIsPure? zero lt false num_clauses clauses).map (
                  fun ⟨evidence⟩ =>
                    HasPureVar.mk zero lt false evidence
                    )
              | some pv => some pv
        | l + 1 =>
          fun lt =>
            let atCursor :=
                match (varIsPure? l (le_step  (le_of_succ_le_succ lt)) true num_clauses clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) true evidence
                ) with
                | none =>
                (varIsPure? l (le_step (le_of_succ_le_succ lt)) false num_clauses clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) false evidence
                )
                | some pv => some pv
            match atCursor with
            | some res => some res
            |none =>
              findPureAux num_clauses clauses l (le_step (le_of_succ_le_succ lt))

def hasPure?{n : Nat}{num_clauses: Nat}(clauses : Vector  (Clause (n +1)) num_clauses)
             : Option (HasPureVar clauses) :=
          findPureAux num_clauses clauses n (Nat.le_refl _)
