import Mathlib.Data.Vector
open Nat


/-
The code that is necessary to represent a SAT problem and the associated propositions
corresponding to its satisfiability. Also a theorem that `isSat` and `isUnsat` are
exclusive.
-/

@[inline] def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

-- inductive Vector (α : Type) : Nat → Type where
--   | nil : Vector α zero
--   | cons{n: Nat}(head: α) (tail: Vector  α n) : Vector α  (n + 1)
--   deriving Repr

infixr:66 "+:" => Vector.cons


namespace Vector
def get' {α : Type}{n : Nat}(v: Vector α n) : FinSeq n α :=
  fun j jw => v.get ⟨j, jw⟩

end Vector

abbrev Clause(n : Nat) : Type := Vector (Option Bool) n

def clauseSummary {n: Nat}(clause : Clause n) : List <| Nat × Bool :=
  let padded := clause.toList.mapIdx (fun i x => (i, x))
  padded.filterMap (fun (i, x) => match x with
    | some b => some (i, b)
    | none => none)

abbrev Valuation(n: Nat) : Type := Vector Bool n

abbrev varSat (clVal: Option Bool)(valuationVal : Bool) : Prop := clVal = some valuationVal

abbrev clauseSat {n: Nat}(clause : Clause n)(valuation: Valuation n) :=
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause.get' k b) (valuation.get' k b)

def isSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∃ valuation : Valuation (n + 1),
           ∀ (p : Nat),
            ∀ pw : p < dom,
              ∃ (k : Nat), ∃ (kw : k < n + 1),
                ((clauses.get' p pw).get' k kw) = some (valuation.get' k kw)

def isUnSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∀ valuation : Valuation (n + 1),
           Not (∀ (p : Nat),
            ∀ pw : p < dom,
              ∃ (k : Nat), ∃ (kw : k < n + 1),
                ((clauses.get' p pw).get' k kw) = some (valuation.get' k kw))

theorem not_sat_and_unsat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom):
    isSat clauses → isUnSat clauses → False := by intro ⟨v, p⟩ h2 ; exact h2 v p
