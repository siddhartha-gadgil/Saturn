import Mathlib.Data.Vector
open Nat
/-!
## SATurn Core

The code that is necessary to represent a SAT problem and the associated propositions corresponding to its satisfiability. Also a theorem that `isSat` and `isUnsat` are exclusive.

Many structures and functions are remnants of an approach from when Lean 4 was young and Mathlib 4 almost non-existent. The code can be refactored to avoid these.
-/

/--
A finite sequence represented as a function from the set of natural numbers less than `n` to a type `α`.
-/
@[inline] def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

infixr:66 "+:" => Vector.cons


namespace Vector
/--
Variant of `Vector.get` used for compatibility with older code.
-/
def get' {α : Type}{n : Nat}(v: Vector α n) : FinSeq n α :=
  fun j jw => v.get ⟨j, jw⟩

end Vector

/--
A *clause*, represented as a vector of `Option Bool` of length `n`. The `Option` type is used to represent the absence of a variable in the clause
and the `Bool` represents whether we include a variable or its negation.
-/
abbrev Clause(n : Nat) : Type := Vector (Option Bool) n

/--
A more compact representation of a clause, essentially as a `HashMap` but more formally as a list of pairs.
-/
def clauseSummary {n: Nat}(clause : Clause n) : List <| Nat × Bool :=
  let padded := clause.toList.mapIdx (fun i x => (i, x))
  padded.filterMap (fun (i, x) => match x with
    | some b => some (i, b)
    | none => none)

/--
Assignment of `true` or `false` to variables.
-/
abbrev Valuation(n: Nat) : Type := Vector Bool n

/--
Whether assignment to variable shows truth of statement.
-/
abbrev VarSat (clVal: Option Bool)(valuationVal : Bool) : Prop := clVal = some valuationVal

/--
Whether valuation satisfies a clause.
-/
abbrev ClauseSat {n: Nat}(clause : Clause n)
    (valuation: Valuation n) : Prop :=
  ∃ (k : Nat), ∃ (b : k < n), VarSat (clause.get ⟨k, b⟩) (valuation.get ⟨k, b⟩)

/--
Whether a collection of clauses is satisfiable.
-/
def IsSat{num_clauses n: Nat}(clauses : Vector (Clause (n + 1)) num_clauses) : Prop :=
          ∃ valuation : Valuation (n + 1),
           ∀ (p : Nat),
            ∀ pw : p < num_clauses,
              ∃ (k : Nat), ∃ (kw : k < n + 1),
                ((clauses.get ⟨p, pw⟩).get ⟨k, kw⟩) = some (valuation.get ⟨k, kw⟩)

/--
Whether a collection of clauses is unsatisfiable.
-/
def IsUnSat{num_clauses n: Nat}(clauses : Vector (Clause (n + 1)) num_clauses) : Prop :=
          ∀ valuation : Valuation (n + 1),
           Not (∀ (p : Nat),
            ∀ pw : p < num_clauses,
              ∃ (k : Nat), ∃ (kw : k < n + 1),
                ((clauses.get ⟨p, pw⟩).get ⟨k, kw⟩) = some (valuation.get ⟨k, kw⟩))

/--
A collection of clauses cannot be `SAT` and `UNSAT`
-/
theorem not_sat_and_unsat{num_clauses n: Nat}(clauses : Vector (Clause (n + 1)) num_clauses):
    IsSat clauses → IsUnSat clauses → False := by intro ⟨v, p⟩ h2 ; exact h2 v p
