open Nat

/-
The code that is necessary to represent a SAT problem and the associated propositions
corresponding to its satisfiability. Also a theorem that `isSat` and `isUnsat` are
exclusive.
-/

def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

inductive Vector (α : Type) : Nat → Type where 
  | nil : Vector α zero
  | cons{n: Nat}(head: α) (tail: Vector  α n) : Vector α  (n + 1) 
  deriving Repr

infixr:66 "+:" => Vector.cons

def Vector.coords {α : Type}{n : Nat}(v: Vector α n) : FinSeq n α :=
  fun j jw =>
  match n, v, j, jw with
  | .(zero), nil, k, lt => nomatch lt
  | m + 1, cons head tail, zero, lt => head
  | m + 1, cons head tail, j + 1, w =>  tail.coords j (Nat.le_of_succ_le_succ w)

abbrev Clause(n : Nat) : Type := Vector (Option Bool) n

abbrev Valuation(n: Nat) : Type := Vector Bool n

abbrev varSat (clVal: Option Bool)(valuationVal : Bool) : Prop := clVal = some valuationVal

abbrev clauseSat {n: Nat}(clause : Clause n)(valuation: Valuation n) := 
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause.coords k b) (valuation.coords k b)

def isSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                ((clauses.coords p pw).coords k kw) = some (valuation.coords k kw)

def isUnSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                ((clauses.coords p pw).coords k kw) = some (valuation.coords k kw))

theorem not_sat_and_unsat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom):
    isSat clauses → isUnSat clauses → False := by intro ⟨v, p⟩ h2 ; exact h2 v p