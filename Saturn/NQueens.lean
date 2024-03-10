import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.DPLL

/-
The N-Queens problem as a SAT problem.
-/

def pairs(n: Nat) : List (Nat × Nat) :=
  List.bind
    (List.range n)
    (fun x =>
      (List.range n).map (fun y => (x, y)))

def row (index n: Nat) : Nat := index / n
def col (index n: Nat) : Nat := index % n

def threaten (index1 index2 n : Nat) : Bool :=
  (row index1 n == row index2 n) || (col index1 n == col index2 n) ||
  ((row index1 n) + (col index1 n) == (row index2 n) + (col index2 n)) ||
  ((row index1 n) + (col index2 n) == (row index2 n) + (col index1 n))

def forbiddenPairs (n: Nat) : List (Nat × Nat) :=
  (pairs (n * n)).filter (fun (x, y) => x < y && threaten x y n)

def forbidPairClauses (n: Nat) : List (Clause (n * n)) :=
  (forbiddenPairs n).map (
    fun (x, y) =>
      Vector.ofFn (fun ⟨i, _⟩  =>
        if i == x || i == y then some false else none)
      )

def rowClause(r n: Nat) : Clause (n * n) :=
  Vector.ofFn (fun ⟨index, _⟩ => if row index n == r then some true else none)

def rowClauses (n: Nat) : List (Clause (n * n)) :=
  (List.range n).map (fun r => rowClause r n)

def Vector.ofList{α : Type}(l : List α) : Vector α l.length :=
  match l with
  | [] => Vector.nil
  | h :: t => Vector.cons h (Vector.ofList t)

def queensClauses(n: Nat) :=
  Vector.ofList <| rowClauses n ++ (forbidPairClauses n)
