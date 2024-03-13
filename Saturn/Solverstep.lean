import Saturn.FinSeq
import Saturn.Vector
open Nat
open Vector
open FinSeq

/-
We define structures that correspond to restricting a SAT problem to a branch as in the
DPLL algorithm.
-/
def boundOpt(n: Nat) : Option (Nat) → Prop
  | none => True
  | some b => b < n

def boundOptSucc(n: Nat)(p: Option Nat) : boundOpt n p → boundOpt (n + 1) (p.map (. + 1)) :=
  match p with
  | none => fun _ => True.intro
  | some a => fun h : a < n => succ_lt_succ h

/-
Reduction of clauses, specifically:
  - a new finite sequence of clauses with length one less (the `focus` variable is dropped)
  - an optional map on indices from the original to the new finite sequence.
  - a map on indices from the new finite sequence to the original.
  - witnesses to bounds so we have maps between the finite sequences.
-/
structure ReductionClauses{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses) where
  num_reducedClauses : Nat
  restClauses : Vector  (Clause n) num_reducedClauses
  forwardVec : Vector (Option Nat) num_clauses
  forwardWit : (k : Fin num_clauses) → boundOpt num_reducedClauses (forwardVec.get' k.val k.isLt)
  reverseVec : Vector Nat num_reducedClauses
  reverseWit : (k : Fin num_reducedClauses) →
    reverseVec.get' k.val k.isLt < num_clauses

abbrev ReductionClauses.forward{num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}
      (rc: ReductionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < num_clauses) → Option Nat := rc.forwardVec.get'

abbrev ReductionClauses.reverse{num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}
      (rc: ReductionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < rc.num_reducedClauses) → Nat := rc.reverseVec.get'

/- The condition that if a clause is mapped to `none` (i.e., dropped), then the value at
  the `focus` index is `some bf` for the chosen branch `bf`, i.e., the clause holds.
-/
structure DroppedProof
  {num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < num_clauses) → rc.forward k w =
        none → (clauses.get' k w).get' focus focusLt = some branch

-- if a clause is not dropped, its image is the restricted clause
structure ForwardRelation{num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < num_clauses) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.num_reducedClauses) →  delete focus focusLt (clauses.get' k w).get' =
        (rc.restClauses.get' j jw).get'

-- a new clause is the restriction of its image under the reverse map
structure ReverseRelation{num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.num_reducedClauses) →
      (rc.restClauses.get' k w).get' = delete focus focusLt
        (clauses.get' (rc.reverse k w) (rc.reverseWit ⟨k, w⟩)).get'

-- the image of a new clause under the reverse map is not `some bf` at the `focus` index.
structure NonPosReverse{num_clauses n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) num_clauses}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.num_reducedClauses)  →
      Not (
        (clauses.get' (rc.reverse k w) (rc.reverseWit ⟨k, w⟩)).get' focus focusLt = some branch)

-- the maps and conditions for the new clauses
structure ReductionData{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses) where
    restrictionClauses : ReductionClauses branch focus focusLt clauses
    droppedProof : DroppedProof restrictionClauses
    forwardRelation : ForwardRelation restrictionClauses
    reverseRelation : ReverseRelation restrictionClauses
    nonPosReverse : NonPosReverse restrictionClauses
