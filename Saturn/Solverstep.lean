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
  | none => fun h => True.intro
  | some a => fun h : a < n => succ_lt_succ h

/-
Reduction of clauses, specifically:
  - a new finite sequence of clauses with length one less (the `focus` variable is dropped)
  - an optional map on indices from the original to the new finite sequence.
  - a map on indices from the new finite sequence to the original.
  - witnesses to bounds so we have maps between the finite sequences.
-/
structure ReductionClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector  (Clause n) codom
  forwardVec : Vector (Option Nat) dom
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forwardVec.coords k w)
  reverseVec : Vector Nat codom
  reverseWit : (k : Nat) → (w : k < codom) → reverseVec.coords k w < dom
  
abbrev ReductionClauses.forward{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: ReductionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < dom) → Option Nat := rc.forwardVec.coords

abbrev ReductionClauses.reverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: ReductionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < rc.codom) → Nat := rc.reverseVec.coords

/- The condition that if a clause is mapped to `none` (i.e., dropped), then the value at 
  the `focus` index is `some bf` for the chosen branch `bf`, i.e., the clause holds.
-/
structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (clauses.coords k w).coords focus focusLt = some branch

-- if a clause is not dropped, its image is the restricted clause
structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  delete focus focusLt (clauses.coords k w).coords = 
        (rc.restClauses.coords j jw).coords

-- a new clause is the restriction of its image under the reverse map 
structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      (rc.restClauses.coords k w).coords = delete focus focusLt 
        (clauses.coords (rc.reverse k w) (rc.reverseWit k w)).coords

-- the image of a new clause under the reverse map is not `some bf` at the `focus` index.
structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: ReductionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not (
        (clauses.coords (rc.reverse k w) (rc.reverseWit k w)).coords focus focusLt = some branch)

-- the maps and conditions for the new clauses
structure ReductionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom) where
    restrictionClauses : ReductionClauses branch focus focusLt clauses
    droppedProof : DroppedProof restrictionClauses
    forwardRelation : ForwardRelation restrictionClauses
    reverseRelation : ReverseRelation restrictionClauses
    nonPosReverse : NonPosReverse restrictionClauses 
