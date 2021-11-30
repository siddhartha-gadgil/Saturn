import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
open Nat
open Vector
open FinSeq

/-
We define structures that correspond to restricting a SAT problem to a branch as in the 
DPLL algorithm. We show that solutions in a branch can be pulled back to solutions to the
original problem.

We also define unit clauses, which are clauses that have only one literal, and pure clauses.
We define functions that find unit clauses and pure variables in a finite sequence of clauses,
with proofs.
-/
def boundOpt(n: Nat) : Option (Nat) → Prop
  | none => True
  | some b => b < n

def boundOptSucc(n: Nat)(p: Option Nat) : boundOpt n p → boundOpt (n + 1) (p.map (. + 1)) :=
  match p with
  | none => fun h => True.intro
  | some a => fun h : a < n => succ_lt_succ h

/-
Restriction of clauses, specifically:
  - a new finite sequence of clauses with length one less (the `focus` variable is dropped)
  - an optional map on indices from the original to the new finite sequence.
  - a map on indices from the new finite sequence to the original.
  - witnesses to bounds so we have maps between the finite sequences.
-/
structure RestrictionClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector  (Clause n) codom
  forwardVec : Vector (Option Nat) dom
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forwardVec.coords k w)
  reverseVec : Vector Nat codom
  reverseWit : (k : Nat) → (w : k < codom) → reverseVec.coords k w < dom
  
def RestrictionClauses.forward{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: RestrictionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < dom) → Option Nat := rc.forwardVec.coords

def RestrictionClauses.reverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: RestrictionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < rc.codom) → Nat := rc.reverseVec.coords

/- The condition that if a clause is mapped to `none` (i.e., dropped), then the value at 
  the `focus` index is `some bf` for the chosen branch `bf`, i.e., the clause holds.
-/
structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (Vector.coords (clauses.coords k w) focus focusLt = some branch)

-- if a clause is not dropped, its image is the restricted clause
structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  delete focus focusLt (Vector.coords (clauses.coords k w)) = 
      Vector.coords (rc.restClauses.coords j jw)

-- a new clause is the restriction of its image under the reverse map 
structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      Vector.coords (rc.restClauses.coords k w) = delete focus focusLt 
        (Vector.coords (clauses.coords (rc.reverse k w) (rc.reverseWit k w)))

-- the image of a new clause under the reverse map is not `some bf` at the `focus` index.
structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not (
        Vector.coords (clauses.coords (rc.reverse k w) (rc.reverseWit k w)) focus focusLt = some branch)

-- the maps and conditions for the new clauses
structure RestrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom) where
    restrictionClauses : RestrictionClauses branch focus focusLt clauses
    droppedProof : DroppedProof restrictionClauses
    forwardRelation : ForwardRelation restrictionClauses
    reverseRelation : ReverseRelation restrictionClauses
    nonPosReverse : NonPosReverse restrictionClauses 

-- pull back of solutions from a branch to the original problem
def pullBackSolution{dom n: Nat}(branch: Bool)(focus : Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom)(rc: RestrictionClauses branch focus focusLt clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (valuation : Valuation n) → 
        ((j : Nat) → (jw : j < rc.codom) → clauseSat (rc.restClauses.coords j jw) valuation) → 
        (j : Nat) → (jw : j < dom) →  
          clauseSat (clauses.coords j jw) (FinSeq.vec (insert branch n focus focusLt valuation.coords)) := 
        fun valuation pf =>
          fun k w => 
            let splitter := (rc.forward k w)
            match eq:splitter with
            | none => 
              let lem1 : Vector.coords (clauses.coords k w) focus focusLt = some branch := dp.dropped k w eq
              let lem2 : insert branch n focus focusLt valuation.coords focus focusLt = branch := by 
                apply insert_at_focus
                done
              let lem3 : Vector.coords (clauses.coords k w) focus focusLt = 
                some (insert branch n focus focusLt valuation.coords focus focusLt) := 
                by
                  rw [lem1]
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
              let lem4 : (Vector.coords (Vector.coords clauses k w) focus focusLt) = some (
                  (Vector.coords 
                    (FinSeq.vec (insert branch n focus focusLt 
                      (Vector.coords valuation))) focus focusLt)) := 
                      by 
                        rw [seq_to_vec_coords (insert branch n focus focusLt 
                      (Vector.coords valuation))]
                        rw [lem3]
                        done
              ⟨focus, focusLt, lem4⟩
            | some j => 
              let bound := rc.forwardWit k w 
              let jWitAux : boundOpt rc.codom (some j) := by
                rw [←  eq]
                exact bound
                done
              let jWit : j < rc.codom := jWitAux
              let lem1 := fr.forwardRelation k w j eq jWit
              let ⟨i, iw, vs⟩ := pf j jWit
              let lem2 : Vector.coords (rc.restClauses.coords j jWit) i iw = 
                      some (valuation.coords i iw) := vs
              let lem3 : delete focus focusLt (Vector.coords (clauses.coords k w)) i iw =
                  some (valuation.coords i iw) := 
                    by
                    rw [←  lem2]
                    rw [lem1]
                    done
              let lem4 : delete focus focusLt (Vector.coords (clauses.coords k w)) i iw =
                (Vector.coords (clauses.coords k w)) (skip focus i) (skip_le_succ iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw) =
                                  valuation.coords i iw := by
                                    apply insert_at_image
                                    done
              let lem6 : (Vector.coords (clauses.coords k w)) (skip focus i) (skip_le_succ iw) =
                          some (insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw)) := by
                              rw [← lem4]
                              rw [lem3]
                              rw [lem5]
                              done
              let lem7 : (Vector.coords (Vector.coords clauses k w) (skip focus i) (skip_le_succ iw)) =
                some (
                  (Vector.coords (FinSeq.vec (insert branch n focus focusLt (Vector.coords valuation))) 
                    (skip focus i) (skip_le_succ iw))) := 
                      by
                        rw [seq_to_vec_coords (insert branch n focus focusLt (Vector.coords valuation))]
                        rw [lem6]
                        done
              ⟨skip focus i, skip_le_succ iw, lem7⟩
