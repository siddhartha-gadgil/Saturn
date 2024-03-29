import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
open Nat
open FinSeq

/-!
If a SAT problem is not satisfiable, then there is a resolution tree that proves it.

Here we define the resolution tree as a structure, building up from resolution triples,
which are proofs of a clause by resolution from other clauses. The apex of the tree is the
empty clause, which is a contradiction.

We also construct lifts of a resolution tree from a branch. The lift is either a contradiction
or the proof of a unit clause associated to a branch.
-/

theorem not_not_eq{bf b bb : Bool} : Not (b = bf) → Not (bb = bf) → b = bb :=
  match bf with
  | true => fun w ww =>
    Eq.trans (eq_false_of_ne_true w) (Eq.symm (eq_false_of_ne_true ww))
  | false => fun w ww =>
    Eq.trans (eq_true_of_ne_false w) (Eq.symm (eq_true_of_ne_false ww))

/-
The structure `Join` corresponds to the values of a literal in the three clauses in a proof
by resolution, with the literal not the literal being resolved, i.e., the one that appears
with opposite signs.
-/
inductive IsJoin : Option Bool → Option Bool → Option Bool → Prop  where
  | noneNone : IsJoin none none none
  | noneSome : (b : Bool) → IsJoin none (some b) (some b)
  | someNone : (b : Bool) → IsJoin (some b) none (some b)
  | someSome : (b : Bool) →  IsJoin (some b) (some b) (some b)

-- Join given the bottom literals and consistency
def getJoin (bf : Bool)(left right : Option Bool) :
  Not (left = some bf) → Not (right = some bf) →
    Σ' (top : Option Bool),  IsJoin left right top :=
      match left with
      | none =>
        match right with
        | none => fun _ _ => ⟨none, .noneNone ⟩
        | some b => fun _ w =>
          if c: b = bf then
            by simp [c] at w
          else
            ⟨some b, .noneSome b⟩
      | some b =>
        fun w =>
          if c: b = bf then
            by simp [c] at w
          else
            match right with
            | none =>
              fun _ => ⟨some b, .someNone b⟩
            | some bb =>
              fun wr =>
                have lem1 : Not (bb = bf) := by
                  intro hyp
                  exact (wr (congrArg some hyp))
                have lem2 : bb = b := not_not_eq lem1 c
                ⟨some b, by
                  rw [lem2]
                  exact .someSome b⟩

-- deduction that the top of the join is not `some bf` if the bottom ones are not
theorem top_of_join_not_positive(bf : Bool)(left right top: Option Bool): IsJoin left right top →
    Not (left = some bf) → Not (right = some bf) →
       Not (top = some bf) := by
      intro join
      induction join with
      | noneNone => intros; simp
      | noneSome b =>
        intros
        assumption
      | someNone b =>
        intros
        assumption
      | someSome b =>
        intros
        assumption

-- valuations at a literal satisy the top of a join if they satisfy the bottom literals
theorem var_resolution_step {left right top : Option Bool}(join: IsJoin left right top)
      (valuationVal : Bool) : Or (VarSat left valuationVal) (VarSat right valuationVal) →
          (VarSat top valuationVal)  := by
        intro hyp
        cases hyp with
        | inl heq =>
          induction join with
          | noneNone =>
            assumption
          | noneSome b =>
            injection heq
          | someNone b =>
            assumption
          | someSome b =>
            assumption
        | inr heq =>
          induction join with
          | noneNone =>
            assumption
          | noneSome b =>
            assumption
          | someNone b =>
            injection heq
          | someSome b =>
            assumption

/- the resolution triple. the `pivot` is where we have `¬ P` on the left and `P` on the right.
 at the rest of the literals we have joins.
-/
structure ResolutionTriple{n: Nat}(left right top : Clause (n + 1)) where
  pivot : Nat
  pivotLt : pivot < n + 1
  leftPivot : left.get' pivot pivotLt = some false
  rightPivot : right.get' pivot pivotLt = some true
  topPivot : top.get' pivot pivotLt = none
  joinRest : (k : Nat) → (w : k < n) →
    IsJoin  (left.get' (skip pivot k) (skip_le_succ w))
          (right.get' (skip pivot k) (skip_le_succ w))
          (top.get' (skip pivot k) (skip_le_succ w))
deriving Repr

-- opposite units resolve to a contradiction
def unitTriple(n : Nat)(k: Nat)(lt : k < n + 1) :
        ResolutionTriple (unitClause n false  k lt) (unitClause n true k lt) (contradiction (n + 1)) :=
          ⟨k, lt,
            unitClause_at_literal n false k lt ,
            unitClause_at_literal n true k lt,
            by
              rw [get'_contradiction]
              done,
            fun j jw => by
              rw [unitClause_skipping_literal n false k lt j jw, unitClause_skipping_literal n true k lt j jw]
              simp [get'_contradiction]
              apply IsJoin.noneNone
                      ⟩

-- if a valuation satisfies the bottom two clauses, it satisfies the top clause as a proposition
theorem triple_step{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (ClauseSat left valuation) →
        (ClauseSat right valuation) → (ClauseSat top valuation) :=
          fun valuation =>
            fun ⟨kl, ⟨llt, wl⟩⟩ =>
              fun ⟨kr, ⟨rlt, wr⟩⟩ =>
                if c : valuation.get' (triple.pivot) (triple.pivotLt)  then
                    -- the left branch survives
                    if cc : kl = triple.pivot then by
                      have lem1 : left.get' kl llt  =
                        left.get' triple.pivot triple.pivotLt := by
                        apply witness_independent
                        apply cc
                      have lem2 : valuation.get' kl llt =
                        valuation.get' triple.pivot triple.pivotLt := by
                        apply witness_independent
                        apply cc
                      rw [Vector.get'] at lem1
                      have lem3 : some true = some false := by
                        rw [← c, ← lem2, Vector.get', ← wl, lem1, triple.leftPivot]
                      simp at lem3
                    else
                      let i := skipInverse triple.pivot kl cc
                      let eql := skipInverse_eq triple.pivot kl cc
                      let iw : i < n := skip_preimage_lt triple.pivotLt llt eql
                      let leftLem :
                        left.get' kl llt = left.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let rightLem :
                        right.get' kl llt = right.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let topLem :
                        top.get' kl llt = top.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let join : IsJoin (left.get' kl llt) (right.get' kl llt) (top.get' kl llt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done
                      ⟨kl, ⟨llt, var_resolution_step join (valuation.get' kl llt) (Or.inl (wl))⟩⟩
                else
                    let cc := eq_false_of_ne_true c
                    if ccc : kr = triple.pivot then
                      by
                      have lem1 : right.get' kr rlt =
                            right.get' triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                      have lem2 : valuation.get' kr rlt =
                            valuation.get' triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                      rw [Vector.get'] at lem1
                      have lem5 : some false = some true := by
                        rw [← cc, ← lem2, Vector.get', ← wr, lem1, triple.rightPivot]
                      simp at lem5
                    else
                      let i := skipInverse triple.pivot kr ccc
                      let eql := skipInverse_eq triple.pivot kr ccc
                      let iw : i < n := skip_preimage_lt triple.pivotLt rlt eql
                      let leftLem :
                        left.get' kr rlt = left.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let rightLem :
                        right.get' kr rlt = right.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let topLem :
                        top.get' kr rlt = top.get' (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let join : IsJoin (left.get' kr rlt) (right.get' kr rlt) (top.get' kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                      ⟨kr, ⟨rlt, var_resolution_step join (valuation.get' kr rlt) (Or.inr (wr))⟩⟩


/--
A resolution tree, with leaves given clauses assumed to be satisfied and nodes resolution steps.
We show that the apex is satisfied by a valuation if the given clauses are satisfied.
-/
inductive ResolutionTree{num_clauses n: Nat}
      (clauses : Vector   (Clause (n + 1)) num_clauses) : (Clause (n + 1)) → Type  where
  | assumption : (index : Nat) → (indexBound : index < num_clauses ) → (top : Clause (n + 1)) →
          clauses.get' index indexBound = top →
          ResolutionTree clauses top
  | resolve : (left right top : Clause (n + 1)) →
                (leftTree : ResolutionTree clauses left) →
                (rightTree: ResolutionTree clauses right) →
                ResolutionTriple left right top
                → ResolutionTree clauses top

open Std
def ResolutionTree.rp {num_clauses n: Nat}{clauses : Vector  (Clause (n + 1)) num_clauses}
      {top : Clause (n + 1)}
        (tree: ResolutionTree clauses top) : Nat →  Format := by
      cases tree
      case assumption j jw eqn  =>
        intro n
        exact (reprPrec
          (clauseSummary <| clauses.get' j jw) n) ++ " ← assumption "
            ++ repr j
      case resolve left right leftTree rightTree triple =>
        intro m
        let deduction :=
          (reprPrec (clauseSummary top) m) ++ " ← " ++
          (reprPrec (clauseSummary left) m) ++ " & " ++
          (reprPrec (clauseSummary right) m) ++  " with pivot: " ++
          (reprPrec triple.pivot m)
        let leftTreeRp := leftTree.rp (m + 2)
        let rightTreeRp := rightTree.rp (m + 2)
        exact deduction ++ .line ++ "· " ++ .group (leftTreeRp) ++ .line ++ "· " ++ .group (rightTreeRp)



instance : Repr (ResolutionTree clauses top) :=
  ⟨ fun tree => tree.rp⟩

/-- proof of the apex from the assumptions as propositions -/
theorem resolutionToProof{num_clauses n: Nat}(clauses : Vector (Clause (n + 1)) num_clauses)(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top) →  (valuation :Valuation (n + 1))→
    ((j : Nat) → (jw : j < num_clauses) → ClauseSat (clauses.get' j jw) valuation) →
            ClauseSat top valuation := by
      intro tree
      induction tree
      case assumption j jw top eqn =>
        intro valuation base
        rw [← eqn]
        apply base
      case resolve left right top' _ _ triple lih rih  =>
        intro valuation base
        let leftBase : ClauseSat left valuation := by
          apply lih valuation base
        let rightBase : ClauseSat right valuation := by
          apply rih valuation base
        exact triple_step left right top' triple valuation leftBase rightBase

-- unsat from a resolution tree
theorem tree_unsat{num_clauses n: Nat}(clauses : Vector (Clause (n + 1)) num_clauses):
      ResolutionTree clauses (contradiction (n + 1)) → IsUnSat clauses :=
  fun tree valuation hyp =>
    contradiction_is_false _ valuation $
      resolutionToProof clauses (contradiction (n + 1)) tree valuation hyp

/-!
Pieces for building trees.
-/

def mergeUnitTrees{num_clauses n: Nat}{clauses : Vector (Clause (n + 1)) num_clauses}
                (focus : Nat)(focusLt : focus < n + 1)
                (left: ResolutionTree clauses (unitClause n false focus focusLt))
                (right: ResolutionTree clauses (unitClause n true focus focusLt)) :
                ResolutionTree clauses (contradiction (n + 1)) :=
                let tree := ResolutionTree.resolve
                      (unitClause n false focus focusLt)
                      (unitClause n true focus focusLt)
                      (contradiction (n + 1))
                     left right (unitTriple n focus focusLt)
                tree

def mergeAlignUnitTrees{num_clauses n: Nat}{branch : Bool}{clauses : Vector (Clause (n + 1)) num_clauses}
                {focus : Nat}{focusLt : focus < n + 1}
                 (first: ResolutionTree clauses (unitClause n branch focus focusLt))
                (second: ResolutionTree clauses (unitClause n (not branch) focus focusLt)) :
                ResolutionTree clauses (contradiction (n + 1)) :=
                match branch, first, second with
                | false, left, right =>
                    mergeUnitTrees focus focusLt left right
                | true, right, left =>
                    mergeUnitTrees focus focusLt left right

def unitProof{num_clauses n: Nat}{branch : Bool}{clauses : Vector (Clause (n + 1)) num_clauses}
                {focus : Nat}{focusLt : focus < n + 1}{j : Nat}{jw : j < num_clauses}
                (eqn: clauses.get' j jw = unitClause n branch focus focusLt):
                ResolutionTree clauses (unitClause n branch focus focusLt) :=
                  ResolutionTree.assumption j jw (unitClause n branch focus focusLt) eqn

-- Lift of a resolution tree with apex `top` from the branch corresponding to `focus` and `topFocus`
structure BranchResolutionProof{num_clauses n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : Vector (Clause (n + 1)) num_clauses)(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionTree clauses (Vector.ofFn' (insert topFocus n focus focusLt top.get'))

/-
Lift of a resolution tree with apex a contradiction, i.e., a resolution proof of unsat,
 from the branch corresponding to `focus` and `topFocus`. The lift could be either a contradiction
 or the proof of a unit clause.
-/
inductive LiftedResTree{num_clauses n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) num_clauses) where
    | contra : ResolutionTree clauses (contradiction (n + 2)) →
                  LiftedResTree branch focus focusLt clauses
    | unit : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) →
                  LiftedResTree branch focus focusLt clauses

theorem not_eq_implies_eq_not(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
  match b with
  | true => fun w => eq_false_of_ne_true w
  | false => fun w => eq_true_of_ne_false w

-- if none of the assumption clauses are `some bf` at a literal, the apex is not
theorem trees_preserve_notsomebranch{num_clauses n : Nat}{clauses : Vector (Clause (n + 1)) num_clauses}
        (bf: Bool)(k : Nat)(kw : k < n + 1)
        (base : (j : Nat) → (lt : j < num_clauses) →
          Not ((clauses.get' j lt).get' k kw = some bf)) :
        (top : Clause (n + 1)) →
        (tree : ResolutionTree clauses top) →
        Not (top.get' k kw = some bf) :=
          fun top tree =>
          match tree with
          | ResolutionTree.assumption ind  bd .(top) chk =>
            fun  hyp => by
              have lem1 : Not (top.get' k kw = some bf) := by
                      rw [←  chk]
                      exact (base ind bd)
              contradiction
          | ResolutionTree.resolve left right .(top) leftTree rightTree triple =>
            fun hyp =>
              let leftLem :=
                trees_preserve_notsomebranch bf k kw base left leftTree
              let rightLem :=
                trees_preserve_notsomebranch bf k kw base right rightTree
              if c : k = triple.pivot then
                  match bf, k, c, kw, leftLem, rightLem with
                  | false, .(triple.pivot), rfl, .(triple.pivotLt), lL, _ =>
                        lL (triple.leftPivot)
                  | true, .(triple.pivot), rfl, .(triple.pivotLt), _, rL =>
                        rL (triple.rightPivot)
              else by
                  let j := skipInverse triple.pivot k c
                  let eqn  := skipInverse_eq triple.pivot k c
                  let jw := skip_preimage_lt triple.pivotLt kw eqn
                  let joinIm := triple.joinRest j jw
                  match (skip triple.pivot j), eqn, (skip_le_succ jw), joinIm with
                  | .(k), rfl, .(kw), join =>
                    apply top_of_join_not_positive bf
                        (left.get' k kw) (right.get' k kw) (top.get' k kw) join
                          leftLem rightLem
                    exact hyp
