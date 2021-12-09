import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
open Nat
open FinSeq

/-
If a SAT problem is not satisfiable, then there is a resolution tree that proves it. 
Here we define the resolution tree as a structure, building up from resolution triples, 
which are proofs of a clause by resolution from other clauses. The apex of the tree is the
empty clause, which is a contradiction.

We also construct lifts of a resolution tree from a branch. The lift is either a contradiction
or the proof of a unit clause associated to a branch.
-/

theorem not_not_eq(bf b bb : Bool) : Not (b = bf) → Not (bb = bf) → b = bb :=
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
inductive Join (left right top : Option Bool) where
  | noneNone : (left = none) → (right = none) → (top = none)→ Join left right top 
  | noneSome : (b : Bool) → (left = none) → (right = some b) → (top = some b)→ Join left right top
  | someNone : (b : Bool) → (left = some b) → (right = none) → (top = some b)→ Join left right top
  | someSome : (b : Bool) → (left = some b) → (right = some b) → (top = some b)→ Join left right top

-- Join given the bottom literals and consistency
def getJoin (bf : Bool)(left right : Option Bool) :
  Not (left = some bf) → Not (right = some bf) → 
    Σ (top : Option Bool),  Join left right top :=
      match left with
      | none => 
        match right with
        | none => fun _ _ => ⟨none, Join.noneNone rfl rfl rfl⟩
        | some b => fun _ w => 
          if c: b = bf then 
            absurd (congrArg some c) w
          else 
            ⟨some b, Join.noneSome b rfl rfl rfl⟩
      | some b => 
        fun w =>
          if c: b = bf then 
            absurd (congrArg some c) w
          else 
            match right with
            | none => 
              fun wr => ⟨some b, Join.someNone b rfl rfl rfl⟩
            | some bb => 
              fun wr =>
                have lem1 : Not (bb = bf) := by
                  intro hyp
                  exact (wr (congrArg some hyp))
                have lem2 : bb = b := not_not_eq bf bb b lem1 c
                ⟨some b, Join.someSome b rfl (congrArg some lem2) rfl⟩

-- deduction that the top of the join is not `some bf` if the bottom ones are not
theorem top_of_join_not_positive(bf : Bool)(left right top: Option Bool): Join left right top →
    Not (left = some bf) → Not (right = some bf) → 
       Not (top = some bf) := 
        fun join =>
          match join with
          | Join.noneNone _ _ wt => fun _ _ hyp => 
            let lem := Eq.trans (Eq.symm hyp) wt
            Option.noConfusion lem
          | Join.someNone b wl _ wt => 
            fun nwl _  hyp => 
              have lem : left = some bf := by
                rw [wl]
                rw [← wt]
                assumption
                done
              nwl lem
          | Join.noneSome b _ wr wt => 
            fun _ nwr  hyp => 
              have lem : right = some bf := by
                rw [wr]
                rw [← wt]
                assumption
                done
              nwr lem
          | Join.someSome b wl _ wt => 
            fun nwl _  hyp => 
              have lem : left = some bf := by
                rw [wl]
                rw [← wt]
                assumption
                done
              nwl lem

-- valuations at a literal satisy the top of a join if they satisfy the bottom literals
theorem var_resolution_step {left right top : Option Bool}(join: Join left right top)
      (valuationVal : Bool) : Or (varSat left valuationVal) (varSat right valuationVal) → 
          (varSat top valuationVal)  :=
  fun hyp  =>
    match join with
    | Join.noneNone pl pr pt => 
      match hyp with
      | Or.inl heq => 
        let contra: none = some (valuationVal) := Eq.trans (Eq.symm pl) heq
        Option.noConfusion contra
      | Or.inr heq => 
        let contra: none = some (valuationVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra 
    | Join.someNone b pl pr pt =>
      match hyp with
      | Or.inl (heq : left = some valuationVal) => 
        have lem : top = left := Eq.trans pt (Eq.symm pl)
        Eq.trans lem heq
      | Or.inr heq => 
        let contra: none = some (valuationVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra  
    | Join.noneSome b pl pr pt =>
      match hyp with
      | Or.inl heq => 
        let contra: none = some (valuationVal) := Eq.trans (Eq.symm pl) heq
        Option.noConfusion contra
      | Or.inr heq => 
        have lem : top = right := Eq.trans pt (Eq.symm pr)
        Eq.trans lem heq  
    | Join.someSome b pl pr pt => 
      match hyp with
      | Or.inl heq => 
        have lem : top = left := Eq.trans pt (Eq.symm pl)
        Eq.trans lem heq
      | Or.inr heq => 
        have lem : top = right := Eq.trans pt (Eq.symm pr)
        Eq.trans lem heq

 
/- the resolution triple. the `pivot` is where we have `¬ P` on the left and `P` on the right.
 at the rest of the literals we have joins.
-/
structure ResolutionTriple{n: Nat}(left right top : Clause (n + 1)) where
  pivot : Nat
  pivotLt : pivot < n + 1
  leftPivot : left.coords pivot pivotLt = some false
  rightPivot : right.coords pivot pivotLt = some true
  topPivot : top.coords pivot pivotLt = none
  joinRest : (k : Nat) → (w : k < n) →  
    Join  (left.coords (skip pivot k) (skip_le_succ w)) 
          (right.coords (skip pivot k) (skip_le_succ w)) 
          (top.coords (skip pivot k) (skip_le_succ w))

-- opposite units resolve to a contradiction
def unitTriple(n : Nat)(k: Nat)(lt : k < n + 1) :
        ResolutionTriple (unitClause n false  k lt) (unitClause n true k lt) (contradiction (n + 1)) :=
          ⟨k, lt, 
            unitDiag n false k lt , 
            unitDiag n true k lt, 
            by
              rw [contra_at_none] 
              done, 
            fun j jw => Join.noneNone 
                      (unitSkip n false k lt j jw) 
                      (unitSkip n true k lt j jw) 
                      (by rw [contra_at_none])
                      ⟩

-- if a valuation satisfies the bottom two clauses, it satisfies the top clause as a proposition
theorem triple_step{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (clauseSat left valuation) → 
        (clauseSat right valuation) → (clauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, ⟨llt, wl⟩⟩ =>
              fun ⟨kr, ⟨rlt, wr⟩⟩ =>
                if c : valuation.coords (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then
                      have lem1 : left.coords kl llt = 
                        left.coords triple.pivot triple.pivotLt := by
                        apply witness_independent
                        apply cc 
                      have lem2 : valuation.coords kl llt = 
                        valuation.coords triple.pivot triple.pivotLt := by
                        apply witness_independent
                        apply cc
                      have lem3 : some true = some false := by 
                        rw [← c]
                        rw [← lem2]
                        rw [← wl]
                        rw [lem1]
                        rw [triple.leftPivot]
                      have lem4 : true = false := by 
                        injection lem3
                        assumption
                        done
                      Bool.noConfusion lem4
                    else  
                      let i := skipInverse triple.pivot kl cc 
                      let eql := skip_inverse_eq triple.pivot kl cc 
                      let iw : i < n := skip_preimage_lt triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.coords kl llt = left.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let rightLem : 
                        right.coords kl llt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let topLem : 
                        top.coords kl llt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let join : Join (left.coords kl llt) (right.coords kl llt) (top.coords kl llt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, ⟨llt, var_resolution_step join (valuation.coords kl llt) (Or.inl (wl))⟩⟩
                else
                    let cc := eq_false_of_ne_true c  
                    if ccc : kr = triple.pivot then 
                      have lem1 : right.coords kr rlt = 
                            right.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                      have lem2 : valuation.coords kr rlt = 
                            valuation.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc 
                      have lem5 : some false = some true := by
                        rw [← cc]
                        rw [← lem2]
                        rw [← wr]
                        rw [lem1]
                        rw [triple.rightPivot]
                      have lem6 : false = true := by 
                        injection lem5
                        assumption
                      Bool.noConfusion lem6
                    else  
                      let i := skipInverse triple.pivot kr ccc 
                      let eql := skip_inverse_eq triple.pivot kr ccc
                      let iw : i < n := skip_preimage_lt triple.pivotLt rlt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.coords kr rlt = left.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let rightLem : 
                        right.coords kr rlt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let topLem : 
                        top.coords kr rlt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                      let join : Join (left.coords kr rlt) (right.coords kr rlt) (top.coords kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                      ⟨kr, ⟨rlt, var_resolution_step join (valuation.coords kr rlt) (Or.inr (wr))⟩⟩

      
/-
A resolution tree, with leaves given clauses assumed to be satisfied and nodes resolution steps.
We show that the apex is satisfied by a valuation if the given clauses are satisfied.
-/
inductive ResolutionTree{dom n: Nat}
      (clauses : Vector   (Clause (n + 1)) dom) : (Clause (n + 1)) → Type  where
  | assumption : (index : Nat) → (indexBound : index < dom ) → (top : Clause (n + 1)) → 
          clauses.coords index indexBound = top → 
          ResolutionTree clauses top
  | resolve : (left right top : Clause (n + 1)) → 
                (leftTree : ResolutionTree clauses left) → 
                (rightTree: ResolutionTree clauses right) →
                ResolutionTriple left right top 
                → ResolutionTree clauses top


def ResolutionTree.toString{dom n: Nat}{clauses : Vector  (Clause (n + 1)) dom}
      {top : Clause (n + 1)}
        (rt: ResolutionTree clauses top) : String := 
      match rt with
      | ResolutionTree.assumption i iw _ _  => 
          (clauses.coords i iw).coords.list.toString
      | ResolutionTree.resolve left right .(top) leftTree rightTree triple => 
                top.toString ++ " from " ++ left.toString ++ " & " ++ right.toString  ++ 
                "; using: {" ++ 
                leftTree.toString ++ "} and {" ++ rightTree.toString ++ "}"

-- proof of the apex from the assumptions as propositions
theorem resolutionToProof{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom)(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top) →  (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → clauseSat (clauses.coords j jw) valuation) → 
            clauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn  => 
          fun valuation base  => 
            have lem0 : clauses.coords j jw = top := eqn
            have lem1 : clauseSat (clauses.coords j jw) valuation := base j jw
          by
            rw [←  lem0]
            exact lem1
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  => 
          fun valuation base => 
              let leftBase : clauseSat left valuation := 
                resolutionToProof clauses left leftTree valuation base 
              let rightBase : clauseSat right valuation := 
                resolutionToProof clauses right rightTree  valuation base 
              let lemStep := triple_step left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

-- unsat from a resolution tree
theorem tree_unsat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom):
      ResolutionTree clauses (contradiction (n + 1)) → isUnSat clauses := 
  fun tree valuation hyp =>
    contradiction_is_false _ valuation $ 
      resolutionToProof clauses (contradiction (n + 1)) tree valuation hyp

/-
Pieces for building trees.
-/

def mergeUnitTrees{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
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

def mergeAlignUnitTrees{dom n: Nat}{branch : Bool}{clauses : Vector (Clause (n + 1)) dom}
                {focus : Nat}{focusLt : focus < n + 1}
                 (first: ResolutionTree clauses (unitClause n branch focus focusLt))
                (second: ResolutionTree clauses (unitClause n (not branch) focus focusLt)) :
                ResolutionTree clauses (contradiction (n + 1)) := 
                match branch, first, second with
                | false, left, right =>
                    mergeUnitTrees focus focusLt left right
                | true, right, left => 
                    mergeUnitTrees focus focusLt left right

def unitProof{dom n: Nat}{branch : Bool}{clauses : Vector (Clause (n + 1)) dom}
                {focus : Nat}{focusLt : focus < n + 1}{j : Nat}{jw : j < dom}
                (eqn: clauses.coords j jw = unitClause n branch focus focusLt):
                ResolutionTree clauses (unitClause n branch focus focusLt) :=
                  ResolutionTree.assumption j jw (unitClause n branch focus focusLt) eqn
                  
-- Lift of a resolution tree with apex `top` from the branch corresponding to `focus` and `topFocus` 
structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : Vector (Clause (n + 1)) dom)(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionTree clauses (FinSeq.vec (insert topFocus n focus focusLt top.coords))

/-
Lift of a resolution tree with apex a contradiction, i.e., a resolution proof of unsat,
 from the branch corresponding to `focus` and `topFocus`. The lift could be either a contradiction
 or the proof of a unit clause.
-/
inductive LiftedResTree{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom) where
    | contra : ResolutionTree clauses (contradiction (n + 2)) → 
                  LiftedResTree branch focus focusLt clauses
    | unit : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) → 
                  LiftedResTree branch focus focusLt clauses

theorem not_eq_implies_eq_not(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
  match b with
  | true => fun w => eq_false_of_ne_true w
  | false => fun w => eq_true_of_ne_false w

-- if none of the assumption clauses are `some bf` at a literal, the apex is not
theorem trees_preserve_notsomebranch{dom n : Nat}{clauses : Vector (Clause (n + 1)) dom}
        (bf: Bool)(k : Nat)(kw : k < n + 1)
        (base : (j : Nat) → (lt : j < dom) → 
          Not ((clauses.coords j lt).coords k kw = some bf)) : 
        (top : Clause (n + 1)) → 
        (tree : ResolutionTree clauses top) → 
        Not (top.coords k kw = some bf) := 
          fun top tree =>
          match tree with
          | ResolutionTree.assumption ind  bd .(top) chk =>
            fun  hyp => 
              have lem0 : clauses.coords ind bd = top := chk
              have lem1 : Not (top.coords k kw = some bf) := by
                      rw [←  lem0]
                      exact (base ind bd)
              absurd hyp lem1
          | ResolutionTree.resolve left right .(top) leftTree rightTree triple =>
            fun hyp => 
              let leftLem :=
                trees_preserve_notsomebranch bf k kw base left leftTree 
              let rightLem :=
                trees_preserve_notsomebranch bf k kw base right rightTree 
              if c : k = triple.pivot then 
                  match bf, k, c, kw, leftLem, rightLem with
                  | false, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                        lL (triple.leftPivot)
                  | true, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                        rL (triple.rightPivot)
              else 
                  let j := skipInverse triple.pivot k c 
                  let eqn  := skip_inverse_eq triple.pivot k c
                  let jw := skip_preimage_lt triple.pivotLt kw eqn
                  let joinIm := triple.joinRest j jw
                  match (skip triple.pivot j), eqn, (skip_le_succ jw), joinIm with 
                  | .(k), rfl, .(kw), join => 
                    let lem := 
                      top_of_join_not_positive bf 
                        (left.coords k kw) (right.coords k kw) (top.coords k kw) join
                          leftLem rightLem
                    lem hyp               
