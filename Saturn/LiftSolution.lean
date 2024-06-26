import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.Solverstep
import Saturn.Resolution
open Nat
open Vector
open FinSeq

/-
We show that solutions in a branch can be pulled back to solutions to the
original problem. We also show that resolution trees with top a contradiction
pull back to lifted resolution trees, which are trees with top either a contradiction
or a specifc unit clause determined by the branch.
-/

-- pull back of a solution
def pullBackSolution{num_clauses n: Nat}(branch: Bool)(focus : Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses)(rc: ReductionClauses branch focus focusLt clauses)
    (dp : DroppedProof rc) (fr: ForwardRelation rc):
      (valuation : Valuation n) →
        ((j : Nat) → (jw : j < rc.num_reducedClauses) → ClauseSat (rc.restClauses.get' j jw) valuation) →
        (j : Nat) → (jw : j < num_clauses) →
          ClauseSat (clauses.get' j jw) (Vector.ofFn' (insert branch n focus focusLt valuation.get')) :=
        by
          intro valuation pf k w
          let fwdOpt := (rc.forward k w)
          match eq:fwdOpt with
          | none =>
            simp [ClauseSat]
            apply Exists.intro focus
            apply Exists.intro focusLt
            let resolve : (clauses.get' k w).get' focus focusLt = some branch := dp.dropped k w eq
            rw [Vector.get'] at resolve
            rw [resolve]
            simp [Vector.get', Vector.of_Fn'_get]
            simp [insert_at_focus]
          | some j =>
            let bound := rc.forwardWit ⟨k, w⟩
            let jWitAux : boundOpt rc.num_reducedClauses (some j) := by
              rw [←  eq]
              exact bound
            let jWit : j < rc.num_reducedClauses := jWitAux
            let fwdEq := fr.forwardRelation k w j eq jWit
            let ⟨i, iw, vs⟩ := pf j jWit
            simp [ClauseSat]
            apply Exists.intro (skip focus i)
            apply Exists.intro (skip_le_succ iw)
            simp [Vector.get', Vector.of_Fn'_get]
            rw [insert_at_image]
            let delSkip : delete focus focusLt ((clauses.get' k w).get') i iw =
              (clauses.get ⟨k, w⟩).get ⟨(skip focus i), (skip_le_succ iw)⟩ := by
                rfl
            rw [← delSkip]
            rw [fwdEq]
            exact vs


-- lift of a resolution triple from a branch: definition and implementation
structure LiftedTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool)
  (left right top : Clause (n + 1))(k: Nat)(lt : k < succ (n + 1)) where
    topFoc : Option Bool
    triple : ResolutionTriple
          (Vector.ofFn' (insert  leftFoc (n + 1) k lt   left.get'))
          (Vector.ofFn' (insert  rightFoc (n + 1) k lt right.get'))
          (Vector.ofFn' (insert  topFoc (n + 1) k lt top.get'))
    topNonPos : Not (topFoc = some bf)

def liftResolutionTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool)
  (left right top : Clause (n + 1)) : (k: Nat) →
    (lt : k < succ (n + 1)) → (lbf : Not (leftFoc = some bf)) → (rbf :Not (rightFoc = some bf)) →
       ResolutionTriple left right top →
        LiftedTriple bf leftFoc rightFoc left right top k lt  :=
  fun k lt lbf rbf rt =>
    let ⟨topFoc, focJoin⟩ :=
      getJoin bf leftFoc rightFoc lbf rbf
    let topNonPos : Not (topFoc = some bf) :=
      top_of_join_not_positive bf leftFoc rightFoc topFoc focJoin lbf rbf
    let pivotN := skip k  rt.pivot
    let pivotNLt : pivotN < n + 2 := skip_le_succ rt.pivotLt
    let leftN := insert leftFoc (n + 1) k lt left.get'
    let rightN := insert rightFoc (n + 1) k lt right.get'
    let topN := insert topFoc (n + 1) k lt top.get'
    let leftPivotN : leftN pivotN pivotNLt = some false :=
      by
        rw [← rt.leftPivot]
        apply insert_at_image
    let rightPivotN : rightN pivotN pivotNLt = some true :=
      by
        rw [← rt.rightPivot]
        apply insert_at_image
    let topPivotN : topN pivotN pivotNLt = none :=
      by
        rw [← rt.topPivot]
        apply insert_at_image
    let joinRestN : (j : Nat) → (jw : j < n + 1) →
      IsJoin  (leftN (skip pivotN j) (skip_le_succ jw))
            (rightN (skip pivotN j) (skip_le_succ jw))
            (topN (skip pivotN j) (skip_le_succ jw)) :=
      fun j jw =>
      let jj := skip pivotN j
      let jjw : jj < n + 2 := skip_le_succ jw
      let notPivot : Not (jj = pivotN) := skip_no_fixedpoints pivotN j
      if jj_eq_k : jj = k then  by
        let leftLem : leftN jj jjw = leftN k lt := by
          apply witness_independent
          assumption
        let rightLem : rightN jj jjw = rightN k lt := by
          apply witness_independent
          assumption
        let topLem : topN jj jjw = topN k lt := by
          apply witness_independent
          assumption
        rw [leftLem, rightLem, topLem]
        simp [leftN, rightN, topN, insert_at_focus]
        exact focJoin
      else
        let i := skipInverse k jj jj_eq_k
        let skp_k_i_jj : skip k i = jj := skipInverse_eq k jj jj_eq_k
        let iw : i < n + 1 := skip_preimage_lt lt jjw skp_k_i_jj
        if i_eq_pivot: i = rt.pivot then by
          have lem2 : skip k  rt.pivot = jj := by
                rw [← i_eq_pivot, skipInverse_eq]
          simp [ ← lem2] at notPivot
        else by
          let ii := skipInverse rt.pivot i i_eq_pivot
          let skp_ii_eq_i : skip rt.pivot ii = i :=
                    skipInverse_eq rt.pivot i i_eq_pivot
          let iiw : ii < n := skip_preimage_lt rt.pivotLt iw skp_ii_eq_i
          let leftLem : leftN jj jjw =
            leftN (skip k i) (skip_le_succ iw) := by
              apply witness_independent
              rw [← skp_k_i_jj]
          let rightLem : rightN jj jjw = rightN (skip k i) (skip_le_succ iw) := by
              apply witness_independent
              rw [← skp_k_i_jj]
          let topLem : topN jj jjw = topN (skip k i) (skip_le_succ iw) := by
              apply witness_independent
              rw [← skp_k_i_jj]
          rw [leftLem, rightLem, topLem]
          let eqL : leftN (skip k i) (skip_le_succ iw) = left.get' i iw := by
              apply insert_at_image
          let eqR : rightN (skip k i) (skip_le_succ iw) = right.get' i iw := by
              apply insert_at_image
          let eqT : topN (skip k i) (skip_le_succ iw) = top.get' i iw := by
              apply insert_at_image
          rw [eqL, eqR, eqT]
          let leftLem2 : left.get' (skip rt.pivot ii) (skip_le_succ iiw) = left.get' i iw := by
              apply witness_independent
              exact skp_ii_eq_i
          let rightLem2 : right.get' (skip rt.pivot ii) (skip_le_succ iiw) = right.get' i iw := by
              apply witness_independent
              exact skp_ii_eq_i
          let topLem2 : top.get' (skip rt.pivot ii) (skip_le_succ iiw) = top.get' i iw := by
              apply witness_independent
              exact skp_ii_eq_i
          rw [← leftLem2, ← rightLem2, ← topLem2]
          exact rt.joinRest ii iiw
  ⟨topFoc, ⟨pivotN, pivotNLt,
                  (by rw [Vector.of_Fn'_get']; rw [← leftPivotN]),
                  (by rw [Vector.of_Fn'_get']; rw [← rightPivotN]),
                  (by rw [Vector.of_Fn'_get']; rw [← topPivotN]),
                  (by
                      rw [Vector.of_Fn'_get']
                      intro k1
                      intro w
                      have lp : leftN =
                        insert leftFoc (n + 1) k lt left.get' := by rfl
                      have rp : rightN =
                        insert rightFoc (n + 1) k lt right.get' := by rfl
                      have tp : topN =
                        insert topFoc (n + 1) k lt top.get' := by rfl
                      rw [← lp, ← rp, ← tp]
                      have rn:  (Vector.ofFn' rightN).get' = rightN :=
                        by rw [Vector.of_Fn'_get']
                      have tn: (Vector.ofFn' topN).get' = topN :=
                        by rw [Vector.of_Fn'_get']
                      rw [rn,  tn]
                      apply joinRestN
                      assumption
                      )⟩, topNonPos⟩


-- pulling back a tree
def pullBackTree{num_clauses n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) num_clauses)(rc: ReductionClauses branch focus focusLt clauses)
    (np : NonPosReverse rc) (rr: ReverseRelation rc): (top : Clause (n + 1)) →
      (tree : ResolutionTree (rc.restClauses) top)
       → BranchResolutionProof branch focus focusLt clauses top  :=
      fun top tree =>
        match tree with
        | ResolutionTree.assumption j jw .(top) ttp =>
            let k := rc.reverse j jw
            let kw : k < num_clauses := rc.reverseWit ⟨j, jw⟩
            let cl := clauses.get' k kw
            let topFocus := cl.get' focus focusLt
            let nonPosLem : Not (topFocus = some branch)  :=
                np.nonPosRev j jw
            have lem1 : (rc.restClauses.get' j jw).get' =
                  delete focus focusLt (clauses.get' k kw).get'
                       := by
                       apply rr.relation
                       done
            have lem3 : insert (cl.get' focus focusLt) (n + 1) focus focusLt
                          (delete focus focusLt cl.get') = cl.get'
                          := insert_delete_id focus focusLt cl.get'
            have lem : insert topFocus (n + 1) focus focusLt top.get' = cl.get' := by
                      rw [← ttp]
                      rw [lem1]
                      rw [lem3]
                      done
            ⟨topFocus, nonPosLem,
              ResolutionTree.assumption k kw  _ (by
                    rw [lem]
                    have lc : Vector.ofFn' (cl.get') = cl := by
                      apply Vector.ext'
                      apply Vector.of_Fn'_get'
                      done
                    rw [lc]
                    done)⟩
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  =>
              let leftBase : BranchResolutionProof branch focus focusLt clauses left :=
                        pullBackTree branch focus focusLt clauses rc np rr left leftTree
              let rightBase : BranchResolutionProof branch focus focusLt clauses right :=
                        pullBackTree branch focus focusLt clauses rc np rr right rightTree

              let ⟨leftFoc, leftNP, leftLiftTree⟩ := leftBase
              let ⟨rightFoc, rightNP, rightLiftTree⟩ := rightBase
              let liftedTriple :=
                    liftResolutionTriple branch leftFoc rightFoc left right top
                          focus focusLt leftNP rightNP triple
              let ⟨topFoc, liftTriple, topNonPos⟩ := liftedTriple
              let tree := ResolutionTree.resolve
                              (Vector.ofFn' (insert leftFoc _ focus focusLt left.get'))
                              (Vector.ofFn' (insert rightFoc _ focus focusLt right.get'))
                              (Vector.ofFn' (insert topFoc _ focus focusLt top.get'))
                              leftLiftTree rightLiftTree liftTriple
              ⟨topFoc, topNonPos, tree⟩

-- pulling back a proof of unsat by resolution to a contradiction or a proof of a unit clause.
def pullBackResTree{num_clauses n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) num_clauses)(rc: ReductionClauses branch focus focusLt clauses)
    (np : NonPosReverse rc) (rr: ReverseRelation rc) :
        ResolutionTree rc.restClauses (contradiction (n + 1)) →
            LiftedResTree branch focus focusLt clauses := by
            intro rpf
            let pbt := pullBackTree branch focus focusLt clauses rc np rr
                                (contradiction (n + 1)) rpf
            match pbt.topFocus, pbt.nonPos, pbt.provedTree with
            | none, _, tree =>
                have lem :
                  Vector.ofFn' (insert none (Nat.add n 1) focus focusLt
                    (contradiction (n + 1)).get') =
                    contradiction (n + 2) := by
                      rw [contradiction_insert_none focus focusLt]
                      apply Vector.ext'
                      apply Vector.of_Fn'_get'
                rw [lem] at tree
                exact LiftedResTree.contra tree
            | some b, ineq, tree =>
                have lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := not_eq_implies_eq_not branch lemPar
                rw [par] at tree
                exact LiftedResTree.unit tree

-- transporting proof from a subset of clauses to a larger set of clauses
def transportResTree{l1 l2 n : Nat}(clauses1 : Vector (Clause (n + 1)) l1)
                  (clauses2: Vector (Clause (n + 1)) l2)
                  (embed: (j : Nat) → (jw : j < l1) → ElemInSeq clauses2.get' (clauses1.get' j jw))
                  (top: Clause (n + 1)):
                  (tree : ResolutionTree clauses1 top) →
                              ResolutionTree clauses2 top :=
                      fun tree =>
                      match tree with
                      | ResolutionTree.assumption ind  bd .(top) te =>
                          let ⟨i, iw, eqn⟩ := embed ind bd
                          ResolutionTree.assumption i iw _ (by
                            rw [eqn]
                            exact te)
                      | ResolutionTree.resolve left right .(top) leftTree rightTree join =>
                          let leftPf2 := transportResTree clauses1 clauses2 embed left
                              leftTree
                          let rightPf2 := transportResTree clauses1 clauses2 embed right
                              rightTree
                          ResolutionTree.resolve left right top
                                      leftPf2 rightPf2 join
