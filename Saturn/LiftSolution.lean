import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.Solverstep 
import Saturn.Resolution
open Nat
open Vector
open FinSeq

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
              let lem1 : (clauses.coords k w).coords focus focusLt = some branch := dp.dropped k w eq
              let lem2 : insert branch n focus focusLt valuation.coords focus focusLt = branch := by 
                apply insert_at_focus
                done
              let lem3 : (clauses.coords k w).coords focus focusLt = 
                some (insert branch n focus focusLt valuation.coords focus focusLt) := 
                by
                  rw [lem1]
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
              let lem4 : ((clauses.coords k w).coords focus focusLt) = some (
                    (FinSeq.vec (insert branch n focus focusLt 
                      valuation.coords)).coords focus focusLt) := 
                      by 
                        rw [seq_to_vec_coords (insert branch n focus focusLt 
                      valuation.coords)]
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
              let lem2 : (rc.restClauses.coords j jWit).coords i iw = 
                      some (valuation.coords i iw) := vs
              let lem3 : delete focus focusLt ((clauses.coords k w).coords) i iw =
                  some (valuation.coords i iw) := 
                    by
                    rw [←  lem2]
                    rw [lem1]
                    done
              let lem4 : delete focus focusLt ((clauses.coords k w).coords) i iw =
                ((clauses.coords k w).coords) (skip focus i) (skip_le_succ iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw) =
                                  valuation.coords i iw := by
                                    apply insert_at_image
                                    done
              let lem6 : ((clauses.coords k w).coords) (skip focus i) (skip_le_succ iw) =
                          some (insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw)) := by
                              rw [← lem4]
                              rw [lem3]
                              rw [lem5]
                              done
              let lem7 : ((clauses.coords k w).coords (skip focus i) (skip_le_succ iw)) =
                some (
                  ((FinSeq.vec (insert branch n focus focusLt valuation.coords)).coords 
                    (skip focus i) (skip_le_succ iw))) := 
                      by
                        rw [seq_to_vec_coords (insert branch n focus focusLt valuation.coords)]
                        rw [lem6]
                        done
              ⟨skip focus i, skip_le_succ iw, lem7⟩

-- pulling back a tree
def pullBackTree{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom)(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc): (top : Clause (n + 1)) → 
      (tree : ResolutionTree (rc.restClauses) top) 
       → BranchResolutionProof branch focus focusLt clauses top  := 
      fun top tree =>
        match tree with
        | ResolutionTree.assumption j jw .(top) ttp => 
            let k := rc.reverse j jw
            let kw : k < dom := rc.reverseWit j jw
            let cl := clauses.coords k kw
            let topFocus := cl.coords focus focusLt
            let nonPosLem : Not (topFocus = some branch)  := 
                np.nonPosRev j jw
            have lem1 : (rc.restClauses.coords j jw).coords = 
                  delete focus focusLt (clauses.coords k kw).coords 
                       := by
                       apply rr.relation
                       done
            have lem3 : insert (cl.coords focus focusLt) (n + 1) focus focusLt 
                          (delete focus focusLt cl.coords) = cl.coords 
                          := insert_delete_id focus focusLt cl.coords
            have lem : insert topFocus (n + 1) focus focusLt top.coords = cl.coords := by
                      rw [← ttp]
                      rw [lem1]
                      rw [lem3]
                      done 
            ⟨topFocus, nonPosLem,
              ResolutionTree.assumption k kw  _ (by
                    rw [lem]
                    have lc : FinSeq.vec (cl.coords) = cl := by 
                      apply coords_eq_implies_vec_eq
                      apply seq_to_vec_coords
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
                              (FinSeq.vec (insert leftFoc _ focus focusLt left.coords))
                              (FinSeq.vec (insert rightFoc _ focus focusLt right.coords))
                              (FinSeq.vec (insert topFoc _ focus focusLt top.coords))
                              leftLiftTree rightLiftTree liftTriple
              ⟨topFoc, topNonPos, tree⟩

-- pulling back a proof of unsat by resolution to a contradiction or a proof of a unit clause.
def pullBackResTree{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom)(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc) : 
        ResolutionTree rc.restClauses (contradiction (n + 1)) → 
            LiftedResTree branch focus focusLt clauses := fun rpf =>
            let pbt := pullBackTree branch focus focusLt clauses rc np rr 
                                (contradiction (n + 1)) rpf 
            match pbt.topFocus, pbt.nonPos, pbt.provedTree with 
            | none, _, tree => 
                have lem :
                  FinSeq.vec (insert none (Nat.add n 1) focus focusLt 
                    (contradiction (n + 1)).coords) =
                    contradiction (n + 2) := by
                      rw [contradiction_insert_none focus focusLt]
                      apply coords_eq_implies_vec_eq
                      apply seq_to_vec_coords
                      done            
                let t : ResolutionTree clauses (contradiction (n + 2)) := by
                            rw [← lem]
                            exact tree
                            done
                LiftedResTree.contra t
            | some b, ineq, tree =>
                have lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := not_eq_implies_eq_not branch lemPar
                let t : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) := 
                          by
                            rw [← par]
                            exact tree
                            done
                LiftedResTree.unit t

-- transporting proof from a subset of clauses to a larger set of clauses
def transportResTree{l1 l2 n : Nat}(clauses1 : Vector (Clause (n + 1)) l1)
                  (clauses2: Vector (Clause (n + 1)) l2)
                  (embed: (j : Nat) → (jw : j < l1) → ElemInSeq clauses2.coords (clauses1.coords j jw))
                  (top: Clause (n + 1)): 
                  (tree : ResolutionTree clauses1 top) → 
                              ResolutionTree clauses2 top := 
                      fun tree => 
                      match tree with
                      | ResolutionTree.assumption ind  bd .(top) te =>
                          let ⟨i, iw, eqn⟩ := embed ind bd                        
                          ResolutionTree.assumption i iw _ (by 
                            rw [eqn]
                            exact te
                            done)
                      | ResolutionTree.resolve left right .(top) leftTree rightTree join =>
                          let leftPf2 := transportResTree clauses1 clauses2 embed left
                              leftTree 
                          let rightPf2 := transportResTree clauses1 clauses2 embed right
                              rightTree  
                          let tree := ResolutionTree.resolve left right top
                                      leftPf2 rightPf2 join

                          tree
