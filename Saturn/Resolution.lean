import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Solverstep
import Lean.Meta
open Nat
open FinSeq

inductive Join (left right top : Option Bool) where
  | noneNone : (left = none) → (right = none) → (top = none)→ Join left right top 
  | noneSome : (b : Bool) → (left = none) → (right = some b) → (top = some b)→ Join left right top
  | someNone : (b : Bool) → (left = some b) → (right = none) → (top = some b)→ Join left right top
  | someSome : (b : Bool) → (left = some b) → (right = some b) → (top = some b)→ Join left right top

theorem not_not_eq(bf b bb : Bool) : Not (b = bf) → Not (bb = bf) → b = bb :=
  match bf with
  | true => fun w ww => 
    Eq.trans (eq_false_of_ne_true w) (Eq.symm (eq_false_of_ne_true ww))
  | false => fun w ww => 
    Eq.trans (eq_true_of_ne_false w) (Eq.symm (eq_true_of_ne_false ww))

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
                  done
                have lem2 : bb = b := not_not_eq bf bb b lem1 c
                ⟨some b, Join.someSome b rfl (congrArg some lem2) rfl⟩

def topJoinNonPos(bf : Bool)(left right top: Option Bool): Join left right top →
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


theorem var_resolution_step {left right top : Option Bool}(join: Join left right top)(valuationVal : Bool) :
  Or (varSat left valuationVal) (varSat right valuationVal) → (varSat top valuationVal)  :=
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

theorem triple_step_proof{n: Nat}(left right top : Clause (n + 1))
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
                            done 
                      have lem2 : valuation.coords kl llt = 
                            valuation.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply cc
                            done 
                      have lem3 : left.coords kl llt = some true := by
                        rw [wl]
                        rw [lem2]
                        rw [c]
                        done
                      have lem4 : left.coords kl llt = some false := by
                        rw [lem1]
                        exact triple.leftPivot
                        done 
                      have lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      have lem6 : true = false := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                  else  
                      let i := skipInverse triple.pivot kl cc 
                      let eql := skip_inverse_eq triple.pivot kl cc 
                      let iw : i < n := skip_preimage_lt triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.coords kl llt = left.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.coords kl llt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let topLem : 
                        top.coords kl llt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
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
                            done 
                      have lem2 : valuation.coords kr rlt = 
                            valuation.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                            done 
                      have lem3 : right.coords kr rlt = some false := by
                        rw [wr]
                        rw [lem2]
                        rw [cc]
                        done
                      have lem4 : right.coords kr rlt = some true := by
                        rw [lem1]
                        exact triple.rightPivot
                        done 
                      have lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      have lem6 : false = true := by 
                        injection lem5
                        assumption
                        done
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
                          done
                      let rightLem : 
                        right.coords kr rlt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let topLem : 
                        top.coords kr rlt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let join : Join (left.coords kr rlt) (right.coords kr rlt) (top.coords kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, ⟨rlt, var_resolution_step join (valuation.coords kr rlt) (Or.inr (wr))⟩⟩

def tripleStepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (ClauseSat left valuation) → 
        (ClauseSat right valuation) → (ClauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, llt, wl⟩ =>
              fun ⟨kr, rlt, wr⟩ =>
                 if c : valuation.coords (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then 
                      have lem1 : left.coords kl llt = 
                            left.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply cc
                            done 
                      have lem2 : valuation.coords kl llt = 
                            valuation.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply cc
                            done 
                      have lem3 : left.coords kl llt = some true := by
                        rw [wl]
                        rw [lem2]
                        rw [c]
                        done
                      have lem4 : left.coords kl llt = some false := by
                        rw [lem1]
                        exact triple.leftPivot
                        done 
                      have lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      have lem6 : true = false := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                    else  
                      let i := skipInverse triple.pivot kl cc 
                      let eql := skip_inverse_eq triple.pivot kl cc
                      let iw : i < n := skip_preimage_lt triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.coords kl llt = left.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.coords kl llt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let topLem : 
                        top.coords kl llt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let join : Join (left.coords kl llt) (right.coords kl llt) (top.coords kl llt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, llt, var_resolution_step join (valuation.coords kl llt) (Or.inl (wl))⟩
                  else
                    let cc := eq_false_of_ne_true c  
                    if ccc : kr = triple.pivot then  
                      have lem1 : right.coords kr rlt = 
                            right.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                            done 
                      have lem2 : valuation.coords kr rlt = 
                            valuation.coords triple.pivot triple.pivotLt := by
                            apply witness_independent
                            apply ccc
                            done 
                      have lem3 : right.coords kr rlt = some false := by
                        rw [wr]
                        rw [lem2]
                        rw [cc]
                        done
                      have lem4 : right.coords kr rlt = some true := by
                        rw [lem1]
                        exact triple.rightPivot
                        done 
                      have lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      have lem6 : false = true := by 
                        injection lem5
                        assumption
                        done
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
                          done
                      let rightLem : 
                        right.coords kr rlt = right.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let topLem : 
                        top.coords kr rlt = top.coords (skip triple.pivot i) (skip_le_succ iw) := by
                          apply witness_independent
                          rw [← eql]
                          done
                      let join : Join (left.coords kr rlt) (right.coords kr rlt) (top.coords kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, rlt, var_resolution_step join (valuation.coords kr rlt) (Or.inr (wr))⟩

structure LiftedTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool) 
  (left right top : Clause (n + 1))(k: Nat)(lt : k < succ (n + 1)) where
    topFoc : Option Bool
    triple : ResolutionTriple 
          (FinSeq.vec (insert  leftFoc (n + 1) k lt   left.coords)) 
          (FinSeq.vec (insert  rightFoc (n + 1) k lt right.coords)) 
          (FinSeq.vec (insert  topFoc (n + 1) k lt top.coords))
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
            topJoinNonPos bf leftFoc rightFoc topFoc focJoin lbf rbf
          let pivotN := skip k  rt.pivot
          let pivotNLt : pivotN < n + 2 := skip_le_succ rt.pivotLt
          let leftN := insert leftFoc (n + 1) k lt left.coords
          let rightN := insert rightFoc (n + 1) k lt right.coords
          let topN := insert topFoc (n + 1) k lt top.coords
          let leftPivotN : leftN pivotN pivotNLt = some false := 
            have lem1 : leftN pivotN pivotNLt = left.coords rt.pivot rt.pivotLt := 
              insert_at_image leftFoc (n + 1) k lt left.coords rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.leftPivot
              done
          let rightPivotN : rightN pivotN pivotNLt = some true := 
            have lem1 : rightN pivotN pivotNLt = right.coords rt.pivot rt.pivotLt := 
              insert_at_image rightFoc (n + 1) k lt right.coords rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.rightPivot
              done
          let topPivotN : topN pivotN pivotNLt = none := 
            have lem1 : topN pivotN pivotNLt = top.coords rt.pivot rt.pivotLt := 
              insert_at_image topFoc (n + 1) k lt top.coords rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.topPivot
              done

          let joinRestN : (j : Nat) → (jw : j < n + 1) →  
            Join  (leftN (skip pivotN j) (skip_le_succ jw)) 
                  (rightN (skip pivotN j) (skip_le_succ jw)) 
                  (topN (skip pivotN j) (skip_le_succ jw)) := 
                  fun j jw => 
                  let jj := skip pivotN j
                  let jjw : jj < n + 2 := skip_le_succ jw
                  let notPivot : Not (jj = pivotN) := skip_no_fixedpoints pivotN j
                  if w : jj = k then  
                    let lem0 := focJoin
                    let eqL : leftN k lt = leftFoc := 
                      insert_at_focus leftFoc (n + 1) k lt left.coords 
                    let eqR : rightN k lt = rightFoc := 
                      insert_at_focus rightFoc (n + 1) k lt right.coords
                    let eqT : topN k lt = topFoc := 
                      insert_at_focus topFoc (n + 1) k lt top.coords
                    let leftLem : leftN jj jjw = leftN k lt := by
                      apply witness_independent
                      exact w
                      done
                    let rightLem : rightN jj jjw = rightN k lt := by
                      apply witness_independent
                      exact w
                      done 
                    let topLem : topN jj jjw = topN k lt := by
                      apply witness_independent
                      exact w
                      done
                    let goal : Join (leftN jj jjw) (rightN jj jjw) (topN jj jjw) := by
                      rw [leftLem, rightLem, topLem]
                      rw [eqL, eqR, eqT]
                      exact lem0
                      done
                    goal
                  else 
                    let i := skipInverse k jj w
                    let w := skip_inverse_eq k jj w
                    let iw : i < n + 1 := skip_preimage_lt lt jjw w
                    if ww: i = rt.pivot then
                      have lem1 : skip k i = skip k rt.pivot := congrArg (skip k) ww
                      have lem2 : skip k  rt.pivot = jj := by 
                            rw [←  lem1]
                            exact w
                            done
                      absurd (Eq.symm lem2) notPivot
                    else 
                      let ii := skipInverse rt.pivot i ww 
                      let  ww  := skip_inverse_eq rt.pivot i ww
                      let iiw : ii < n := skip_preimage_lt rt.pivotLt iw ww
                      let eqL : 
                        leftN (skip k i) (skip_le_succ iw) = 
                          left.coords i iw := 
                          insert_at_image leftFoc (n + 1) k lt left.coords i iw
                      let eqR : 
                        rightN (skip k i) (skip_le_succ iw) = 
                          right.coords i iw := 
                          insert_at_image rightFoc (n + 1) k lt right.coords i iw              
                      let eqT :
                        topN (skip k i) (skip_le_succ iw) = 
                          top.coords i iw := 
                          insert_at_image topFoc (n + 1) k lt top.coords i iw
                      let leftLem :
                        leftN jj jjw = leftN (skip k i) (skip_le_succ iw) := 
                          witness_independent leftN jj (skip k i) jjw (skip_le_succ iw) (Eq.symm w)
                      let rightLem :
                        rightN jj jjw = rightN (skip k i) (skip_le_succ iw) := 
                          witness_independent rightN jj (skip k i) jjw (skip_le_succ iw) (Eq.symm w)
                      let topLem :
                        topN jj jjw = topN (skip k i) (skip_le_succ iw) := 
                          witness_independent topN jj (skip k i) jjw (skip_le_succ iw) (Eq.symm w)
                      let leftLem2 :
                        left.coords (skip rt.pivot ii) (skip_le_succ iiw) = left.coords i iw := by
                          apply witness_independent
                          exact ww
                          done
                      let rightLem2 :
                        right.coords (skip rt.pivot ii) (skip_le_succ iiw) = right.coords i iw := by
                          apply witness_independent
                          exact ww
                          done
                      let topLem2 :
                        top.coords (skip rt.pivot ii) (skip_le_succ iiw) = top.coords i iw := by
                          apply witness_independent
                          exact ww
                          done
                      let prevJoin := rt.joinRest ii iiw
                      let goal : Join (leftN jj jjw) (rightN jj jjw) (topN jj jjw) := by
                        rw [leftLem, rightLem, topLem]
                        rw [eqL, eqR, eqT]
                        rw [← leftLem2]
                        rw [← rightLem2]
                        rw [← topLem2]
                        exact prevJoin
                        done
                      goal
      ⟨topFoc, ⟨pivotN, pivotNLt,
                       (
                         by
                          rw [seq_to_vec_coords]
                          rw [← leftPivotN]
                          done
                          ), (
                         by
                          rw [seq_to_vec_coords]
                          rw [←  rightPivotN]
                          done
                          ), (
                         by
                          rw [seq_to_vec_coords]
                          rw [← topPivotN]
                          done
                          ), (
                         by
                          rw [seq_to_vec_coords]
                          intro k1
                          intro w
                          have lp : leftN =
                            insert leftFoc (n + 1) k lt left.coords := by rfl
                          have rp : rightN =
                            insert rightFoc (n + 1) k lt right.coords := by rfl
                          have tp : topN =
                            insert topFoc (n + 1) k lt top.coords := by rfl
                          rw [← lp, ← rp, ← tp]
                          have rn: (Vector.coords (FinSeq.vec rightN)) = rightN :=
                            by rw [seq_to_vec_coords] 
                          have ln: (Vector.coords (FinSeq.vec leftN)) = leftN :=
                            by rw [seq_to_vec_coords]
                          have tn: (Vector.coords (FinSeq.vec topN)) = topN :=
                            by rw [seq_to_vec_coords]
                          rw [rn, tn]
                          apply joinRestN
                          assumption
                          done
                          )⟩, topNonPos⟩
      

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


def Clause.toString {n: Nat}: Clause n → String :=
  fun (cls : Clause n) => (cls.coords.list).toString

instance {n: Nat} : ToString (Clause n) := 
  ⟨fun (cls : Clause n) => (cls.coords.list).toString⟩

instance {n: Nat}{α: Type}[ToString α] : ToString (FinSeq n α) := 
  ⟨fun seq => (seq.list).toString⟩

def ResolutionTree.toString{dom n: Nat}{clauses : Vector  (Clause (n + 1)) dom}
      {top : Clause (n + 1)}
        (rt: ResolutionTree clauses top) : String := 
      match rt with
      | ResolutionTree.assumption i iw _ _  => (FinSeq.list (Vector.coords (clauses.coords i iw))).toString
      | ResolutionTree.resolve left right .(top) leftTree rightTree triple => 
                top.toString ++ " from " ++ left.toString ++ " & " ++ right.toString  ++ 
                "; using: {" ++ 
                leftTree.toString ++ "} and {" ++ rightTree.toString ++ "}"


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
              let lemStep := triple_step_proof left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom)(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top)  → (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → ClauseSat (clauses.coords j jw) valuation)
           → ClauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn => 
          fun valuation base  => 
            have lem1 : ClauseSat (clauses.coords j jw) valuation := base j jw
          by
            rw [← eqn]
            exact lem1
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  => 
          fun valuation base => 
              let leftBase : ClauseSat left valuation := 
                resolutionToSat clauses left leftTree valuation base 
              let rightBase : ClauseSat right valuation := 
                resolutionToSat clauses right rightTree valuation base 
              let lemStep := tripleStepSat left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

inductive SatSolution{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) where
  | unsat : (tree : ResolutionTree clauses (contradiction (n + 1))) → 
          SatSolution clauses
  | sat : (valuation : Valuation (n + 1)) → ((k : Nat) → (kw : k < dom) 
        → ClauseSat (clauses.coords k kw) valuation) → SatSolution clauses 

def SatSolution.toString{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
        (sol: SatSolution clauses) →  String := 
      fun sol =>
      match sol with
      | unsat tree => "unsat: " ++ tree.toString 
      | sat valuation _ => "sat: " ++ (valuation.coords.list).toString

def satProp{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                (Vector.coords (clauses.coords p pw) k kw) = some (valuation.coords k kw)

def unsatProp{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) :=
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                (Vector.coords (clauses.coords p pw) k kw) = some (valuation.coords k kw))



def solutionProp{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat tree  => unsatProp clauses
  | SatSolution.sat _ _ => satProp clauses



def solutionProof{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree   => 
          fun valuation =>
            fun hyp : ∀ p : Nat, ∀ pw : p < dom, clauseSat (clauses.coords p pw) valuation =>
              let lem := resolutionToProof clauses (contradiction (n + 1))
                            tree valuation hyp
              contradiction_is_false _ valuation lem
  | SatSolution.sat valuation evidence =>
          ⟨valuation, fun k kw => getProof (evidence k kw)⟩


def treeToUnsat{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom} :
                (rpf : ResolutionTree clauses (contradiction _)) → 
                        SatSolution clauses := fun rpf =>
          SatSolution.unsat rpf 

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
                  


structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : Vector (Clause (n + 1)) dom)(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionTree clauses (FinSeq.vec (insert topFocus n focus focusLt top.coords))

inductive LiftedResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom) where
    | contra : ResolutionTree clauses (contradiction (n + 2)) → 
                  LiftedResPf branch focus focusLt clauses
    | unit : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) → 
                  LiftedResPf branch focus focusLt clauses

theorem not_eq_implies_eq_not(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
  match b with
  | true => fun w => eq_false_of_ne_true w
  | false => fun w => eq_true_of_ne_false w

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
            have lem1 : Vector.coords (rc.restClauses.coords j jw) = 
                  delete focus focusLt (Vector.coords (clauses.coords k kw)) 
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
                    have lc : FinSeq.vec (Vector.coords cl) = cl := by 
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

def pullBackResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom)(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc) : 
        ResolutionTree rc.restClauses (contradiction (n + 1)) → 
            LiftedResPf branch focus focusLt clauses := fun rpf =>
            let pbt := pullBackTree branch focus focusLt clauses rc np rr 
                                (contradiction (n + 1)) rpf 
            match pbt.topFocus, pbt.nonPos, pbt.provedTree with 
            | none, _, tree => 
                have lem :
                  FinSeq.vec (insert none (Nat.add n 1) focus focusLt (Vector.coords (contradiction (n + 1)))) =
                    contradiction (n + 2) := by
                      rw [contradiction_insert_none focus focusLt]
                      apply coords_eq_implies_vec_eq
                      apply seq_to_vec_coords
                      done            
                let t : ResolutionTree clauses (contradiction (n + 2)) := by
                            rw [← lem]
                            exact tree
                            done
                LiftedResPf.contra t
            | some b, ineq, tree =>
                have lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := not_eq_implies_eq_not branch lemPar
                let t : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) := 
                          by
                            rw [← par]
                            exact tree
                            done
                LiftedResPf.unit t

def transportResPf{l1 l2 n : Nat}(clauses1 : Vector (Clause (n + 1)) l1)
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
                          let leftPf2 := transportResPf clauses1 clauses2 embed left
                              leftTree 
                          let rightPf2 := transportResPf clauses1 clauses2 embed right
                              rightTree  
                          let tree := ResolutionTree.resolve left right top
                                      leftPf2 rightPf2 join

                          tree

theorem proofs_preserve_notsomebranch{dom n : Nat}{clauses : Vector (Clause (n + 1)) dom}
                (bf: Bool)(k : Nat)(kw : k < n + 1)
                (base : (j : Nat) → (lt : j < dom) → 
                  Not (Vector.coords (clauses.coords j lt) k kw = some bf)) : 
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
                        proofs_preserve_notsomebranch bf k kw base left leftTree 
                      let rightLem :=
                        proofs_preserve_notsomebranch bf k kw base right rightTree 
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
                              topJoinNonPos bf (left.coords k kw) (right.coords k kw) (top.coords k kw) join
                                leftLem rightLem
                            lem hyp               



