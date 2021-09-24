import Saturn.FinSeq
import Saturn.Clause 
import Saturn.Solverstep
open Nat


inductive Join (left right top : Option Bool) where
  | noneNone : (left = none) → (right = none) → (top = none)→ Join left right top 
  | noneSome : (b : Bool) → (left = none) → (right = some b) → (top = some b)→ Join left right top
  | someNone : (b : Bool) → (left = some b) → (right = none) → (top = some b)→ Join left right top
  | someSome : (b : Bool) → (left = some b) → (right = some b) → (top = some b)→ Join left right top

theorem notNot(bf b bb : Bool) : Not (b = bf) → Not (bb = bf) → b = bb :=
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
                have lem2 : bb = b := notNot bf bb b lem1 c
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


theorem varResolution {left right top : Option Bool}(join: Join left right top)(valuationVal : Bool) :
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
  leftPivot : left.at pivot pivotLt = some false
  rightPivot : right.at pivot pivotLt = some true
  topPivot : top.at pivot pivotLt = none
  joinRest : (k : Nat) → (w : k < n) →  
    Join  (left.at (skip pivot k) (skipPlusOne w)) 
          (right.at (skip pivot k) (skipPlusOne w)) 
          (top.at (skip pivot k) (skipPlusOne w))

def unitTriple(n : Nat)(k: Nat)(lt : k < n + 1) :
        ResolutionTriple (unitClause n false  k lt) (unitClause n true k lt) (contradiction (n + 1)) :=
          ⟨k, lt, 
            unitDiag n false k lt , 
            unitDiag n true k lt, 
            by
              rw [contraAt] 
              done, 
            fun j jw => Join.noneNone 
                      (unitSkip n false k lt j jw) 
                      (unitSkip n true k lt j jw) 
                      (by rw [contraAt])
                      ⟩

def triple_stepProof{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (clauseSat left valuation) → 
        (clauseSat right valuation) → (clauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, ⟨llt, wl⟩⟩ =>
              fun ⟨kr, ⟨rlt, wr⟩⟩ =>
                 if c : valuation.at (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then
                      have lem1 : left.at kl llt = 
                            left.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      have lem2 : valuation.at kl llt = 
                            valuation.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      have lem3 : left.at kl llt = some true := by
                        rw [wl]
                        rw [lem2]
                        rw [c]
                        done
                      have lem4 : left.at kl llt = some false := by
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
                      let eql := skipInverseEqn triple.pivot kl cc 
                      let iw : i < n := skipPreImageBound triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.at kl llt = left.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.at kl llt = right.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let topLem : 
                        top.at kl llt = top.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let join : Join (left.at kl llt) (right.at kl llt) (top.at kl llt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, ⟨llt, varResolution join (valuation.at kl llt) (Or.inl (wl))⟩⟩
                  else
                    let cc := eq_false_of_ne_true c  
                    if ccc : kr = triple.pivot then 
                      have lem1 : right.at kr rlt = 
                            right.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      have lem2 : valuation.at kr rlt = 
                            valuation.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      have lem3 : right.at kr rlt = some false := by
                        rw [wr]
                        rw [lem2]
                        rw [cc]
                        done
                      have lem4 : right.at kr rlt = some true := by
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
                      let eql := skipInverseEqn triple.pivot kr ccc
                      let iw : i < n := skipPreImageBound triple.pivotLt rlt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.at kr rlt = left.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.at kr rlt = right.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let topLem : 
                        top.at kr rlt = top.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let join : Join (left.at kr rlt) (right.at kr rlt) (top.at kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, ⟨rlt, varResolution join (valuation.at kr rlt) (Or.inr (wr))⟩⟩

def triple_stepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (ClauseSat left valuation) → 
        (ClauseSat right valuation) → (ClauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, llt, wl⟩ =>
              fun ⟨kr, rlt, wr⟩ =>
                 if c : valuation.at (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then 
                      have lem1 : left.at kl llt = 
                            left.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      have lem2 : valuation.at kl llt = 
                            valuation.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      have lem3 : left.at kl llt = some true := by
                        rw [wl]
                        rw [lem2]
                        rw [c]
                        done
                      have lem4 : left.at kl llt = some false := by
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
                      let eql := skipInverseEqn triple.pivot kl cc
                      let iw : i < n := skipPreImageBound triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.at kl llt = left.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.at kl llt = right.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let topLem : 
                        top.at kl llt = top.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let join : Join (left.at kl llt) (right.at kl llt) (top.at kl llt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, llt, varResolution join (valuation.at kl llt) (Or.inl (wl))⟩
                  else
                    let cc := eq_false_of_ne_true c  
                    if ccc : kr = triple.pivot then  
                      have lem1 : right.at kr rlt = 
                            right.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      have lem2 : valuation.at kr rlt = 
                            valuation.at triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      have lem3 : right.at kr rlt = some false := by
                        rw [wr]
                        rw [lem2]
                        rw [cc]
                        done
                      have lem4 : right.at kr rlt = some true := by
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
                      let eql := skipInverseEqn triple.pivot kr ccc
                      let iw : i < n := skipPreImageBound triple.pivotLt rlt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left.at kr rlt = left.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let rightLem : 
                        right.at kr rlt = right.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let topLem : 
                        top.at kr rlt = top.at (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw [← eql]
                          done
                      let join : Join (left.at kr rlt) (right.at kr rlt) (top.at kr rlt)  := by
                        rw [leftLem, rightLem, topLem]
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, rlt, varResolution join (valuation.at kr rlt) (Or.inr (wr))⟩

structure LiftedTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool) 
  (left right top : Clause (n + 1))(k: Nat)(lt : k < succ (n + 1)) where
    topFoc : Option Bool
    triple : ResolutionTriple 
          (FinSeq.vec (insert  leftFoc (n + 1) k lt   left.at)) 
          (FinSeq.vec (insert  rightFoc (n + 1) k lt right.at)) 
          (FinSeq.vec (insert  topFoc (n + 1) k lt top.at))
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
          let pivotNLt : pivotN < n + 2 := skipPlusOne rt.pivotLt
          let leftN := insert leftFoc (n + 1) k lt left.at
          let rightN := insert rightFoc (n + 1) k lt right.at
          let topN := insert topFoc (n + 1) k lt top.at
          let leftPivotN : leftN pivotN pivotNLt = some false := 
            have lem1 : leftN pivotN pivotNLt = left.at rt.pivot rt.pivotLt := 
              insertAtImage leftFoc (n + 1) k lt left.at rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.leftPivot
              done
          let rightPivotN : rightN pivotN pivotNLt = some true := 
            have lem1 : rightN pivotN pivotNLt = right.at rt.pivot rt.pivotLt := 
              insertAtImage rightFoc (n + 1) k lt right.at rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.rightPivot
              done
          let topPivotN : topN pivotN pivotNLt = none := 
            have lem1 : topN pivotN pivotNLt = top.at rt.pivot rt.pivotLt := 
              insertAtImage topFoc (n + 1) k lt top.at rt.pivot rt.pivotLt
            by
              rw [lem1]
              exact rt.topPivot
              done

          let joinRestN : (j : Nat) → (jw : j < n + 1) →  
            Join  (leftN (skip pivotN j) (skipPlusOne jw)) 
                  (rightN (skip pivotN j) (skipPlusOne jw)) 
                  (topN (skip pivotN j) (skipPlusOne jw)) := 
                  fun j jw => 
                  let jj := skip pivotN j
                  let jjw : jj < n + 2 := skipPlusOne jw
                  let notPivot : Not (jj = pivotN) := skipNotDiag pivotN j
                  if w : jj = k then  
                    let lem0 := focJoin
                    let eqL : leftN k lt = leftFoc := 
                      insertAtFocus leftFoc (n + 1) k lt left.at 
                    let eqR : rightN k lt = rightFoc := 
                      insertAtFocus rightFoc (n + 1) k lt right.at
                    let eqT : topN k lt = topFoc := 
                      insertAtFocus topFoc (n + 1) k lt top.at
                    let leftLem : leftN jj jjw = leftN k lt := by
                      apply witnessIndependent
                      exact w
                      done
                    let rightLem : rightN jj jjw = rightN k lt := by
                      apply witnessIndependent
                      exact w
                      done 
                    let topLem : topN jj jjw = topN k lt := by
                      apply witnessIndependent
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
                    let w := skipInverseEqn k jj w
                    let iw : i < n + 1 := skipPreImageBound lt jjw w
                    if ww: i = rt.pivot then
                      have lem1 : skip k i = skip k rt.pivot := congrArg (skip k) ww
                      have lem2 : skip k  rt.pivot = jj := by 
                            rw [←  lem1]
                            exact w
                            done
                      absurd (Eq.symm lem2) notPivot
                    else 
                      let ii := skipInverse rt.pivot i ww 
                      let  ww  := skipInverseEqn rt.pivot i ww
                      let iiw : ii < n := skipPreImageBound rt.pivotLt iw ww
                      let eqL : 
                        leftN (skip k i) (skipPlusOne iw) = 
                          left.at i iw := 
                          insertAtImage leftFoc (n + 1) k lt left.at i iw
                      let eqR : 
                        rightN (skip k i) (skipPlusOne iw) = 
                          right.at i iw := 
                          insertAtImage rightFoc (n + 1) k lt right.at i iw              
                      let eqT :
                        topN (skip k i) (skipPlusOne iw) = 
                          top.at i iw := 
                          insertAtImage topFoc (n + 1) k lt top.at i iw
                      let leftLem :
                        leftN jj jjw = leftN (skip k i) (skipPlusOne iw) := 
                          witnessIndependent leftN jj (skip k i) jjw (skipPlusOne iw) (Eq.symm w)
                      let rightLem :
                        rightN jj jjw = rightN (skip k i) (skipPlusOne iw) := 
                          witnessIndependent rightN jj (skip k i) jjw (skipPlusOne iw) (Eq.symm w)
                      let topLem :
                        topN jj jjw = topN (skip k i) (skipPlusOne iw) := 
                          witnessIndependent topN jj (skip k i) jjw (skipPlusOne iw) (Eq.symm w)
                      let leftLem2 :
                        left.at (skip rt.pivot ii) (skipPlusOne iiw) = left.at i iw := by
                          apply witnessIndependent
                          exact ww
                          done
                      let rightLem2 :
                        right.at (skip rt.pivot ii) (skipPlusOne iiw) = right.at i iw := by
                          apply witnessIndependent
                          exact ww
                          done
                      let topLem2 :
                        top.at (skip rt.pivot ii) (skipPlusOne iiw) = top.at i iw := by
                          apply witnessIndependent
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
                          rw [seqAt]
                          rw [← leftPivotN]
                          done
                          ), (
                         by
                          rw [seqAt]
                          rw [←  rightPivotN]
                          done
                          ), (
                         by
                          rw [seqAt]
                          rw [← topPivotN]
                          done
                          ), (
                         by
                          rw [seqAt]
                          intro k1
                          intro w
                          have lp : leftN =
                            insert leftFoc (n + 1) k lt left.at := by rfl
                          have rp : rightN =
                            insert rightFoc (n + 1) k lt right.at := by rfl
                          have tp : topN =
                            insert topFoc (n + 1) k lt top.at := by rfl
                          rw [← lp, ← rp, ← tp]
                          have rn: (Vector.at (FinSeq.vec rightN)) = rightN :=
                            by rw [seqAt] 
                          have ln: (Vector.at (FinSeq.vec leftN)) = leftN :=
                            by rw [seqAt]
                          have tn: (Vector.at (FinSeq.vec topN)) = topN :=
                            by rw [seqAt]
                          rw [rn, tn]
                          apply joinRestN
                          assumption
                          done
                          )⟩, topNonPos⟩
      

inductive ResolutionTree{dom n: Nat}
      (clauses : Vector   (Clause (n + 1)) dom) : (Clause (n + 1)) → Type  where
  | assumption : (index : Nat) → (indexBound : index < dom ) → (top : Clause (n + 1)) → 
          clauses.at index indexBound = top → 
          ResolutionTree clauses top
  | resolve : (left right top : Clause (n + 1)) → 
                (leftTree : ResolutionTree clauses left) → 
                (rightTree: ResolutionTree clauses right) →
                ResolutionTriple left right top 
                → ResolutionTree clauses top


def Clause.toString {n: Nat}: Clause n → String :=
  fun (cls : Clause n) => (cls.at.list).toString

instance {n: Nat} : ToString (Clause n) := 
  ⟨fun (cls : Clause n) => (cls.at.list).toString⟩

instance {n: Nat}{α: Type}[ToString α] : ToString (FinSeq n α) := 
  ⟨fun seq => (seq.list).toString⟩

def ResolutionTree.toString{dom n: Nat}{clauses : Vector  (Clause (n + 1)) dom}
      {top : Clause (n + 1)}
        (rt: ResolutionTree clauses top) : String := 
      match rt with
      | ResolutionTree.assumption i iw _ _  => (FinSeq.list (Vector.at (clauses.at i iw))).toString
      | ResolutionTree.resolve left right .(top) leftTree rightTree triple => 
                top.toString ++ " from " ++ left.toString ++ " & " ++ right.toString  ++ 
                "; using: {" ++ 
                leftTree.toString ++ "} and {" ++ rightTree.toString ++ "}"


def resolutionToProof{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom)(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top) →  (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → clauseSat (clauses.at j jw) valuation) → clauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn  => 
          fun valuation base  => 
            have lem0 : clauses.at j jw = top := eqn
            have lem1 : clauseSat (clauses.at j jw) valuation := base j jw
          by
            rw [←  lem0]
            exact lem1
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  => 
          fun valuation base => 
              let leftBase : clauseSat left valuation := 
                resolutionToProof clauses left leftTree valuation base 
              let rightBase : clauseSat right valuation := 
                resolutionToProof clauses right rightTree  valuation base 
              let lemStep := triple_stepProof left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom)(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top)  → (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → ClauseSat (clauses.at j jw) valuation)
           → ClauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn => 
          fun valuation base  => 
            have lem1 : ClauseSat (clauses.at j jw) valuation := base j jw
          by
            rw [← eqn]
            exact lem1
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  => 
          fun valuation base => 
              let leftBase : ClauseSat left valuation := 
                resolutionToSat clauses left leftTree valuation base 
              let rightBase : ClauseSat right valuation := 
                resolutionToSat clauses right rightTree valuation base 
              let lemStep := triple_stepSat left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

inductive SatSolution{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) where
  | unsat : (tree : ResolutionTree clauses (contradiction (n + 1))) → 
          SatSolution clauses
  | sat : (valuation : Valuation (n + 1)) → ((k : Nat) → (kw : k < dom) 
        → ClauseSat (clauses.at k kw) valuation) → SatSolution clauses 

def SatSolution.toString{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
        (sol: SatSolution clauses) →  String := 
      fun sol =>
      match sol with
      | unsat tree => "unsat: " ++ tree.toString 
      | sat valuation _ => "sat: " ++ (valuation.at.list).toString

def solutionProp{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat tree  => 
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                (Vector.at (clauses.at p pw) k kw) = some (valuation.at k kw))
  | SatSolution.sat _ _ =>
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), 
                (Vector.at (clauses.at p pw) k kw) = some (valuation.at k kw) 



def solutionProof{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree   => 
          fun valuation =>
            fun hyp : ∀ p : Nat, ∀ pw : p < dom, clauseSat (clauses.at p pw) valuation =>
              let lem := resolutionToProof clauses (contradiction (n + 1))
                            tree valuation hyp
              contradictionFalse _ valuation lem
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
                (eqn: clauses.at j jw = unitClause n branch focus focusLt):
                ResolutionTree clauses (unitClause n branch focus focusLt) :=
                  ResolutionTree.assumption j jw (unitClause n branch focus focusLt) eqn
                  


structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : Vector (Clause (n + 1)) dom)(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionTree clauses (FinSeq.vec (insert topFocus n focus focusLt top.at))

inductive LiftedResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: Vector (Clause (n + 2)) dom) where
    | contra : ResolutionTree clauses (contradiction (n + 2)) → 
                  LiftedResPf branch focus focusLt clauses
    | unit : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) → 
                  LiftedResPf branch focus focusLt clauses

theorem notNot2(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
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
            let cl := clauses.at k kw
            let topFocus := cl.at focus focusLt
            let nonPosLem : Not (topFocus = some branch)  := 
                np.nonPosRev j jw
            have lem1 : Vector.at (rc.restClauses.at j jw) = 
                  delete focus focusLt (Vector.at (clauses.at k kw)) 
                       := by
                       apply rr.relation
                       done
            have lem3 : insert (cl.at focus focusLt) (n + 1) focus focusLt 
                          (delete focus focusLt cl.at) = cl.at 
                          := insertDelete focus focusLt cl.at
            have lem : insert topFocus (n + 1) focus focusLt top.at = cl.at := by
                      rw [← ttp]
                      rw [lem1]
                      rw [lem3]
                      done 
            ⟨topFocus, nonPosLem,
              ResolutionTree.assumption k kw  _ (by
                    rw [lem]
                    have lc : FinSeq.vec (Vector.at cl) = cl := by 
                      apply equalCoords
                      apply seqAt
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
                              (FinSeq.vec (insert leftFoc _ focus focusLt left.at))
                              (FinSeq.vec (insert rightFoc _ focus focusLt right.at))
                              (FinSeq.vec (insert topFoc _ focus focusLt top.at))
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
                  FinSeq.vec (insert none (Nat.add n 1) focus focusLt (Vector.at (contradiction (n + 1)))) =
                    contradiction (n + 2) := by
                      rw [contradictionInsNone focus focusLt]
                      apply equalCoords
                      apply seqAt
                      done            
                let t : ResolutionTree clauses (contradiction (n + 2)) := by
                            rw [← lem]
                            exact tree
                            done
                LiftedResPf.contra t
            | some b, ineq, tree =>
                have lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := notNot2 branch lemPar
                let t : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) := 
                          by
                            rw [← par]
                            exact tree
                            done
                LiftedResPf.unit t

def transportResPf{l1 l2 n : Nat}(clauses1 : Vector (Clause (n + 1)) l1)
                  (clauses2: Vector (Clause (n + 1)) l2)
                  (embed: (j : Nat) → (jw : j < l1) → ElemInSeq clauses2.at (clauses1.at j jw))
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

theorem proofsPreverveNonPos{dom n : Nat}{clauses : Vector (Clause (n + 1)) dom}
                (bf: Bool)(k : Nat)(kw : k < n + 1)
                (base : (j : Nat) → (lt : j < dom) → 
                  Not (Vector.at (clauses.at j lt) k kw = some bf)) : 
                (top : Clause (n + 1)) → 
                (tree : ResolutionTree clauses top) → 
                Not (top.at k kw = some bf) := 
                  fun top tree =>
                  match tree with
                  | ResolutionTree.assumption ind  bd .(top) chk =>
                    fun  hyp => 
                      have lem0 : clauses.at ind bd = top := chk
                      have lem1 : Not (top.at k kw = some bf) := by
                              rw [←  lem0]
                              exact (base ind bd)
                      absurd hyp lem1
                  | ResolutionTree.resolve left right .(top) leftTree rightTree triple =>
                    fun hyp => 
                      let leftLem :=
                        proofsPreverveNonPos bf k kw base left leftTree 
                      let rightLem :=
                        proofsPreverveNonPos bf k kw base right rightTree 
                      if c : k = triple.pivot then 
                          match bf, k, c, kw, leftLem, rightLem with
                          | false, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                                lL (triple.leftPivot)
                          | true, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                                rL (triple.rightPivot)
                      else 
                          let j := skipInverse triple.pivot k c 
                          let eqn  := skipInverseEqn triple.pivot k c
                          let jw := skipPreImageBound triple.pivotLt kw eqn
                          let joinIm := triple.joinRest j jw
                          match (skip triple.pivot j), eqn, (skipPlusOne jw), joinIm with 
                          | .(k), rfl, .(kw), join => 
                            let lem := 
                              topJoinNonPos bf (left.at k kw) (right.at k kw) (top.at k kw) join
                                leftLem rightLem
                            lem hyp               



