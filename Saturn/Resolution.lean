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
    Eq.trans (eqFalseOfNeTrue w) (Eq.symm (eqFalseOfNeTrue ww))
  | false => fun w ww => 
    Eq.trans (eqTrueOfNeFalse w) (Eq.symm (eqTrueOfNeFalse ww))

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
                let lem1 : Not (bb = bf) := by
                  intro hyp
                  exact (wr (congrArg some hyp))
                  done
                let lem2 : bb = b := notNot bf bb b lem1 c
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
              let lem : left = some bf := by
                rw wl
                rw ← wt
                assumption
                done
              nwl lem
          | Join.noneSome b _ wr wt => 
            fun _ nwr  hyp => 
              let lem : right = some bf := by
                rw wr
                rw ← wt
                assumption
                done
              nwr lem
          | Join.someSome b wl _ wt => 
            fun nwl _  hyp => 
              let lem : left = some bf := by
                rw wl
                rw ← wt
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
        let lem : top = left := Eq.trans pt (Eq.symm pl)
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
        let lem : top = right := Eq.trans pt (Eq.symm pr)
        Eq.trans lem heq  
    | Join.someSome b pl pr pt => 
      match hyp with
      | Or.inl heq => 
        let lem : top = left := Eq.trans pt (Eq.symm pl)
        Eq.trans lem heq
      | Or.inr heq => 
        let lem : top = right := Eq.trans pt (Eq.symm pr)
        Eq.trans lem heq

 

structure ResolutionTriple{n: Nat}(left right top : Clause (n + 1)) where
  pivot : Nat
  pivotLt : pivot < n + 1
  leftPivot : left pivot pivotLt = some false
  rightPivot : right pivot pivotLt = some true
  topPivot : top pivot pivotLt = none
  joinRest : (k : Nat) → (w : k < n) →  
    Join  (left (skip pivot k) (skipPlusOne w)) 
          (right (skip pivot k) (skipPlusOne w)) 
          (top (skip pivot k) (skipPlusOne w))

def unitTriple(n : Nat)(k: Nat)(lt : k < n + 1) :
        ResolutionTriple (unitClause n false  k lt) (unitClause n true k lt) (contradiction (n + 1)) :=
          ⟨k, lt, 
            unitDiag n false k lt , 
            unitDiag n true k lt, 
            rfl, 
            fun j jw => Join.noneNone 
                      (unitSkip n false k lt j jw) 
                      (unitSkip n true k lt j jw) 
                      rfl
                      ⟩

def tripleStepProof{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (clauseSat left valuation) → 
        (clauseSat right valuation) → (clauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, ⟨llt, wl⟩⟩ =>
              fun ⟨kr, ⟨rlt, wr⟩⟩ =>
                 if c : valuation (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then
                      let lem1 : left kl llt = 
                            left triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      let lem2 : valuation kl llt = 
                            valuation triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      let lem3 : left kl llt = some true := by
                        rw wl
                        rw lem2
                        rw c
                        done
                      let lem4 : left kl llt = some false := by
                        rw lem1
                        exact triple.leftPivot
                        done 
                      let lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : true = false := by 
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
                        left kl llt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let rightLem : 
                        right kl llt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let topLem : 
                        top kl llt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let join : Join (left kl llt) (right kl llt) (top kl llt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, ⟨llt, varResolution join (valuation kl llt) (Or.inl (wl))⟩⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    if ccc : kr = triple.pivot then 
                      let lem1 : right kr rlt = 
                            right triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      let lem2 : valuation kr rlt = 
                            valuation triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      let lem3 : right kr rlt = some false := by
                        rw wr
                        rw lem2
                        rw cc
                        done
                      let lem4 : right kr rlt = some true := by
                        rw lem1
                        exact triple.rightPivot
                        done 
                      let lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : false = true := by 
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
                        left kr rlt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let rightLem : 
                        right kr rlt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let topLem : 
                        top kr rlt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let join : Join (left kr rlt) (right kr rlt) (top kr rlt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, ⟨rlt, varResolution join (valuation kr rlt) (Or.inr (wr))⟩⟩

def tripleStepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuation: Valuation (n + 1))  → (ClauseSat left valuation) → 
        (ClauseSat right valuation) → (ClauseSat top valuation) := 
          fun valuation =>
            fun ⟨kl, llt, wl⟩ =>
              fun ⟨kr, rlt, wr⟩ =>
                 if c : valuation (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    if cc : kl = triple.pivot then 
                      let lem1 : left kl llt = 
                            left triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      let lem2 : valuation kl llt = 
                            valuation triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply cc
                            done 
                      let lem3 : left kl llt = some true := by
                        rw wl
                        rw lem2
                        rw c
                        done
                      let lem4 : left kl llt = some false := by
                        rw lem1
                        exact triple.leftPivot
                        done 
                      let lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : true = false := by 
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
                        left kl llt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let rightLem : 
                        right kl llt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let topLem : 
                        top kl llt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let join : Join (left kl llt) (right kl llt) (top kl llt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, llt, varResolution join (valuation kl llt) (Or.inl (wl))⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    if ccc : kr = triple.pivot then  
                      let lem1 : right kr rlt = 
                            right triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      let lem2 : valuation kr rlt = 
                            valuation triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply ccc
                            done 
                      let lem3 : right kr rlt = some false := by
                        rw wr
                        rw lem2
                        rw cc
                        done
                      let lem4 : right kr rlt = some true := by
                        rw lem1
                        exact triple.rightPivot
                        done 
                      let lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : false = true := by 
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
                        left kr rlt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let rightLem : 
                        right kr rlt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let topLem : 
                        top kr rlt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          rw ← eql
                          done
                      let join : Join (left kr rlt) (right kr rlt) (top kr rlt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, rlt, varResolution join (valuation kr rlt) (Or.inr (wr))⟩

structure LiftedTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool) 
  (left right top : Clause (n + 1))(k: Nat)(lt : k < succ (n + 1)) where
    topFoc : Option Bool
    triple : ResolutionTriple 
          (insert  leftFoc (n + 1) k lt   left) 
          (insert  rightFoc (n + 1) k lt right) 
          (insert  topFoc (n + 1) k lt top)
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
          let leftN := insert leftFoc (n + 1) k lt left
          let rightN := insert rightFoc (n + 1) k lt right
          let topN := insert topFoc (n + 1) k lt top
          let leftPivotN : leftN pivotN pivotNLt = some false := 
            let lem1 : leftN pivotN pivotNLt = left rt.pivot rt.pivotLt := 
              insertAtImage leftFoc (n + 1) k lt left rt.pivot rt.pivotLt
            by
              rw lem1
              exact rt.leftPivot
              done
          let rightPivotN : rightN pivotN pivotNLt = some true := 
            let lem1 : rightN pivotN pivotNLt = right rt.pivot rt.pivotLt := 
              insertAtImage rightFoc (n + 1) k lt right rt.pivot rt.pivotLt
            by
              rw lem1
              exact rt.rightPivot
              done
          let topPivotN : topN pivotN pivotNLt = none := 
            let lem1 : topN pivotN pivotNLt = top rt.pivot rt.pivotLt := 
              insertAtImage topFoc (n + 1) k lt top rt.pivot rt.pivotLt
            by
              rw lem1
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
                      insertAtFocus leftFoc (n + 1) k lt left 
                    let eqR : rightN k lt = rightFoc := 
                      insertAtFocus rightFoc (n + 1) k lt right
                    let eqT : topN k lt = topFoc := 
                      insertAtFocus topFoc (n + 1) k lt top
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
                      rw leftLem
                      rw rightLem
                      rw topLem
                      rw eqL
                      rw eqR
                      rw eqT
                      exact lem0
                      done
                    goal
                  else 
                    let i := skipInverse k jj w
                    let w := skipInverseEqn k jj w
                    let iw : i < n + 1 := skipPreImageBound lt jjw w
                    if ww: i = rt.pivot then
                      let lem1 : skip k i = skip k rt.pivot := congrArg (skip k) ww
                      let lem2 : skip k  rt.pivot = jj := by 
                            rw (Eq.symm lem1)
                            exact w
                            done
                      absurd (Eq.symm lem2) notPivot
                    else 
                      let ii := skipInverse rt.pivot i ww 
                      let  ww  := skipInverseEqn rt.pivot i ww
                      let iiw : ii < n := skipPreImageBound rt.pivotLt iw ww
                      let eqL : 
                        leftN (skip k i) (skipPlusOne iw) = 
                          left i iw := 
                          insertAtImage leftFoc (n + 1) k lt left i iw
                      let eqR : 
                        rightN (skip k i) (skipPlusOne iw) = 
                          right i iw := 
                          insertAtImage rightFoc (n + 1) k lt right i iw              
                      let eqT :
                        topN (skip k i) (skipPlusOne iw) = 
                          top i iw := 
                          insertAtImage topFoc (n + 1) k lt top i iw
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
                        left (skip rt.pivot ii) (skipPlusOne iiw) = left i iw := by
                          apply witnessIndependent
                          exact ww
                          done
                      let rightLem2 :
                        right (skip rt.pivot ii) (skipPlusOne iiw) = right i iw := by
                          apply witnessIndependent
                          exact ww
                          done
                      let topLem2 :
                        top (skip rt.pivot ii) (skipPlusOne iiw) = top i iw := by
                          apply witnessIndependent
                          exact ww
                          done
                      let prevJoin := rt.joinRest ii iiw
                      let goal : Join (leftN jj jjw) (rightN jj jjw) (topN jj jjw) := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        rw eqL
                        rw eqR
                        rw eqT
                        rw ← leftLem2
                        rw ← rightLem2
                        rw ← topLem2
                        exact prevJoin
                        done
                      goal
      ⟨topFoc, ⟨pivotN, pivotNLt,
                       leftPivotN, rightPivotN, topPivotN, joinRestN⟩, topNonPos⟩
      

inductive ResolutionTree{dom n: Nat}
      (clauses : FinSeq dom   (Clause (n + 1))) : (Clause (n + 1)) → Type  where
  | assumption : (index : Nat) → (indexBound : index < dom ) → (top : Clause (n + 1)) → 
          clauses index indexBound = top → 
          ResolutionTree clauses top
  | resolve : (left right top : Clause (n + 1)) → 
                (leftTree : ResolutionTree clauses left) → 
                (rightTree: ResolutionTree clauses right) →
                ResolutionTriple left right top 
                → ResolutionTree clauses top


def Clause.toString {n: Nat}: Clause n → String :=
  fun (cls : Clause n) => (list cls).toString

instance {n: Nat} : ToString (Clause n) := 
  ⟨fun (cls : Clause n) => (list cls).toString⟩

instance {n: Nat}{α: Type}[ToString α] : ToString (FinSeq n α) := 
  ⟨fun seq => (list seq).toString⟩

def ResolutionTree.toString{dom n: Nat}{clauses : FinSeq dom   (Clause (n + 1))}
      {top : Clause (n + 1)}
        (rt: ResolutionTree clauses top) : String := 
      match rt with
      | ResolutionTree.assumption i iw _ _  => (list (clauses i iw)).toString
      | ResolutionTree.resolve left right .(top) leftTree rightTree triple => 
                top.toString ++ " from " ++ left.toString ++ " & " ++ right.toString  ++ 
                "; using: {" ++ 
                leftTree.toString ++ "} and {" ++ rightTree.toString ++ "}"


-- def treeTop{dom n: Nat}{clauses : FinSeq dom   (Clause (n + 1))}
--               (tree: ResolutionTree clauses) : Clause (n + 1) :=
--       match tree with
--       | ResolutionTree.assumption j jw => clauses j jw
--       | ResolutionTree.resolve left right  top leftTree rightTree triple  => top 

-- def treeCheck{dom n: Nat}{clauses : FinSeq dom   (Clause (n + 1))}
--               (tree: ResolutionTree clauses)(top : Clause (n + 1)) : Prop :=
--       match tree with
--       | ResolutionTree.assumption j jw => clauses j jw = top
--       | ResolutionTree.resolve left right  top leftTree rightTree triple  => 
--           (((treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
--           ((treeTop leftTree = left) ∧  ((treeTop rightTree = right)))

-- structure ResolutionProof{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))
--         (top : Clause (n + 1)) where
--   tree : ResolutionTree clauses
--   check : treeCheck tree top
--   checkTop : treeTop tree = top

def resolutionToProof{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top) →  (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → clauseSat (clauses j jw) valuation) → clauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn  => 
          fun valuation base  => 
            let lem0 : clauses j jw = top := eqn
            let lem1 : clauseSat (clauses j jw) valuation := base j jw
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  .(top) leftTree rightTree triple  => 
          fun valuation base => 
              let leftBase : clauseSat left valuation := 
                resolutionToProof clauses left leftTree valuation base 
              let rightBase : clauseSat right valuation := 
                resolutionToProof clauses right rightTree  valuation base 
              let lemStep := tripleStepProof left right top triple valuation leftBase rightBase
            by
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses top)  → (valuation :Valuation (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → ClauseSat (clauses j jw) valuation) → ClauseSat top valuation := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw .(top) eqn => 
          fun valuation base  => 
            let lem1 : ClauseSat (clauses j jw) valuation := base j jw
          by
            rw ← eqn
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

inductive SatSolution{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1))) where
  | unsat : (tree : ResolutionTree clauses (contradiction (n + 1))) → 
          SatSolution clauses
  | sat : (valuation : Valuation (n + 1)) → ((k : Nat) → (kw : k < dom) 
        → ClauseSat (clauses k kw) valuation) → SatSolution clauses 

def SatSolution.toString{dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}:
        (sol: SatSolution clauses) →  String := 
      fun sol =>
      match sol with
      | unsat tree => "unsat: " ++ tree.toString 
      | sat valuation _ => "sat: " ++ (list valuation).toString

def solutionProp{dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat tree  => 
          ∀ valuation : Valuation (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuation k kw))
  | SatSolution.sat _ _ =>
          ∃ valuation : Valuation (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuation k kw) 



def solutionProof{dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree   => 
          fun valuation =>
            fun hyp : ∀ p : Nat, ∀ pw : p < dom, clauseSat (clauses p pw) valuation =>
              let lem := resolutionToProof clauses (contradiction (n + 1))
                            tree valuation hyp
              contradictionFalse _ valuation lem
  | SatSolution.sat valuation evidence =>
          ⟨valuation, fun k kw => getProof (evidence k kw)⟩

instance {dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                   : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def treeToUnsat{dom n: Nat}{clauses : FinSeq dom  (Clause (n + 1))} :
                (rpf : ResolutionTree clauses (contradiction _)) → 
                        SatSolution clauses := fun rpf =>
          SatSolution.unsat rpf 

def mergeUnitTrees{dom n: Nat}{clauses : FinSeq dom  (Clause (n + 1))}
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

def mergeAlignUnitTrees{dom n: Nat}{branch : Bool}{clauses : FinSeq dom  (Clause (n + 1))}
                {focus : Nat}{focusLt : focus < n + 1}
                 (first: ResolutionTree clauses (unitClause n branch focus focusLt))
                (second: ResolutionTree clauses (unitClause n (not branch) focus focusLt)) :
                ResolutionTree clauses (contradiction (n + 1)) := 
                match branch, first, second with
                | false, left, right =>
                    mergeUnitTrees focus focusLt left right
                | true, right, left => 
                    mergeUnitTrees focus focusLt left right

def unitProof{dom n: Nat}{branch : Bool}{clauses : FinSeq dom  (Clause (n + 1))}
                {focus : Nat}{focusLt : focus < n + 1}{j : Nat}{jw : j < dom}
                (eqn: clauses j jw = unitClause n branch focus focusLt):
                ResolutionTree clauses (unitClause n branch focus focusLt) :=
                  ResolutionTree.assumption j jw (unitClause n branch focus focusLt) eqn
                  


structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionTree clauses (insert topFocus n focus focusLt top)

inductive LiftedResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2))) where
    | contra : ResolutionTree clauses (contradiction (n + 2)) → 
                  LiftedResPf branch focus focusLt clauses
    | unit : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) → 
                  LiftedResPf branch focus focusLt clauses

theorem notNot2(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
  match b with
  | true => fun w => eqFalseOfNeTrue w
  | false => fun w => eqTrueOfNeFalse w

def pullBackTree{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc): (top : Clause (n + 1)) → 
      (tree : ResolutionTree (rc.restClauses) top) 
       → BranchResolutionProof branch focus focusLt clauses top  := 
      fun top tree =>
        match tree with
        | ResolutionTree.assumption j jw .(top) ttp => 
            let k := rc.reverse j jw
            let kw : k < dom := rc.reverseWit j jw
            let cl := clauses k kw
            let topFocus := cl focus focusLt
            let nonPosLem : Not (topFocus = some branch)  := 
                np.nonPosRev j jw
            let lem1 : rc.restClauses j jw = 
                  delete focus focusLt (clauses k kw) 
                       := by
                       apply rr.relation
                       done
            let lem3 : insert (cl focus focusLt) (n + 1) focus focusLt 
                          (delete focus focusLt cl) = cl 
                          := insertDelete focus focusLt cl
            let lem : insert topFocus (n + 1) focus focusLt top = cl := by
                      rw ← ttp
                      rw lem1
                      rw lem3
                      done 
            ⟨topFocus, nonPosLem,
              ResolutionTree.assumption k kw  _ (by
                    rw lem
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
                              (insert leftFoc _ focus focusLt left)
                              (insert rightFoc _ focus focusLt right)
                              (insert topFoc _ focus focusLt top)
                              leftLiftTree rightLiftTree liftTriple
              ⟨topFoc, topNonPos, tree⟩

def pullBackResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc) : 
        ResolutionTree rc.restClauses (contradiction (n + 1)) → 
            LiftedResPf branch focus focusLt clauses := fun rpf =>
            let pbt := pullBackTree branch focus focusLt clauses rc np rr 
                                (contradiction (n + 1)) rpf 
            match pbt.topFocus, pbt.nonPos, pbt.provedTree with 
            | none, _, tree => 
                let lem := contradictionInsNone focus focusLt            
                let t : ResolutionTree clauses (contradiction (n + 2)) := by
                            rw ← lem
                            exact tree
                LiftedResPf.contra t
            | some b, ineq, tree =>
                let lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := notNot2 branch lemPar
                let t : ResolutionTree clauses (unitClause (n + 1) (not branch) focus focusLt) := 
                          by
                            rw ← par
                            exact tree
                            done
                LiftedResPf.unit t

def transportResPf{l1 l2 n : Nat}(clauses1 : FinSeq l1 (Clause (n + 1)))
                  (clauses2: FinSeq l2 (Clause (n + 1)))
                  (embed: (j : Nat) → (jw : j < l1) → ElemInSeq clauses2 (clauses1 j jw))
                  (top: Clause (n + 1)): 
                  (tree : ResolutionTree clauses1 top) → 
                              ResolutionTree clauses2 top := 
                      fun tree => 
                      match tree with
                      | ResolutionTree.assumption ind  bd .(top) te =>
                          let ⟨i, iw, eqn⟩ := embed ind bd                        
                          ResolutionTree.assumption i iw _ (by 
                            rw eqn
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

theorem proofsPreverveNonPos{dom n : Nat}{clauses : FinSeq dom (Clause (n + 1))}
                (bf: Bool)(k : Nat)(kw : k < n + 1)
                (base : (j : Nat) → (lt : j < dom) → Not (clauses j lt k kw = some bf)) : 
                (top : Clause (n + 1)) → 
                (tree : ResolutionTree clauses top) → 
                Not (top k kw = some bf) := 
                  fun top tree =>
                  match tree with
                  | ResolutionTree.assumption ind  bd .(top) chk =>
                    fun  hyp => 
                      let lem0 : clauses ind bd = top := chk
                      let lem1 : Not (top k kw = some bf) := by
                              rw (Eq.symm lem0)
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
                              topJoinNonPos bf (left k kw) (right k kw) (top k kw) join
                                leftLem rightLem
                            lem hyp               



