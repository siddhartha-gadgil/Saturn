import Saturn.Basic
import Saturn.FinSeq 
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
                rw (Eq.symm wt)
                assumption
                done
              nwl lem
          | Join.noneSome b _ wr wt => 
            fun _ nwr  hyp => 
              let lem : right = some bf := by
                rw wr
                rw (Eq.symm wt)
                assumption
                done
              nwr lem
          | Join.someSome b wl _ wt => 
            fun nwl _  hyp => 
              let lem : left = some bf := by
                rw wl
                rw (Eq.symm wt)
                assumption
                done
              nwl lem


theorem varResolution {left right top : Option Bool}(join: Join left right top)(valuatVal : Bool) :
  Or (varSat left valuatVal) (varSat right valuatVal) → (varSat top valuatVal)  :=
  fun hyp  =>
    match join with
    | Join.noneNone pl pr pt => 
      match hyp with
      | Or.inl heq => 
        let contra: none = some (valuatVal) := Eq.trans (Eq.symm pl) heq
        Option.noConfusion contra
      | Or.inr heq => 
        let contra: none = some (valuatVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra 
    | Join.someNone b pl pr pt =>
      match hyp with
      | Or.inl (heq : left = some valuatVal) => 
        let lem : top = left := Eq.trans pt (Eq.symm pl)
        Eq.trans lem heq
      | Or.inr heq => 
        let contra: none = some (valuatVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra  
    | Join.noneSome b pl pr pt =>
      match hyp with
      | Or.inl heq => 
        let contra: none = some (valuatVal) := Eq.trans (Eq.symm pl) heq
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

namespace leaner 

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
        ResolutionTriple (unitClause n false  k lt) (unitClause n true k lt) (contrad (n + 1)) :=
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
        (valuat: Valuat (n + 1))  → (clauseSat left valuat) → 
        (clauseSat right valuat) → (clauseSat top valuat) := 
          fun valuat =>
            fun ⟨kl, ⟨llt, wl⟩⟩ =>
              fun ⟨kr, ⟨rlt, wr⟩⟩ =>
                 if c : valuat (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    match skipImageCase triple.pivot kl  with
                    | SkipImageCase.diag eql => 
                      let lem1 : left kl llt = 
                            left triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
                            done 
                      let lem2 : valuat kl llt = 
                            valuat triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
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
                    | SkipImageCase.image i eql => 
                      let iw : i < n := skipPreImageBound triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left kl llt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let rightLem : 
                        right kl llt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let topLem : 
                        top kl llt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let join : Join (left kl llt) (right kl llt) (top kl llt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, ⟨llt, varResolution join (valuat kl llt) (Or.inl (wl))⟩⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    match skipImageCase triple.pivot kr  with
                    | SkipImageCase.diag eql => 
                      let lem1 : right kr rlt = 
                            right triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
                            done 
                      let lem2 : valuat kr rlt = 
                            valuat triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
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
                    | SkipImageCase.image i eql => 
                      let iw : i < n := skipPreImageBound triple.pivotLt rlt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left kr rlt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let rightLem : 
                        right kr rlt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let topLem : 
                        top kr rlt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let join : Join (left kr rlt) (right kr rlt) (top kr rlt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, ⟨rlt, varResolution join (valuat kr rlt) (Or.inr (wr))⟩⟩

def tripleStepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuat: Valuat (n + 1))  → (ClauseSat left valuat) → 
        (ClauseSat right valuat) → (ClauseSat top valuat) := 
          fun valuat =>
            fun ⟨kl, llt, wl⟩ =>
              fun ⟨kr, rlt, wr⟩ =>
                 if c : valuat (triple.pivot) (triple.pivotLt)  then 
                    -- the left branch survives
                    match skipImageCase triple.pivot kl  with
                    | SkipImageCase.diag eql => 
                      let lem1 : left kl llt = 
                            left triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
                            done 
                      let lem2 : valuat kl llt = 
                            valuat triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
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
                    | SkipImageCase.image i eql => 
                      let iw : i < n := skipPreImageBound triple.pivotLt llt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left kl llt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let rightLem : 
                        right kl llt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let topLem : 
                        top kl llt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let join : Join (left kl llt) (right kl llt) (top kl llt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kl, llt, varResolution join (valuat kl llt) (Or.inl (wl))⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    match skipImageCase triple.pivot kr  with
                    | SkipImageCase.diag eql => 
                      let lem1 : right kr rlt = 
                            right triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
                            done 
                      let lem2 : valuat kr rlt = 
                            valuat triple.pivot triple.pivotLt := by
                            apply witnessIndependent
                            apply eql
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
                    | SkipImageCase.image i eql => 
                      let iw : i < n := skipPreImageBound triple.pivotLt rlt eql 
                      let jj := triple.joinRest i iw
                      let leftLem : 
                        left kr rlt = left (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let rightLem : 
                        right kr rlt = right (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let topLem : 
                        top kr rlt = top (skip triple.pivot i) (skipPlusOne iw) := by
                          apply witnessIndependent
                          apply (Eq.symm eql)
                          done
                      let join : Join (left kr rlt) (right kr rlt) (top kr rlt)  := by
                        rw leftLem
                        rw rightLem
                        rw topLem
                        exact triple.joinRest i iw
                        done 
                      ⟨kr, rlt, varResolution join (valuat kr rlt) (Or.inr (wr))⟩

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
                  match skipImageCase k jj with
                  | SkipImageCase.diag w =>  
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
                  | SkipImageCase.image i w => 
                    let iw : i < n + 1 := skipPreImageBound lt jjw w
                    match skipImageCase rt.pivot i with
                    | SkipImageCase.diag ww => 
                      let lem1 : skip k i = skip k rt.pivot := congrArg (skip k) ww
                      let lem2 : skip k  rt.pivot = jj := by 
                            rw (Eq.symm lem1)
                            exact w
                            done
                      absurd (Eq.symm lem2) notPivot
                    | SkipImageCase.image ii ww => 
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
                        rw (Eq.symm leftLem2)
                        rw (Eq.symm rightLem2)
                        rw (Eq.symm topLem2)
                        exact prevJoin
                        done
                      goal
      ⟨topFoc, ⟨pivotN, pivotNLt,
                       leftPivotN, rightPivotN, topPivotN, joinRestN⟩, topNonPos⟩
      

inductive ResolutionTree{dom n: Nat}(clauses : FinSeq dom   (Clause (n + 1))) where
  | assumption : (index : Nat) → (indexBound : index < dom ) → ResolutionTree clauses 
  | resolve : (left right top : Clause (n + 1)) → 
                (leftTree : ResolutionTree clauses) → 
                (rightTree: ResolutionTree clauses) →
                ResolutionTriple left right top 
                → ResolutionTree clauses

def treeTop{dom n: Nat}{clauses : FinSeq dom   (Clause (n + 1))}
              (tree: ResolutionTree clauses) : Clause (n + 1) :=
      match tree with
      | ResolutionTree.assumption j jw => clauses j jw
      | ResolutionTree.resolve left right  top leftTree rightTree triple  => top 

def treeCheck{dom n: Nat}{clauses : FinSeq dom   (Clause (n + 1))}
              (tree: ResolutionTree clauses)(top : Clause (n + 1)) : Prop :=
      match tree with
      | ResolutionTree.assumption j jw => clauses j jw = top
      | ResolutionTree.resolve left right  top leftTree rightTree triple  => 
          (((treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
          ((treeTop leftTree = left) ∧  ((treeTop rightTree = right)))

structure ResolutionProof{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))
        (top : Clause (n + 1)) where
  tree : ResolutionTree clauses
  check : treeCheck tree top
  checkTop : treeTop tree = top

def resolutionToProof{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (valuat :Valuat (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → clauseSat (clauses j jw) valuat) → clauseSat top valuat := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw => 
          fun tpf _ valuat base  => 
            let lem0 : clauses j jw = top := tpf
            let lem1 : clauseSat (clauses j jw) valuat := base j jw
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) valuat base => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧  ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : clauseSat left valuat := 
                resolutionToProof clauses left leftTree lemLc lemLt valuat base 
              let rightBase : clauseSat right valuat := 
                resolutionToProof clauses right rightTree lemRc lemRt valuat base 
              let lemStep := tripleStepProof left right topt triple valuat leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (valuat :Valuat (n + 1))→ 
    ((j : Nat) → (jw : j < dom) → ClauseSat (clauses j jw) valuat) → ClauseSat top valuat := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j jw => 
          fun tpf _ valuat base  => 
            let lem0 : clauses j jw = top := tpf
            let lem1 : ClauseSat (clauses j jw) valuat := base j jw
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) valuat base => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧  ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : ClauseSat left valuat := 
                resolutionToSat clauses left leftTree lemLc lemLt valuat base 
              let rightBase : ClauseSat right valuat := 
                resolutionToSat clauses right rightTree lemRc lemRt valuat base 
              let lemStep := tripleStepSat left right topt triple valuat leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

inductive SatSolution{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1))) where
  | unsat : (tree : ResolutionTree clauses) → 
        treeCheck tree (contrad (n + 1))  →  treeTop tree = contrad (n + 1) 
          →  SatSolution clauses
  | sat : (valuat : Valuat (n + 1)) → ((k : Nat) → (kw : k < dom) 
        → ClauseSat (clauses k kw) valuat) → SatSolution clauses 

def solutionProp{dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat _ _ _   => 
          ∀ valuat : Valuat (n + 1),  
           Not (∀ (p : Nat),
            ∀ pw : p < dom,   
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuat k kw))
  | SatSolution.sat _ _ =>
          ∃ valuat : Valuat (n + 1),  
           ∀ (p : Nat),
            ∀ pw : p < dom, 
              ∃ (k : Nat), ∃ (kw : k < n + 1), (clauses p pw k kw) = some (valuat k kw) 

def solutionProof{dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree check checkTop   => 
          fun valuat =>
            fun hyp : ∀ p : Nat, ∀ pw : p < dom, clauseSat (clauses p pw) valuat =>
              let lem := resolutionToProof clauses (contrad (n + 1))
                            tree check checkTop valuat hyp
              contradFalse _ valuat lem
  | SatSolution.sat valuat evidence =>
          ⟨valuat, fun k kw => getProof (evidence k kw)⟩

instance {dom n: Nat}{clauses : FinSeq dom (Clause (n + 1))}
                  (sol : SatSolution clauses) : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def treeToUnsat{dom n: Nat}{clauses : FinSeq dom  (Clause (n + 1))} :
                (rpf : ResolutionProof clauses (contrad _)) → 
                        SatSolution clauses := fun rpf =>
          SatSolution.unsat rpf.tree rpf.check rpf.checkTop

def mergeUnitTrees{dom n: Nat}{clauses : FinSeq dom  (Clause (n + 1))}
                (focus : Nat)(focusLt : focus < n + 1)
                (left: ResolutionProof clauses (unitClause n false focus focusLt))
                (right: ResolutionProof clauses (unitClause n true focus focusLt)) :
                ResolutionProof clauses (contrad (n + 1)) := 
                let tree := ResolutionTree.resolve 
                      (unitClause n false focus focusLt)
                      (unitClause n true focus focusLt)
                      (contrad (n + 1))
                     left.tree right.tree (unitTriple n focus focusLt)
                let check : treeCheck tree (contrad (n + 1)) := 
                    And.intro (And.intro left.check  right.check) 
                              (And.intro left.checkTop  right.checkTop)
                ⟨tree, check, rfl⟩

def mergeAlignUnitTrees{dom n: Nat}{branch : Bool}{clauses : FinSeq dom  (Clause (n + 1))}
                {focus : Nat}{focusLt : focus < n + 1}
                (first: ResolutionProof clauses (unitClause n branch focus focusLt))
                (second: ResolutionProof clauses (unitClause n (not branch) focus focusLt)) :
                ResolutionProof clauses (contrad (n + 1)) := 
                match branch, first, second with
                | false, left, right =>
                    mergeUnitTrees focus focusLt left right
                | true, right, left => 
                    mergeUnitTrees focus focusLt left right

def unitProof{dom n: Nat}{branch : Bool}{clauses : FinSeq dom  (Clause (n + 1))}
                {focus : Nat}{focusLt : focus < n + 1}{j : Nat}{jw : j < dom}
                (eqn: clauses j jw = unitClause n branch focus focusLt):
                ResolutionProof clauses (unitClause n branch focus focusLt) :=
                  let tree : ResolutionTree clauses := ResolutionTree.assumption j jw
                  let check: treeCheck tree (unitClause n branch focus focusLt) := eqn
                  let checkTop : treeTop tree = unitClause n branch focus focusLt := eqn
                  ⟨tree, eqn, eqn⟩


structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Nat)(focusLt : focus < n + 1)
  (clauses : FinSeq dom (Clause (n + 1)))(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionProof clauses (insert topFocus n focus focusLt top)

inductive LiftedResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2))) where
    | contra : ResolutionProof clauses (contrad (n + 2)) → 
                  LiftedResPf branch focus focusLt clauses
    | unit : ResolutionProof clauses (unitClause (n + 1) (not branch) focus focusLt) → 
                  LiftedResPf branch focus focusLt clauses

theorem notNot(b: Bool){x : Bool} : Not (x = b) → x = (not b) :=
  match b with
  | true => fun w => eqFalseOfNeTrue w
  | false => fun w => eqTrueOfNeFalse w

def pullBackTree{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc): (top : Clause (n + 1)) → 
      (tree : ResolutionTree (rc.restClauses)) → treeCheck tree top → treeTop tree = top
       → BranchResolutionProof branch focus focusLt clauses top  := 
      fun top tree =>
        match tree with
        | ResolutionTree.assumption j jw => 
          fun tpf ttp =>
            let k := rc.reverse j jw
            let kw : k < dom := rc.reverseWit j jw
            let tree := ResolutionTree.assumption k kw
            let cl := clauses k kw
            let topFocus := cl focus focusLt
            let checkCl : treeCheck tree cl := by rfl
            let checkTopCl : treeTop tree = cl := by rfl
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
                      rw (Eq.symm tpf)
                      rw lem1
                      rw lem3
                      done 
            let check : treeCheck tree (insert topFocus (n + 1) focus focusLt top) := by
                      rw lem 
                      rfl
                      done 
            let checkTop : treeTop tree = insert topFocus (n + 1) focus focusLt top := by
                      rw lem 
                      rfl
                      done 
            ⟨topFocus, nonPosLem, ⟨tree, check, checkTop⟩⟩
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
            fun tpf (tt : topt = top)  => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧ ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : BranchResolutionProof branch focus focusLt clauses left := 
                        pullBackTree branch focus focusLt clauses rc np rr left leftTree lemLc lemLt
              let rightBase : BranchResolutionProof branch focus focusLt clauses right := 
                        pullBackTree branch focus focusLt clauses rc np rr right rightTree lemRc lemRt
              let ⟨leftFoc, leftNP, ⟨leftLiftTree, leftCheck, leftCheckTop⟩⟩ := leftBase
              let ⟨rightFoc, rightNP, ⟨rightLiftTree, rightCheck, rightCheckTop⟩⟩ := rightBase
              let trip : ResolutionTriple left right top := by
                    rw (Eq.symm tt)
                    exact triple
                    done 
              let liftedTriple := 
                    liftResolutionTriple branch leftFoc rightFoc left right top 
                          focus focusLt leftNP rightNP trip
              let ⟨topFoc, liftTriple, topNonPos⟩ := liftedTriple
              let tree := ResolutionTree.resolve
                              (insert leftFoc _ focus focusLt left)
                              (insert rightFoc _ focus focusLt right)
                              (insert topFoc _ focus focusLt top)
                              leftLiftTree rightLiftTree liftTriple
              let check := And.intro (And.intro leftCheck rightCheck) 
                                      (And.intro leftCheckTop rightCheckTop)
              ⟨topFoc, topNonPos, ⟨tree, check, rfl⟩⟩

def pullBackResPf{dom n: Nat}(branch: Bool)(focus: Nat )(focusLt : focus <  (n + 2))
    (clauses: FinSeq dom (Clause (n + 2)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc) : 
        ResolutionProof rc.restClauses (contrad (n + 1)) → 
            LiftedResPf branch focus focusLt clauses := fun rpf =>
            let pbt := pullBackTree branch focus focusLt clauses rc np rr 
                                (contrad (n + 1)) rpf.tree rpf.check rpf.checkTop
            match pbt.topFocus, pbt.nonPos, pbt.provedTree with 
            | none, _, tree => 
                let lem := contradInsNone focus focusLt            
                let t : ResolutionProof clauses (contrad (n + 2)) := by
                            rw (Eq.symm lem)
                            exact tree
                LiftedResPf.contra t
            | some b, ineq, tree =>
                let lemPar : Not (b = branch) := fun hyp => ineq (congrArg some hyp)
                let par : b = not branch := notNot branch lemPar
                let t : ResolutionProof clauses (unitClause (n + 1) (not branch) focus focusLt) := 
                          by
                            rw (Eq.symm par)
                            exact tree
                            done
                LiftedResPf.unit t

def transportResPf{l1 l2 n : Nat}(clauses1 : FinSeq l1 (Clause (n + 1)))
                  (clauses2: FinSeq l2 (Clause (n + 1)))
                  (embed: (j : Nat) → (jw : j < l1) → ElemInSeq clauses2 (clauses1 j jw))
                  (top: Clause (n + 1)): 
                  (tree : ResolutionTree clauses1) → treeCheck tree top → treeTop tree = top → 
                              ResolutionProof clauses2 top := 
                      fun tree => 
                      match tree with
                      | ResolutionTree.assumption ind  bd =>
                        fun  chk  chkTop => 
                          let ⟨i, iw, eqn⟩ := embed ind bd
                          let check2 : clauses2 i iw = top := by
                              rw eqn
                              exact chk
                          let tree := ResolutionTree.assumption i iw
                          let lem1 : treeTop tree = clauses2 i iw := by rfl                          
                        ⟨tree, check2, by 
                                    rw lem1
                                    exact check2⟩
                      | ResolutionTree.resolve left right top1 leftTree rightTree join =>
                        fun  chk chkTop => 
                            let lem1 : top1 = top := chkTop
                            let c : (((treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
                              ((treeTop leftTree = left) ∧  ((treeTop rightTree = right))) := chk
                            let leftPf2 := transportResPf clauses1 clauses2 embed left
                                leftTree c.left.left c.right.left 
                            let rightPf2 := transportResPf clauses1 clauses2 embed right
                                rightTree c.left.right c.right.right
                            let join2 : ResolutionTriple left right top := by
                                    rw (Eq.symm lem1)
                                    exact join
                                    done 
                            let tree := ResolutionTree.resolve left right top
                                        leftPf2.tree rightPf2.tree join2
                            let check := And.intro (And.intro leftPf2.check  rightPf2.check)
                                            (And.intro leftPf2.checkTop rightPf2.checkTop)
                            ⟨tree, check, rfl⟩

theorem proofsPreverveNonPos{dom n : Nat}{clauses : FinSeq dom (Clause (n + 1))}
                (bf: Bool)(k : Nat)(kw : k < n + 1)
                (base : (j : Nat) → (lt : j < dom) → Not (clauses j lt k kw = some bf)) : 
                (top : Clause (n + 1)) → 
                (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top → 
                Not (top k kw = some bf) := 
                  fun top tree =>
                  match tree with
                  | ResolutionTree.assumption ind  bd =>
                    fun  chk  chkTop hyp => 
                      let lem0 : clauses ind bd = top := chk
                      let lem1 : Not (top k kw = some bf) := by
                              rw (Eq.symm lem0)
                              exact (base ind bd)
                      absurd hyp lem1
                  | ResolutionTree.resolve left right top1 leftTree rightTree triple1 =>
                    fun  chk chkTop hyp => 
                      let lem1 : top1 = top := chkTop
                      let c : (((treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
                          ((treeTop leftTree = left) ∧  ((treeTop rightTree = right))) := chk
                      let leftLem :=
                        proofsPreverveNonPos bf k kw base left leftTree c.left.left c.right.left
                      let rightLem :=
                        proofsPreverveNonPos bf k kw base right rightTree c.left.right c.right.right
                      let triple : ResolutionTriple left right top := by
                                    rw (Eq.symm lem1)
                                    exact triple1
                                    done
                      match skipImageCase triple.pivot k with
                      | SkipImageCase.diag eqn => 
                          match bf, k, eqn, kw, leftLem, rightLem with
                          | false, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                                lL (triple.leftPivot)
                          | true, .(triple.pivot), rfl, .(triple.pivotLt), lL, rL => 
                                rL (triple.rightPivot)
                      | SkipImageCase.image j eqn => 
                            let jw := skipPreImageBound triple.pivotLt kw eqn
                            let joinIm := triple.joinRest j jw
                            match (skip triple.pivot j), eqn, (skipPlusOne jw), joinIm with 
                            | .(k), rfl, .(kw), join => 
                              let lem := 
                                topJoinNonPos bf (left k kw) (right k kw) (top k kw) join
                                  leftLem rightLem
                              lem hyp               
end leaner



namespace clunky

structure ResolutionTriple{n: Nat}(left right top : Clause (n + 1)) where
  pivot : Fin (n + 1)
  leftPivot : left pivot = some false
  rightPivot : right pivot = some true
  topPivot : top pivot = none
  joinRest : (k : Fin n) → 
    Join  (left (shiftAt _ pivot.val pivot.isLt k)) 
          (right (shiftAt _ pivot.val pivot.isLt k)) 
          (top (shiftAt _ pivot.val pivot.isLt k))

def tripleStepProof{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuat: Valuat (n + 1))  → (clauseSat left valuat) → 
        (clauseSat right valuat) → (clauseSat top valuat) := 
          fun valuat =>
            fun ⟨kl, wl⟩ =>
              fun ⟨kr, wr⟩ =>
                 if c : valuat (triple.pivot)  then 
                    -- the left branch survives
                    match shiftIsSectionProp _ triple.pivot kl  with
                    | Or.inl eql => 
                      let lem1 := congrArg valuat (Eq.symm eql)
                      let lem2 :=  congrArg some (Eq.trans lem1 c)
                      let lem3 := Eq.trans wl lem2
                      let lem4 : left kl = some false := by
                        rw (congrArg left (Eq.symm eql))
                        exact triple.leftPivot
                        done 
                      let lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : true = false := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                    | Or.inr ⟨i, eql⟩ => 
                      let j := shiftAt n triple.pivot.val triple.pivot.isLt i
                      let lem1 : left j = left kl := congrArg left eql
                      let lem2 : left j = some (valuat j) := by
                        rw lem1
                        rw wl
                        apply congrArg some
                        apply congrArg valuat
                        apply Eq.symm
                        exact eql
                        done
                      let lem3 := 
                        varResolution  (triple.joinRest i) 
                          (valuat j) (Or.inl lem2)
                      ⟨j , lem3⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    -- the right branch survives
                    match shiftIsSectionProp _ triple.pivot kr  with
                    | Or.inl eqr => 
                      let lem1 := congrArg valuat (Eq.symm eqr)
                      let lem2 :=  congrArg some (Eq.trans lem1 cc)
                      let lem3 := Eq.trans wr lem2
                      let lem4 : right kr = some true := by
                        rw (congrArg right (Eq.symm eqr))
                        exact triple.rightPivot
                        done 
                      let lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : false = true := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                    | Or.inr ⟨i, eqr⟩ => 
                      let j := shiftAt n triple.pivot.val triple.pivot.isLt i
                      let lem1 : right j = right kr := congrArg right eqr
                      let lem2 : right j = some (valuat j) := by
                        rw lem1
                        rw wr
                        apply congrArg some
                        apply congrArg valuat
                        apply Eq.symm
                        exact eqr
                        done
                      let lem3 := 
                        varResolution  (triple.joinRest i) 
                          (valuat j) (Or.inr lem2)
                      ⟨j , lem3⟩

def tripleStepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (valuat: Valuat (n + 1))  → (ClauseSat left valuat) → 
        (ClauseSat right valuat) → (ClauseSat top valuat) := 
          fun valuat =>
            fun ⟨kl, wl⟩ =>
              fun ⟨kr, wr⟩ =>
                 if c : valuat (triple.pivot)  then 
                    -- the left branch survives
                    match shiftIsSection _ triple.pivot kl  with
                    | SectionCase.diagonal eql => 
                      let lem1 := congrArg valuat (Eq.symm eql)
                      let lem2 :=  congrArg some (Eq.trans lem1 c)
                      let lem3 := Eq.trans wl lem2
                      let lem4 : left kl = some false := by
                        rw (congrArg left (Eq.symm eql))
                        exact triple.leftPivot
                        done 
                      let lem5 : some true = some false := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : true = false := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                    | SectionCase.image i eql => 
                      let j := shiftAt n triple.pivot.val triple.pivot.isLt i
                      let lem1 : left j = left kl := congrArg left eql
                      let lem2 : left j = some (valuat j) := by
                        rw lem1
                        rw wl
                        apply congrArg some
                        apply congrArg valuat
                        apply Eq.symm
                        exact eql
                        done
                      let lem3 := 
                        varResolution  (triple.joinRest i) 
                          (valuat j) (Or.inl lem2)
                      ⟨j , lem3⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    -- the right branch survives
                    match shiftIsSection _ triple.pivot kr  with
                    | SectionCase.diagonal eqr => 
                      let lem1 := congrArg valuat (Eq.symm eqr)
                      let lem2 :=  congrArg some (Eq.trans lem1 cc)
                      let lem3 := Eq.trans wr lem2
                      let lem4 : right kr = some true := by
                        rw (congrArg right (Eq.symm eqr))
                        exact triple.rightPivot
                        done 
                      let lem5 : some false = some true := 
                        Eq.trans (Eq.symm lem3) lem4
                      let lem6 : false = true := by 
                        injection lem5
                        assumption
                        done
                      Bool.noConfusion lem6
                    | SectionCase.image i eqr => 
                      let j := shiftAt n triple.pivot.val triple.pivot.isLt i
                      let lem1 : right j = right kr := congrArg right eqr
                      let lem2 : right j = some (valuat j) := by
                        rw lem1
                        rw wr
                        apply congrArg some
                        apply congrArg valuat
                        apply Eq.symm
                        exact eqr
                        done
                      let lem3 := 
                        varResolution  (triple.joinRest i) 
                          (valuat j) (Or.inr lem2)
                      ⟨j , lem3⟩


structure LiftedTriple{n : Nat} (bf : Bool) (leftFoc rightFoc : Option Bool) 
  (left right top : Clause (n + 1))(k: Nat)(lt : k < succ (n + 1)) where
    topFoc : Option Bool
    triple : ResolutionTriple 
          (liftAt  leftFoc (n + 1) k lt   left) 
          (liftAt  rightFoc (n + 1) k lt right) 
          (liftAt  topFoc (n + 1) k lt top)
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
          let pivotN := shiftAt (n + 1) k lt rt.pivot
          let leftN := liftAt leftFoc (n + 1) k lt left
          let rightN := liftAt rightFoc (n + 1) k lt right
          let topN := liftAt topFoc (n + 1) k lt top
          let leftPivotN : leftN pivotN = some false := 
            let lem1 : leftN pivotN = left rt.pivot := 
              liftAtImage leftFoc (n + 1) k lt left rt.pivot
            by
              rw lem1
              exact rt.leftPivot
              done
          let rightPivotN : rightN pivotN = some true := 
            let lem1 : rightN pivotN = right rt.pivot := 
              liftAtImage rightFoc (n + 1) k lt right rt.pivot
            by
              rw lem1
              exact rt.rightPivot
              done
          let topPivotN : topN pivotN = none := 
            let lem1 : topN pivotN = top rt.pivot := 
              liftAtImage topFoc (n + 1) k lt top rt.pivot
            by
              rw lem1
              exact rt.topPivot
              done

          let joinRestN : (j : Fin (n + 1)) → 
            Join  (leftN (shiftAt _ pivotN.val pivotN.isLt j)) 
                  (rightN (shiftAt _ pivotN.val pivotN.isLt j)) 
                  (topN (shiftAt _ pivotN.val pivotN.isLt j)) := 
                  fun j =>
                  let jj := shiftAt (n + 1) pivotN.val pivotN.isLt j
                  let notPivotAux : Not (jj = ⟨pivotN.val, pivotN.isLt⟩) :=
                    shiftSkipsEq (n + 1) pivotN.val pivotN.isLt j
                  let notPivot : Not (jj = pivotN) := 
                    fun hyp =>
                      let lem1 := congrArg Fin.val hyp
                      let lem2 : jj = ⟨pivotN.val, pivotN.isLt⟩ := by
                        apply Fin.eqOfVeq
                        exact lem1
                        done 
                      notPivotAux lem2
                  match shiftIsSection (n + 1) ⟨k, lt⟩ 
                    (jj) with
                  | SectionCase.diagonal w =>  
                    let lem0 := focJoin
                    let eqL : leftN ⟨k, lt⟩ = leftFoc := 
                      liftAtFocus leftFoc (n + 1) k lt left 
                    let eqR : rightN ⟨k, lt⟩ = rightFoc := 
                      liftAtFocus rightFoc (n + 1) k lt right
                    let eqT : topN ⟨k, lt⟩ = topFoc := 
                      liftAtFocus topFoc (n + 1) k lt top
                    let goal : Join (leftN jj) (rightN jj) (topN jj) := by
                      rw (Eq.symm w)
                      rw eqL
                      rw eqR
                      rw eqT
                      exact lem0
                      done
                    goal
                  | SectionCase.image i w => 
                    match shiftIsSection n rt.pivot i with
                    | SectionCase.diagonal ww => 
                      let lem1 := congrArg (shiftAt (n + 1) k lt) ww
                      let lem2 : pivotN = jj := Eq.trans lem1 w
                      absurd (Eq.symm lem2) notPivot
                    | SectionCase.image ii ww => 
                      let eqL : leftN (shiftAt (n + 1) k lt i) =
                        left i := 
                        liftAtImage leftFoc (n + 1) k lt left i
                      let eqR : rightN (shiftAt (n + 1) k lt i) =
                        right i := 
                        liftAtImage rightFoc (n + 1) k lt right i
                      let eqT : topN (shiftAt (n + 1) k lt i) =
                        top i := 
                        liftAtImage topFoc (n + 1) k lt top i
                      let goal : Join (leftN jj) (rightN jj) (topN jj) := by
                        rw (Eq.symm w)
                        rw eqL
                        rw eqR
                        rw eqT
                        rw (Eq.symm ww)
                        apply rt.joinRest
                        done
                      goal
          ⟨topFoc, ⟨pivotN, leftPivotN, rightPivotN, topPivotN, joinRestN⟩, topNonPos⟩

def shiftOne{α: Type}{n m: Nat} : (n = m + 1) → (Fin n → α) → (Fin (m + 1) → α) :=
  fun eq fn =>
    fun j => 
      let i : Fin n := by
        rw eq
        exact j
        done
      fn i

inductive ResolutionTree{dom n: Nat}(clauses : Fin dom →  Clause (n + 1)) where
  | assumption : (index : Fin dom) →   ResolutionTree clauses 
  | resolve : (left right top : Clause (n + 1)) → 
                (leftTree : ResolutionTree clauses) → 
                (rightTree: ResolutionTree clauses) →
                ResolutionTriple left right top 
                → ResolutionTree clauses

def treeTop{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
              (tree: ResolutionTree clauses) : Clause (n + 1) :=
      match tree with
      | ResolutionTree.assumption j => clauses j
      | ResolutionTree.resolve left right  top leftTree rightTree triple  => top 

def treeCheck{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
              (tree: ResolutionTree clauses)(top : Clause (n + 1)) : Prop :=
      match tree with
      | ResolutionTree.assumption j => clauses j = top
      | ResolutionTree.resolve left right  top leftTree rightTree triple  => 
           ((  (treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
          ( (treeTop leftTree = left) ∧  ((treeTop rightTree = right)))

structure ResolutionProof{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)) where
  tree : ResolutionTree clauses
  check : treeCheck tree top
  checkTop : treeTop tree = top
  -- need separate checks for the cases of the tree

def resolutionToProof{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (valuat :Valuat (n + 1))→ 
    ((j : Fin dom) → clauseSat (clauses j) valuat) → clauseSat top valuat := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j => 
          fun tpf _ valuat base  => 
            let lem0 : clauses j = top := tpf
            let lem1 : clauseSat (clauses j) valuat := base j
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) valuat base => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧  (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧  ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : clauseSat left valuat := 
                resolutionToProof clauses left leftTree lemLc lemLt valuat base 
              let rightBase : clauseSat right valuat := 
                resolutionToProof clauses right rightTree lemRc lemRt valuat base 
              let lemStep := tripleStepProof left right topt triple valuat leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (valuat :Valuat (n + 1))→ 
    ((j : Fin dom) → ClauseSat (clauses j) valuat) → ClauseSat top valuat := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j => 
          fun tpf _ valuat base  => 
            let lem0 : clauses j = top := tpf
            let lem1 : ClauseSat (clauses j) valuat := base j
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) valuat base => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧ (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧ ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : ClauseSat left valuat := 
                resolutionToSat clauses left leftTree lemLc lemLt valuat base 
              let rightBase : ClauseSat right valuat := 
                resolutionToSat clauses right rightTree lemRc lemRt valuat base 
              let lemStep := tripleStepSat left right topt triple valuat leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

inductive SatSolution{dom n: Nat}(clauses : Fin dom →  Clause (n + 1)) where
  | unsat : (tree : ResolutionTree clauses) → 
        treeCheck tree (contrad (n + 1))  →  treeTop tree = contrad (n + 1) 
          →  SatSolution clauses
  | sat : (valuat : Valuat (n + 1)) → ((k : Fin dom) → ClauseSat (clauses k) valuat) → SatSolution clauses 

def solutionProp{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat _ _ _   => 
          ∀ valuat : Valuat (n + 1),  
           Not (∀ (p : Fin dom),  ∃ (k : Fin (n + 1)), (clauses p k) = some (valuat k))
  | SatSolution.sat _ _ =>
          ∃ valuat : Valuat (n + 1),  
            ∀ (p : Fin dom),  ∃ (k : Fin (n + 1)), (clauses p k) = some (valuat k) 

def solutionProof{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree check checkTop   => 
          fun valuat =>
            fun hyp : ∀ p : Fin dom, clauseSat (clauses p) valuat =>
              let lem := resolutionToProof clauses (contrad (n + 1))
                            tree check checkTop valuat hyp
              contradFalse _ valuat lem
  | SatSolution.sat valuat evidence =>
          ⟨valuat, fun k => getProof (evidence k)⟩

instance {dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol

def treeToUnsat{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)} :
                (rpf : ResolutionProof clauses (contrad _)) → 
                        SatSolution clauses := fun rpf =>
          SatSolution.unsat rpf.tree rpf.check rpf.checkTop

structure BranchResolutionProof{dom n: Nat}(bf: Bool)(focus : Fin (n + 1))
  (clauses : Fin dom →  Clause (n + 1))(top : Clause (n))  where
    topFocus : Option Bool
    nonPos : Not (topFocus = some bf)
    provedTree : ResolutionProof clauses (liftAt topFocus n focus.val focus.isLt top)

def pullBackTree{dom n: Nat}(branch: Bool)(focus: Fin (n + 2))
    (clauses: Fin dom →  Clause (n + 2))(rc: RestrictionClauses branch focus clauses) 
    (np : NonPosReverse rc) (rr: ReverseRelation rc): (top : Clause (n + 1)) → 
      (tree : ResolutionTree (rc.restClauses)) → treeCheck tree top → treeTop tree = top
       → BranchResolutionProof branch focus clauses top  := 
      fun top tree =>
        match tree with
        | ResolutionTree.assumption ⟨j, jw⟩ => 
          fun tpf ttp =>
            let k := rc.reverse j jw
            let kw : k < dom := rc.reverseWit j jw
            let tree := ResolutionTree.assumption ⟨k, kw⟩
            let cl := clauses ⟨k, kw⟩
            let topFocus := cl focus
            let checkCl : treeCheck tree cl := by rfl
            let checkTopCl : treeTop tree = cl := by rfl
            let nonPosLem : Not (topFocus = some branch)  := 
                np.nonPosRev j jw
            let lem1 : rc.restClauses ⟨j, jw⟩ = 
                  dropAt (n + 1) focus.val focus.isLt (clauses ⟨k, kw⟩) 
                       := by
                       apply rr.relation
                       done
            let lem3 : liftAt (cl ⟨focus.val, focus.isLt⟩) (n + 1) focus.val focus.isLt 
                          (dropAt (n + 1) focus.val focus.isLt cl) = cl 
                          := liftDrop (n + 1) focus.val focus.isLt cl
            let lemSilly : ⟨focus.val, focus.isLt⟩ = focus := by
                              apply Fin.eqOfVeq
                              rfl
                              done
            let lem4 : liftAt (cl ⟨focus.val, focus.isLt⟩) (n + 1) focus.val focus.isLt 
                          (dropAt (n + 1) focus.val focus.isLt cl) =
                          liftAt topFocus (n + 1) focus.val focus.isLt 
                          (dropAt (n + 1) focus.val focus.isLt cl) := congrArg (fun foc : Fin (n + 2) => 
                      liftAt (cl foc ) (n + 1) focus.val focus.isLt 
                          (dropAt (n + 1) focus.val focus.isLt cl)) lemSilly
            let lem : liftAt topFocus (n + 1) focus.val focus.isLt top = cl := by
                      rw (Eq.symm tpf)
                      rw lem1
                      rw (Eq.symm lem4)
                      rw lem3
                      done 
            let check : treeCheck tree (liftAt topFocus (n + 1) focus.val focus.isLt top) := by
                      rw lem 
                      rfl
                      done 
            let checkTop : treeTop tree = liftAt topFocus (n + 1) focus.val focus.isLt top := by
                      rw lem 
                      rfl
                      done 
            ⟨topFocus, nonPosLem, ⟨tree, check, checkTop⟩⟩
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
            fun tpf (tt : topt = top)  => 
            let lem0 :  
               ((  (treeCheck leftTree left) ∧ (treeCheck rightTree right))) ∧ 
               ( (treeTop leftTree = left) ∧ ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : BranchResolutionProof branch focus clauses left := 
                        pullBackTree branch focus clauses rc np rr left leftTree lemLc lemLt
              let rightBase : BranchResolutionProof branch focus clauses right := 
                        pullBackTree branch focus clauses rc np rr right rightTree lemRc lemRt
              let ⟨leftFoc, leftNP, ⟨leftLiftTree, leftCheck, leftCheckTop⟩⟩ := leftBase
              let ⟨rightFoc, rightNP, ⟨rightLiftTree, rightCheck, rightCheckTop⟩⟩ := rightBase
              let trip : ResolutionTriple left right top := by
                    rw (Eq.symm tt)
                    exact triple
                    done 
              let liftedTriple := 
                    liftResolutionTriple branch leftFoc rightFoc left right top 
                          focus.val focus.isLt leftNP rightNP trip
              let ⟨topFoc, liftTriple, topNonPos⟩ := liftedTriple
              let tree := ResolutionTree.resolve
                              (liftAt leftFoc _ focus.val focus.isLt left)
                              (liftAt rightFoc _ focus.val focus.isLt right)
                              (liftAt topFoc _ focus.val focus.isLt top)
                              leftLiftTree rightLiftTree liftTriple
              let check := And.intro (And.intro leftCheck rightCheck) 
                                      (And.intro leftCheckTop rightCheckTop)
              ⟨topFoc, topNonPos, ⟨tree, check, rfl⟩⟩