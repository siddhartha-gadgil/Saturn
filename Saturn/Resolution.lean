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

theorem varResolution (left right top : Option Bool)(join: Join left right top)(sectVal : Bool) :
  Or (varSat left sectVal) (varSat right sectVal) → (varSat top sectVal)  :=
  fun hyp  =>
    match join with
    | Join.noneNone pl pr pt => 
      match hyp with
      | Or.inl heq => 
        let contra: none = some (sectVal) := Eq.trans (Eq.symm pl) heq
        Option.noConfusion contra
      | Or.inr heq => 
        let contra: none = some (sectVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra 
    | Join.someNone b pl pr pt =>
      match hyp with
      | Or.inl (heq : left = some sectVal) => 
        let lem : top = left := Eq.trans pt (Eq.symm pl)
        Eq.trans lem heq
      | Or.inr heq => 
        let contra: none = some (sectVal) := Eq.trans (Eq.symm pr) heq
        Option.noConfusion contra  
    | Join.noneSome b pl pr pt =>
      match hyp with
      | Or.inl heq => 
        let contra: none = some (sectVal) := Eq.trans (Eq.symm pl) heq
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
        (sect: Sect (n + 1))  → (clauseSat left sect) → 
        (clauseSat right sect) → (clauseSat top sect) := 
          fun sect =>
            fun ⟨kl, wl⟩ =>
              fun ⟨kr, wr⟩ =>
                 if c : sect (triple.pivot)  then 
                    -- the left branch survives
                    match shiftIsSectionProp _ triple.pivot kl  with
                    | Or.inl eql => 
                      let lem1 := congrArg sect (Eq.symm eql)
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
                      let lem2 : left j = some (sect j) := by
                        rw lem1
                        rw wl
                        apply congrArg some
                        apply congrArg sect
                        apply Eq.symm
                        exact eql
                        done
                      let lem3 := 
                        varResolution (left j) (right j) (top j) (triple.joinRest i) 
                          (sect j) (Or.inl lem2)
                      ⟨j , lem3⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    -- the right branch survives
                    match shiftIsSectionProp _ triple.pivot kr  with
                    | Or.inl eqr => 
                      let lem1 := congrArg sect (Eq.symm eqr)
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
                      let lem2 : right j = some (sect j) := by
                        rw lem1
                        rw wr
                        apply congrArg some
                        apply congrArg sect
                        apply Eq.symm
                        exact eqr
                        done
                      let lem3 := 
                        varResolution (left j) (right j) (top j) (triple.joinRest i) 
                          (sect j) (Or.inr lem2)
                      ⟨j , lem3⟩

def tripleStepSat{n: Nat}(left right top : Clause (n + 1))
  (triple : ResolutionTriple left right top) :
        (sect: Sect (n + 1))  → (ClauseSat left sect) → 
        (ClauseSat right sect) → (ClauseSat top sect) := 
          fun sect =>
            fun ⟨kl, wl⟩ =>
              fun ⟨kr, wr⟩ =>
                 if c : sect (triple.pivot)  then 
                    -- the left branch survives
                    match shiftIsSection _ triple.pivot kl  with
                    | SectionCase.diagonal eql => 
                      let lem1 := congrArg sect (Eq.symm eql)
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
                      let lem2 : left j = some (sect j) := by
                        rw lem1
                        rw wl
                        apply congrArg some
                        apply congrArg sect
                        apply Eq.symm
                        exact eql
                        done
                      let lem3 := 
                        varResolution (left j) (right j) (top j) (triple.joinRest i) 
                          (sect j) (Or.inl lem2)
                      ⟨j , lem3⟩
                  else
                    let cc := eqFalseOfNeTrue c  
                    -- the right branch survives
                    match shiftIsSection _ triple.pivot kr  with
                    | SectionCase.diagonal eqr => 
                      let lem1 := congrArg sect (Eq.symm eqr)
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
                      let lem2 : right j = some (sect j) := by
                        rw lem1
                        rw wr
                        apply congrArg some
                        apply congrArg sect
                        apply Eq.symm
                        exact eqr
                        done
                      let lem3 := 
                        varResolution (left j) (right j) (top j) (triple.joinRest i) 
                          (sect j) (Or.inr lem2)
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
          And ((And  (treeCheck leftTree left) (treeCheck rightTree right)))
          (And (treeTop leftTree = left) ((treeTop rightTree = right)))

structure ResolutionProof{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)) where
  tree : ResolutionTree clauses
  check : treeCheck tree top
  checkTop : treeTop tree = top
  -- need separate checks for the cases of the tree

def resolutionToProof{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (sect :Sect (n + 1))→ 
    ((j : Fin dom) → clauseSat (clauses j) sect) → clauseSat top sect := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j => 
          fun tpf _ sect base  => 
            let lem0 : clauses j = top := tpf
            let lem1 : clauseSat (clauses j) sect := base j
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) sect base => 
            let lem0 :  
              And ((And  (treeCheck leftTree left) (treeCheck rightTree right)))
               (And (treeTop leftTree = left) ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : clauseSat left sect := 
                resolutionToProof clauses left leftTree lemLc lemLt sect base 
              let rightBase : clauseSat right sect := 
                resolutionToProof clauses right rightTree lemRc lemRt sect base 
              let lemStep := tripleStepProof left right topt triple sect leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

def resolutionToSat{dom n: Nat}(clauses : Fin dom →  Clause (n + 1))(top : Clause (n + 1)):
  (tree : ResolutionTree clauses) → treeCheck tree top → treeTop tree = top  → (sect :Sect (n + 1))→ 
    ((j : Fin dom) → ClauseSat (clauses j) sect) → ClauseSat top sect := 
      fun tree  => 
        match tree with
        | ResolutionTree.assumption j => 
          fun tpf _ sect base  => 
            let lem0 : clauses j = top := tpf
            let lem1 : ClauseSat (clauses j) sect := base j
          by
            rw (Eq.symm lem0)
            exact lem1
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => 
          fun tpf (tt : topt = top) sect base => 
            let lem0 :  
              And ((And  (treeCheck leftTree left) (treeCheck rightTree right)))
               (And (treeTop leftTree = left) ((treeTop rightTree = right))) 
                := tpf
              let lemLc : treeCheck leftTree left := lem0.left.left
              let lemRc := lem0.left.right
              let lemLt := lem0.right.left
              let lemRt := lem0.right.right
              let leftBase : ClauseSat left sect := 
                resolutionToSat clauses left leftTree lemLc lemLt sect base 
              let rightBase : ClauseSat right sect := 
                resolutionToSat clauses right rightTree lemRc lemRt sect base 
              let lemStep := tripleStepSat left right topt triple sect leftBase rightBase
            by
              rw (Eq.symm tt)
              exact lemStep
              done

inductive SatSolution{dom n: Nat}(clauses : Fin dom →  Clause (n + 1)) where
  | unsat : (tree : ResolutionTree clauses) → 
        treeCheck tree (contradiction (n + 1))  →  treeTop tree = contradiction (n + 1) 
          →  SatSolution clauses
  | sat : (sect : Sect (n + 1)) → ((k : Fin dom) → ClauseSat (clauses k) sect) → SatSolution clauses 

def solutionProp{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) : Prop :=
  match sol with
  | SatSolution.unsat _ _ _   => 
          ∀ sect : Sect (n + 1),  
           Not (∀ (p : Fin dom),  ∃ (k : Fin (n + 1)), (clauses p k) = some (sect k))
  | SatSolution.sat _ _ =>
          ∃ sect : Sect (n + 1),  
            ∀ (p : Fin dom),  ∃ (k : Fin (n + 1)), (clauses p k) = some (sect k) 

def solutionProof{dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) :
                    solutionProp sol :=
  match sol with
  | SatSolution.unsat tree check checkTop   => 
          fun sect =>
            fun hyp : ∀ p : Fin dom, clauseSat (clauses p) sect =>
              let lem := resolutionToProof clauses (contradiction (n + 1))
                            tree check checkTop sect hyp
              contradictionFalse _ sect lem
  | SatSolution.sat sect evidence =>
          ⟨sect, fun k => getProof (evidence k)⟩

instance {dom n: Nat}{clauses : Fin dom →  Clause (n + 1)}
                  (sol : SatSolution clauses) : Prover (SatSolution clauses) where
      statement := fun sol => solutionProp sol 
      proof := fun sol => solutionProof sol


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
            let lem0 : rc.restClauses ⟨j, jw⟩ = top := tpf
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
            let lem2 := Eq.trans (Eq.symm lem0) lem1
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
                      rw lem2
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
        | ResolutionTree.resolve left right  topt leftTree rightTree triple  => sorry
      