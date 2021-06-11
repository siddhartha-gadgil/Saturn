import Saturn.Basic
import Saturn.FinSeq 
open Nat

inductive Join (left right top : Option Bool) where
  | noneNone : (left = none) → (right = none) → (top = none)→ Join left right top 
  | noneSome : (b : Bool) → (left = none) → (right = some b) → (top = some b)→ Join left right top
  | someNone : (b : Bool) → (left = some b) → (right = none) → (top = some b)→ Join left right top
  | someSome : (b : Bool) → (left = some b) → (right = some b) → (top = some b)→ Join left right top

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

def tripleStep{n: Nat}(left right top : Clause (n + 1))
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
