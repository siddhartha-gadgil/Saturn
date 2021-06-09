import Saturn.Basic
open Nat

-- theorems about finite sequences

theorem dropPlusOne{α : Type}(n: Nat)(zeroVal : α)(j: Fin n)(g: (Fin (succ n)) → α) 
        : (dropHead n g j) = g (plusOne n j) := by
        rfl
        done

theorem zeroLenClsEql : ∀ (cl1: Clause 0), ∀ (cl2: Clause 0) ,  (cl1 = cl2) := 
  fun cl1 =>
    fun cl2 =>
      funext (
        fun (x : Fin 0) =>
          match x with 
            | ⟨_, h⟩ => absurd h (notLtZero _)
      )


theorem prependPlusOne{α: Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n):
  prepend n zeroVal fn (plusOne n j) = fn j :=
    let l1 : prepend n zeroVal fn (plusOne n j) = fn (Fin.mk j.val j.isLt) := by rfl
    let l2 :  Fin.mk j.val j.isLt = j := by
      apply Fin.eqOfVeq
      rfl
      done
    let l3 := congrArg fn l2
    Eq.trans l1 l3
  

theorem dropOnePrepend{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n) : 
    dropHead n (prepend n zeroVal fn) j = fn j := 
        let dropPlusOne : dropHead n (prepend n zeroVal fn) j = prepend n zeroVal fn (plusOne n j) := by rfl
        Eq.trans dropPlusOne (prependPlusOne n zeroVal fn j)

def deqClause {α : Type}[DecidableEq α] (n: Nat) : (c1 : Fin n → α) → (c2: Fin n → α) → Decidable (c1 = c2) := 
  match n with
  | 0 => 
    fun c1 c2 => 
      isTrue (funext 
        (fun x => nomatch x))
  | m + 1 => 
    fun c1 c2 =>
      match deqClause _ (dropHead _ c1) (dropHead _ c2) with
      | isTrue h => 
          if c : c1 (⟨0, zeroLtSucc m⟩) = c2 (⟨0, zeroLtSucc m⟩) then
            isTrue 
              (funext fun k =>
                match k with
                | ⟨0, w⟩ => c
                | ⟨j+ 1, w⟩ => 
                  let l1 : dropHead m c1 ⟨j, w⟩ = c1 ⟨j+ 1, w⟩ := by rfl
                  let l2 : dropHead m c2 ⟨j, w⟩ = c2 ⟨j+ 1, w⟩ := by rfl
                  let l3 : dropHead m c1 ⟨j, w⟩ = dropHead m c2 ⟨j, w⟩ := congr h rfl
                  by 
                    rw (Eq.symm l1)
                    apply Eq.symm 
                    rw (Eq.symm l2)
                    exact (Eq.symm l3)
                    done)
          else 
            isFalse (
              fun hyp =>
                let lem : c1 (⟨0, zeroLtSucc m⟩) = c2 (⟨0, zeroLtSucc m⟩) := congr hyp rfl
                c lem
            )
      |isFalse h => 
        isFalse (
          fun hyp => 
            let lem : (dropHead m c1) = (dropHead m c2) := 
              funext (
                fun x =>
                  let l1 : (dropHead m c1) x = c1 (plusOne m x) := rfl
                  let l2 : (dropHead m c2) x = c2 (plusOne m x) := rfl
                  let l3 : c1 (plusOne m x) = c2 (plusOne m x) := congr hyp rfl 
                  by 
                    rw l1
                    rw l3
                    apply Eq.symm
                    exact l2
                    done)
            h lem)

instance {n: Nat}[DecidableEq α] : DecidableEq (Fin n → α) := fun c1 c2 => deqClause _ c1 c2

-- need this as Sigma, Prop and Option don't work together
structure SigmaEqElem{α: Type}{n: Nat}(seq: Fin n → α)(elem: α) where
  index: Fin n 
  equality: seq index = elem

def SigmaEqElem.toProof{α: Type}{n: Nat}{seq: Fin n → α}
  {elem: α}(s : SigmaEqElem (seq) (elem)) :  ∃ (j : Fin n), seq j = elem := 
    ⟨s.index, s.equality⟩ 

structure SigmaPredElem{α: Type}{n: Nat}(seq: Fin n → α)(pred: α → Prop) where
  index: Fin n 
  property: pred (seq index) 

def SigmaPredElem.toProof{α: Type}{n: Nat}{seq: Fin n → α}{pred: α → Prop}
  (s : SigmaPredElem seq pred) : ∃ (j : Fin n), pred (seq j) :=
    ⟨s.index, s.property⟩

structure PiPred{α: Type}{n: Nat}(seq: Fin n → α)(pred: α → Prop) where
  property : (x : Fin n) → pred (seq x)

def PiPred.toProof{α: Type}{n: Nat}{seq: Fin n → α}{pred: α → Prop}
  (p: PiPred seq pred) : ∀ (j : Fin n), pred (seq j) := p.property

def findElem{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: Fin n → α) → (elem: α) →  Option (SigmaEqElem seq elem) :=
    match n with
    | 0 => fun _  => fun _ => none
    | m + 1 => 
      fun fn =>
        fun x =>
          if pf : (fn (Fin.mk 0 (zeroLtSucc m))) =  x then
            let e  := ⟨Fin.mk 0 (zeroLtSucc m), pf⟩
            some (e)
          else
            let pred := findElem (dropHead _ fn) x
            pred.map (fun ⟨j, eql⟩ => 
              let zeroVal := fn (Fin.mk 0 (zeroLtSucc m))
              let l1 := dropPlusOne _ zeroVal j fn
              let l2 : fn (plusOne m j) = x := Eq.trans (Eq.symm l1) eql
              ⟨(plusOne _ j), l2⟩ 
            )

def findPred{α: Type}(pred: α → Prop)[DecidablePred pred]{n: Nat}: 
  (seq: Fin n → α)  →  Option (SigmaPredElem seq pred) :=
    match n with
    | 0 => fun _  => none
    | m + 1 => 
      fun fn =>
        if pf : pred (fn (Fin.mk 0 (zeroLtSucc m))) then
          let e  := ⟨Fin.mk 0 (zeroLtSucc m), pf⟩
          some (e)
        else
          let tail := findPred pred (dropHead _ fn) 
          tail.map (fun ⟨j, eql⟩ => 
            let zeroVal := fn (Fin.mk 0 (zeroLtSucc m))
            let l1 := dropPlusOne _ zeroVal j fn
            let l2  := congrArg pred l1
            let l3 : pred (fn (plusOne m j)) := by
              rw (Eq.symm l2)
              exact eql
              done
            ⟨(plusOne _ j), l3⟩ 
          )

 def showForAll{α: Type}(pred: α → Prop)[DecidablePred pred]{n: Nat}: 
  (seq: Fin n → α)  →  Option (PiPred seq pred) := 
    match n with
    | 0 =>
      fun seq => 
        let pf : (x : Fin 0) → pred (seq x) := fun x => nomatch x  
        some (⟨pf⟩)
    | m + 1 => 
      fun seq =>
        if c : pred (seq (Fin.mk 0 (zeroLtSucc m))) then
          let tail : Fin m → α := dropHead _ seq
          (showForAll pred tail).map (
            fun ⟨ tpf ⟩ =>
              let pf : (j :Fin (m +1)) → pred (seq j) := 
                fun j =>
                  match j with 
                  | ⟨0, w⟩ => c
                  | ⟨i + 1, w⟩ =>
                    let tailWit : i < m := leOfSuccLeSucc w 
                    tpf (⟨i, tailWit⟩)
              ⟨ pf ⟩
          )
        else 
          none

def shiftAtNat : Nat → Nat → Nat :=
    fun k =>
      match k with
      | 0 => 
          fun i =>
            i + 1
      | l+1 => 
          fun j =>
            match j with
            | 0 => 0
            | i + 1 => 
                (shiftAtNat l i) + 1

theorem shiftBound: (k j: Nat) →  shiftAtNat k j < j + 2 :=
    fun k =>
      match k with
      | 0 => 
          fun i =>
            let unfold : shiftAtNat 0 i = i + 1 := by rfl
            by
              rw unfold
              apply Nat.leRefl
              done
      | l+1 => 
          fun j =>
            match j with
            | 0 => 
              let isZero : shiftAtNat (l + 1) 0 = 0 := by rfl
              by
                rw isZero
                exact zeroLtSucc 0
                done 
            | i + 1 => 
              let  unfold : shiftAtNat (l + 1) (i + 1) = (shiftAtNat  l  i) + 1 := by rfl
              let base : shiftAtNat l i < i + 2  :=  shiftBound l i
              let baseP1 : succ (shiftAtNat l i) < succ (i + 2) := succ_lt_succ base
              by
                rw unfold
                exact baseP1
                done

def shiftInheritBound (n k j : Nat) : j < n → shiftAtNat k j < n + 1 := 
  fun h =>
    Nat.leTrans (shiftBound k j) h

def shiftAt : (n : Nat) →  (k: Nat) → (lt : k < succ n) → 
    Fin n → Fin (n + 1) :=
      fun n k lt =>
        fun ⟨i, w⟩ => 
          ⟨shiftAtNat k i, (shiftInheritBound n k i w)⟩

#check Nat.leTrans

theorem seqShiftNatLemma: (l: Nat) → (i : Nat) →   
    (shiftAtNat (l + 1)  (i + 1)) = (shiftAtNat  l  i) + 1 := 
      fun l => fun i => rfl



def dropAtShift{α : Type} : (n : Nat) →  
  (k: Nat) → (lt : k < succ n) →  (fn :Fin (Nat.succ n) → α) → 
    (j : Fin n) →  dropAt n k lt fn j = fn (shiftAt n k lt j) := 
    fun n =>
      match n with
        | 0 =>
          fun k =>
            fun lt =>
              fun fn => 
                 fun l => nomatch l
        | m + 1 => 
          fun k =>            
            match k with
            | 0 =>
              fun lt =>
               fun fn =>
                fun ⟨i, w⟩ => by rfl
            | l + 1 => 
              fun lt =>
               fun fn =>
                fun j =>
                  match j with
                  | ⟨0, w⟩ => by rfl
                  | ⟨i + 1, w⟩ =>
                    let predwit : l < m + 1 := leOfSuccLeSucc lt  
                    let tfn := dropHead _ fn
                    let tail := dropAt m l predwit tfn
                    let head := fn (⟨0, zeroLtSucc (m + 1)⟩)
                    let caseFunc := prepend m head tail
                    let unfold1 : dropAt (m + 1) (l +1) lt fn ⟨i + 1, w⟩ =
                      caseFunc ⟨i + 1, w⟩ := by rfl
                    let unfold2 : caseFunc ⟨i + 1, w⟩ = tail ⟨i, w⟩ := by rfl
                    let base : tail ⟨i, w⟩ = 
                                  fn (shiftAt (m + 1) (l + 1) lt ⟨i + 1, w⟩) := 
                                dropAtShift m l predwit tfn ⟨i, w⟩
                    by 
                      rw unfold1
                      rw unfold2
                      rw base
                      done

-- More specific to SAT

def varSat (clVal: Option Bool)(sectVal : Bool) := clVal = some sectVal

def clauseSat {n: Nat}(clause : Clause n)(sect: Sect n) := 
  ∃ (k : Fin n), varSat (clause k) (sect k)

#check clauseSat

theorem liftSatHead {n: Nat}(clause : Clause (n + 1))(sect: Sect (n + 1)) :
  clauseSat (dropHead n clause) (dropHead n sect) → clauseSat clause sect := 
    fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropHead n clause ⟨k, w⟩ = clause (⟨k+1, _⟩) := by rfl
      let l2 : dropHead n sect ⟨k, w⟩ = sect ⟨k+1, _⟩ := by rfl
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause ⟨k+1, _⟩) (sect ⟨k+1, _⟩) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨⟨k+1, _⟩, pf⟩


theorem liftSatAt {n: Nat}(clause : Clause (n + 1))(sect: Sect (n + 1)) :
  (j : Nat) → (lt : j < n + 1) → 
  clauseSat (dropAt n j lt clause) (dropAt n j lt sect) → clauseSat clause sect := 
    fun j =>
    fun lt =>
     fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropAt n j lt clause ⟨k, w⟩ = clause (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt clause ⟨k, w⟩
      let l2 : dropAt n j lt sect ⟨k, w⟩ = sect (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt sect ⟨k, w⟩
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause (shiftAt n j lt ⟨k, w⟩)) (sect (shiftAt n j lt ⟨k, w⟩)) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨(shiftAt n j lt ⟨k, w⟩), pf⟩

structure ClauseHead{n: Nat}(clause: Clause (n + 1))(branch: Bool) where
  check : clause (⟨0, zeroLtSucc n⟩) = some branch

structure ClauseAt{n: Nat}(k: Fin n)(clause: Clause n)(branch: Bool) where
  check : clause k = some branch

structure DropHeadMatch{n: Nat}(clause: Clause (n + 1))(restriction: Clause n) where
  check : dropHead n clause = restriction

structure DropAtMatch{n: Nat}(k: Fin (n + 1))(clause: Clause (n +1))(restriction: Clause n) where
  check : dropAt n k.val k.isLt clause = restriction


inductive HeadRestrictions{n q: Nat}
  (branch: Bool)(restrictions: Fin q → Clause n)(clause : Clause (n + 1)) where    
  |  headProof : (clause (⟨0, zeroLtSucc n⟩) = some branch) → 
          (HeadRestrictions branch restrictions clause)
  |  restrictClause:  
        (Σ (i: Fin q),  
          DropHeadMatch clause (restrictions i)) → 
            (HeadRestrictions branch restrictions clause)
                       
inductive RestrictionsAt{n q: Nat}(k : Fin (n + 1))
  (branch: Bool)(restrictions: Fin q → Clause n)(clause : Clause (n + 1)) where    
  |  proofAt : (clause (k) = some branch) → 
          (RestrictionsAt k branch restrictions clause)
  |  restrictClause:  
        (Σ (i: Fin q),  
          DropAtMatch k clause (restrictions i)) → 
            (RestrictionsAt k branch restrictions clause)
