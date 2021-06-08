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

-- good exercise but not needed if using decidable equality


def boolEqOfBeqEqTrue : {x y : Bool} → (x == y) = true →  x = y
  | true,   true,   h => rfl
  | true,   false, h => Bool.noConfusion h
  | false,   false,   h => rfl
  | false,   true, h => Bool.noConfusion h

def boolNEqOfBeqEqFalse : {x y : Bool} → (x == y) = false → Not  (x = y)
  | true,   true,   h1, h2 => Bool.noConfusion h1
  | true,   false, h1, h2 => Bool.noConfusion h2
  | false,   false,   h1, h2 => Bool.noConfusion h1 
  | false,   true, h1, h2 => Bool.noConfusion h2

class LiftEq(α : Type)[BEq α] where
  liftEq : (x : α) → (y : α) → (x == y) = true → x = y
  liftNeq : (x : α) → (y : α) → (x == y) = false → Not (x = y)

def liftEquality{α: Type}[beq : BEq α][leq : LiftEq α]{x y : α} : (x == y) = true → x = y :=
  fun eq => leq.liftEq x y eq

def liftInEquality{α: Type}[beq : BEq α][leq : LiftEq α]{x y : α} : (x == y) = false → Not (x = y) :=
  fun eq => leq.liftNeq x y eq  

def optLiftTrue{α: Type}[BEq α][LiftEq α] : {x y : Option α} → (x == y) = true →  x = y   
  | some x, none, h => Bool.noConfusion h
  | none, some x, h => Bool.noConfusion h
  | none, none, h => rfl
  | some x, some y, h =>
    let lem1 : (x == y) = (some x == some y) := by rfl
    let lem2 := Eq.trans lem1 h
    let lem3 := liftEquality lem2
    congrArg some lem3

def optLiftFalse{α: Type}[BEq α][LiftEq α] : {x y : Option α} → (x == y) = false → Not (x = y)   
  | some x, none, h1, h2 => Option.noConfusion h2
  | none, some x, h1, h2 => Option.noConfusion h2
  | none, none, h1, h2 => Bool.noConfusion h1
  | some x, some y, h1, h2 =>
    let lem1 : (x == y) = (some x == some y) := by rfl
    let lem2 := Eq.trans lem1 h1
    let lem3 := liftInEquality lem2
    let lem4 : x = y := by
      injection h2
      assumption
      done
    absurd lem4 lem3

instance : LiftEq Bool where 
  liftEq := fun x => fun y => fun eq => boolEqOfBeqEqTrue eq
  liftNeq := fun x => fun y => fun eq => boolNEqOfBeqEqFalse eq

instance {α: Type}[BEq α][LiftEq α] : LiftEq (Option α) where
  liftEq := fun x => fun y => fun eq => optLiftTrue eq
  liftNeq := fun x => fun y => fun neq => optLiftFalse neq


-- scratch : miscellaneous theorems

theorem succEq(k: Nat)(l: Nat) : (k = l) →  (succ k = succ l):= by
  intro h
  apply congrArg
  assumption
  done 

theorem succNotZero(n : Nat) : ((succ n) = 0) → False := by
  simp
  done

theorem zeroNotSucc(n : Nat) : (0 = (succ n)) → False := by
  simp
  done

theorem succInjective(k: Nat)(l: Nat) : (succ k = succ l) → k = l := by
  intro h
  injection h
  assumption
  done


def indc {α: Type} (zeroVal : α) (fn: Nat → α) : Nat → α :=
  fun n =>
    match n with
    | 0 => zeroVal
    | n + 1 => fn (n)
  
theorem lemInd{α: Type}(n: Nat)(zeroVal: α)(fn: Nat → α) : indc zeroVal fn (succ n) = fn n := by rfl 

def boolBranch(b: Bool)(n: Nat) := 
  match b with
  | true => n 
  | false => n + 1

theorem boolBranchTest(n: Nat) : boolBranch false n = n + 1 := by rfl 

inductive NEq(k: Nat)(l: Nat) where
  | AreEq (pf : k = l) : NEq k l
  | AreUneq (contra : (k = l) → False) : NEq k l

def decNEq(k: Nat)(l: Nat): NEq k l :=
  match k with
    | 0 =>
      match l with
      | 0 =>
        let lem : 0 = 0 := by rfl  
        NEq.AreEq lem
      | succ m => NEq.AreUneq (zeroNotSucc m)
    | n + 1 => 
      match l with
      | 0 => NEq.AreUneq (succNotZero n)
      | m + 1 =>
        let pred := decNEq n m
        match pred with
        | NEq.AreEq pf =>
          NEq.AreEq (congrArg succ pf)
        | NEq.AreUneq contra =>
          NEq.AreUneq (fun h => contra (succInjective n m h))

