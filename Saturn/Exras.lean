import Saturn.Basic
import Saturn.FinSeq

open Nat 

#check Nat.rec

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


