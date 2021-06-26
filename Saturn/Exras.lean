import Saturn.Basic
import Saturn.FinSeq

open Nat
open clunky 

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


def unitClauseRecDefn(n : Nat)(b : Bool): (k : Fin (n + 1)) →    Clause (n + 1) := 
  match n with
    | 0 => fun k => fun j => some b
    | m + 1 => 
      fun k =>
        match k with
          | ⟨0, _⟩ => prepend _ (some b) (contrad (m + 1))
          | ⟨l + 1, w⟩ => prepend _ none (unitClauseRecDefn m b ⟨l , leOfSuccLeSucc w⟩)

theorem unitClauseDiag(n : Nat)(b : Bool): (k : Fin (n + 1)) → 
                                  unitClauseRecDefn n b k k = some b :=
  match n with
    | 0 => fun k => by rfl
    | m + 1 => 
       fun k =>
        match k with
          | ⟨0, w⟩ => 
            let lhs := prepend _ (some b) (contrad (m + 1)) 0
            let defLHS : unitClauseRecDefn (m + 1) b ⟨0, w⟩ ⟨0, w⟩ = 
              lhs := by rfl
            let lem : lhs = some b := by rfl
            by 
              rw defLHS
              exact lem
              done
          | ⟨l + 1, w⟩ => 
            let lhs := prepend _ none (unitClauseRecDefn m b ⟨l , leOfSuccLeSucc w⟩) ⟨l + 1, w⟩
            let defLHS : unitClauseRecDefn (m + 1) b ⟨l + 1, w⟩ ⟨l + 1, w⟩ = 
              lhs := by rfl 
            let lem : lhs = (unitClauseRecDefn m b ⟨l , leOfSuccLeSucc w⟩) ⟨l, w⟩ := by rfl
            let base : unitClauseRecDefn m b ⟨l , leOfSuccLeSucc w⟩ ⟨l , w⟩
              = some b := unitClauseDiag m b ⟨l , leOfSuccLeSucc w⟩
            by 
              rw defLHS
              rw lem
              rw base
              done

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
        (i: Fin q) →   
          DropHeadMatch clause (restrictions i) → 
            (HeadRestrictions branch restrictions clause)
                       
inductive RestrictionsAt{n q: Nat}(k : Fin (n + 1))
  (branch: Bool)(restrictions: Fin q → Clause n)(clause : Clause (n + 1)) where    
  |  proofAt : (clause (k) = some branch) → 
          (RestrictionsAt k branch restrictions clause)
  |  restrictClause:  
        (i: Fin q) →   
          DropAtMatch k clause (restrictions i) → 
            (RestrictionsAt k branch restrictions clause)

def shiftAtFin : (n : Nat) →  (k: Nat) → (lt : k < succ n) → 
    Fin n → Fin (n + 1) :=
      fun n => 
        match n with 
        | 0 => 
          fun k =>
            fun lt =>
                  fun _ => 
                    ⟨0, zeroLtSucc 0⟩
        | m + 1 => 
          fun k =>
            match k with
            | 0 => 
              fun lt =>
                fun ⟨i, w⟩ =>
                  let wit : i < m + 2 := leStep w
                  ⟨i + 1, succ_lt_succ w⟩
            | l+1 => 
              fun lt =>
                fun j =>
                  match j with
                  | ⟨0, _⟩ => ⟨0, zeroLtSucc _⟩
                  | ⟨i + 1, w⟩ => 
                      plusOne (m + 1) (shiftAtFin m l (leOfSuccLeSucc lt) ⟨i, leOfSuccLeSucc w⟩)
