open Nat

def Clause(n : Nat) : Type := (Fin n) → Option Bool

#eval true && false

def plusOne(n: Nat) : Fin n → Fin (n + 1) :=
  fun arg => Fin.mk (succ (Fin.val arg)) (succ_lt_succ (Fin.isLt arg))

def restrict{α : Type}(n : Nat) : (Fin (Nat.succ n) → α) → Fin n →  α :=
  fun fn =>
    fun arg =>
      fn (plusOne n arg)

def lem1{α : Type}(n: Nat)(zeroVal : α)(j: Fin n)(g: (Fin (succ n)) → α) 
        : (restrict n g j) = g (plusOne n j) := by
        rfl
        done
        

def eqClause (n: Nat): (Clause n) → (Clause n) → Bool := 
  match n with
    | 0 => fun c1 => (fun c2 => true)
    | k + 1 => 
      fun c1 => (fun c2 => 
          let head1 := c1 0
          let head2 := c2 0
          (head1 == head2) && (eqClause k (restrict k c1) (restrict k c2))) 

instance {n: Nat} : BEq (Clause n) :=   BEq.mk (eqClause n)

def pred(n: Nat)(k: Nat) : k + 1 < n + 1 → Fin n :=
  fun witness =>
    let predwit : k < n := leOfSuccLeSucc witness
    Fin.mk k (predwit)

def induce{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(arg: Fin (n + 1)) : α :=
  match arg with
    | Fin.mk 0 _ => zeroVal
    | Fin.mk (k + 1) witness =>
      fn (pred n k witness)


def branchClause {n: Nat} (branch: Bool) (clause : Clause (n + 1)) : Option (Clause n) :=
  if (clause (Fin.mk 0 (zeroLtSucc n))) == some (branch) then
    none
  else
    some (restrict n clause)

def branchMap  {n: Nat} (branch: Bool)(clauses : List (Clause (n  + 1))) 
  : List (Clause n) :=
    (List.filterMap (branchClause branch) clauses).eraseDups

def contradiction(n: Nat) : Clause n :=
  fun n => none

def Solution(n: Nat) : Type := (Fin n) → Bool

def dpSAT (n: Nat): (List (Clause n)) →  Option (Solution n) :=
  match n with 
    | 0 => 
      fun clauses => 
        if clauses == [contradiction 0] then 
          none 
        else some (fun n => true) 
    | k + 1 => 
      fun clauses =>
          ((dpSAT k (branchMap true clauses)).map (induce k true)).orElse
          ((dpSAT k (branchMap false clauses)).map (induce k false))

def isContradiction(n: Nat) : (Clause n) → Bool :=
  match n with
    | 0 => fun clause => true
    | k + 1 => fun clause => ((clause 0) == none) && (isContradiction k (restrict k clause))

#eval isContradiction 3 (contradiction 3)
#eval isContradiction 3 (fun x => some (true))


def eg : Bool × Nat := 
  match (true, 0) with
    | (x, y) => (not x, y + 1)
  
#eval eg

def findUnit(n: Nat) : Clause n → Option ((Fin n) × Bool) :=
  match n with 
    | 0 => fun _ => none
    | k + 1 => 
      fun clause =>
        match clause 0 with 
          | some (b) => 
            if isContradiction _ (restrict k clause) then 
              some ((0, b))
            else
              none
          | none =>
            let shift : (Fin k) × Bool → (Fin (k + 1)) × Bool :=
              fun (x, b) => (plusOne k x, b)
           (findUnit k (restrict k clause)).map shift

def pureSign (l : List (Option Bool)) :  Option Bool :=
  match l with
    | [] => none
    | x :: ys => 
      match x with 
      | some (b) =>
        let allowed : Option Bool → Bool :=
          fun op => op != some (not b) 
        if  ys.all allowed then
          some (b)
        else
          none
      | none => none

def findPure (n: Nat) : List (Clause n) →  Option ((Fin n) × Bool) :=
  match n with
    | 0 => fun _ => none
    | k + 1 =>
      fun clauses =>
        let zeroSect := clauses.map (fun cl => cl 0)
        if zeroSect.all (Option.isNone) then 
          some ((0, true))
        else 
          match (pureSign zeroSect) with 
            | some (b) => (0, b)
            | none =>
              let shift : (Fin k) × Bool → (Fin (k + 1)) × Bool :=
                fun (x, b) => (plusOne k x, b)
              let shorterClauses := clauses.map (restrict k)
              (findPure k (shorterClauses)).map (shift)
              
def transposeZero {α : Type}{n: Nat} (k: Fin (succ n)) (fn :Fin (succ n) → α) : (Fin (succ n) → α) :=
  fun l =>
    if l == k then 
      fn 0
    else 
      if l == 0 then
        fn k
      else 
        fn l

def preAssign {n: Nat}(clauses : List (Clause (succ n))) : Option ((Fin (succ n)) × Bool) :=
  Option.orElse (List.findSome? (findUnit (succ n)) clauses) 
    (findPure (succ n) clauses)

def dlppSAT (n: Nat): (List (Clause n)) →  Option (Solution n) :=
  match n with 
    | 0 => 
      fun clauses => 
        match clauses with 
          | x :: ys => none
          | [] => some (fun n => true) 
    | k + 1 => 
      fun clauses =>
        if clauses.contains (contradiction (k + 1)) then 
        none
        else 
          match preAssign clauses with
            | none =>
              ((dlppSAT k (branchMap true clauses)).map (induce k true)).orElse
              ((dlppSAT k (branchMap false clauses)).map (induce k false))
            | some ((j, b)) =>
                let permuted := clauses.map (transposeZero j)
                ((dlppSAT k (branchMap b permuted)).map (induce k b)).map (transposeZero j)

theorem zeroLenClsEql : ∀ (cl1: Clause 0), ∀ (cl2: Clause 0) ,  (cl1 = cl2) := 
  fun cl1 =>
    fun cl2 =>
      funext (
        fun (x : Fin 0) =>
          match x with 
            | ⟨_, h⟩ => absurd h (notLtZero _)
      )


def transpZero {n: Nat} (k: Fin (succ n)) (l: Fin (succ n)) : Fin (succ n) :=
    if (l == 0) then 
      k
    else 
      if (l == k) then
        0
      else l

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
 
      
-- scratch

def lem2{α: Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n):
  induce n zeroVal fn (plusOne n j) = fn j :=
    let k := j.val
    let witness := j.isLt
    let l0 : Fin.val (plusOne n j) = succ k := by rfl
    let l1 : induce n zeroVal fn (Fin.mk (succ k) 
      (succ_lt_succ witness)) = fn (Fin.mk k witness) := by rfl
    let l2 : (plusOne n j) = Fin.mk (succ k) (succ_lt_succ witness) := by rfl
    let indFn: Fin (n + 1) → α := 
      fun p1j => induce n zeroVal fn p1j
    let l3 : induce n zeroVal fn (plusOne n j) =
       induce n zeroVal fn (Fin.mk (succ k) (succ_lt_succ witness)) := congrArg indFn l2
    let l4 := Eq.trans l3 l1
    let l5 :  Fin.mk k witness = j := by
      apply Fin.eqOfVeq
      rfl
      done
    let l6 := congrArg fn l5
    Eq.trans l4 l6
  

def restrictInduce{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n) : 
    restrict n (induce n zeroVal fn) j = fn j := 
        let lem1 : restrict n (induce n zeroVal fn) j = induce n zeroVal fn (plusOne n j) := by rfl
        let lem3 := Eq.trans lem1 (lem2 n zeroVal fn j)
        lem3

def indc {α: Type} (zeroVal : α) (fn: Nat → α) : Nat → α :=
  fun n =>
    match n with
    | 0 => zeroVal
    | n + 1 => fn (n)
  
def lemInd{α: Type}(n: Nat)(zeroVal: α)(fn: Nat → α) : indc zeroVal fn (succ n) = fn n := by rfl 




-- scratch

def transpLemma1{n: Nat}(fn :Fin (succ n) → α)(k : Fin (succ n)):
  (transpZero k (transpZero k 0)) = k := 
    sorry

def transposeInvolution {α : Type}{n: Nat}(fn :Fin (succ n) → α) : ∀ k : Fin (succ n), 
  (transposeZero k ((transposeZero k fn))) = fn := 
    fun k =>
      funext (
        fun l =>
          if c: l == k then
            sorry
          else if l == 0
            then sorry
          else sorry
      ) 


def testDec (a: Nat)[C : Decidable (Not (a = 2))] : Bool :=
  match C with 
    | isTrue pf => true
    | isFalse pf => 
      false
#eval testDec 2

theorem s : 1 = 1 := by
  simp
  done

def piEg := (n : Nat) → (n = 1)

#reduce piEg

#check funext

