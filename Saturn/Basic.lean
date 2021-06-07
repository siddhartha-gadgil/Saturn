open Nat

def Clause(n : Nat) : Type := (Fin n) → Option Bool

def plusOne(n: Nat) : Fin n → Fin (n + 1) :=
  fun arg => Fin.mk (succ (Fin.val arg)) (succ_lt_succ (Fin.isLt arg))

def dropHead{α : Type}(n : Nat) : (Fin (Nat.succ n) → α) → Fin n →  α :=
  fun fn =>
    fun arg =>
      fn (plusOne n arg)


        

def eqClause (n: Nat): (Clause n) → (Clause n) → Bool := 
  match n with
    | 0 => fun c1 => (fun c2 => true)
    | k + 1 => 
      fun c1 => (fun c2 => 
          let head1 := c1 0
          let head2 := c2 0
          (head1 == head2) && (eqClause k (dropHead
         k c1) (dropHead
         k c2))) 

instance {n: Nat} : BEq (Clause n) :=   BEq.mk (eqClause n)

def pred(n: Nat)(k: Nat) : k + 1 < n + 1 → Fin n :=
  fun witness =>
    let predwit : k < n := leOfSuccLeSucc witness
    Fin.mk k (predwit)

def prepend{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(arg: Fin (n + 1)) : α :=
  match arg with
    | Fin.mk 0 _ => zeroVal
    | Fin.mk (k + 1) witness =>
      fn (pred n k witness)


def branchClause {n: Nat} (branch: Bool) (clause : Clause (n + 1)) : Option (Clause n) :=
  match (clause (Fin.mk 0 (zeroLtSucc n))) with 
  | some (branch) => none
  | none => some (dropHead
 n clause)

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
          ((dpSAT k (branchMap true clauses)).map (prepend k true)).orElse
          ((dpSAT k (branchMap false clauses)).map (prepend k false))

def isContradiction(n: Nat) : (Clause n) → Bool :=
  match n with
    | 0 => fun clause => true
    | k + 1 => fun clause => ((clause 0) == none) && (isContradiction k (dropHead
   k clause))


def findUnit(n: Nat) : Clause n → Option ((Fin n) × Bool) :=
  match n with 
    | 0 => fun _ => none
    | k + 1 => 
      fun clause =>
        match clause 0 with 
          | some (b) => 
            if isContradiction _ (dropHead
           k clause) then 
              some ((0, b))
            else
              none
          | none =>
            let shift : (Fin k) × Bool → (Fin (k + 1)) × Bool :=
              fun (x, b) => (plusOne k x, b)
           (findUnit k (dropHead
           k clause)).map shift

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
              let shorterClauses := clauses.map (dropHead
             k)
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
              ((dlppSAT k (branchMap true clauses)).map (prepend k true)).orElse
              ((dlppSAT k (branchMap false clauses)).map (prepend k false))
            | some ((j, b)) =>
                let permuted := clauses.map (transposeZero j)
                ((dlppSAT k (branchMap b permuted)).map (prepend k b)).map (transposeZero j)


