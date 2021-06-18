open Nat

namespace clunky

def Clause(n : Nat) : Type := (Fin n) → Option Bool

def Sect(n: Nat) : Type := Fin n → Bool

end clunky

open clunky

def plusOne(n: Nat) : Fin n → Fin (n + 1) :=
  fun arg => Fin.mk (succ (Fin.val arg)) (succ_lt_succ (Fin.isLt arg))

def dropHead{α : Type}(n : Nat) : (Fin (Nat.succ n) → α) → Fin n →  α :=
  fun fn =>
    fun arg =>
      fn (plusOne n arg)

def beqClause (n: Nat): (Clause n) → (Clause n) → Bool := 
  match n with
    | 0 => fun c1 => (fun c2 => true)
    | k + 1 => 
      fun c1 => (fun c2 => 
          let head1 := c1 0
          let head2 := c2 0
          (head1 == head2) && (beqClause k (dropHead
         k c1) (dropHead
         k c2))) 

instance {n: Nat} : BEq (Clause n) :=   BEq.mk (beqClause n)

def prepend{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(arg: Fin (n + 1)) : α :=
  match arg with
    | ⟨0, _⟩ => zeroVal
    | ⟨k + 1, witness⟩ =>
      fn (⟨k, leOfSuccLeSucc witness⟩)

infixr:80 "::::" => prepend _

def dropAt{α : Type} : (n : Nat) →  
  (k: Nat) → (lt : k < succ n) →  (Fin (Nat.succ n) → α) → Fin n →  α := 
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
                dropHead (m + 1) fn
            | l + 1 => 
              fun lt =>
               fun fn =>
                let predwit : l < m + 1 := leOfSuccLeSucc lt  
                let tail := dropAt m l predwit (dropHead _ fn)
                let head := fn (⟨0, zeroLtSucc (m + 1)⟩)
                prepend m head tail

def insertAt{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (Fin n →  α) →  (Fin (Nat.succ n) → α) := 
      fun n =>
        match n with
          | 0 =>  
            fun k =>
              fun lt =>
                fun _ => 
                  fun l => value
          | m + 1 => 
            fun k =>
              match k with
              | 0 =>
                fun lt =>
                fun fn =>
                  prepend _ value fn
              | l + 1 => 
                fun lt =>
                fun fn =>
                  let predwit : l < m + 1 := leOfSuccLeSucc lt
                  let head := fn (Fin.mk 0 (zeroLtSucc (m)))
                  let tail := insertAt value m l predwit (dropHead _ fn)
                  prepend _ head tail


def branchClause {n: Nat} (branch: Bool) (clause : Clause (n + 1)) : Option (Clause n) :=
  match (clause (Fin.mk 0 (zeroLtSucc n))) with 
  | some (branch) => none
  | none => some (dropHead n clause)

def branchAtClause {n: Nat} (branch: Bool)(k : Fin (n + 1)) (clause : Clause (n + 1)) : 
  Option (Clause n) :=
    match (clause (k)) with 
    | some (branch) => none
    | none => some (dropAt n k.val k.isLt clause)

def branchMap  {n: Nat} (branch: Bool)(clauses : List (Clause (n  + 1))) 
  : List (Clause n) :=
    (List.filterMap (branchClause branch) clauses).eraseDups

def branchAtMap  {n: Nat} (branch: Bool)(k : Fin (n + 1))(clauses : List (Clause (n  + 1))) 
  : List (Clause n) :=
    (List.filterMap (branchAtClause branch k) clauses).eraseDups 

def contradiction(n: Nat) : Clause n :=
  fun j => none

def Solution(n: Nat) : Type := (Fin n) → Bool

def dpSAT (n: Nat): (List (Clause n)) →  Option (Solution n) :=
  match n with 
    | 0 => 
      fun clauses => 
        if clauses == [contradiction 0] then 
          none 
        else some (fun n => nomatch n) 
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
            if isContradiction _ (dropHead k clause) then 
              some ((0, b))
            else
              none
          | none =>
            let skip : (Fin k) × Bool → (Fin (k + 1)) × Bool :=
              fun (x, b) => (plusOne k x, b)
           (findUnit k (dropHead
           k clause)).map skip

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
              let skip : (Fin k) × Bool → (Fin (k + 1)) × Bool :=
                fun (x, b) => (plusOne k x, b)
              let shorterClauses := clauses.map (dropHead
             k)
              (findPure k (shorterClauses)).map (skip)
              

def preAssign {n: Nat}(clauses : List (Clause (succ n))) : Option ((Fin (succ n)) × Bool) :=
  Option.orElse (List.findSome? (findUnit (succ n)) clauses) 
    (findPure (succ n) clauses)

def dlppSAT (n: Nat): (List (Clause n)) →  Option (Solution n) :=
  match n with 
    | 0 => 
      fun clauses => 
        match clauses with 
          | x :: ys => none
          | [] => some (fun n => nomatch n) 
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
                -- let permuted := clauses.map (transposeZero j)
                -- ((dlppSAT k (branchMap b permuted)).map (prepend k b)).map (transposeZero j)
                ((dlppSAT k (branchAtMap b j clauses)).map (insertAt b k j.val j.isLt))


