open Nat

def Clause(n : Nat) : Type := (Fin n) → Option Bool

#eval true && false

def restrict{α : Type}(n : Nat)(fn: (Fin (Nat.succ n)) → α)(arg: Fin n) : α :=
  fn (Fin.mk (Nat.succ arg.val) (succ_lt_succ arg.isLt))

def eqClause (n: Nat): (Clause n) → (Clause n) → Bool := 
  match n with
    | 0 => fun c1 => (fun c2 => true)
    | k + 1 => 
      fun c1 => (fun c2 => 
          let head1 := c1 0
          let head2 := c2 0
          (head1 == head2) && (eqClause k (restrict k c1) (restrict k c2))) 

instance {n: Nat} : BEq (Clause n) :=   BEq.mk (eqClause n)

def induce{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(arg: Fin (n + 1)) : α :=
  match arg with
    | Fin.mk 0 _ => zeroVal
    | Fin.mk (k + 1) witness =>
      let pred := Fin.mk k witness
      fn (pred)


def branchClause {n: Nat} (branch: Bool) (clause : Clause (n + 1)) : Option (Clause n) :=
  if (clause (Fin.mk 0 (zeroLtSucc n))) == some (branch) then
    none
  else
    some (restrict n clause)

def branchMap  {n: Nat} (branch: Bool)(clauses : List (Clause (n  + 1))) 
  : List (Clause n) :=
    List.eraseDups (List.filterMap (branchClause branch) clauses)

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
        Option.orElse
          (Option.map (induce k true) (dpSAT k (branchMap true clauses)))
          (Option.map (induce k false) (dpSAT k (branchMap false clauses)))