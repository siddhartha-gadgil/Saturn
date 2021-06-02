open Nat

def Clause(n : Nat) : Type := (Fin n) → Option Bool

def restrict{α : Type}(n : Nat)(fn: (Fin (Nat.succ n)) → α)(arg: Fin n) : α :=
  fn (Fin.mk (Nat.succ arg.val) (succ_lt_succ arg.isLt))

def eqClause (n: Nat): (Clause n) → (Clause n) → Bool := 
  match n with
    | 0 => fun c1 => (fun c2 => true)
    | k + 1 => 
      fun c1 => (fun c2 => eqClause k (restrict k c1) (restrict k c2)) 

instance {n: Nat} : BEq (Clause n) :=   BEq.mk (eqClause n)

def induce{α : Type}{n : Nat}(fn : (Fin n → α))(zeroVal : α)(arg: Fin (n + 1)) : α :=
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