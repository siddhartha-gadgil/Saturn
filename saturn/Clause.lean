open Nat

def Clause(n : Nat) : Type := (Fin n) → Option Bool

def restrict{α : Type}(n : Nat)(fn: (Fin (Nat.succ n)) → α)(arg: Fin n) : α :=
  fn (Fin.mk (Nat.succ arg.val) (succ_lt_succ arg.isLt))

#check restrict (5) (fun k => (k.val % 2 == 0))

def induce{α : Type}(n : Nat)(fn : (Fin n → α))(zeroVal : α)(arg: Fin (n + 1)) : α :=
  match arg with
    | Fin.mk 0 _ => zeroVal
    | Fin.mk (k + 1) witness =>
      let pred := Fin.mk k witness
      fn (pred)

def testRestrictClause(n: Nat): (Clause (n + 1)) → (Clause n) := restrict (n)

#check testRestrictClause (6)

def branchClause {n: Nat} (branch: Bool) (clause : Clause (n + 1)) : Option (Clause n) :=
  if (clause (Fin.mk 0 (zeroLtSucc n))) == some (branch) then
    none
  else
    some (restrict n clause)