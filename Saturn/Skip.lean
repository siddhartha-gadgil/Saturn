open Nat


/-
The function `skip n` function maps `Nat` to `Nat` skipping the natural number `n`, 
with numbers less than `n` mapped to themselves and those above mapped to the next number. 
The image is the complement of `n` among natural numbers. 

We need various properties of `skip`, so we define first a function with associated identities,
and project to the value and the desired properties. The structure `ProvedSkip` consists of the
result of `skip` and the associated identities.
-/
structure ProvedSkip(n m: Nat) where
  result : Nat
  lt : m < n → result = m
  ge : n ≤ m → result = m + 1

def provedSkip (n m : Nat) : ProvedSkip n m := 
  if c : m < n then
    ⟨m, fun _ => rfl, fun hyp => False.elim (Nat.lt_irrefl m (Nat.lt_of_lt_of_le c hyp))⟩
  else
    ⟨m + 1, fun hyp => absurd hyp c, fun _ => rfl⟩

-- the `skip` function
def skip: Nat → Nat → Nat 
  | n, m => (provedSkip n m).result

-- equations for `skip` below and above the skipped value

theorem skip_below_eq(n m : Nat) : m < n → (skip n m = m)
  | hyp => (provedSkip n m).lt hyp 

theorem skip_above_eq(n m : Nat) : n ≤ m → (skip n m = m + 1)
  | hyp => (provedSkip n m).ge hyp

theorem skip_not_below_eq(n m : Nat) : Not (m < n) → (skip n m = m + 1) 
  | hyp =>
    let lem : n ≤ m :=
      match Nat.lt_or_ge m n with
      | Or.inl lt => absurd lt hyp
      | Or.inr ge => ge 
    skip_above_eq n m lem

/- We prove that skip has an inverse for points different from the point skipped.
We need some helpers. As usual, we have a proved version of the function first.
-/
structure NatSucc (n: Nat) where
  pred: Nat
  eqn : n = succ (pred)

def posSucc : (n : Nat) → Not (zero = n) → NatSucc n 
  | zero, w => absurd rfl w
  | l + 1, _ => ⟨l, rfl⟩

structure SkipProvedInv(n m : Nat) where
  k : Nat
  eqn : skip n k = m

def provedSkipInverse : (n : Nat) → (m : Nat) → (m ≠ n) →  SkipProvedInv n m :=
  fun n m eqn =>
  if m_lt_n : m < n then
    ⟨m, skip_below_eq n m m_lt_n⟩
  else 
    have n_lt_m : n < m := 
        match Nat.lt_or_ge m n with
        | Or.inl p => absurd p m_lt_n
        | Or.inr p => 
          match Nat.eq_or_lt_of_le p with
          | Or.inl q => absurd (Eq.symm q) eqn
          | Or.inr q => q
    have notZero : Not (zero = m) := by
        intro hyp
        let nLt0 : n < zero := by
          rw [hyp]
          exact n_lt_m
        let n_lt_n : n < n :=
          Nat.lt_of_lt_of_le nLt0 (Nat.zero_le _)
        exact Nat.lt_irrefl n n_lt_n
    let ⟨p, seq⟩ := posSucc m notZero
    have n_le_p : n ≤ p := 
      Nat.le_of_succ_le_succ (by
        rw [← seq]
        exact n_lt_m)
    have imeq : skip n p = m := by
      rw [seq]
      exact (skip_above_eq n p n_le_p)
    ⟨p, imeq⟩

def skipInverse (n m : Nat) : (m ≠ n) → Nat := 
        fun eqn =>  (provedSkipInverse n m eqn).k

theorem skip_inverse_eq(n m : Nat)(eqn : m ≠ n): skip n (skipInverse n m eqn) = m  := 
        (provedSkipInverse n m eqn).eqn

-- Various bounds on the `skip` function.
theorem skip_lt: (k j: Nat) →  skip k j < j + 2 :=
    fun k j =>
      if c : j < k then
        let eqn := skip_below_eq k j c 
        by 
          rw [eqn]
          apply Nat.le_step
          apply Nat.le_refl
      else 
        let eqn := skip_not_below_eq k j c
        by 
          rw [eqn]
          apply Nat.le_refl

theorem skip_ge :(k j: Nat) →  j ≤ skip k j  :=
    fun k j =>
      if c : j < k then
        let eqn := skip_below_eq k j c  
          by 
            rw [eqn]
            apply Nat.le_refl
      else 
        let eqn := skip_not_below_eq k j c
        by 
          rw [eqn]
          apply Nat.le_step
          apply Nat.le_refl

theorem skip_gt_or_arg_below :(k j: Nat) →  Or (j + 1 ≤ skip k j) (j <  k)  :=
    fun k j =>
      if c : j < k then Or.inr c
      else
          let eqn := skip_not_below_eq k j c
          Or.inl (by 
                    rw [eqn]
                    apply Nat.le_refl)

theorem skip_le_succ {n k j : Nat} : j < n → skip k j < n + 1 := 
   by
    intro hyp 
    apply Nat.le_trans (skip_lt k j)
    apply Nat.succ_lt_succ
    exact hyp

theorem skip_preimage_lt {i j k n : Nat}: (k < n + 1) → (j < n + 1) → 
                                skip k i = j → i < n :=
          fun kw jw eqn =>
            match skip_gt_or_arg_below k i with
              | Or.inl ineq =>
                by 
                  have lem1 : i <  j :=
                  by
                    rw [← eqn]
                    exact ineq                
                  apply Nat.lt_of_lt_of_le lem1
                  apply Nat.le_of_succ_le_succ
                  apply jw
              | Or.inr ineqn => by
                  apply Nat.lt_of_lt_of_le ineqn 
                  apply Nat.le_of_succ_le_succ
                  apply kw

-- Injectivity and image of the skip function.
theorem skip_injective: (n: Nat) → (j1 : Nat) → (j2 : Nat) → 
                              (skip n j1 = skip n j2) → j1 = j2 :=
      fun n j1 j2 hyp =>
        match Nat.lt_or_ge j1 n with
        | Or.inl p1 => 
          let eq1 : skip n j1 = j1 := skip_below_eq n j1 p1
          match Nat.lt_or_ge j2 n with
          | Or.inl p2 => 
            let eq2 : skip n j2 = j2 := skip_below_eq n j2 p2
            by
              rw [← eq1]
              rw [← eq2]
              exact hyp
              done
          | Or.inr p2 => 
            let ineq1 : j1 < j2 := Nat.lt_of_lt_of_le p1 p2
            let ineq2 : j1 < skip n j2 := Nat.lt_of_lt_of_le ineq1 (skip_ge n j2)
            let ineq3 : j1 < skip n j1 := Nat.lt_of_lt_of_le ineq2 (Nat.le_of_eq (Eq.symm hyp))
            let ineq4 : j1 < j1 := Nat.lt_of_lt_of_le ineq3 (Nat.le_of_eq eq1)
            False.elim (Nat.lt_irrefl j1 ineq4)
        | Or.inr p1 => 
          let eq1 : skip n j1 = succ j1 := skip_above_eq n j1 p1
          match Nat.lt_or_ge j2 n with
          | Or.inl p2 =>
            let ineq1 : j2 < j1 := Nat.lt_of_lt_of_le p2 p1 
            let ineq2 : j2 < skip n j1 := Nat.lt_of_lt_of_le ineq1 (skip_ge n j1)
            let ineq3 : j2 < skip n j2 := Nat.lt_of_lt_of_le ineq2 (Nat.le_of_eq (hyp))
            let eq2 : skip n j2 = j2 := skip_below_eq n j2 p2
            let ineq4 : j2 < j2 := Nat.lt_of_lt_of_le ineq3 (Nat.le_of_eq eq2)
            False.elim (Nat.lt_irrefl j2 ineq4)
          | Or.inr p2 => 
            let eq2 : skip n j2 = succ j2 := skip_above_eq n j2 p2
            let eq3 : succ j1 = succ j2 := by
              rw [← eq1]
              rw [← eq2]
              exact hyp
              done
            by
              injection eq3
              assumption
              done

theorem skip_no_fixedpoints (k: Nat) : (j: Nat) → Not (skip k j = k) :=
  fun j =>
    if c : j < k then
      let eqn := skip_below_eq k j c  
      fun hyp =>
        let lem1 : k ≤  j := by
          rw [←hyp] 
          rw [eqn]
          apply Nat.le_refl
          done
        let lem2  := Nat.lt_of_lt_of_le c lem1
        not_succ_le_self j lem2
    else 
      let eqn := skip_not_below_eq k j c 
      fun hyp => 
        let lemEq : j + 1 = k := by
          rw [←hyp]
          rw [eqn]
        let lemIneq : j < k := by
          rw [←lemEq]
          apply Nat.lt_succ_self
        c lemIneq
