import Lean.Meta
open Nat

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
def skip: Nat → Nat → Nat :=
  fun n m => (provedSkip n m).result

-- equations for `skip` below and above the skipped value

theorem skip_below_eq(n m : Nat) : m < n → (skip n m = m) :=
  fun hyp => (provedSkip n m).lt hyp 

theorem skip_above_eq(n m : Nat) : n ≤ m → (skip n m = m + 1) :=
  fun hyp => (provedSkip n m).ge hyp

theorem skip_not_below_eq(n m : Nat) : Not (m < n) → (skip n m = m + 1) :=
  fun hyp =>
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

def posSucc : (n : Nat) → Not (zero = n) → NatSucc n :=
  fun n =>
  match n with
  | zero => fun w => absurd rfl w
  | l + 1 => fun _ => ⟨l, rfl⟩

structure SkipProvedInv(n m : Nat) where
  k : Nat
  eqn : skip n k = m

def provedSkipInverse : (n : Nat) → (m : Nat) → (m ≠ n) →  SkipProvedInv n m :=
  fun n m eqn =>
  if mLtn : m < n then
    ⟨m, skip_below_eq n m mLtn⟩
  else 
    let nLtm : n < m := 
        match Nat.lt_or_ge m n with
        | Or.inl p => absurd p mLtn
        | Or.inr p => 
          match Nat.eq_or_lt_of_le p with
          | Or.inl q => absurd (Eq.symm q) eqn
          |Or.inr q => q
    let notZero : Not (zero = m) := 
      fun hyp =>
        let nLt0 : n < zero := by
          rw [hyp]
          exact nLtm
        let nLtn : n < n :=
          Nat.lt_of_lt_of_le nLt0 (Nat.zero_le _)
        Nat.lt_irrefl n nLtn
    let ⟨p, seq⟩ := posSucc m notZero
    let nLep : n ≤ p := 
      Nat.le_of_succ_le_succ (by
        rw [← seq]
        exact nLtm
        done)
    let imeq : skip n p = m := by
      rw [seq]
      exact (skip_above_eq n p nLep)
      done
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
          done
      else 
        let eqn := skip_not_below_eq k j c
        by 
          rw [eqn]
          apply Nat.le_refl
          done 

theorem skip_ge :(k j: Nat) →  j ≤ skip k j  :=
    fun k j =>
      if c : j < k then
        let eqn := skip_below_eq k j c  
          by 
            rw [eqn]
            apply Nat.le_refl
            done
      else 
        let eqn := skip_not_below_eq k j c
        by 
          rw [eqn]
          apply Nat.le_step
          apply Nat.le_refl
          done

theorem skip_gt_or :(k j: Nat) →  Or (j + 1 ≤ skip k j) (j <  k)  :=
    fun k j =>
      if c : j < k then
          Or.inr c
      else
          let eqn := skip_not_below_eq k j c
          Or.inl (by 
                    rw [eqn]
                    apply Nat.le_refl
                    done)

theorem skip_le_succ {n k j : Nat} : j < n → skip k j < n + 1 := 
   by
    intro hyp 
    apply Nat.le_trans (skip_lt k j)
    apply Nat.succ_lt_succ
    exact hyp

theorem skip_preimage_lt {i j k n : Nat}: (k < n + 1) → (j < n + 1) → 
                                skip k i = j → i < n :=
          fun kw jw eqn =>
            match skip_gt_or k i with
              | Or.inl ineq =>
                by 
                  have lem1 : i <  j :=
                  by
                    rw [← eqn]
                    exact ineq
                    done                 
                  have lem2 : i < n :=
                  by
                    apply Nat.lt_of_lt_of_le
                    apply lem1
                    apply Nat.le_of_succ_le_succ
                    apply jw
                    done 
                  exact lem2
                  done
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


def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

theorem witness_independent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) → 
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          match j, eqn, jw with 
          | .(i), rfl, ijw =>
               rfl

namespace FinSeq
def init {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq k (Nat.le_step w)

def last{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq n (Nat.le_refl _)

def delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α := 
  fun j w =>
    seq (skip k j) (skip_le_succ w)

structure ProvedInsert{α : Type}{n: Nat}(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n + 1)(j: Nat) (jw : j < n + 1) where
  result : α
  checkImage : (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw
  checkFocus : j = k → result = value

def provedInsert{α : Type}(n: Nat)(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n + 1)(j: Nat) (jw : j < n + 1) : 
                  ProvedInsert value seq k kw j jw := 
          if c: j = k then
            let result := value
            let checkImage : 
              (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw := 
                fun i iw hyp =>
                  let lem : skip k i = k := by
                    rw [hyp]
                    rw [c]
                    done
                  let contra := skip_no_fixedpoints k i lem
                  nomatch contra
            let  checkFocus : j = k → result = value := fun  _  => rfl
            ⟨result, checkImage, checkFocus⟩
          else  
            let i := skipInverse k j c 
            let eqn := skip_inverse_eq k j c  
            let bound : i < n  := skip_preimage_lt kw jw eqn
            let result := seq i bound
            let checkImage : 
              (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw := 
                fun i1 iw1 hyp =>
                  let lem1 : i1 = i := by 
                    apply (skip_injective k)
                    rw [hyp]
                    rw [(Eq.symm eqn)]
                    done
                  let lem2 : seq i1 iw1 = seq i bound := 
                    witness_independent seq i1 i iw1 bound lem1
                  by
                    rw [lem2]
                    done
            let  checkFocus : j = k → result = value := 
              fun  hyp  => 
                let lem : skip k i = k := by
                    rw [eqn]
                    rw [hyp]
                    done
                  let contra := skip_no_fixedpoints k i lem
                  nomatch contra 
            ⟨result, checkImage, checkFocus⟩

def insert{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (FinSeq n   α) →  (FinSeq (Nat.succ n)  α) := 
  fun n k lt seq j w =>  
    (provedInsert n value seq k lt j w).result
end FinSeq


inductive Vector (α : Type) : Nat → Type where 
  | nil : Vector α zero
  | cons{n: Nat}(head: α) (tail: Vector  α n) : Vector α  (n + 1) 

infixr:66 "+:" => Vector.cons

open Vector

def Vector.coords {α : Type}{n : Nat}(v: Vector α n) : FinSeq n α :=
  fun j jw =>
  match n, v, j, jw with
  | .(zero), nil, k, lt => nomatch lt
  | m + 1, cons head tail, zero, lt => head
  | m + 1, cons head tail, j + 1, w =>  tail.coords j (Nat.le_of_succ_le_succ w)

def seqVecAux {α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (accum : Vector α m) →  
       Vector α l:= 
    match n with
    | zero => fun s => fun _ => fun seq2 =>
      by
        have ss : l = m := by 
          rw [← s]
          apply Nat.zero_add
          done
        have sf : Vector α l = Vector α m := by
          rw [ss]
        exact Eq.mpr sf seq2
        done
    | k + 1 => fun s seq1 seq2 => 
      let ss : k + (m + 1)  = l := 
        by
          rw [← s]
          rw [(Nat.add_comm m 1)]
          rw [(Nat.add_assoc k 1 m)]
          done
      seqVecAux ss (seq1.init) ((seq1.last) +: seq2)

def FinSeq.vec {α : Type}{n: Nat} : FinSeq n α  →  Vector α n := 
    fun seq => seqVecAux (Nat.add_zero n) seq Vector.nil
  
def Clause(n : Nat) : Type := Vector (Option Bool) n

def Valuation(n: Nat) : Type := Vector Bool n

inductive SatAnswer{dom n: Nat}(clauses : Vector (Clause n) dom) where
  | unsat : SatAnswer clauses
  | sat : (valuation : Valuation n) → SatAnswer clauses 

structure SimpleRestrictionClauses{dom n: Nat}
    (clauses: Vector (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector  (Clause n) codom

def prependRes{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom): 
        (rd : SimpleRestrictionClauses clauses) → 
           (head : Clause (n + 1)) → 
        SimpleRestrictionClauses (head +: clauses) := 
        fun rd  head => 
          if c : head.coords focus focusLt = some branch then
            ⟨rd.codom, rd.restClauses⟩
          else
            ⟨rd.codom + 1, (FinSeq.vec (FinSeq.delete focus focusLt head.coords)) +: rd.restClauses⟩

def restClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)  
        (clauses: Vector (Clause (n + 1)) dom) :
         SimpleRestrictionClauses clauses :=
            match dom, clauses with
            | 0, _ =>  ⟨0, Vector.nil⟩
            | m + 1, Vector.cons head clauses =>
                prependRes branch focus focusLt clauses 
                            (restClauses branch focus focusLt clauses) head           

def answerSAT{n dom : Nat}: (clauses : Vector (Clause n) dom) →  SatAnswer clauses :=
      match n with
      | zero => 
           match dom with
            | zero => fun cls => SatAnswer.sat Vector.nil
            | l + 1 => fun _ =>  SatAnswer.unsat     
      | m + 1 =>
        fun clauses =>
        let cls := clauses 
        let bd := zero_lt_succ m
        let rd  := 
            restClauses false zero bd clauses
        let subCls := rd.restClauses
        let subSol: SatAnswer subCls := answerSAT subCls
        match subSol with
        | SatAnswer.sat valuation  => 
          let valuationN := FinSeq.insert false m zero bd valuation.coords
          SatAnswer.sat valuationN.vec 
        | SatAnswer.unsat  => 
            let rd 
                := restClauses true zero bd cls
            let subCls := rd.restClauses
            let subSol : SatAnswer subCls := answerSAT subCls
            match subSol with
            | SatAnswer.sat valuation  => 
                let valuationN := FinSeq.insert true _ zero bd valuation.coords
                SatAnswer.sat valuationN.vec 
            | SatAnswer.unsat   => 
                SatAnswer.unsat

open Lean.Meta
open Lean.Elab.Term

syntax (name:= nrmlform)"whnf!" term : term
@[termElab nrmlform] def normalformImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(whnf! $s) => 
      do
        let t ← elabTerm s none 
        let e ← whnf t
        return e
  | _ => Lean.Elab.throwIllFormedSyntax


def cls1 : Clause 2 := -- ¬P
  (some false) +: (none) +: Vector.nil

def cls2 : Clause 2 := (some true) +: none +: Vector.nil  -- P

def egStatement := cls1 +: cls2 +: Vector.nil

def egAnswer : SatAnswer egStatement := answerSAT egStatement

def egAnswerNorm : SatAnswer egStatement := whnf! egAnswer