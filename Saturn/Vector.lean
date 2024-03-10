import Saturn.FinSeq
import Saturn.Core
import Mathlib.Data.Vector.Basic
open Nat
/-
Functions and theorems for working with vectors. Most of these are conversions from
finite sequences to vectors,  its consistency with the conversion from vectors to
finite sequences defined in `Core`, and the consistency of various operations with conversions
between finite sequences and vectors in both directions.
-/
open Vector

#check Vector
#check List.count



def Vector.count {α : Type}{n : Nat}(v: Vector α n)(pred: α → Bool) : Nat := match v with
  | ⟨l, _⟩ => l.filter pred |>.length

def seqVecAux {α: Type}{n m l: Nat}: (s : n + m = l) →
    (seq1 : FinSeq n α) → (accum : Vector α m) →
       Vector α l:=
    match n with
    | zero => fun s => fun _ => fun seq2 =>
      by
        have ss : l = m := by
          rw [← s]
          apply Nat.zero_add
        rw [ss]
        exact seq2
    | k + 1 => fun s seq1 seq2 =>
      let ss : k + (m + 1)  = l :=
        by
          rw [← s]
          rw [(Nat.add_comm m 1)]
          rw [(Nat.add_assoc k 1 m)]
      seqVecAux ss (seq1.init) ((seq1.last) +: seq2)

def FinSeq.vec {α : Type}{n: Nat} : FinSeq n α  →  Vector α n :=
    fun seq => seqVecAux (Nat.add_zero n) seq Vector.nil

def Vector.ofFn' {α : Type}{n: Nat} : ((k : Nat) → k < n → α) → Vector α n :=
    fun f => seqVecAux (Nat.add_zero n) f Vector.nil

theorem prevsum{n m l: Nat}: n + 1 + m = l + 1 → n + m = l :=
  by
    intro hyp
    rw [Nat.add_assoc] at hyp
    rw [Nat.add_comm 1 m] at hyp
    rw [← Nat.add_assoc] at hyp
    have sc : succ (n + m) = succ l := hyp
    injection sc


theorem seq_vec_cons_aux {α: Type}{n m l: Nat}(s : (n + 1) + m = l + 1) (seq1 : FinSeq (n + 1) α)
        (accum : Vector α m) : seqVecAux s seq1 accum =
                (seq1.head) +: (seqVecAux (prevsum s) (seq1.tail)  accum) :=
            match n, l, s, seq1 with
            |  zero, l, s'', seq1  =>
              by
              have eql : m = l := by
                rw [←  prevsum s'']
                rw [Nat.zero_add]
              match m, l, eql, s'', accum with
              | m', .(m'), rfl, s', accum =>
                rfl
            | succ n', l, s'', seq1  =>
              by
              let ss : (n' + 1) + (m + 1)  = l + 1 :=
                by
                  rw [← s'']
                  rw [(Nat.add_comm m 1)]
                  rw [(Nat.add_assoc (n' + 1) 1 m)]
              have resolve :
                seqVecAux s'' seq1 accum =
                  seqVecAux ss (seq1.init) ((seq1.last) +: accum) := by rfl
              rw [resolve]
              let base := seq_vec_cons_aux ss (seq1.init) (seq1.last+:accum)
              rw [base]
              rfl


theorem seq_vec_cons_eq {α: Type}{n : Nat} (seq : FinSeq (n + 1) α) :
          Vector.ofFn' seq  = (seq.head) +: (seq.tail.vec) :=
                  seq_vec_cons_aux _ seq Vector.nil

theorem Vector.ext'{α: Type}{n : Nat}{v1 v2 : Vector α n}:
    v1.get' = v2.get' → v1 = v2 := by
    intro h
    apply Vector.ext
    intro ⟨i, iw⟩
    show get' v1 i iw = get' v2 i iw
    let lem := congrFun h i
    let lem' := (congrFun lem iw)
    exact lem'

theorem Vector.of_Fn'_get'{α : Type}{n : Nat}: (seq: FinSeq n α) →
  (Vector.ofFn' seq).get' = seq :=
  match n with
  | zero => by
    intro seq
    apply funext
    intro k
    apply funext
    intro kw
    exact nomatch kw
  | succ m => by
    intro seq
    apply funext
    intro k
    cases k with
    | zero =>
      apply funext
      intro kw
      have resolve : Vector.ofFn' seq = cons (seq.head) (Vector.ofFn' (seq.tail)) := by apply seq_vec_cons_eq
      rw [resolve]
      rfl
    | succ k' =>
      apply funext
      intro kw
      have tl :(Vector.ofFn' seq).get' (succ k') kw =
          (Vector.ofFn' (seq.tail)).get' k' (Nat.le_of_succ_le_succ kw) := by
              rw [(seq_vec_cons_eq seq)]
              rfl
      let base := Vector.of_Fn'_get' (seq.tail)
      rw [tl]
      rw [base]
      rfl

theorem Vector.of_Fn'_get{α : Type}{n : Nat}:
  (seq: FinSeq n α) → (k :Fin n) →
  (Vector.ofFn' seq).get k = seq k.val k.isLt := by
  intro seq ⟨k, kw⟩
  let lem := congrFun (Vector.of_Fn'_get' seq) k
  let lem' := (congrFun lem kw)
  exact lem'

theorem cons_commutes{α : Type}{n : Nat} (head : α) (tail : Vector α n) :
          (head +: tail).get' = head +| tail.get' := by
            apply funext
            intro k
            induction k with
            | zero =>
              apply funext
              intro kw
              rfl
            | succ k' =>
              apply funext
              intro kw
              rfl

theorem Vector.get'_of_Fn' {α : Type}{n : Nat} (f : (k : Nat) → k < n → α) (k : Nat) (kw : k < n) :
      (Vector.ofFn' f).get' k kw = f k kw :=
      by
      let lem := Vector.of_Fn'_get' f
      let lem' := congrFun lem k
      apply congrFun lem'

theorem get'_cons_succ {α : Type}{n : Nat} (x : α) (ys : Vector α n)
      (i: Nat) (iw : i < n) :
      (x +: ys).get' (i + 1) (Nat.succ_le_succ iw) = ys.get' i iw :=
        by
        rfl


theorem get'_map{α β : Type}{n : Nat}(vec: Vector α n) (f : α → β) (j : Nat) (jw : Nat.lt j n) :
          (Vector.map f vec).get' j jw = f (vec.get' j jw) := by
          rw [get']
          simp [Vector.get_map]
          rfl
