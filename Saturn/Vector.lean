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

def Vector.count {α : Type}{n : Nat}(v: Vector α n)(pred: α → Bool) : Nat := match v with
  | ⟨l, _⟩ => l.filterTR pred |>.length

def Vector.ofFn' {α : Type}{n: Nat} : ((k : Nat) → k < n → α) → Vector α n :=
    fun f => Vector.ofFn (fun ⟨k, w⟩ => f k w)

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
  (Vector.ofFn' seq).get' = seq := by
  intro seq
  apply funext
  intro k
  apply funext
  intro kw
  simp [Vector.get', Vector.ofFn']

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
