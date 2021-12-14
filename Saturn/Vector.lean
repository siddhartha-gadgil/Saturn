import Saturn.FinSeq
import Saturn.Core
open Nat 
/-
Functions and theorems for working with vectors. Most of these are conversions from
finite sequences to vectors,  its consistency with the conversion from vectors to
finite sequences defined in `Core`, and the consistency of various operations with conversions
between finite sequences and vectors in both directions.
-/
open Vector

def countAux {α : Type}{n : Nat}(v: Vector α n)(pred: α → Bool)(accum : Nat) : Nat :=
  match n, v, accum with
  | .(zero), nil, accum => accum
  | m + 1, cons head tail, accum => 
      if (pred head) then countAux tail pred (accum + 1) else countAux tail pred accum

def Vector.count {α : Type}{n : Nat}(v: Vector α n)(pred: α → Bool) : Nat :=
    countAux v pred zero

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

theorem prevsum{n m l: Nat}: n + 1 + m = l + 1 → n + m = l := 
  by
    intro hyp
    rw [Nat.add_assoc] at hyp
    rw [Nat.add_comm 1 m] at hyp
    rw [← Nat.add_assoc] at hyp    
    have sc : succ (n + m) = succ l := hyp
    injection sc
    assumption

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
          seq.vec  = (seq.head) +: (seq.tail.vec) := 
                  seq_vec_cons_aux _ seq Vector.nil

theorem coords_eq_implies_vec_eq{α: Type}{n : Nat}{v1 v2 : Vector α n}: 
    v1.coords = v2.coords → v1 = v2 := 
    match n, v1, v2 with
    | zero, nil, nil => fun _ => rfl
    | m + 1, cons head1 tail1, cons head2 tail2 =>
      by
        intro hyp
        have h1 : head1 = (cons head1 tail1).coords zero (Nat.zero_lt_succ m) := by rfl
        have h2 : head2 = (cons head2 tail2).coords zero (Nat.zero_lt_succ m) := by rfl
        have hypHead : head1 = head2 :=
          by 
            rw [h1, h2, hyp]            
        rw [hypHead]
        apply congrArg
        let base := @coords_eq_implies_vec_eq _ _ tail1 tail2
        apply base
        apply funext
        intro k
        apply funext
        intro kw
        have t1 : tail1.coords k kw = 
          (cons head1 tail1).coords (k + 1) (Nat.succ_lt_succ kw) := by rfl
        have t2 : tail2.coords k kw = 
          (cons head2 tail2).coords (k + 1) (Nat.succ_lt_succ kw) := by rfl
        rw [t1, t2, hyp]

theorem seq_to_vec_coords{α : Type}{n : Nat}: (seq: FinSeq n α) →   seq.vec.coords = seq := 
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
      have resolve : seq.vec = cons (seq.head) (FinSeq.vec (seq.tail)) := by apply seq_vec_cons_eq 
      rw [resolve]
      rfl
    | succ k' => 
      apply funext
      intro kw
      have tl :(FinSeq.vec seq).coords (succ k') kw = 
          (FinSeq.vec (seq.tail)).coords k' (Nat.le_of_succ_le_succ kw) := by
              rw [(seq_vec_cons_eq seq)] 
              rfl 
      let base := seq_to_vec_coords (seq.tail)
      rw [tl]
      rw [base]
      rfl

theorem cons_commutes{α : Type}{n : Nat} (head : α) (tail : Vector α n) :
          (head +: tail).coords = head +| tail.coords := by
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

theorem tail_commutes{α : Type}{n : Nat} (x : α) (ys : Vector α n) :
      (x +: ys).coords.tail = ys.coords := 
        by
        apply funext
        intro kw
        rfl 

def Vector.map {α β : Type}{n: Nat}(vec: Vector α n) (f : α → β) : Vector β n :=
    FinSeq.vec (fun j jw => f (vec.coords j jw))

theorem map_coords_commute{α β : Type}{n : Nat}(vec: Vector α n) (f : α → β) (j : Nat) (jw : Nat.lt j n) :
          (Vector.map vec f).coords j jw = f (vec.coords j jw) := by
          have resolve: (map vec f).coords j jw = 
                (FinSeq.vec (fun j jw => f (vec.coords j jw)) ).coords j jw := rfl
          rw [resolve]
          rw [seq_to_vec_coords]
