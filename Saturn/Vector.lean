import Saturn.FinSeq
open Nat 


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

theorem prevsum{n m l: Nat}: n + 1 + m = l + 1 → n + m = l := 
  by
    rw [Nat.add_assoc n 1 m]
    rw [Nat.add_comm 1  m]
    rw [← (Nat.add_assoc n m 1)]
    intro hyp
    have as1 : (n + m) + 1 = succ (n + m) := by rfl
    have as2 : l + 1 = succ l := by rfl
    have sc : succ (n + m) = succ l := by
      rw [← as1]
      rw [← as2]
      exact hyp
    injection sc
    assumption
    done

theorem seq_vec_cons_aux {α: Type}{n m l: Nat}(s : (n + 1) + m = l + 1) (seq1 : FinSeq (n + 1) α) 
        (accum : Vector α m) : seqVecAux s seq1 accum =
                (seq1.head) +: (
                  seqVecAux 
                  (prevsum s)
                  (seq1.tail)  accum) := 
                    match n, l, s, seq1 with
                    |  zero, l, s'', seq1  => 
                      by
                      have eql : m = l := by
                        rw [←  prevsum s'']
                        rw [Nat.zero_add]
                        done
                      match m, l, eql, s'', accum with
                      | m', .(m'), rfl, s', accum =>
                        have ss : zero + (m' +1) = (m' +1) :=  by
                          rw [Nat.zero_add]
                        have resolve :
                          seqVecAux s' seq1 accum =
                            seqVecAux ss (seq1.init) ((seq1.last) +: accum) := by rfl
                        rw [resolve]
                        have res2 : 
                          seqVecAux ss (seq1.init) (seq1.last+:accum) =
                            (seq1.last+:accum) := by rfl
                        rw [res2]
                        have res3 : seqVecAux (prevsum s') (seq1.tail) accum =  accum
                            := by rfl
                        rw [res3]
                        have hh : seq1.head = seq1 0 (zero_lt_succ _) := by rfl
                        have hl: seq1.last = seq1 0 (zero_lt_succ _) := by rfl
                        rw [hh, hl]
                        done 
                    | succ n', l, s'', seq1  =>
                      by 
                      let ss : (n' + 1) + (m + 1)  = l + 1 := 
                        by
                          rw [← s'']
                          rw [(Nat.add_comm m 1)]
                          rw [(Nat.add_assoc (n' + 1) 1 m)]
                          done
                      have resolve :
                        seqVecAux s'' seq1 accum =
                          seqVecAux ss (seq1.init) ((seq1.last) +: accum) := by rfl
                      rw [resolve]
                      let v := seq1.init
                      let base := seq_vec_cons_aux ss (seq1.init) (seq1.last+:accum)
                      rw [base]
                      have he : FinSeq.head (seq1.init)  = seq1.head := by rfl
                      rw [he]
                      apply congrArg (cons (seq1.head))
                      have sss : n' + (m + 1) = l := by
                        rw [← (prevsum ss)]
                        done
                      have resolve2 :
                        seqVecAux (prevsum s'') (seq1.tail) accum =
                          seqVecAux sss (seq1.tail.init) 
                            (seq1.tail.last  +: accum) := by rfl
                      rw [resolve2]
                      have intl:  seq1.tail.init = FinSeq.tail (seq1.init) := by rfl
                      rw [intl]
                      have lst : seq1.tail.last = seq1.last := by rfl
                      rw [lst]
                      done

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
        have h1 : head1 = Vector.coords (cons head1 tail1) zero (Nat.zero_lt_succ m) := by rfl
        have h2 : head2 = Vector.coords (cons head2 tail2) zero (Nat.zero_lt_succ m) := by rfl
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
        have t1 : Vector.coords tail1 k kw = 
          Vector.coords (cons head1 tail1) (k + 1) (Nat.succ_lt_succ kw) := by rfl
        have t2 : Vector.coords tail2 k kw = 
          Vector.coords (cons head2 tail2) (k + 1) (Nat.succ_lt_succ kw) := by rfl
        rw [t1, t2, hyp]
        done

theorem seq_to_vec_coords{α : Type}{n : Nat}: (seq: FinSeq n α) →   seq.vec.coords = seq := 
  match n with
  | zero => by
    intro seq
    apply funext
    intro k
    apply funext
    intro kw
    exact nomatch kw
    done
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
      have res2 : Vector.coords (seq.head+:FinSeq.vec (seq.tail)) zero kw = seq.head := by rfl
      rw [res2]
      rfl
      done
    | succ k' => 
      apply funext
      intro kw
      have tl :Vector.coords (FinSeq.vec seq) (succ k') kw = 
          Vector.coords (FinSeq.vec (seq.tail)) k' (Nat.le_of_succ_le_succ kw) := by
              have dfn : FinSeq.vec seq = seq.vec := by rfl
              rw [dfn]
              rw [(seq_vec_cons_eq seq)] 
              rfl 
      let base := seq_to_vec_coords (seq.tail)
      rw [tl]
      rw [base]
      rfl
      done

theorem cons_commutes{α : Type}{n : Nat} (head : α) (tail : Vector α n) :
          Vector.coords (head +: tail) = head +| (Vector.coords tail) := by
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
      FinSeq.tail (Vector.coords (x +: ys)) = ys.coords := 
        by
        apply funext
        intro kw
        rfl 
        done

def Vector.map {α β : Type}{n: Nat}(vec: Vector α n) (f : α → β) : Vector β n :=
    FinSeq.vec (fun j jw => f (vec.coords j jw))

theorem map_coords_commute{α β : Type}{n : Nat}(vec: Vector α n) (f : α → β) (j : Nat) (jw : Nat.lt j n) :
          Vector.coords (Vector.map vec f) j jw = f (vec.coords j jw) := by
          have resolve: 
            Vector.coords (map vec f) j jw = 
                Vector.coords (FinSeq.vec (fun j jw => f (vec.coords j jw))) j jw := rfl
          rw [resolve]
          rw [seq_to_vec_coords]
          done
