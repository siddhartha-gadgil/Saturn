import Saturn.Skip
import Saturn.Core
open Nat

 /- Operations and relations on the types `FinSeq α` of finite sequences, 
    with proofs of correctness. Specifically, we implement:
    * elementary operations
    * concatenation of sequences
      - including a proof that the concatenation function is as required.
    * deletion and insertion of elements
      - we define deletion (properties are easy to prove)
      - we define insertion, and prove that the sequence after insertion has correct values.
      - we prove the relation between deletion and insertion.
    * searching for elements
      - we implement functions to search for elements equal to given ones 
          or satisfying a predicate.
      - these functions return an index and a proof of correctness.
      - another function either finds an element with proof or shows it is not in the sequence
    * decidable equality of sequences
      - if `α` is a type with decidable equality, we implement decidable equality of `FinSeq α`.
 -/

-- Part 1:  elementary operations on `FinSeq`

namespace FinSeq
def cons {α : Type}{n: Nat}(head : α)(tail : FinSeq n α) : FinSeq (n + 1) α 
  | zero, _  => head
  | j + 1, w => tail j (le_of_succ_le_succ w)

def empty {α: Type} : FinSeq zero α := 
  fun j jw => nomatch jw

infixr:66 "+|" => cons

def tail {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α 
  | k, w => seq (k + 1) (succ_lt_succ w)

def head{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α := seq zero (zero_lt_succ _)

def init {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α 
 | k, w => seq k (Nat.le_step w)

def last{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq n (Nat.le_refl _)

def list{α : Type}{n : Nat}: FinSeq n α → List α :=
  match n with
  | zero => fun _ => []
  | l + 1 => fun s => (s.head) :: (list (s.tail))
end FinSeq


theorem witness_independent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) →  (i = j) → seq i iw = seq j jw 
    | i, j, _, _, eqn => 
    match j, eqn with 
    | .(i), rfl => rfl

-- Part 2: concatenation
def concatSeqAux {α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) →  
       FinSeq l α := 
    match n with
    | zero => fun s => fun _ => fun seq2 => by
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
      concatSeqAux ss (seq1.init) ((seq1.last) +| seq2)

def concatSeq {α: Type}{n m: Nat}(seq1 : FinSeq n α)(seq2 : FinSeq m α): 
  FinSeq (n + m) α := concatSeqAux rfl seq1 seq2

theorem concat_aux_eqs{α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) → (k: Nat) → 
      ((kw : k < n) → (w : k < l) → concatSeqAux s seq1 seq2 k w = seq1 k kw) ∧ 
      ((kw : k < m) → (w : (n + k) < l) → concatSeqAux s seq1 seq2 (n + k) w = seq2 k kw) := by
        match n with
        | zero => 

            intro s seq1 seq2 k
            have ss : l = m := by 
              rw [← s]
              apply Nat.zero_add
            have sf : FinSeq l α = FinSeq m α := by
              rw [ss]
            apply And.intro
            focus
              intro kw
              exact nomatch kw
            match l, m, ss, sf, seq2 with
                | d, .(d), rfl, rfl, seq => 
                    intro kw w
                    apply witness_independent
                    apply Nat.zero_add
        | p + 1 => 
          intro s seq1 seq2 k
          let ss : p + (m + 1)  = l := 
            by
              rw [← s]
              rw [(Nat.add_comm m 1)]
              rw [(Nat.add_assoc p 1 m)]
              done
          let resolve : concatSeqAux s seq1 seq2=
              concatSeqAux ss (seq1.init) ((seq1.last) +| seq2) := rfl
          rw [resolve]
          let hyp := concat_aux_eqs ss (seq1.init) ((seq1.last) +| seq2)
          let hyp1 := (hyp k).left
          apply And.intro
          focus
              intro kw w  
              match Nat.eq_or_lt_of_le kw with
              | Or.inr kww => exact hyp1 (le_of_succ_le_succ kww) w
              | Or.inl eql =>
                  match k, eql, kw, w with
                  | .(p), rfl, pw, w =>
                    let ww : p + zero < l := by
                      rw [(Nat.add_zero p)]
                      assumption 
                    let hyp2 := (hyp zero).right (Nat.zero_lt_succ _) ww
                    let lem2 : concatSeqAux ss (seq1.init) (seq1.last+|seq2) (p + zero) ww =
                          concatSeqAux ss (seq1.init) (seq1.last+|seq2) p w := 
                          match (p + zero), Nat.add_zero p, ww with
                          | .(p), rfl, ww => rfl                    
                    rw [← lem2]
                    rw [hyp2]
                    rfl
          let ass := Nat.add_assoc p 1 k
          let comm := Nat.add_comm 1 k
          intro kw w 
          match p + 1 + k, ass, w with
          | .(p + (1 + k)), rfl, ww => 
            let hypw := (hyp (1 + k)).right
            let kww : 1 + k < m + 1 := by
              rw [comm]
              apply Nat.succ_lt_succ
              assumption
            let resol := hypw kww ww
            rw [resol]
            match 1 + k, comm, kww with 
            | .(k + 1), rfl, kwww => rfl

infix:65 "++|" => concatSeq

theorem concat_empty_seq_id{α: Type}{n: Nat}: (seq : FinSeq n α) → seq ++| (FinSeq.empty) = seq := 
          by
            intro seq
            apply funext
            intro k
            apply funext
            intro kw            
            apply (concat_aux_eqs rfl seq FinSeq.empty k).left 
            
-- Part 3 : insertion and deletion

def FinSeq.delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α 
  | j, w => seq (skip k j) (skip_le_succ w)

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
              (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw := by
                  intro i iw hyp
                  rw [c] at hyp
                  exact False.elim $ skip_no_fixedpoints k i hyp
            let  checkFocus : j = k → result = value := fun  _  => rfl
            ⟨result, checkImage, checkFocus⟩
          else  
            let ii := skipInverse k j c 
            let eqn := skip_inverse_eq k j c  
            let bound : ii < n  := skip_preimage_lt kw jw eqn
            let result := seq ii bound
            let checkImage : 
              (i : Nat) → (iw : i < n) → (skip  k i = j) → seq ii bound = seq i iw := by
                  intro i1 iw1 hyp 
                  apply witness_independent
                  apply (skip_injective k)
                  rw [hyp]
                  rw [← eqn]
            let  checkFocus : j = k → result = value := by
                intro  hyp  
                rw [← eqn] at hyp
                exact False.elim $ skip_no_fixedpoints k ii hyp
            ⟨result, checkImage, checkFocus⟩

def FinSeq.insert{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (FinSeq n   α) →  (FinSeq (Nat.succ n)  α) 
  | n, k, lt, seq, j, w => (provedInsert n value seq k lt j w).result

open FinSeq

theorem insert_at_focus{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) →  insert value n k lt seq k lt = value 
  | n, k, lt, seq =>   (provedInsert n value seq k lt k lt).checkFocus rfl

theorem insert_at_image(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) → (i : Nat) → (iw : i < n) → 
      insert value n k lt seq (skip k i) (skip_le_succ iw) = seq i iw 
     | n, k, lt, seq, i, iw => 
       (provedInsert n value seq k lt (skip k i) (skip_le_succ iw)).checkImage i iw rfl 

theorem insert_delete_id{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α) :
  insert (seq k kw) n k kw (delete k kw seq) = seq := 
    funext $ fun j => funext $ fun jw => 
        if c : j = k then
          by
          match j, jw, c with
          | .(k), .(kw), rfl => apply insert_at_focus
        else 
          by 
          let i := skipInverse k j c 
          let eqn : skip k i = j  := skip_inverse_eq k j c
          let iw : i < n := skip_preimage_lt kw jw eqn
          let lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw
            = insert (seq k kw) n k kw (delete k kw seq) (skip k i) (skip_le_succ iw) := 
              by 
                apply witness_independent
                rw [← eqn]
          let lem2 : insert (seq k kw) n k kw (delete k kw seq) (skip k i) (_ : skip k i < n + 1) = 
                        delete k kw seq i iw := by apply insert_at_image 
          let resolve : delete k kw seq i iw = seq (skip k i) (skip_le_succ iw) := by rfl
          rw [lem1]
          rw [lem2]
          rw [resolve]
          apply witness_independent
          exact eqn    

-- Part 4 : searching

structure ElemInSeq{α: Type}{n : Nat} (seq : FinSeq n α) (elem : α) where
  index: Nat
  bound : index < n
  equation : seq index bound = elem

inductive ExistsElem{α: Type}{n : Nat} (seq : FinSeq n α) (elem : α) where
  | exsts : (index: Nat) →  (bound : index < n) → 
            (equation : seq index bound = elem) → ExistsElem seq elem
  | notExst : ((index: Nat) →  (bound : index < n) → 
                 Not (seq index bound = elem)) → ExistsElem seq elem 

structure ElemSeqPred{α: Type}{n : Nat} (seq : FinSeq n α) (pred : α → Prop) where
  index: Nat
  bound : index < n
  equation : pred (seq index bound)

def elemPredAt{α: Type}{n : Nat}(pred : α → Prop)[DecidablePred pred]
  (seq : FinSeq n α)(k: Nat): Option (ElemSeqPred seq pred) := 
    if lt : k <n then 
      if eqn : pred (seq k lt) 
        then some ⟨k, lt, eqn⟩
        else none 
    else none

def findAux?{α: Type}{n : Nat}(pred : α → Prop)(cursor: Nat)
      (cursorBound : cursor < n)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) := 
    fun seq =>
      if eqn : pred (seq cursor cursorBound) 
        then some ⟨cursor, cursorBound, eqn⟩
        else 
          match cursor, cursorBound with
          | zero, _ => none
          | l + 1, cb => 
            let bd : l + 1 ≤  n := by
                apply Nat.le_of_lt
                exact cb
            findAux? pred l bd seq    

def find?{α: Type}{n : Nat}(pred : α → Prop)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) :=
  match n with
  | zero => fun _ =>  none
  | m + 1 => fun seq => findAux? pred m (Nat.le_refl _) seq

def findFilteredAux?{α: Type}{n : Nat}(filter : FinSeq n Bool)(pred : α → Prop)(cursor: Nat)
      (cursorBound : cursor < n)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) := 
    fun seq =>
    if filter cursor cursorBound then
      if eqn : pred (seq cursor cursorBound) 
        then some ⟨cursor, cursorBound, eqn⟩
        else 
          match cursor, cursorBound with
          | zero, _ => none
          | l + 1, cb => 
            let bd : l + 1 ≤  n := by
                apply Nat.le_of_lt
                exact cb
            findFilteredAux? filter pred l bd seq    
    else
      match cursor, cursorBound with
          | zero, _ => none
          | l + 1, cb => 
            let bd : l + 1 ≤  n := by
                apply Nat.le_of_lt
                exact cb
            findFilteredAux? filter pred l bd seq

def findFiltered?{α: Type}{n : Nat}(filter : FinSeq n Bool)(pred : α → Prop)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) :=
  match n, filter with
  | zero, _ => fun _ =>  none
  | m + 1, filter => fun seq => findFilteredAux? filter pred m (Nat.le_refl _) seq


def findElemAux?{α: Type}{n : Nat}(cursor: Nat)
      (cursorBound : cursor < n)[DecidableEq α]:
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) := 
    fun seq  elem =>
      if eqn : seq cursor cursorBound = elem 
        then some ⟨cursor, cursorBound, eqn⟩
        else 
          match cursor, cursorBound with
          | zero, _ => none
          | l + 1, cb => 
            let bd : l + 1 ≤  n := by
                apply Nat.le_of_lt
                exact cb
            findElemAux? l bd seq elem  

def findElem?{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) :=
   match n with
  | zero => fun _ _ =>  none
  | m + 1 => fun seq elem => findElemAux?  m (Nat.le_refl _) seq elem

def elemNotBeyond{α: Type}{n : Nat}(seq : FinSeq n α)(elem : α)(m: Nat): Prop :=
      ∀ k: Nat, ∀ kw : k <n, ∀ mw : m ≤ k, Not (seq k kw = elem)

def elem_not_beyond_zero_implies_not_exsts{α: Type}{n : Nat}(seq : FinSeq n α)(elem: α):
    elemNotBeyond seq elem zero → ExistsElem seq elem := 
    fun hyp => ExistsElem.notExst $ 
    by
      intro k
      intro kw
      exact hyp k kw  (Nat.zero_le k)
    
theorem elem_not_beyond_vacuously{α: Type}{n : Nat}(seq : FinSeq n α)(elem: α)(m: Nat):
    (n ≤ m) → elemNotBeyond seq elem m  := by
      intro hyp k kw ineq
      let inq := Nat.le_trans hyp ineq
      let inq2 := Nat.lt_of_lt_of_le kw inq
      exact (False.elim (Nat.lt_irrefl k inq2))

def searchElemRec{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  
  (m: Nat) → elemNotBeyond seq elem m →   ExistsElem seq elem := 
  fun seq elem m =>
  match m with
  | zero => fun hyp => elem_not_beyond_zero_implies_not_exsts seq elem hyp
  | l + 1 => 
    fun hyp =>
    if lw : l < n then 
      if eqn : seq l lw = elem 
        then ExistsElem.exsts l lw eqn
        else 
          let accum : elemNotBeyond seq elem l := 
            by
                    intro k kw ineq
                    cases Nat.eq_or_lt_of_le ineq with
                    | inl eql => 
                      let lem1 : seq l lw = seq k kw := by
                        apply witness_independent
                        exact eql
                      rw [← lem1]
                      exact eqn
                    | inr lt => exact hyp k kw lt
        searchElemRec seq elem l accum
    else 
    let overshoot : n ≤ l := by
            cases Nat.lt_or_ge l n with
            | inl l1 => exact absurd l1 lw
            | inr l2 => exact l2
          let accum: elemNotBeyond seq elem l := 
            elem_not_beyond_vacuously seq elem l overshoot
          searchElemRec seq elem l accum

def searchElem{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  ExistsElem seq elem :=
  fun seq elem => searchElemRec seq elem n 
            (elem_not_beyond_vacuously seq elem n (Nat.le_refl _))

def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (FinSeq n  α) → Option β :=
    match n with
    | zero => fun _ => none
    | m + 1 => 
      fun seq => 
        match (f (seq zero (zero_lt_succ m))) with
        | none => 
          findSome? f (fun t : Nat => fun w : t < m => seq (t + 1) 
                (Nat.succ_lt_succ w) )
        | some b => some b

-- Part 5 : equality

def equalBeyond{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat): Prop :=
  ∀ k: Nat, ∀ kw : k <n, ∀ mw : m ≤ k, seq1 k kw = seq2 k kw

theorem equal_beyond_zero_implies_equals{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α):
    equalBeyond seq1 seq2 zero → seq1 = seq2 := by
      intro hyp
      apply funext
      intro k
      apply funext
      intro kw
      exact hyp k kw  (Nat.zero_le k)

theorem equal_beyond_vacuously{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat):
    (n ≤ m) → equalBeyond seq1 seq2 m := by
      intro hyp k kw ineq
      let inq := Nat.le_trans hyp ineq
      let inq2 := Nat.lt_of_lt_of_le kw inq
      exact (False.elim (Nat.lt_irrefl k inq2))

def deqSeqRec{α: Type}[DecidableEq α]{n : Nat}(seq1 seq2 : FinSeq n α): (m: Nat) → 
      Decidable (equalBeyond seq1 seq2 m) → 
      Decidable (seq1 = seq2) :=
      fun m dec => 
      match m, dec with
      | m, isFalse contra => 
        isFalse (
          by
            intro hyp
            have restr : equalBeyond seq1 seq2 m := by
              intro k kw _
              rw [hyp]
            exact contra restr)
      | zero, isTrue pf => 
        isTrue (equal_beyond_zero_implies_equals seq1 seq2 pf)
      | l + 1, isTrue eql_bynd  => 
        if lw : l < n then
          match decEq (seq1 l lw) (seq2 l lw) with
          | isTrue eql_at_l => 
              let accum: Decidable (equalBeyond seq1 seq2 l) := 
                isTrue (
                  by
                    intro k kw ineq
                    cases Nat.eq_or_lt_of_le ineq with
                    | inl eql =>
                      let lem1 : seq1 l lw = seq1 k kw := by
                        apply witness_independent
                        exact eql
                      let lem2 : seq2 l lw = seq2 k kw := by
                        apply witness_independent
                        exact eql
                      rw [← lem1]
                      rw [← lem2]
                      exact eql_at_l
                    | inr l2 => 
                      exact eql_bynd k kw l2                      
                )
              deqSeqRec seq1 seq2 l accum
          | isFalse contra => isFalse (fun hyp =>
                        contra ( 
                          by
                            rw [hyp]
                            done
                          )                           
                          )
        else
          let overshoot : n ≤ l := by
            cases Nat.lt_or_ge l n with
            | inl l1 => exact absurd l1 lw
            | inr l2 => exact l2
          let accum: Decidable (equalBeyond seq1 seq2 l) := 
            isTrue (equal_beyond_vacuously seq1 seq2 l overshoot)
          deqSeqRec seq1 seq2 l accum
      

def deqSeq {α : Type}[DecidableEq α] (n: Nat) : (c1 : FinSeq n  α) → 
                              (c2: FinSeq n  α) → Decidable (c1 = c2) := 
              fun seq1 seq2 => 
                deqSeqRec seq1 seq2 n (isTrue (equal_beyond_vacuously seq1 seq2 n (Nat.le_refl n)))

instance {n: Nat}[DecidableEq α] : DecidableEq (FinSeq n  α) := fun c1 c2 => deqSeq _ c1 c2
