import Saturn.Skip
open Nat


class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 

 /- `FinSeq` is an implementation of finite sequences. We define insertion and deletion 
 and prove properties of these operations. We also show equality is decidable for `FinSeq α` 
 if it is for `α`. We also search within finite sequences. -/
def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

def FinSeq.cons {α : Type}{n: Nat}(head : α)(tail : FinSeq n α) : FinSeq (n + 1) α :=
  fun k =>
  match k with
  | zero => fun _ => head
  | j + 1 => 
    fun w =>
      tail j (le_of_succ_le_succ w)

def FinSeq.empty {α: Type} : FinSeq zero α := 
  fun j jw => nomatch jw

infixr:66 "+|" => FinSeq.cons

def FinSeq.tail {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq (k + 1) (succ_lt_succ w)

def FinSeq.head{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq zero (zero_lt_succ _)


def init {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq k (Nat.le_step w)

def last{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq n (Nat.le_refl _)

def concatSeqAux {α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) →  
       FinSeq l α := 
    match n with
    | zero => fun s => fun _ => fun seq2 => by
        have ss : l = m := by
          rw [← s]
          apply Nat.zero_add
          done
        have sf : FinSeq l α = FinSeq m α := by
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
      concatSeqAux ss (init seq1) ((last seq1) +| seq2)

def concatSeq {α: Type}{n m: Nat}(seq1 : FinSeq n α)(seq2 : FinSeq m α): 
  FinSeq (n + m) α := 
    concatSeqAux rfl seq1 seq2

theorem witness_independent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) → 
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          match j, eqn, jw with 
          | .(i), rfl, ijw =>
               rfl

theorem concat_aux_eqs{α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) → (k: Nat) → 
      ((kw : k < n) → (w : k < l) → concatSeqAux s seq1 seq2 k w = seq1 k kw) ∧ 
      ((kw : k < m) → (w : (n + k) < l) → concatSeqAux s seq1 seq2 (n + k) w = seq2 k kw) := 
        match n with
        | zero => fun s => fun seq1 => fun seq2 =>
          by
            have ss : l = m := by 
              rw [← s]
              apply Nat.zero_add
              done
            have sf : FinSeq l α = FinSeq m α := by
              rw [ss]
              done
            have resolve : concatSeqAux s seq1 seq2 = Eq.mpr sf seq2 := rfl
            rw [resolve]
            let lem1 : ∀ (k : Nat),
                (∀ (kw : k < zero) (w : k < l), Eq.mpr sf seq2 k w = seq1 k kw) := 
                  fun k kw => nomatch kw
            let lem2 :  ∀ (k : Nat),
              ∀ (kw : k < m) (w : zero + k < l), Eq.mpr sf seq2 (zero + k) w = 
              seq2 k kw := 
                match l, m, ss, sf, seq2 with
                | d, .(d), rfl, rfl, seq => 
                  by 
                    intro k
                    intro kw
                    intro w
                    let zp: zero + k = k :=
                        Nat.zero_add k
                    let lm : Eq.mpr rfl seq (zero + k) w = seq (zero + k) w := rfl 
                    rw [lm]
                    apply witness_independent
                    exact zp
                    done
            exact (fun k => And.intro (lem1 k) (lem2 k))
            done
        | p + 1 => 
          fun s seq1 seq2 => 
          let ss : p + (m + 1)  = l := 
            by
              rw [← s]
              rw [(Nat.add_comm m 1)]
              rw [(Nat.add_assoc p 1 m)]
              done
          let resolve : concatSeqAux s seq1 seq2=
              concatSeqAux ss (init seq1) ((last seq1) +| seq2) := rfl
          let hyp := concat_aux_eqs ss (init seq1) ((last seq1) +| seq2)
          by
            rw [resolve]
            intro k
            let hyp1 := (hyp k).left
            let lem1 : (∀ (kw : k < p + 1) (w : k < l), 
                concatSeqAux ss (init seq1) (last seq1+|seq2) k w = seq1 k kw) := 
                fun kw w => 
                  if kww : k < p then 
                    hyp1 kww w 
                  else 
                    let eql: k = p := 
                      match Nat.eq_or_lt_of_le kw with
                      | Or.inl h => by 
                                      injection h
                                      assumption
                      | Or.inr h =>
                          let contra : k < p := by
                              apply Nat.le_of_succ_le_succ
                              exact h

                          absurd contra kww
                    match k, eql, kw, w with
                    | .(p), rfl, pw, w =>
                      let ww : p + zero < l := by
                        rw [(Nat.add_zero p)]
                        assumption 
                      let hyp2 := (hyp zero).right (Nat.zero_lt_succ _) ww
                      let lem2 : concatSeqAux ss (init seq1) (last seq1+|seq2) (p + zero) ww =
                            concatSeqAux ss (init seq1) (last seq1+|seq2) p w := 
                            match (p + zero), Nat.add_zero p, ww with
                            | .(p), rfl, ww => rfl
                      by
                        rw [← lem2]
                        rw [hyp2]
                        rfl
                        done
            let ass := Nat.add_assoc p 1 k
            let comm := Nat.add_comm 1 k
            let lem2 : ∀ (kw : k < m) (w : p + 1 + k < l), 
                concatSeqAux ss (init seq1) (last seq1+|seq2) (p + 1 + k) w = 
                    seq2 k kw := fun kw w =>
                    match p + 1 + k, ass, w with
                    | .(p + (1 + k)), rfl, ww => 
                      by
                      let hypw := (hyp (1 + k)).right
                      let kww : 1 + k < m + 1 := by
                        rw [comm]
                        apply Nat.succ_lt_succ
                        assumption
                        done 
                      let lm := hypw kww ww
                      rw [lm]
                      let lmc : FinSeq.cons (last seq1) seq2 (1 + k) kww = 
                                  FinSeq.cons (last seq1) seq2 (k + 1) 
                                  (succ_lt_succ kw) := 
                              match 1 + k, comm, kww with 
                              | .(k + 1), rfl, kwww => by rfl
                      rw [lmc]
                      rfl
                      done
            exact (And.intro lem1 lem2)
            done

infix:65 "++|" => concatSeq

theorem concat_empty_seq_id{α: Type}{n: Nat}: (seq : FinSeq n α) → seq ++| (FinSeq.empty) = seq := 
          by
            intro seq
            apply funext
            intro k
            apply funext
            intro kw
            let resolve : concatSeq seq FinSeq.empty =  
                  concatSeqAux rfl seq FinSeq.empty := rfl
            rw [resolve]
            have w : k < n + zero := by
              rw [(Nat.add_zero n)]
              assumption
              done
            let lem := (concat_aux_eqs rfl seq FinSeq.empty k).left kw w
            exact lem
            done

def FinSeq.list{α : Type}{n : Nat}: FinSeq n α → List α :=
  match n with
  | zero => fun _ => []
  | l + 1 => fun s => (s.head) :: (list (s.tail))


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

theorem insertAtFocus{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) →  
      insert value n k lt seq k lt = value :=
    fun n k lt seq  =>   
      (provedInsert n value seq k lt k lt).checkFocus rfl

theorem insertAtImage(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) → (i : Nat) → (iw : i < n) → 
      insert value n k lt seq (skip k i) (skip_le_succ iw) = seq i iw :=
      fun n k lt seq i iw => 
       (provedInsert n value seq k lt (skip k i) (skip_le_succ iw)).checkImage i iw rfl 

theorem insertDelete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α) :
  insert (seq k kw) n k kw (delete k kw seq) = seq := 
    let delSeq := delete k kw seq
    funext (
      fun j =>
        funext (
          fun jw => 
            if c : j = k then
              by
              have lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw =
                insert (seq k kw) n k kw (delete k kw seq) k kw :=
                by
                  apply witness_independent
                  apply c
                  done 
              rw [lem1]
              rw [(insertAtFocus (seq k kw) n k kw (delete k kw seq))]
              apply witness_independent
              rw [← c]
              done  
            else  
              let i := skipInverse k j c 
              let eqn := skip_inverse_eq k j c
              let iw : i < n := skip_preimage_lt kw jw eqn
              let lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw
                = insert (seq k kw) n k kw (delete k kw seq) (skip k i) (skip_le_succ iw) := 
                  by 
                    apply witness_independent
                    rw [← eqn]
                    done
              let lem2 := insertAtImage (seq k kw) n k kw (delete k kw seq) i iw
              let lem3 : delete k kw seq i iw = seq (skip k i) (skip_le_succ iw) := by rfl
              by
                rw [lem1]
                rw [lem2]
                rw [lem3]
                apply witness_independent
                exact eqn
                done
        )
    )

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
            let lem : l + 1 ≤  n := by
                apply (Nat.le_trans ·  cb)
                apply Nat.le_succ
                done
            findAux? pred l lem seq    

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
            let lem : l + 1 ≤  n := by
                apply (Nat.le_trans ·  cb)
                apply Nat.le_succ
                done
            findFilteredAux? filter pred l lem seq    
    else
      match cursor, cursorBound with
          | zero, _ => none
          | l + 1, cb => 
            let lem : l + 1 ≤  n := by
                apply (Nat.le_trans ·  cb)
                apply Nat.le_succ
                done
            findFilteredAux? filter pred l lem seq

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
            let lem : l + 1 ≤  n := by
                apply (Nat.le_trans ·  cb)
                apply Nat.le_succ
                done
            findElemAux? l lem seq elem  

def findElem?{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) :=
   match n with
  | zero => fun _ _ =>  none
  | m + 1 => fun seq elem => findElemAux?  m (Nat.le_refl _) seq elem

def searchElem{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  ExistsElem seq elem :=
    match n with
    | zero => fun seq  => fun elem => ExistsElem.notExst (fun j jw => nomatch jw)
    | m + 1 => 
      fun fn =>
        fun x =>
          if pf0 : fn zero (zero_lt_succ m) =  x then
            ExistsElem.exsts zero (zero_lt_succ m) pf0
          else
            match searchElem (fn.tail) x with
            | ExistsElem.exsts j jw eql => 
              let l1 : fn (j + 1) (succ_lt_succ jw) = (fn.tail) j jw := by rfl 
              let l2 : fn (j + 1) (succ_lt_succ jw) = x := by 
                    rw [l1]
                    exact eql
              ExistsElem.exsts (j + 1) (succ_lt_succ jw) l2              
            | ExistsElem.notExst tailPf => 
                  ExistsElem.notExst (
                    fun j =>
                    match j with
                    | zero => fun jw => pf0 
                    | i + 1 => fun iw => tailPf i (le_of_succ_le_succ iw)
                  )


def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (FinSeq n  α) → Option β :=
    match n with
    | zero => fun _ => none
    | m + 1 => 
      fun seq => 
        (f (seq zero (zero_lt_succ m))).orElse (
          findSome? f (fun t : Nat => fun w : t < m => seq (t + 1) 
                (Nat.succ_lt_succ w) )
        ) 

def equalBeyond{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat): Prop :=
  ∀ k: Nat, ∀ kw : k <n, ∀ mw : m ≤ k, seq1 k kw = seq2 k kw

theorem equalBeyondZero{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α):
    equalBeyond seq1 seq2 zero → seq1 = seq2 := by
      intro hyp
      apply funext
      intro k
      apply funext
      intro kw
      exact hyp k kw  (Nat.zero_le k)
      done


def equalBeyondVacuous{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat):
    (n ≤ m) → equalBeyond seq1 seq2 m := by
      intro hyp
      intro k
      intro kw
      intro ineq
      let inq := Nat.le_trans hyp ineq
      let inq2 := Nat.lt_of_lt_of_le kw inq
      exact (False.elim (Nat.lt_irrefl k inq2))
      done

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
              intro k
              intro kw
              intro _ 
              rw [hyp]
              done
            exact contra restr
            done)
      | zero, isTrue pf => 
        isTrue (equalBeyondZero seq1 seq2 pf)
      | l + 1, isTrue pf  => 
        if lw : l < n then
          match decEq (seq1 l lw) (seq2 l lw) with
          | isTrue pfHead => 
              let accum: Decidable (equalBeyond seq1 seq2 l) := 
                isTrue (
                  by
                    intro k 
                    intro kw
                    intro ineq
                    cases Nat.eq_or_lt_of_le ineq with
                    | inl eql =>
                      let lem0 := pfHead
                      let lem1 : seq1 l lw = seq1 k kw := by
                        apply witness_independent
                        exact eql
                        done
                      let lem2 : seq2 l lw = seq2 k kw := by
                        apply witness_independent
                        exact eql
                      rw [← lem1]
                      rw [← lem2]
                      exact lem0
                      done
                    | inr l2 => 
                      exact pf k kw l2 
                      done                      
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
            isTrue (equalBeyondVacuous seq1 seq2 l overshoot)
          deqSeqRec seq1 seq2 l accum
      

def deqSeq {α : Type}[DecidableEq α] (n: Nat) : (c1 : FinSeq n  α) → 
                              (c2: FinSeq n  α) → Decidable (c1 = c2) := 
              fun seq1 seq2 => 
                deqSeqRec seq1 seq2 n (isTrue (equalBeyondVacuous seq1 seq2 n (Nat.le_refl n)))

instance {n: Nat}[DecidableEq α] : DecidableEq (FinSeq n  α) := fun c1 c2 => deqSeq _ c1 c2

inductive Vector (α : Type) : Nat → Type where 
  | Nil : Vector α zero
  | Cons{n: Nat}(head: α) (tail: Vector  α n) : Vector α  (n + 1) 

infixr:66 "+:" => Vector.Cons

open Vector

def Vector.coords {α : Type}{n : Nat}(v: Vector α n) : FinSeq n α :=
  fun j jw =>
  match n, v, j, jw with
  | .(zero), Nil, k, lt => nomatch lt
  | m + 1, Cons head tail, zero, lt => head
  | m + 1, Cons head tail, j + 1, w =>  tail.coords j (Nat.le_of_succ_le_succ w)

def countAux {α : Type}{n : Nat}(v: Vector α n)(pred: α → Bool)(accum : Nat) : Nat :=
  match n, v, accum with
  | .(zero), Nil, accum => accum
  | m + 1, Cons head tail, accum => 
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
      seqVecAux ss (init seq1) ((last seq1) +: seq2)

def FinSeq.vec {α : Type}{n: Nat} : FinSeq n α  →  Vector α n := 
    fun seq => seqVecAux (Nat.add_zero n) seq Vector.Nil

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
                            seqVecAux ss (init seq1) ((last seq1) +: accum) := by rfl
                        rw [resolve]
                        have res2 : 
                          seqVecAux ss (init seq1) (last seq1+:accum) =
                            (last seq1+:accum) := by rfl
                        rw [res2]
                        have res3 : seqVecAux (prevsum s') (seq1.tail) accum =  accum
                            := by rfl
                        rw [res3]
                        have hh : seq1.head = seq1 0 (zero_lt_succ _) := by rfl
                        have hl: last seq1 = seq1 0 (zero_lt_succ _) := by rfl
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
                          seqVecAux ss (init seq1) ((last seq1) +: accum) := by rfl
                      rw [resolve]
                      let v := init seq1
                      let base := seq_vec_cons_aux ss (init seq1) (last seq1+:accum)
                      rw [base]
                      have he : FinSeq.head (init seq1)  = seq1.head := by rfl
                      rw [he]
                      apply congrArg (Cons (seq1.head))
                      have sss : n' + (m + 1) = l := by
                        rw [← (prevsum ss)]
                        done
                      have resolve2 :
                        seqVecAux (prevsum s'') (seq1.tail) accum =
                          seqVecAux sss (init (seq1.tail)) 
                            (last (seq1.tail ) +: accum) := by rfl
                      rw [resolve2]
                      have intl:  init (seq1.tail) = FinSeq.tail (init seq1) := by rfl
                      rw [intl]
                      have lst : last (seq1.tail) = last seq1 := by rfl
                      rw [lst]
                      done

theorem seq_vec_cons_eq {α: Type}{n : Nat} (seq : FinSeq (n + 1) α) : 
          seq.vec  = (seq.head) +: (seq.tail.vec) := 
                  seq_vec_cons_aux _ seq Vector.Nil

theorem coords_eq_implies_vec_eq{α: Type}{n : Nat}{v1 v2 : Vector α n}: 
    v1.coords = v2.coords → v1 = v2 := 
    match n, v1, v2 with
    | zero, Nil, Nil => fun _ => rfl
    | m + 1, Cons head1 tail1, Cons head2 tail2 =>
      by
        intro hyp
        have h1 : head1 = Vector.coords (Cons head1 tail1) zero (Nat.zero_lt_succ m) := by rfl
        have h2 : head2 = Vector.coords (Cons head2 tail2) zero (Nat.zero_lt_succ m) := by rfl
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
          Vector.coords (Cons head1 tail1) (k + 1) (Nat.succ_lt_succ kw) := by rfl
        have t2 : Vector.coords tail2 k kw = 
          Vector.coords (Cons head2 tail2) (k + 1) (Nat.succ_lt_succ kw) := by rfl
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
      have resolve : seq.vec = Cons (seq.head) (FinSeq.vec (seq.tail)) := by apply seq_vec_cons_eq 
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
