open Nat

syntax:max "scowl" (ident)+? : term
macro_rules  
| `(scowl $[$es]*) => `(sorry)
| `(scowl) => `(sorry)

-- def hard_problem : String := scowl
-- def harder_problem : Nat := scowl strongly
-- def hardest_problem : Nat := scowl very strongly


class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 

structure NatSucc (n: Nat) where
  pred: Nat
  eqn : n = succ (pred)

def posSucc : (n : Nat) → Not (0 = n) → NatSucc n :=
  fun n =>
  match n with
  | 0 => fun w => absurd rfl w
  | l + 1 => fun _ => ⟨l, rfl⟩

structure ProvedSkip(n m: Nat) where
  result : Nat
  lt : m < n → result = m
  ge : n ≤ m → result = m + 1

def provedSkip (n m : Nat) : ProvedSkip n m := 
  if c : m < n then
    ⟨m, fun _ => rfl, fun hyp => False.elim (Nat.ltIrrefl m (Nat.ltOfLtOfLe c hyp))⟩
  else
    ⟨m + 1, fun hyp => absurd hyp c, fun _ => rfl⟩

def skip: Nat → Nat → Nat :=
  fun n m => (provedSkip n m).result

def skipBelow(n m : Nat) : m < n → (skip n m = m) :=
  fun hyp => (provedSkip n m).lt hyp 

def skipAbove(n m : Nat) : n ≤ m → (skip n m = m + 1) :=
  fun hyp => (provedSkip n m).ge hyp

inductive SkipEquations(n m : Nat) where
  | lt : m < n → skip n m = m → SkipEquations n m
  | ge : n ≤ m → skip n m = m + 1 → SkipEquations n m   

inductive SkipImageCase(n m : Nat) where
  | diag : m = n → SkipImageCase n m
  | image : (k : Nat) → skip n k = m →  SkipImageCase n m

def skipEquations: (n : Nat) →  (m : Nat) →  SkipEquations n m := 
  fun n m =>
  if c : m < n then
    SkipEquations.lt c (skipBelow n m c)
  else
    let lem : n ≤ m :=
      match Nat.ltOrGe m n with
      | Or.inl lt => absurd lt c
      | Or.inr ge => ge
    SkipEquations.ge lem (skipAbove n m lem)

def skipImageCase : (n : Nat) →  (m : Nat) →  SkipImageCase n m := 
  fun n m =>
  if mLtn : m < n then
    SkipImageCase.image m (skipBelow n m mLtn)
  else
    if mEqn : m = n then
      SkipImageCase.diag mEqn
    else
      let nLtm : n < m := 
        match Nat.ltOrGe m n with
        | Or.inl p => absurd p mLtn
        | Or.inr p => 
          match Nat.eqOrLtOfLe p with
          | Or.inl q => absurd (Eq.symm q) mEqn
          |Or.inr q => q
      let notZero : Not (0 = m) := 
        fun hyp =>
          let nLt0 : n < 0 := by
            rw hyp
            exact nLtm
          let nLtn : n < n :=
            Nat.ltOfLtOfLe nLt0 (Nat.zeroLe _)
          Nat.ltIrrefl n nLtn
      let ⟨p, seq⟩ := posSucc m notZero
      let nLep : n ≤ p := 
        Nat.leOfSuccLeSucc (by
          rw ← seq
          exact nLtm
          done)
      let imeq : skip n p = m := by
        rw seq
        exact (skipAbove n p nLep)
        done
      SkipImageCase.image p imeq

theorem skipBound: (k j: Nat) →  skip k j < j + 2 :=
    fun k j =>
      match skipEquations k j with
      | SkipEquations.lt _ eqn => 
          by 
            rw eqn
            apply Nat.leStep
            apply Nat.leRefl
            done
      | SkipEquations.ge _ eqn => 
        by 
          rw eqn
          apply Nat.leRefl
          done 

theorem skipLowerBound :(k j: Nat) →  j ≤ skip k j  :=
    fun k j =>
      match skipEquations k j with
      | SkipEquations.lt ineqn eqn => 
          by 
            rw eqn
            apply Nat.leRefl
            done
      | SkipEquations.ge ineqn eqn => 
        by 
          rw eqn
          apply Nat.leStep
          apply Nat.leRefl
          done

theorem skipSharpLowerBound :(k j: Nat) →  Or (j + 1 ≤ skip k j) (j <  k)  :=
    fun k j =>
      match skipEquations k j with
      | SkipEquations.lt ineqn eqn => 
          Or.inr ineqn
      | SkipEquations.ge ineqn eqn => 
          Or.inl (by 
                    rw eqn
                    apply Nat.leRefl
                    done)

theorem skipInjective: (n: Nat) → (j1 : Nat) → (j2 : Nat) → 
                              (skip n j1 = skip n j2) → j1 = j2 :=
      fun n j1 j2 hyp =>
        match Nat.ltOrGe j1 n with
        | Or.inl p1 => 
          let eq1 : skip n j1 = j1 := skipBelow n j1 p1
          match Nat.ltOrGe j2 n with
          | Or.inl p2 => 
            let eq2 : skip n j2 = j2 := skipBelow n j2 p2
            by
              rw ←  eq1
              rw ← eq2
              exact hyp
              done
          | Or.inr p2 => 
            let ineq1 : j1 < j2 := Nat.ltOfLtOfLe p1 p2
            let ineq2 : j1 < skip n j2 := Nat.ltOfLtOfLe ineq1 (skipLowerBound n j2)
            let ineq3 : j1 < skip n j1 := Nat.ltOfLtOfLe ineq2 (Nat.leOfEq (Eq.symm hyp))
            let ineq4 : j1 < j1 := Nat.ltOfLtOfLe ineq3 (Nat.leOfEq eq1)
            False.elim (Nat.ltIrrefl j1 ineq4)
        | Or.inr p1 => 
          let eq1 : skip n j1 = succ j1 := skipAbove n j1 p1
          match Nat.ltOrGe j2 n with
          | Or.inl p2 =>
            let ineq1 : j2 < j1 := Nat.ltOfLtOfLe p2 p1 
            let ineq2 : j2 < skip n j1 := Nat.ltOfLtOfLe ineq1 (skipLowerBound n j1)
            let ineq3 : j2 < skip n j2 := Nat.ltOfLtOfLe ineq2 (Nat.leOfEq (hyp))
            let eq2 : skip n j2 = j2 := skipBelow n j2 p2
            let ineq4 : j2 < j2 := Nat.ltOfLtOfLe ineq3 (Nat.leOfEq eq2)
            False.elim (Nat.ltIrrefl j2 ineq4)
          | Or.inr p2 => 
            let eq2 : skip n j2 = succ j2 := skipAbove n j2 p2
            let eq3 : succ j1 = succ j2 := by
              rw ← eq1
              rw ← eq2
              exact hyp
              done
            by
              injection eq3
              assumption
              done



def skipPlusOne {n k j : Nat} : j < n → skip k j < n + 1 := 
  fun h =>
    Nat.leTrans (skipBound k j) h

theorem skipNotDiag (k: Nat) : (j: Nat) → Not (skip k j = k) :=
  fun j =>
    match skipEquations k j with
    | SkipEquations.lt ineqn eqn => 
      fun hyp =>
        let lem1 : k ≤  j := by
          rw ←hyp 
          rw eqn
          apply Nat.leRefl
          done
        let lem2  := Nat.ltOfLtOfLe ineqn lem1
        notSuccLeSelf j lem2
    | SkipEquations.ge ineqn eqn => 
      fun hyp =>  
        let lem1 : j + 1 ≤ k := by
          rw ←hyp 
          rw eqn
          apply Nat.leRefl
          done
        let lem2 : j < j := Nat.leTrans lem1 ineqn
        Nat.ltIrrefl j lem2

def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

def FinSeq.cons {α : Type}{n: Nat}(head : α)(tail : FinSeq n α) : FinSeq (n + 1) α :=
  fun k =>
  match k with
  | 0 => fun _ => head
  | j + 1 => 
    fun w =>
      tail j (leOfSuccLeSucc w)

def FinSeq.empty {α: Type} : FinSeq 0 α := 
  fun j jw => nomatch jw

def seq{α : Type}(l : List α) : FinSeq (l.length) α := 
  fun j jw => l.get j jw

infixr:66 "+:" => FinSeq.cons

def tail {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq (k + 1) (succ_lt_succ w)

def head{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq 0 (zeroLtSucc _)

theorem headTail{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): 
      (head seq) +: (tail seq) = seq := 
        funext (
          fun k => 
            match k with
            | 0 => by rfl 
            | i + 1 => by rfl
        )

def init {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq k (Nat.leStep w)

def last{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq n (Nat.leRefl _)

def concatSeqAux {α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) →  
       FinSeq l α := 
    match n with
    | 0 => fun s => fun _ => fun seq2 =>
      by
        have ss : l = m by 
          rw ← s
          apply Nat.zero_add
          done
        have sf : FinSeq l α = FinSeq m α by
          rw ss
        exact Eq.mpr sf seq2
        done
    | k + 1 => fun s seq1 seq2 => 
      let ss : k + (m + 1)  = l := 
        by
          rw ← s
          rw (Nat.add_comm m 1)
          rw (Nat.add_assoc k 1 m)
          done
      concatSeqAux ss (init seq1) ((last seq1) +: seq2)

def concatSeq {α: Type}{n m: Nat}(seq1 : FinSeq n α)(seq2 : FinSeq m α): 
  FinSeq (n + m) α := 
    concatSeqAux rfl seq1 seq2

theorem witnessIndependent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) → 
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          match j, eqn, jw with 
          | .(i), rfl, ijw =>
               rfl

theorem concatAuxValues{α: Type}{n m l: Nat}: (s : n + m = l) →   
    (seq1 : FinSeq n α) → (seq2 : FinSeq m α) → (k: Nat) → 
      ((kw : k < n) → (w : k < l) → concatSeqAux s seq1 seq2 k w = seq1 k kw) ∧ 
      ((kw : k < m) → (w : (n + k) < l) → concatSeqAux s seq1 seq2 (n + k) w = seq2 k kw) := 
        match n with
        | 0 => fun s => fun seq1 => fun seq2 =>
          by
            have ss : l = m by 
              rw ← s
              apply Nat.zero_add
              done
            have sf : FinSeq l α = FinSeq m α by
              rw ss
              done
            have resolve : concatSeqAux s seq1 seq2 = Eq.mpr sf seq2 := rfl
            rw resolve
            let lem1 : ∀ (k : Nat),
                (∀ (kw : k < 0) (w : k < l), Eq.mpr sf seq2 k w = seq1 k kw) := 
                  fun k kw => nomatch kw
            let lem2 :  ∀ (k : Nat),
              ∀ (kw : k < m) (w : 0 + k < l), Eq.mpr sf seq2 (0 + k) w = 
              seq2 k kw := 
                match l, m, ss, sf, seq2 with
                | d, .(d), rfl, rfl, seq => 
                  by 
                    intro k
                    intro kw
                    intro w
                    let zp: 0 + k = k :=
                        Nat.zero_add k
                    let lm : Eq.mpr rfl seq (0 + k) w = seq (0 + k) w := rfl 
                    rw lm
                    apply witnessIndependent
                    exact zp
                    done
            exact (fun k => And.intro (lem1 k) (lem2 k))
            done
        | p + 1 => 
          fun s seq1 seq2 => 
          let ss : p + (m + 1)  = l := 
            by
              rw ← s
              rw (Nat.add_comm m 1)
              rw (Nat.add_assoc p 1 m)
              done
          let resolve : concatSeqAux s seq1 seq2=
              concatSeqAux ss (init seq1) ((last seq1) +: seq2) := rfl
          let hyp := concatAuxValues ss (init seq1) ((last seq1) +: seq2)
          by
            rw resolve
            intro k
            let hyp1 := (hyp k).left
            let lem1 : (∀ (kw : k < p + 1) (w : k < l), 
                concatSeqAux ss (init seq1) (last seq1+:seq2) k w = seq1 k kw) := 
                fun kw w => 
                  if kww : k < p then 
                    hyp1 kww w 
                  else 
                    let eql: k = p := 
                      match Nat.eqOrLtOfLe kw with
                      | Or.inl h => by 
                                      injection h
                                      assumption
                      | Or.inr h =>
                          let contra : k < p := 
                              Nat.succ_lt_succ h 
                          absurd contra kww
                    match k, eql, kw, w with
                    | .(p), rfl, pw, w =>
                      let ww : p + 0 < l := by
                        rw (Nat.add_zero p)
                        assumption
                      let hyp2 := (hyp 0).right (Nat.zeroLe _) ww
                      let lem2 : concatSeqAux ss (init seq1) (last seq1+:seq2) (p + 0) ww =
                            concatSeqAux ss (init seq1) (last seq1+:seq2) p w := 
                            match (p + 0), Nat.add_zero p, ww with
                            | .(p), rfl, ww => rfl
                      by
                        rw ← lem2
                        rw hyp2
                        rfl
                        done
            let ass := Nat.add_assoc p 1 k
            let comm := Nat.add_comm 1 k
            let lem2 : ∀ (kw : k < m) (w : p + 1 + k < l), 
                concatSeqAux ss (init seq1) (last seq1+:seq2) (p + 1 + k) w = 
                    seq2 k kw := fun kw w =>
                    match p + 1 + k, ass, w with
                    | .(p + (1 + k)), rfl, ww => 
                      by
                      let hypw := (hyp (1 + k)).right
                      let kww : 1 + k < m + 1 := by
                        rw comm
                        apply Nat.succ_lt_succ
                        assumption
                        done 
                      let lm := hypw kww ww
                      rw lm
                      let lmc : FinSeq.cons (last seq1) seq2 (1 + k) kww = 
                                  FinSeq.cons (last seq1) seq2 (k + 1) 
                                  kw := 
                              match 1 + k, comm, kww with 
                              | .(k + 1), rfl, kwww => by rfl
                      rw lmc
                      rfl
                      done
            exact (And.intro lem1 lem2)
            done

infix:65 "++:" => concatSeq

theorem concatEmptySeq{α: Type}{n: Nat}: (seq : FinSeq n α) → seq ++: (FinSeq.empty) = seq := 
          by
            intro seq
            apply funext
            intro k
            apply funext
            intro kw
            let resolve : concatSeq seq FinSeq.empty =  
                  concatSeqAux rfl seq FinSeq.empty := rfl
            rw resolve
            have w : k < n + 0 by
              rw (Nat.add_zero n)
              assumption
              done
            let lem := (concatAuxValues rfl seq FinSeq.empty k).left kw w
            exact lem
            done

def list{α : Type}{n : Nat}: FinSeq n α → List α :=
  match n with
  | 0 => fun _ => []
  | l + 1 => fun s => (head s) :: (list (tail s))


def delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α := 
  fun j w =>
    seq (skip k j) (skipPlusOne w)

structure ProvedInsert{α : Type}{n: Nat}(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n + 1)(j: Nat) (jw : j < n + 1) where
  result : α
  checkImage : (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw
  checkFocus : j = k → result = value


theorem skipPreImageBound {i j k n : Nat}: (k < n + 1) → (j < n + 1) → 
                                skip k i = j → i < n :=
          fun kw jw eqn =>
            match skipSharpLowerBound k i with
              | Or.inl ineq =>
                by 
                  have lem1 : i <  j
                  by
                    rw ← eqn
                    exact ineq
                    done                 
                  have lem2 : i < n
                  by
                    apply Nat.ltOfLtOfLe
                    apply lem1
                    apply jw
                    done 
                  exact lem2
                  done
              | Or.inr ineqn => 
                  Nat.ltOfLtOfLe ineqn kw

def provedInsert{α : Type}(n: Nat)(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n + 1)(j: Nat) (jw : j < n + 1) : 
                  ProvedInsert value seq k kw j jw := 
          match skipImageCase k j with
          | SkipImageCase.diag eqn => 
            let result := value
            let checkImage : 
              (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw := 
                fun i iw hyp =>
                  let lem : skip k i = k := by
                    rw hyp
                    rw eqn
                    done
                  let contra := skipNotDiag k i lem
                  nomatch contra
            let  checkFocus : j = k → result = value := fun  _  => rfl
            ⟨result, checkImage, checkFocus⟩
          | SkipImageCase.image i eqn => 
            let bound : i < n  := skipPreImageBound kw jw eqn
            let result := seq i bound
            let checkImage : 
              (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw := 
                fun i1 iw1 hyp =>
                  let lem1 : i1 = i := by 
                    apply (skipInjective k)
                    rw hyp
                    rw (Eq.symm eqn)
                    done
                  let lem2 : seq i1 iw1 = seq i bound := 
                    witnessIndependent seq i1 i iw1 bound lem1
                  by
                    rw lem2
                    done
            let  checkFocus : j = k → result = value := 
              fun  hyp  => 
                let lem : skip k i = k := by
                    rw eqn
                    rw hyp
                    done
                  let contra := skipNotDiag k i lem
                  nomatch contra 
            ⟨result, checkImage, checkFocus⟩

def insert{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (FinSeq n   α) →  (FinSeq (Nat.succ n)  α) := 
  fun n k lt seq j w =>  
    (provedInsert n value seq k lt j w).result

def insertAtFocus{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) →  
      insert value n k lt seq k lt = value :=
    fun n k lt seq  =>   
      (provedInsert n value seq k lt k lt).checkFocus rfl

def insertAtImage(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (seq :FinSeq n   α) → (i : Nat) → (iw : i < n) → 
      insert value n k lt seq (skip k i) (skipPlusOne iw) = seq i iw :=
      fun n k lt seq i iw => 
       (provedInsert n value seq k lt (skip k i) (skipPlusOne iw)).checkImage i iw rfl 

def insertDelete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α) :
  insert (seq k kw) n k kw (delete k kw seq) = seq := 
    let delSeq := delete k kw seq
    funext (
      fun j =>
        funext (
          fun jw => 
            match skipImageCase k j with
            | SkipImageCase.diag eqn => 
              by
              have lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw =
                insert (seq k kw) n k kw (delete k kw seq) k kw 
                by
                  apply witnessIndependent
                  apply eqn
                  done 
              rw lem1
              rw (insertAtFocus (seq k kw) n k kw (delete k kw seq))
              apply witnessIndependent
              rw ← eqn
              done  
            | SkipImageCase.image i eqn => 
              let iw : i < n := skipPreImageBound kw jw eqn
              let lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw
                = insert (seq k kw) n k kw (delete k kw seq) (skip k i) (skipPlusOne iw) := 
                  by 
                    apply witnessIndependent
                    rw ← eqn
                    done
              let lem2 := insertAtImage (seq k kw) n k kw (delete k kw seq) i iw
              let lem3 : delete k kw seq i iw = seq (skip k i) (skipPlusOne iw) := by rfl
              by
                rw lem1
                rw lem2
                rw lem3
                apply witnessIndependent
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
          | 0, _ => none
          | l + 1, cb => 
            let lem : l + 1 ≤  n := by
                apply (Nat.leTrans ·  cb)
                apply Nat.leSucc
                done
            findAux? pred l lem seq    

def find?{α: Type}{n : Nat}(pred : α → Prop)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) :=
  match n with
  | 0 => fun _ =>  none
  | m + 1 => fun seq => findAux? pred m (Nat.leRefl _) seq

def elemAt{α: Type}[deq: DecidableEq α]{n: Nat}(seq: FinSeq n  α)(elem: α)(k: Nat):
  Option (ElemInSeq seq elem) :=
    if lt : k <n then 
      if eqn : seq k lt = elem 
        then some ⟨k, lt, eqn⟩
        else none 
    else none

def findElemAux?{α: Type}{n : Nat}(cursor: Nat)
      (cursorBound : cursor < n)[DecidableEq α]:
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) := 
    fun seq  elem =>
      if eqn : seq cursor cursorBound = elem 
        then some ⟨cursor, cursorBound, eqn⟩
        else 
          match cursor, cursorBound with
          | 0, _ => none
          | l + 1, cb => 
            let lem : l + 1 ≤  n := by
                apply (Nat.leTrans ·  cb)
                apply Nat.leSucc
                done
            findElemAux? l lem seq elem  

def findElem?{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) :=
   match n with
  | 0 => fun _ _ =>  none
  | m + 1 => fun seq elem => findElemAux?  m (Nat.leRefl _) seq elem

def searchElem{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  ExistsElem seq elem :=
    match n with
    | 0 => fun seq  => fun elem => ExistsElem.notExst (fun j jw => nomatch jw)
    | m + 1 => 
      fun fn =>
        fun x =>
          if pf0 : fn 0 (zeroLtSucc m) =  x then
            ExistsElem.exsts 0 (zeroLtSucc m) pf0
          else
            match searchElem (tail fn) x with
            | ExistsElem.exsts j jw eql => 
              let l1 : fn (j + 1) (succ_lt_succ jw) = (tail fn) j jw := by rfl 
              let l2 : fn (j + 1) (succ_lt_succ jw) = x := by 
                    rw l1
                    exact eql
              ExistsElem.exsts (j + 1) (succ_lt_succ jw) l2              
            | ExistsElem.notExst tailPf => 
                  ExistsElem.notExst (
                    fun j =>
                    match j with
                    | 0 => fun jw => pf0 
                    | i + 1 => fun iw => tailPf i (leOfSuccLeSucc iw)
                  )

structure ProvedUpdate{α β: Type}(fn : α → β)( a : α )( val : β )( x : α) where
  result : β
  checkFocus : (x = a) → result = val
  checkNotFocus : Not (x = a) → result = fn x

def provedUpdate{α β: Type}[DecidableEq α](fn : α → β)( a : α )( val : β )( x : α) : 
  ProvedUpdate fn a val x :=
    if c : x = a then 
      let result := val
      let checkFocus : (x = a) → result = val := fun _ => rfl
      let checkNotFocus : Not (x = a) → result = fn x := fun d => absurd c d
      ⟨result, checkFocus, checkNotFocus⟩
    else 
      let result := fn x
      let checkFocus : (x = a) → result = val := fun d => absurd d c
      let checkNotFocus : Not (x = a) → result = fn x := fun _ => rfl 
      ⟨result, checkFocus, checkNotFocus⟩

def update{α β : Type}[DecidableEq α](fn : α → β)( a : α )( val : β )( x : α) : β :=
  (provedUpdate fn a val x).result

def updateAtFocus{α β: Type}[DecidableEq α](fn : α → β)( a : α )( val : β ) :
  (update fn a val a = val) := (provedUpdate fn a val a).checkFocus rfl

def updateNotAtFocus{α β: Type}[DecidableEq α](fn : α → β)( a : α )( val : β )( x : α) :
  Not (x = a) →  (update fn a val x = fn x) :=
    fun hyp =>
      (provedUpdate fn a val x).checkNotFocus hyp

structure ProvedUpdateType{α : Type}(fn : α → Type)( a : α )( val : Type )( x : α) where
  result : Type
  checkFocus : (x = a) → result = val
  checkNotFocus : Not (x = a) → result = fn x

def provedUpdateType{α : Type}[DecidableEq α](fn : α → Type)( a : α )( val : Type )( x : α) : 
  ProvedUpdateType fn a val x :=
    if c : x = a then 
      let result := val
      let checkFocus : (x = a) → result = val := fun _ => rfl
      let checkNotFocus : Not (x = a) → result = fn x := fun d => absurd c d
      ⟨result, checkFocus, checkNotFocus⟩
    else 
      let result := fn x
      let checkFocus : (x = a) → result = val := fun d => absurd d c
      let checkNotFocus : Not (x = a) → result = fn x := fun _ => rfl 
      ⟨result, checkFocus, checkNotFocus⟩

def updateType{α: Type}[DecidableEq α](fn : α → Type)( a : α )( val : Type )( x : α) : Type :=
  (provedUpdateType fn a val x).result

def updateAtFocusType{α : Type}[DecidableEq α](fn : α → Type)( a : α )( val : Type ) :
  (updateType fn a val a = val) := (provedUpdateType fn a val a).checkFocus rfl

def updateNotAtFocusType{α : Type}[DecidableEq α](fn : α → Type)( a : α )( val : Type )( x : α) :
  Not (x = a) →  (updateType fn a val x = fn x) :=
    fun hyp =>
      (provedUpdateType fn a val x).checkNotFocus hyp


structure ProvedDepUpdate{α :Type}[DecidableEq α]{β : α → Type}(fn : (x :α) → β x)
          ( a : α )(ValType : Type)( val : ValType )
            ( x : α) where
  result : updateType β a ValType x
  checkFocus : (eqn : x = a) → result = 
          Eq.mpr (by 
            rw eqn
            apply updateAtFocusType
            done 
            ) val
  checkNotFocus : (neq:  Not (x = a)) → result = 
          Eq.mpr (by
            apply updateNotAtFocusType 
            exact neq
            done)  (fn x)


def enumOptBool : (n : Nat) → n < 2 → Option Bool :=
  fun n =>
  match n with
  | 0 => fun _ => some true
  | 1 => fun _ => some false
  | 2 => fun _ => none
  | l + 2 => fun w => nomatch w

def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (FinSeq n  α) → Option β :=
    match n with
    | 0 => fun _ => none
    | m + 1 => 
      fun seq => 
        (f (seq 0 (zeroLtSucc m))).orElse (
          findSome? f (fun t : Nat => fun w : t < m => seq (t + 1) w )
        ) 

def equalBeyond{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat): Prop :=
  ∀ k: Nat, ∀ kw : k <n, ∀ mw : m ≤ k, seq1 k kw = seq2 k kw

theorem equalBeyondZero{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α):
    equalBeyond seq1 seq2 0 → seq1 = seq2 := by
      intro hyp
      apply funext
      intro k
      apply funext
      intro kw
      exact hyp k kw  (Nat.zeroLe k)
      done


def equalBeyondVacuous{α: Type}{n : Nat}(seq1 seq2 : FinSeq n α)(m: Nat):
    (n ≤ m) → equalBeyond seq1 seq2 m := by
      intro hyp
      intro k
      intro kw
      intro ineq
      let inq := Nat.leTrans hyp ineq
      let inq2 := Nat.ltOfLtOfLe kw inq
      exact (False.elim (Nat.ltIrrefl k inq2))
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
            have restr : equalBeyond seq1 seq2 m by
              intro k
              intro kw
              intro _ 
              rw hyp
              done
            exact contra restr
            done)
      | 0, isTrue pf => 
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
                    cases Nat.eqOrLtOfLe ineq with
                    | inl eql =>
                      let lem0 := pfHead
                      let lem1 : seq1 l lw = seq1 k kw := by
                        apply witnessIndependent
                        exact eql
                        done
                      let lem2 : seq2 l lw = seq2 k kw := by
                        apply witnessIndependent
                        exact eql
                      rw ← lem1
                      rw ← lem2
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
                            rw hyp
                            done
                          )                           
                          )
        else
          let overshoot : n ≤ l := by
            cases Nat.ltOrGe l n with
            | inl l1 => exact absurd l1 lw
            | inr l2 => exact l2
          let accum: Decidable (equalBeyond seq1 seq2 l) := 
            isTrue (equalBeyondVacuous seq1 seq2 l overshoot)
          deqSeqRec seq1 seq2 l accum
      

def deqSeq {α : Type}[DecidableEq α] (n: Nat) : (c1 : FinSeq n  α) → 
                              (c2: FinSeq n  α) → Decidable (c1 = c2) := 
              fun seq1 seq2 => 
                deqSeqRec seq1 seq2 n (isTrue (equalBeyondVacuous seq1 seq2 n (Nat.leRefl n)))

instance {n: Nat}[DecidableEq α] : DecidableEq (FinSeq n  α) := fun c1 c2 => deqSeq _ c1 c2

