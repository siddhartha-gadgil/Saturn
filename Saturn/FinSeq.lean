open Nat

class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 

def skip : Nat → Nat → Nat :=
    fun k =>
      match k with
      | 0 => 
          fun i =>
            i + 1
      | l + 1 => 
          fun j =>
            match j with
            | 0 => 0
            | i + 1 => 
                (skip l i) + 1

inductive SkipEquations(n m : Nat) where
  | lt : m < n → skip n m = m → SkipEquations n m
  | ge : n ≤ m → skip n m = m + 1 → SkipEquations n m   

inductive SkipImageCase(n m : Nat) where
  | diag : m = n → SkipImageCase n m
  | image : (k : Nat) → skip n k = m →  SkipImageCase n m

def skipEquations: (n : Nat) →  (m : Nat) →  SkipEquations n m := 
  fun k =>
      match k with
      | 0 => 
          fun i =>
            SkipEquations.ge (zeroLe _) rfl
      | l+1 => 
          fun j =>
            match j with
            | 0 => 
              SkipEquations.lt (zeroLtSucc _) rfl
            | i + 1 =>
              let unfold : skip (l + 1) (i + 1) = skip l i + 1 := by rfl 
                match skipEquations l i with
                | SkipEquations.lt ineq eqn => 
                  SkipEquations.lt 
                    (succ_lt_succ ineq) (
                      by  
                        rw unfold
                        rw eqn
                        done)
                | SkipEquations.ge ineq eqn =>
                    SkipEquations.ge (succLeSucc ineq) (
                      by  
                        rw unfold
                        rw eqn
                        done)

def skipImageCase : (n : Nat) →  (m : Nat) →  SkipImageCase n m := 
  fun k =>
      match k with
      | 0 => 
          fun j =>
            match j with 
            | 0 => SkipImageCase.diag rfl
            | i + 1 => SkipImageCase.image i rfl
      | l + 1 => 
          fun j =>
            match j with
            | 0 => 
              SkipImageCase.image 0 rfl
            | i + 1 =>               
                match skipImageCase l i with
                | SkipImageCase.diag  eqn => 
                    SkipImageCase.diag (by rw eqn)
                | SkipImageCase.image p eqn =>
                    let unfold : skip (l + 1) (p + 1) = skip l p + 1 := by rfl
                    SkipImageCase.image (p + 1) (by (rw unfold) (rw eqn))

theorem skipSuccNotZero : (n: Nat) → (j: Nat) → Not (skip n (succ j) = 0) :=
  fun n =>
  match n with 
  | 0 => 
    fun j =>
      fun hyp : succ (succ j) = 0 =>
        Nat.noConfusion hyp
  | m + 1 => 
    fun j =>
            match j with
            | 0 => 
              fun hyp : succ (skip m 0)  = 0 =>
                Nat.noConfusion hyp
            | i + 1 => 
              fun hyp =>
                let lem1 : skip (m + 1) (succ (i + 1)) = skip m (succ i) + 1 := by rfl
                let lem2 := Eq.trans (Eq.symm hyp) lem1
                Nat.noConfusion lem2

theorem skipInjective: (n: Nat) → (j1 : Nat) → (j2 : Nat) → 
                              (skip n j1 = skip n j2) → j1 = j2 :=
      fun n =>
      match n with
      | 0 =>
        fun j1 j2 =>
          fun eqn : succ j1 = succ j2 =>  
              by 
                injection eqn
                assumption
                done
      | m + 1 => 
        fun j1 =>
        match j1 with
        | 0 =>
          fun j2 =>
            match j2 with
            | 0 => fun _ => rfl
            | i2 + 1 => 
              fun hyp : 0 = skip (m + 1) (i2 + 1) =>
                let lem := skipSuccNotZero (m + 1) i2
                absurd (Eq.symm hyp) lem
        | i1 + 1 => 
          fun j2 =>
            match j2 with
            | 0 => fun hyp : skip (m + 1) (i1 + 1) = 0 =>
                let lem := skipSuccNotZero (m + 1) i1
                absurd hyp lem
            | i2 + 1 => 
              fun hyp : skip m i1 + 1 = skip m i2 + 1 =>
                let hyp1 : skip m i1 = skip m i2 := by
                  injection hyp
                  assumption
                  done
                let lem := skipInjective m i1 i2 hyp1
                congrArg succ lem


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

def concatSeq {α: Type}{n m: Nat} : (seq1 : FinSeq n α) → (seq2 : FinSeq m α) →  
  FinSeq (m + n) α := 
    match n with
    | 0 => fun _ => fun seq2 => seq2
    | l + 1 => fun seq1 => fun seq2 => 
      (head seq1) +: (concatSeq (tail seq1) seq2)

infix:65 "++:" => concatSeq

def list{α : Type}{n : Nat}: FinSeq n α → List α :=
  match n with
  | 0 => fun _ => []
  | l + 1 => fun s => (head s) :: (list (tail s))


theorem nullsEqual{α: Type}(s1 s2 : FinSeq 0 α) : s1 = s2 :=
  funext (fun j =>
            funext (fun lt =>
              nomatch lt))

def delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α := 
  fun j w =>
    seq (skip k j) (skipPlusOne w)

structure ProvedInsert{α : Type}{n: Nat}(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n + 1)(j: Nat) (jw : j < n + 1) where
  result : α
  checkImage : (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw
  checkFocus : j = k → result = value

theorem witnessIndependent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) → 
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          match j, eqn, jw with 
          | .(i), rfl, ijw =>
               rfl

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

def find?{α: Type}{n : Nat}(pred : α → Prop)[DecidablePred pred]:
  (seq : FinSeq n α) → Option (ElemSeqPred seq pred) :=
  match n with
  | 0 => fun seq => none
  | m + 1 =>
      fun seq =>
        if c : pred (head seq) then
          some ⟨0, zeroLtSucc _, c⟩
        else 
          (find? pred (tail seq)).map (fun ⟨i, iw, eqn⟩ => 
            ⟨i +1, succ_lt_succ iw, eqn⟩)

def findElem?{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: FinSeq n  α) → (elem: α) →  Option (ElemInSeq seq elem) :=
    match n with
    | 0 => fun _  => fun _ => none
    | m + 1 => 
      fun fn =>
        fun x =>
          if pf : fn 0 (zeroLtSucc m) =  x then
            some ⟨0, (zeroLtSucc m), pf⟩
          else
            let pred := findElem? (tail fn) x
            pred.map (fun ⟨j, jw, eql⟩ => 
              let l1 : fn (j + 1) (succ_lt_succ jw) = (tail fn) j jw := by rfl 
              let l2 : fn (j + 1) (succ_lt_succ jw) = x := by 
                    rw l1
                    exact eql
              ⟨j + 1 , succ_lt_succ jw, l2⟩ 
            )

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


structure GroupedSequence {n: Nat} {α β : Type}(part : α → β)(seq : FinSeq n α) where
  length : β → Nat
  seqs : (b : β) → FinSeq (length b) α
  proj: (j : Nat) → (jw : j < n) → ElemInSeq (seqs (part (seq j jw))) (seq j jw)
  sects : (b : β) → (j : Nat) → (jw : j < length b) → Nat
  sectsBound : (b : β) → (j : Nat) → (jw : j < length b) → sects b j jw < n
  equations: (b : β) → (j : Nat) → (jw : j < length b) → 
          (proj (sects b j jw) (sectsBound b j jw)).index = j


structure GroupedSequenceBranch{n: Nat} {α β : Type}(part : α → β)
      (seq : FinSeq n α)(b : β) where
  length : Nat
  seqs : FinSeq (length) α
  proj: (j : Nat) → (jw : j < n) → part (seq j jw) = b  → ElemInSeq seqs (seq j jw)
  sects : (j : Nat) → (jw : j < length) → ElemInSeq seq (seqs j jw)
  groupPart : (j : Nat) → (jw : j < length) → part (seqs j jw) = b
  
def groupedPrepend{n: Nat} {α β : Type}[DecidableEq β]{part : α → β}{seq : FinSeq n α} 
      (gps : (b: β) →   GroupedSequenceBranch part seq b) :
              (head: α) → 
                ((b: β) →  GroupedSequenceBranch part (head +: seq) b) := 
                fun head b =>
                  let seqN := head +: seq
                  let br := gps b 
                  if c : part head = b then                    
                    let lengthN := br.length + 1
                    let seqsN := head +: br.seqs
                    let projN : 
                      (j : Nat) → (jw : j < n + 1) → part (seqN j jw) = 
                          b  → ElemInSeq seqsN (seqN j jw) := 
                          fun j =>
                          match j with
                          | 0 =>
                            fun jw eqn =>
                            ⟨0, zeroLtSucc _, rfl⟩
                          | l + 1 => 
                            fun jw eqn =>
                            let lw : l < n := leOfSuccLeSucc jw
                            let ⟨i, iw, ieq⟩ := br.proj l lw eqn
                            let lem1 : seqN (l + 1) jw = seq l lw := rfl
                            let lem2 : seqsN (i + 1) (succ_lt_succ iw) =
                                    br.seqs i iw := by rfl
                            ⟨i + 1, succ_lt_succ iw, by (
                              rw lem2
                              rw lem1
                              exact ieq
                            )⟩
                    let sectsN : (j : Nat) → (jw : j < lengthN) → 
                          ElemInSeq seqN (seqsN j jw) :=
                        fun j =>
                          match j with
                          | 0 =>
                            fun jw  =>
                            ⟨0, zeroLtSucc _, rfl⟩
                          | l + 1 => 
                            fun jw  =>
                            let lw : l < br.length := leOfSuccLeSucc jw
                            let ⟨i, iw, ieq⟩ := br.sects l lw
                            let lem1 : seqsN (l + 1) jw = br.seqs l lw := rfl
                            let lem2 : seqN (i + 1) (succ_lt_succ iw) =
                                    seq i iw := by rfl
                            ⟨i + 1, succ_lt_succ iw, by (
                              rw lem2
                              rw lem1
                              exact ieq
                            )⟩
                      let groupPartN : (j : Nat) → (jw : j < lengthN) → 
                        part (seqsN j jw) = b := 
                          fun j =>
                          match j with
                          | 0 =>
                            fun jw  =>
                            c
                          | l + 1 => 
                            fun jw  =>
                            let lw : l < br.length := leOfSuccLeSucc jw
                            let ⟨i, iw, ieq⟩ := br.sects l lw
                            br.groupPart l lw
                    ⟨lengthN, seqsN, projN, sectsN, groupPartN⟩
                  else
                    let lengthN := br.length
                    let seqsN := br.seqs 
                    let projN : 
                      (j : Nat) → (jw : j < n + 1) → part (seqN j jw) = 
                          b  → ElemInSeq seqsN (seqN j jw) := 
                          fun j =>
                          match j with
                          | 0 =>
                            fun jw eqn =>
                              absurd eqn c
                          | l + 1 => 
                            fun jw eqn =>
                            let lw : l < n := leOfSuccLeSucc jw
                            br.proj l lw eqn
                    let sectsN : (j : Nat) → (jw : j < lengthN) → 
                          ElemInSeq seqN (seqsN j jw) := 
                          fun j jw =>
                            let ⟨i, iw, ieq⟩ := br.sects j jw
                            let lem1 : seqsN j jw = br.seqs j jw := rfl
                            let lem2 : seqN (i + 1) (succ_lt_succ iw) =
                                    seq i iw := by rfl
                            ⟨i + 1, succ_lt_succ iw, by (
                              rw lem2
                              rw lem1
                              exact ieq
                            )⟩
                    let groupPartN : (j : Nat) → (jw : j < lengthN) → 
                        part (seqsN j jw) = b := 
                          fun j jw => br.groupPart j jw
                    ⟨lengthN, seqsN, projN, sectsN, groupPartN⟩ 

def groupedSequence{n: Nat} {α β : Type}[DecidableEq β](part : α → β) :
      (seq: FinSeq n α) → 
      ((b: β) →   GroupedSequenceBranch part seq b) :=  
          match n with 
          | 0 => fun seq b => 
            ⟨0, FinSeq.empty, fun j jw => nomatch jw , fun j jw => nomatch jw, 
                fun j jw => nomatch jw⟩
          | m + 1 => 
            fun seq  =>
              let step :=
                groupedPrepend (fun b => groupedSequence part (tail seq) b) (head seq)
              let lem1 := headTail seq
              by
                rw Eq.symm lem1
                exact step
                done


def enumOptBool : (n : Nat) → n < 2 → Option Bool :=
  fun n =>
  match n with
  | 0 => fun _ => some true
  | 1 => fun _ => some false
  | 2 => fun _ => none
  | l + 2 => fun w => nomatch w

class FinType(α : Type) where
  length : Nat
  enum : (j: Nat) → j < n → α
  enumInv : α → Nat
  enumInvBound : (x : α) → enumInv x < length
  enumEnumInv : (x : α) → enum (enumInv x) (enumInvBound x) = x
  enumInvEnum : (j: Nat) → (jw : j < n) → enumInv (enum j jw) = j

def element{α: Type}[ft : FinType α]: (j : Nat) → (j < ft.length) → α :=
      fun j jw => ft.enum j jw

def ordinal{α: Type}[ft : FinType α]: α → Nat :=
  fun x => ft.enumInv x

def size(α: Type)[ft : FinType α]: Nat := ft.length

def ordinalBound{α: Type}[ft : FinType α]: (x : α) → ordinal x < size α :=
  fun x => ft.enumInvBound x

def ordElem{α: Type}[ft : FinType α]: (j : Nat) → (jw : j < ft.length) → 
              ordinal (element j jw) = j := ft.enumInvEnum 

def elemOrd{α: Type}[ft : FinType α]: (x : α) → 
              element (ordinal x) (ordinalBound x) = x := ft.enumEnumInv



def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (FinSeq n  α) → Option β :=
    match n with
    | 0 => fun _ => none
    | m + 1 => 
      fun seq => 
        (f (seq 0 (zeroLtSucc m))).orElse (
          findSome? f (fun t : Nat => fun w : t < m => seq (t + 1) w )
        ) 


def varSat (clVal: Option Bool)(valuatVal : Bool) : Prop := clVal = some valuatVal

def deqSeq {α : Type}[DecidableEq α] (n: Nat) : (c1 : FinSeq n  α) → 
                              (c2: FinSeq n  α) → Decidable (c1 = c2) := 
  match n with
  | 0 => 
    fun c1 c2 => 
      isTrue (funext 
        (fun x => 
          funext (fun w => nomatch w)))
  | m + 1 => 
    fun c1 c2 =>
      match deqSeq _ (tail c1) (tail c2) with
      | isTrue h => 
          if c : c1 0 (zeroLtSucc m) = c2 (0) (zeroLtSucc m) then
            isTrue 
              (funext fun k =>
                match k with
                | 0 => funext (fun w =>  c)
                | j+ 1 => funext (fun  w => 
                  let l1 : tail c1 j w = c1 (j + 1) w := by rfl
                  let l2 : tail c2 j w = c2 (j + 1) w := by rfl
                  by 
                    rw (Eq.symm l1)                    
                    rw (Eq.symm l2)
                    rw h
                    done
                    ))
          else 
            isFalse (
              fun hyp =>
                let lem : c1 0 (zeroLtSucc m) = c2 0 (zeroLtSucc m) := by
                  rw hyp
                c lem
            )
      |isFalse h => 
        isFalse (
          fun hyp => 
            let lem : (tail c1) = (tail c2) := 
              funext (
                fun j =>
                funext (
                fun w =>
                  let l1 : tail c1 j w = c1 (j + 1) w := by rfl 
                  let l2 : tail c2 j w = c2 (j + 1) w := by rfl                   
                  by 
                    rw l1
                    rw hyp
                    apply Eq.symm
                    exact l2
                    done
                    )
              )
            h lem)

instance {n: Nat}[DecidableEq α] : DecidableEq (FinSeq n  α) := fun c1 c2 => deqSeq _ c1 c2

