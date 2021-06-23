import Saturn.Basic
open Nat

macro_rules
  | `(scowl) => `(sorry)

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
              let lem : skip (l + 1) 0 = 0 := by rfl
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
                    let fst := succLeSucc ineq 
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

#check Nat.leTrans

theorem skipNotDiag (k: Nat) : (j: Nat) → Not (skip k j = k) :=
  fun j =>
    match skipEquations k j with
    | SkipEquations.lt ineqn eqn => 
      fun hyp =>
        let lem1 : k ≤  j := by
          rw (Eq.symm hyp) 
          rw eqn
          apply Nat.leRefl
          done
        let lem2  := Nat.ltOfLtOfLe ineqn lem1
        notSuccLeSelf j lem2
    | SkipEquations.ge ineqn eqn => 
      fun hyp =>  
        let lem1 : j + 1 ≤ k := by
          rw (Eq.symm hyp) 
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

theorem propValue(p: Prop) : (a b: p) → a = b :=
                fun a b => by rfl

#print congr
#print Eq.ndrec

theorem witnessIndependent{α : Type}{n : Nat}(seq: FinSeq n α) :
    (i : Nat)→ (j : Nat) → (iw : i < n) → (jw : j < n) → 
        (i = j) → seq i iw = seq j jw :=
        fun i j iw jw eqn =>
          let fn : Fin n → α := fun ⟨i, w⟩ => seq i w
          let lem : (⟨i, iw⟩ : Fin n) = ⟨j, jw⟩ := by
                apply Fin.eqOfVeq
                exact eqn
                done
          let eq1 : fn ⟨i, iw⟩ = seq i iw := by rfl
          let eq2 : fn ⟨j, jw⟩ = seq j jw := by rfl
          let eqc := congrArg fn lem
          by 
            rw (Eq.symm eq1)
            rw (Eq.symm eq2)
            exact eqc
            done

theorem skipPreImageBound {i j k n : Nat}: (k < n + 1) → (j < n + 1) → 
                                skip k i = j → i < n :=
          fun kw jw eqn =>
            match skipSharpLowerBound k i with
              | Or.inl ineq =>
                let lem1 : i <  j := by 
                  rw (Eq.symm eqn)
                  exact ineq
                  done 
                let lem2 := Nat.ltOfLtOfLe lem1 jw
                by 
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
              let lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw =
                insert (seq k kw) n k kw (delete k kw seq) k kw := by
                  apply witnessIndependent
                  apply eqn
                  done
              by 
                rw lem1
                rw (insertAtFocus (seq k kw) n k kw (delete k kw seq))
                apply witnessIndependent
                apply (Eq.symm eqn)
                done  
            | SkipImageCase.image i eqn => 
              let iw : i < n := skipPreImageBound kw jw eqn
              let lem1 : insert (seq k kw) n k kw (delete k kw seq) j jw
                = insert (seq k kw) n k kw (delete k kw seq) (skip k i) (skipPlusOne iw) := 
                  by 
                    apply witnessIndependent
                    apply (Eq.symm eqn)
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

-- just for lookup
def transport(α β : Type)(eql: α = β): α → β :=
  fun x =>
     Eq.mp eql x

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

def provedDepUpdate{α :Type}[DecidableEq α]{β : α → Type}(fn : (x :α) → β x)
          ( a : α )(ValType : Type)( val : ValType )
            ( x : α) : ProvedDepUpdate fn a ValType val x := 
          if c : x = a then
            let result : updateType β a ValType x := Eq.mpr (by 
              rw c
              apply updateAtFocusType
              done 
            ) val
            let checkFocus : (eqn : x = a) → result = 
              Eq.mpr (by 
                rw eqn
                apply updateAtFocusType
                done 
                ) val := fun _ => rfl
            let checkNotFocus : (neq:  Not (x = a)) → result = 
              Eq.mpr (by
                apply updateNotAtFocusType 
                exact neq
                done)  (fn x) := fun d => absurd c d
            ⟨result, checkFocus, checkNotFocus⟩
          else 
            let result : updateType β a ValType x := Eq.mpr (by
                apply updateNotAtFocusType 
                exact c
                done)  (fn x)
            let checkFocus : (eqn : x = a) → result = 
              Eq.mpr (by 
                rw eqn
                apply updateAtFocusType
                done 
              ) val := fun d => absurd d c
            let checkNotFocus : (neq:  Not (x = a)) → result = 
              Eq.mpr (by
                apply updateNotAtFocusType 
                exact neq
                done)  (fn x) := fun _ => rfl
            ⟨result, checkFocus, checkNotFocus⟩


def depUpdate{α :Type}[DecidableEq α]{β : α → Type}(fn : (x :α) → β x)
          ( a : α )(ValType : Type)( val : ValType )
            ( x : α) : updateType β a ValType x := 
          (provedDepUpdate fn a ValType val x).result

structure Sect{α β : Type}{n m : Nat}(total : FinSeq n α) (base : FinSeq m β)
        (proj: (i: Nat) → i < n → Nat)(bound : (i : Nat) → (w : i < n) → proj i w < m) where
    sect: (j : Nat) → j < m → Nat
    sectBound : (j : Nat) → (bd : j < m) → sect j bd < n
    equation: (j : Nat) → (bd : j < m) → proj (sect j bd) (sectBound j bd) = j


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

structure FlattenSeq{α : Type}{n: Nat}(lengths : (j : Nat) → j < n → Nat)
                                    (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) where
          length : Nat
          seq : FinSeq length α
          forward: (j : Nat) → (jw : j < length) → Σ (i : Nat), (iw : i < n) → 
                      ElemInSeq (seqs i iw) (seq j jw)
          reverse: (i : Nat) → (iw : i < n) → (j : Nat) → (jw : j < lengths i iw) → 
                      ElemInSeq seq (seqs i iw j jw)

#check Nat.zeroLe

structure PartialFlattenSeq{α : Type}{n: Nat}(lengths : (j : Nat) → j < n → Nat)
                            (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) 
                            (gp : Nat)(gpBound : gp < n)(max: Nat)(maxBound : max ≤  lengths gp gpBound)
                                        where
          length : Nat
          seq : FinSeq length α
          forward: (j : Nat) → (jw : j < length) → Σ (i : Nat), (iw : i < n) → 
                      ElemInSeq (seqs i iw) (seq j jw)
          reverse: (i : Nat) → (iw : i < n) → (j : Nat) → (jw : j < lengths i iw) → 
                    i < gp ∨ (i = gp ∧ j < max)  → 
                      ElemInSeq seq (seqs i iw j jw)

def partToFullFlatten{α : Type}{n: Nat}(lengths : (j : Nat) → j < n + 1 → Nat)
                                    (seqs : (j : Nat) → (jw : j < n + 1) → FinSeq (lengths j jw) α) :
                PartialFlattenSeq lengths seqs n (Nat.leRefl _) 
                    (lengths n (Nat.leRefl _)) (Nat.leRefl _) → 
                    FlattenSeq lengths seqs  := 
                    fun pfs => 
                      let reverseN : (i : Nat) → (iw : i < (n +1)) → 
                        (j : Nat) → (jw : j < lengths i iw) → 
                        ElemInSeq pfs.seq (seqs i iw j jw) := 
                          fun i iw j jw =>
                            let lem : i < n ∨ i = n ∧ 
                              j < lengths n (Nat.leRefl (succ n)) :=
                                let switch := Nat.eqOrLtOfLe iw
                                match switch with 
                                | Or.inl p => 
                                  let p1 : i = n := by
                                    injection p
                                    assumption
                                  let lem : lengths n (Nat.leRefl (succ n)) =
                                            lengths i iw := by
                                          apply witnessIndependent
                                          exact Eq.symm p1
                                          done
                                  Or.inr (And.intro p1 (by 
                                                          rw lem
                                                          exact jw))
                                | Or.inr p => 
                                    Or.inl (leOfSuccLeSucc p)
                            pfs.reverse i iw j jw lem
                      ⟨pfs.length, pfs.seq, pfs.forward, reverseN⟩

#check Eq.ndrec
#check 1 ≅ [3]
#check HEq.ndrec


def partFlatInGp{α : Type}{n: Nat}(lengths : (j : Nat) → j < n → Nat)
                          (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) 
                          (gp : Nat)(gpBound : gp < n)
                            (base: PartialFlattenSeq lengths seqs gp gpBound 0 (Nat.zeroLe _)):
                          (max: Nat) → (maxBound : max ≤  lengths gp gpBound) → 
                            PartialFlattenSeq lengths seqs gp gpBound max maxBound := 
                  fun max => 
                  match max with
                  | 0 => fun _ =>
                      base
                  | k + 1 =>
                    fun maxBound => 
                      let prev := partFlatInGp lengths seqs gp gpBound base k (leStep maxBound)
                      let head := seqs gp gpBound k maxBound
                      let lengthN := prev.length +1
                      let seqN := head +: prev.seq 
                      let forwardN : (j : Nat) → (jw : j < lengthN) → Σ (i : Nat), (iw : i < n) → 
                            ElemInSeq (seqs i iw) (seqN j jw) := 
                              fun j =>
                              match j with
                              | 0 => 
                                fun jw =>
                                  ⟨gp, fun w => ⟨k, maxBound, rfl⟩⟩
                              | l + 1 => 
                                fun jw =>
                                  let lw := leOfSuccLeSucc jw
                                  by
                                    apply (prev.forward l lw)
                                    done
                      let reverseN : (i : Nat) → (iw : i < n) → (j : Nat) → (jw : j < lengths i iw) → 
                          i < gp ∨ (i = gp ∧ j < k + 1)  → 
                          ElemInSeq seqN (seqs i iw j jw) := 
                          fun i iw j jw p =>
                            if c : i < gp then 
                              let ⟨ind, bd, eqn⟩ := prev.reverse i iw j jw (Or.inl c)
                              let lem : seqN (ind + 1) (succ_lt_succ bd) =
                                      prev.seq ind bd := by rfl
                              ⟨ind + 1, succ_lt_succ bd, (by 
                                      rw lem
                                      exact eqn
                                      )⟩
                            else
                              let q : i = gp ∧ j < k + 1 := 
                                match p with
                                | Or.inl eqn => absurd eqn c
                                | Or.inr eqn => eqn
                              let q1 := q.left
                              let q2 := q.right
                              if mc : j = k then
                                let lem : 
                                  seqN 0 (zeroLtSucc prev.length) = seqs gp gpBound k maxBound := by rfl
                                let lem1 : lengths i iw = lengths gp gpBound := by
                                  apply witnessIndependent
                                  rw q1
                                  done
                                let lem2 := congrArg FinSeq lem1
                                let trnsport : FinSeq (lengths i iw) α  → FinSeq (lengths gp gpBound) α  :=
                                  fun fs =>
                                    by 
                                      rw (Eq.symm lem2)
                                      exact fs
                                      done                                    
                                let lem3 : seqs i  ≅ seqs gp  := by
                                    rw q1
                                    apply HEq.rfl
                                    done
                                  
                                let goal : seqs gp gpBound k maxBound = seqs i iw j jw := sorry

                                ⟨0, zeroLtSucc _, (by 
                                  rw lem
                                  exact goal
                                  done
                                )⟩
                              else 
                                let jww : j < k := 
                                  match Nat.eqOrLtOfLe q2 with
                                  | Or.inl ee => 
                                      let ll : j = k := by
                                      injection ee
                                      assumption 
                                    absurd ll mc
                                  | Or.inr ee => leOfSuccLeSucc ee
                                let ⟨ind, bd, eqn⟩ := prev.reverse i iw j jw (Or.inr (And.intro q1 jww))
                                let lem : seqN (ind + 1) (succ_lt_succ bd) =
                                      prev.seq ind bd := by rfl
                               ⟨ind + 1, succ_lt_succ bd, (by 
                                      rw lem
                                      exact eqn
                                      )⟩
                      ⟨lengthN , seqN, forwardN, reverseN⟩ 

-- def partFlatSeq{α : Type}(gp: Nat):
--         (max: Nat) → (n: Nat) → 
--           (lengths : (j : Nat) → j < n + 1  → Nat) → 
--           (seqs : (j : Nat) → (jw : j < n + 1) → FinSeq (lengths j jw) α) → (gpBound : gp < n + 1)  → (maxBound : max ≤  lengths gp gpBound) → 
--         PartialFlattenSeq lengths seqs gp gpBound max maxBound := 
--         -- fun gp =>
--         match gp with
--         | 0 => 
--           fun max =>
--             match max with
--             | 0 => fun _ _ _ _ _ =>
--               ⟨0, FinSeq.empty, 
--                 fun j jw => nomatch jw, 
--                 fun i iw j jw p => 
--                   let q : ¬(i < 0 ∨ i = 0 ∧ j < 0) := 
--                     match p with
--                     | Or.inl p1 => nomatch p1
--                     | Or.inr p2 => nomatch p2
--                   absurd p q ⟩
--             | k + 1 => 
--               fun n lengths seqs =>
--               fun gpBound =>
--               fun maxBound => 
--                 let prev := partFlatSeq 0 k n lengths seqs gpBound  (leStep maxBound)
--                 let head := seqs 0 gpBound k maxBound
--                 let lengthN := prev.length +1
--                 let seqN := head +: prev.seq 
--                 let forwardN : (j : Nat) → (jw : j < lengthN) → Σ (i : Nat), (iw : i < n + 1) → 
--                       ElemInSeq (seqs i iw) (seqN j jw) := 
--                         fun j =>
--                         match j with
--                         | 0 => 
--                           fun jw =>
--                             ⟨0, fun w => ⟨k, maxBound, rfl⟩⟩
--                         | l + 1 => 
--                           fun jw =>
--                             let lw := leOfSuccLeSucc jw
--                             by
--                               apply (prev.forward l lw)
--                               done
--                 ⟨lengthN , seqN, forwardN, sorry⟩
--         | l + 1 => sorry      

def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (FinSeq n  α) → Option β :=
    match n with
    | 0 => fun _ => none
    | m + 1 => 
      fun seq => 
        (f (seq 0 (zeroLtSucc m))).orElse (
          findSome? f (fun t : Nat => fun w : t < m => seq (t + 1) w )
        ) 


def varSat (clVal: Option Bool)(valuatVal : Bool) : Prop := clVal = some valuatVal
namespace leaner


def Clause(n : Nat) : Type := FinSeq n (Option Bool)

def Valuat(n: Nat) : Type := FinSeq n  Bool



structure ClauseSat{n: Nat}(clause : Clause n)(valuat: Valuat n) where
  coord : Nat
  bound : coord < n  
  witness: varSat (clause coord bound) (valuat coord bound)

def clauseSat {n: Nat}(clause : Clause n)(valuat: Valuat n) := 
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuat k b)

instance {n: Nat}(clause : Clause n)(valuat: Valuat n): Prover (ClauseSat clause valuat) where 
  statement := fun cs => ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuat k b)
  proof := fun cs => ⟨cs.coord, ⟨cs.bound, cs.witness⟩⟩

def contradiction(n: Nat) : Clause n :=
  fun _ _ => none

theorem contradictionFalse (n: Nat) : ∀ valuat : Valuat n, Not (clauseSat (contradiction n) valuat) :=
  fun valuat => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : (contradiction n) k b = none := by rfl
    let lem2 := congrArg varSat lem1
    let lem3 : varSat (contradiction n k b) (valuat k b) = 
                varSat none (valuat k b) := congr lem2 rfl
    let lem4 : (varSat none (valuat k b)) = (none = some (valuat k b)) := rfl
    let lem5 : (none = some (valuat k b)) := by
      rw (Eq.symm lem4)
      rw lem4
      assumption
      done 
    Option.noConfusion lem5

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


def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  insert (some b) n k w (contradiction n) 

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1)) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) := 
    fun ⟨k, w⟩ =>
      match deqSeq _ clause  (unitClause n true k w) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w true pf 
        some (cl)
      | isFalse _ => 
        match deqSeq _ clause  (unitClause n false k w) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w false pf 
        some (cl)
      | isFalse _ => none  
  let seq : FinSeq (n + 1) (Fin (n + 1)) := fun k w => ⟨k, w⟩
  findSome? f seq

def someUnitClause {l : Nat} : (n : Nat) →  (clauses : Fin l → (Clause (n + 1))) →  
  Option (Σ k : Fin l, IsUnitClause (clauses k))  := 
    match l with 
    | 0 => fun _ _ =>  none
    | m + 1 => 
      fun n cls =>
        match clauseUnit (cls ⟨0, (zeroLtSucc m)⟩) with
        | some u => some ⟨⟨0, (zeroLtSucc m)⟩, u⟩ 
        | none => 
          let tcls := dropHead _ cls
          let tail := someUnitClause n tcls
          match tail with
          | some ⟨⟨i, w⟩, u⟩ => 
            some ⟨⟨i + 1, leOfSuccLeSucc w⟩, u⟩
          | none => none

structure HasPureVar{dom n : Nat}(clauses : FinSeq dom  (Clause n)) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < dom) → 
          (clauses k lt index bound = none) ∨  (clauses k lt index bound = some parity)

structure IsPureVar{dom n : Nat}(clauses : FinSeq dom  (Clause n))
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < dom) → (clauses k lt index bound = none) ∨ 
                                (clauses k lt index bound = some parity)

def varIsPure{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) : 
  (dom: Nat) →  (clauses : FinSeq dom  (Clause n)) → 
    Option (IsPureVar clauses index bound parity) :=
  fun dom =>
  match dom with
  | 0 => 
    fun clauses =>
      let evidence : (k : Nat) → (lt : k < 0) →  
        (clauses k lt index bound = none) ∨ (clauses k lt index bound = some parity) := 
          fun k lt => nomatch lt
      some ⟨evidence⟩
  | m + 1 => 
      fun clauses =>
        let head := clauses 0 (zeroLtSucc _) index bound
        if c : (head = none) ∨  (head = some parity) then
          let tailSeq  := tail clauses
          (varIsPure index bound parity _ tailSeq).map (
            fun ⟨ tpf ⟩ =>
              let pf : (j : Nat) → (w : j < (m +1)) → 
                (clauses j w index bound = none) ∨ (clauses j w index bound = some parity) := 
                fun j =>
                  match j with 
                  | 0 => fun w => c
                  | i + 1 => fun w =>
                    let tailWit : i < m := leOfSuccLeSucc w 
                    tpf i tailWit
              ⟨ pf ⟩
          )
        else none

def findPureAux{n : Nat} : (dom: Nat) →  (clauses : FinSeq dom (Clause (n +1))) → 
  (ub: Nat) → (lt : ub < n + 1) → 
      Option (HasPureVar clauses) :=
      fun dom clauses ub => 
        match ub with
        | 0 =>
          fun lt =>
           ((varIsPure 0 lt true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk 0 lt true evidence
              )).orElse (
                (varIsPure 0 lt false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk 0 lt false evidence
              )
              )
        | l + 1 =>
          fun lt =>
            ((findPureAux dom clauses l (leStep lt)).orElse (              
              (varIsPure l (leStep lt) true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk l (leStep lt) true evidence
              )
              )).orElse (              
              (varIsPure l (leStep lt) false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk l (leStep lt) false evidence
              )
              )
            
def hasPure{n : Nat}(dom: Nat)(clauses : FinSeq dom  (Clause (n +1))) 
            (ub: Nat)(lt : ub < n + 1) : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.leRefl _)


end leaner

-- helpers and theorems for old style finite sequences 

namespace clunky

theorem dropPlusOne{α : Type}(n: Nat)(zeroVal : α)(j: Fin n)(g: (Fin (succ n)) → α) 
        : (dropHead n g j) = g (plusOne n j) := by
        rfl
        done

theorem zeroLenClsEql : ∀ (cl1: Clause 0), ∀ (cl2: Clause 0) ,  (cl1 = cl2) := 
  fun cl1 =>
    fun cl2 =>
      funext (
        fun (x : Fin 0) =>
          match x with 
            | ⟨_, h⟩ => absurd h (notLtZero _)
      )


theorem prependPlusOne{α: Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n):
  prepend n zeroVal fn (plusOne n j) = fn j :=
    let l1 : prepend n zeroVal fn (plusOne n j) = fn (Fin.mk j.val j.isLt) := by rfl
    let l2 :  Fin.mk j.val j.isLt = j := by
      apply Fin.eqOfVeq
      rfl
      done
    let l3 := congrArg fn l2
    Eq.trans l1 l3
  

theorem dropOnePrepend{α : Type}(n : Nat)(zeroVal : α)(fn : (Fin n → α))(j: Fin n) : 
    dropHead n (prepend n zeroVal fn) j = fn j := 
        let dropPlusOne : dropHead n (prepend n zeroVal fn) j = prepend n zeroVal fn (plusOne n j) := by rfl
        Eq.trans dropPlusOne (prependPlusOne n zeroVal fn j)

def deqClause {α : Type}[DecidableEq α] (n: Nat) : (c1 : Fin n → α) → 
                              (c2: Fin n → α) → Decidable (c1 = c2) := 
  match n with
  | 0 => 
    fun c1 c2 => 
      isTrue (funext 
        (fun x => nomatch x))
  | m + 1 => 
    fun c1 c2 =>
      match deqClause _ (dropHead _ c1) (dropHead _ c2) with
      | isTrue h => 
          if c : c1 (⟨0, zeroLtSucc m⟩) = c2 (⟨0, zeroLtSucc m⟩) then
            isTrue 
              (funext fun k =>
                match k with
                | ⟨0, w⟩ => c
                | ⟨j+ 1, w⟩ => 
                  let l1 : dropHead m c1 ⟨j, w⟩ = c1 ⟨j+ 1, w⟩ := by rfl
                  let l2 : dropHead m c2 ⟨j, w⟩ = c2 ⟨j+ 1, w⟩ := by rfl
                  let l3 : dropHead m c1 ⟨j, w⟩ = dropHead m c2 ⟨j, w⟩ := congr h rfl
                  by 
                    rw (Eq.symm l1)
                    apply Eq.symm 
                    rw (Eq.symm l2)
                    exact (Eq.symm l3)
                    done)
          else 
            isFalse (
              fun hyp =>
                let lem : c1 (⟨0, zeroLtSucc m⟩) = c2 (⟨0, zeroLtSucc m⟩) := congr hyp rfl
                c lem
            )
      |isFalse h => 
        isFalse (
          fun hyp => 
            let lem : (dropHead m c1) = (dropHead m c2) := 
              funext (
                fun x =>
                  let l1 : (dropHead m c1) x = c1 (plusOne m x) := rfl
                  let l2 : (dropHead m c2) x = c2 (plusOne m x) := rfl
                  let l3 : c1 (plusOne m x) = c2 (plusOne m x) := congr hyp rfl 
                  by 
                    rw l1
                    rw l3
                    apply Eq.symm
                    exact l2
                    done)
            h lem)

instance {n: Nat}[DecidableEq α] : DecidableEq (Fin n → α) := fun c1 c2 => deqClause _ c1 c2

-- need this as Sigma, Prop and Option don't work together
structure SigmaEqElem{α: Type}{n: Nat}(seq: Fin n → α)(elem: α) where
  index: Fin n 
  equality: seq index = elem

def SigmaEqElem.toProof{α: Type}{n: Nat}{seq: Fin n → α}
  {elem: α}(s : SigmaEqElem (seq) (elem)) :  ∃ (j : Fin n), seq j = elem := 
    ⟨s.index, s.equality⟩ 

structure SigmaPredElem{α: Type}{n: Nat}(seq: Fin n → α)(pred: α → Prop) where
  index: Fin n 
  property: pred (seq index) 

def SigmaPredElem.toProof{α: Type}{n: Nat}{seq: Fin n → α}{pred: α → Prop}
  (s : SigmaPredElem seq pred) : ∃ (j : Fin n), pred (seq j) :=
    ⟨s.index, s.property⟩

structure PiPred{α: Type}{n: Nat}(seq: Fin n → α)(pred: α → Prop) where
  property : (x : Fin n) → pred (seq x)

def PiPred.toProof{α: Type}{n: Nat}{seq: Fin n → α}{pred: α → Prop}
  (p: PiPred seq pred) : ∀ (j : Fin n), pred (seq j) := p.property

def findElem{α: Type}[deq: DecidableEq α]{n: Nat}: 
  (seq: Fin n → α) → (elem: α) →  Option (SigmaEqElem seq elem) :=
    match n with
    | 0 => fun _  => fun _ => none
    | m + 1 => 
      fun fn =>
        fun x =>
          if pf : (fn (Fin.mk 0 (zeroLtSucc m))) =  x then
            let e  := ⟨Fin.mk 0 (zeroLtSucc m), pf⟩
            some (e)
          else
            let pred := findElem (dropHead _ fn) x
            pred.map (fun ⟨j, eql⟩ => 
              let zeroVal := fn (Fin.mk 0 (zeroLtSucc m))
              let l1 := dropPlusOne _ zeroVal j fn
              let l2 : fn (plusOne m j) = x := Eq.trans (Eq.symm l1) eql
              ⟨(plusOne _ j), l2⟩ 
            )

def findPred{α: Type}(pred: α → Prop)[DecidablePred pred]{n: Nat}: 
  (seq: Fin n → α)  →  Option (SigmaPredElem seq pred) :=
    match n with
    | 0 => fun _  => none
    | m + 1 => 
      fun fn =>
        if pf : pred (fn (Fin.mk 0 (zeroLtSucc m))) then
          let e  := ⟨Fin.mk 0 (zeroLtSucc m), pf⟩
          some (e)
        else
          let tail := findPred pred (dropHead _ fn) 
          tail.map (fun ⟨j, eql⟩ => 
            let zeroVal := fn (Fin.mk 0 (zeroLtSucc m))
            let l1 := dropPlusOne _ zeroVal j fn
            let l2  := congrArg pred l1
            let l3 : pred (fn (plusOne m j)) := by
              rw (Eq.symm l2)
              exact eql
              done
            ⟨(plusOne _ j), l3⟩ 
          )

def findSome?{α β : Type}{n: Nat}(f : α → Option β) : (Fin n → α) → Option β :=
    match n with
    | 0 => fun _ => none
    | m + 1 => 
      fun seq => 
        (f (seq ⟨0, zeroLtSucc m⟩)).orElse (
          findSome? f (fun t : Fin m => seq (plusOne _ t))
        ) 
         

def showForAll{α: Type}(pred: α → Prop)[DecidablePred pred]{n: Nat}: 
(seq: Fin n → α)  →  Option (PiPred seq pred) := 
  match n with
  | 0 =>
    fun seq => 
      let pf : (x : Fin 0) → pred (seq x) := fun x => nomatch x  
      some (⟨pf⟩)
  | m + 1 => 
    fun seq =>
      if c : pred (seq (Fin.mk 0 (zeroLtSucc m))) then
        let tail : Fin m → α := dropHead _ seq
        (showForAll pred tail).map (
          fun ⟨ tpf ⟩ =>
            let pf : (j :Fin (m +1)) → pred (seq j) := 
              fun j =>
                match j with 
                | ⟨0, w⟩ => c
                | ⟨i + 1, w⟩ =>
                  let tailWit : i < m := leOfSuccLeSucc w 
                  tpf (⟨i, tailWit⟩)
            ⟨ pf ⟩
        )
      else 
        none

def shiftAt : (n : Nat) →  (k: Nat) → (lt : k < succ n) → 
    Fin n → Fin (n + 1) :=
      fun n k lt =>
        fun ⟨i, w⟩ => 
          ⟨skip k i, (skipPlusOne w)⟩

def shifAtInjective: (n : Nat) →  (k: Nat) → (lt : k < succ n) → 
    (j1 :Fin n) → (j2 : Fin n) → 
      shiftAt n k lt j1 = shiftAt n k  lt j2 → j1 = j2 :=
      fun n k lt ⟨j1, w1⟩ ⟨j2, w2⟩  =>
        fun hyp =>
        let hyp1 : skip k j1 = skip k j2 := congrArg Fin.val hyp
        by
          apply Fin.eqOfVeq
          apply skipInjective k j1 j2
          exact hyp1
          done

theorem seqShiftNatLemma: (l: Nat) → (i : Nat) →   
    (skip (l + 1)  (i + 1)) = (skip  l  i) + 1 := 
      fun l => fun i => rfl



def dropAtShift{α : Type} : (n : Nat) →  
  (k: Nat) → (lt : k < succ n) →  (fn :Fin (Nat.succ n) → α) → 
    (j : Fin n) →  dropAt n k lt fn j = fn (shiftAt n k lt j) := 
    fun n =>
      match n with
        | 0 =>
          fun k =>
            fun lt =>
              fun fn => 
                 fun l => nomatch l
        | m + 1 => 
          fun k =>            
            match k with
            | 0 =>
              fun lt =>
               fun fn =>
                fun ⟨i, w⟩ => by rfl
            | l + 1 => 
              fun lt =>
               fun fn =>
                fun j =>
                  match j with
                  | ⟨0, w⟩ => by rfl
                  | ⟨i + 1, w⟩ =>
                    let predwit : l < m + 1 := leOfSuccLeSucc lt  
                    let tfn := dropHead _ fn
                    let tail := dropAt m l predwit tfn
                    let head := fn (⟨0, zeroLtSucc (m + 1)⟩)
                    let caseFunc := prepend m head tail
                    let unfold1 : dropAt (m + 1) (l +1) lt fn ⟨i + 1, w⟩ =
                      caseFunc ⟨i + 1, w⟩ := by rfl
                    let unfold2 : caseFunc ⟨i + 1, w⟩ = tail ⟨i, w⟩ := by rfl
                    let base : tail ⟨i, w⟩ = 
                                  fn (shiftAt (m + 1) (l + 1) lt ⟨i + 1, w⟩) := 
                                dropAtShift m l predwit tfn ⟨i, w⟩
                    by 
                      rw unfold1
                      rw unfold2
                      rw base
                      done

inductive SectionCase (n: Nat) (k j: Fin (n + 1)) where
  | diagonal : k = j → SectionCase n k j
  | image : (i : Fin n) →  (shiftAt n k.val k.isLt i) = j → SectionCase n k j

instance {n: Nat} {k j: Fin (n + 1)}: Prover (SectionCase n k j) where
  statement := fun s => 
     (k = j) ∨  (∃ i : Fin n, (shiftAt n k.val k.isLt i) = j)
  proof := fun s => 
    match s with
    | SectionCase.diagonal w => Or.inl w
    | SectionCase.image i w => Or.inr ⟨i, w⟩

def shiftIsSection (n: Nat): (k j: Fin (n + 1)) →  
    SectionCase n k j := 
    match n with 
    | 0 => 
      fun k =>
        match k with
        | ⟨0, w⟩ => 
          fun j =>
          match j with
          | ⟨0, w⟩ => SectionCase.diagonal rfl
    | m + 1 => 
      fun k =>
        match k with
        | ⟨0, w⟩ => 
          fun j =>
          match j with
          | ⟨0, wj⟩ => SectionCase.diagonal rfl
          | ⟨i + 1, wj⟩ =>
            let eql : shiftAt (m + 1) 0 w ⟨i, leOfSuccLeSucc wj⟩ = ⟨i + 1, wj⟩ := by rfl 
            SectionCase.image ⟨i, leOfSuccLeSucc wj⟩ eql
        | ⟨l + 1, w⟩ => 
          fun j => 
          match j with
          | ⟨0, wj⟩ =>
            let eql : shiftAt (m + 1) (l + 1) w ⟨0, zeroLtSucc _⟩ = ⟨0, wj⟩ := by rfl 
            SectionCase.image ⟨0, zeroLtSucc _⟩ eql
          | ⟨i + 1, wj⟩ => 
            let base := shiftIsSection m ⟨l, (leOfSuccLeSucc w)⟩ ⟨i, leOfSuccLeSucc wj⟩
            match base with
            | SectionCase.diagonal beql => 
              let beqlv : l = i := congrArg Fin.val beql
              by
                apply SectionCase.diagonal
                apply Fin.eqOfVeq
                apply (congrArg succ)
                exact beqlv
                done
            | SectionCase.image ⟨p, wp⟩  beql => 
              let unfold : shiftAt (m + 1) (l + 1) (succ_lt_succ w) ⟨p + 1, succ_lt_succ wp⟩ =
                plusOne (m + 1) (shiftAt m l w ⟨p, wp⟩) := by rfl
              let p1eql : plusOne (m + 1) ⟨i, leOfSuccLeSucc wj⟩ =  ⟨i + 1, wj⟩ := by rfl
              let eql : shiftAt (m + 1) (l + 1) (succ_lt_succ w) ⟨p + 1, succ_lt_succ wp⟩ =
                ⟨i + 1, wj⟩ := by
                  rw unfold
                  apply Eq.symm
                  rw (Eq.symm p1eql)
                  apply (Eq.symm)
                  exact (congrArg (plusOne (m + 1)) beql)
                  done               
              SectionCase.image ⟨p + 1, succ_lt_succ wp⟩ eql

theorem shiftSkipsEq(n: Nat): (k: Nat) → (lt : k < n + 1)→   
    (j: Fin n) → Not ((shiftAt n k lt j) = ⟨k, lt⟩) := 
    match n with 
    | 0 => 
      fun k =>      
      match k with
      | 0 => 
        fun lt =>
        fun j => nomatch j
      | l + 1 => 
        fun lt =>
          nomatch lt
    | m + 1 => 
      fun k =>
        match k with
        | 0 =>
          fun w =>
          fun ⟨j, wj⟩ =>   
            let unfold : (shiftAt (m + 1) 0 w ⟨j, wj⟩).val = j + 1 := by rfl
            fun hyp =>
              let hypV : (shiftAt (m + 1) 0 w ⟨j, wj⟩).val = 0 := congrArg Fin.val hyp
              let contra : (succ j) = 0 := Eq.trans (Eq.symm unfold) hypV 
              Nat.noConfusion contra
        | l + 1 =>
          fun w => 
          fun j => 
          match j with
          | ⟨0, wj⟩ =>
            let unfold : (shiftAt (m + 1) (l + 1) w ⟨0, wj⟩).val = 0 := by rfl
            fun hyp =>
              let hypV : (shiftAt (m + 1) (l + 1) w ⟨0, wj⟩).val = l + 1 := congrArg Fin.val hyp
              let contra : 0 =  (succ l) := Eq.trans (Eq.symm unfold) hypV 
              Nat.noConfusion contra
          | ⟨i + 1, wj⟩ => 
            let base : Not (shiftAt m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩ = 
              ⟨l, leOfSuccLeSucc w⟩)  := shiftSkipsEq m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩
            fun hyp => 
              let unfold : shiftAt (m + 1) (l + 1) w ⟨i + 1, wj⟩ =
                plusOne (m + 1) (shiftAt m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩) := by rfl
              let unfoldV : (shiftAt (m + 1) (l + 1) w ⟨i + 1, wj⟩).val = 
                (shiftAt m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩).val + 1 := 
                  congrArg Fin.val unfold
              let lem : 
                (shiftAt m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩).val + 1 
                  = l + 1 := by
                    rw (Eq.symm unfoldV )
                    rw (congrArg Fin.val hyp)
                    done
              let contra : shiftAt m l (leOfSuccLeSucc w) ⟨i, leOfSuccLeSucc wj⟩ = 
              ⟨l, leOfSuccLeSucc w⟩ := by 
                apply Fin.eqOfVeq
                injection lem
                assumption
                done
              base (contra)

structure ProvedLift{α : Type}(value : α) (n: Nat)(fn : Fin n →  α) (k j: Fin (n + 1)) where
  result : α
  checkImage : (i : Fin n) → (shiftAt n k.val k.isLt i = j) → result = fn i
  checkFocus : k = j → result = value

def provedLift{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn : Fin n →  α) →  
      (j : Fin (Nat.succ n)) →  ProvedLift value n fn ⟨k, lt⟩ j := 
  fun n k lt fn j =>  
    let switch := shiftIsSection n ⟨k, lt⟩ j
    match switch with
    | SectionCase.diagonal w => 
        let result := value
        let checkFocus : ⟨k, lt⟩ = j → result = value := fun _ => rfl
        let checkImage : (i : Fin n) → (shiftAt n k lt i = j) → result = fn i :=
          fun i =>
            fun hyp =>
            let lem1 := shiftSkipsEq n k lt i
            let lem2 := Eq.trans hyp (Eq.symm w)
            absurd lem2 lem1
        ⟨result, checkImage, checkFocus⟩
    | SectionCase.image i w => 
        let result := fn i
        let checkFocus : ⟨k, lt⟩ = j → result = value := 
          fun hyp => 
            let lem1 := shiftSkipsEq n k lt i
            let lem2 := Eq.trans w (Eq.symm hyp)
            absurd lem2 lem1
        let checkImage : (i : Fin n) → (shiftAt n k lt i = j) → result = fn i := 
          fun i1 =>
            fun hyp =>
              let lem1 := Eq.trans w (Eq.symm hyp)
              let lem2 := shifAtInjective n k lt i i1 lem1
              congrArg fn lem2
        ⟨result, checkImage, checkFocus⟩


def liftAt{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (Fin n →  α) →  (Fin (Nat.succ n) → α) := 
  fun n k lt fn j =>  
    (provedLift value n k lt fn j).result

def liftAtFocus{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn :Fin n →  α) →  
      liftAt value n k lt fn ⟨k, lt⟩ = value :=
    fun n k lt fn  =>  
      (provedLift value n k lt fn ⟨k, lt⟩).checkFocus rfl

def liftAtImage{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn :Fin n →  α) → (i : Fin n) →   
      liftAt value n k lt fn (shiftAt n k lt i) = fn i :=
    fun n k lt fn i =>  
      (provedLift value n k lt fn (shiftAt n k lt i)).checkImage i rfl

def liftDrop{α : Type}: (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn :Fin (n + 1) →  α)  →   
      liftAt (fn ⟨k, lt⟩) n k lt 
        (dropAt n k lt fn)  = fn := 
      fun n k lt fn  =>
      funext (fun j =>
        let switch := shiftIsSection n ⟨k, lt⟩ j
          match switch with
          | SectionCase.diagonal w => 
            let lem :=
              congrArg (liftAt (fn ⟨k, lt⟩) n k lt  (dropAt n k lt fn)) w
            by
              rw (Eq.symm lem)
              apply Eq.symm
              rw Eq.symm (congrArg fn w)
              apply Eq.symm
              apply liftAtFocus 
              done              
          | SectionCase.image i w => 
            let lem :=
              congrArg (liftAt (fn ⟨k, lt⟩) n k lt  (dropAt n k lt fn)) w
              let lem2 := liftAtImage (fn ⟨k, lt⟩) n k lt  (dropAt n k lt fn) i
            by 
              rw (Eq.symm lem)
              apply Eq.symm
              rw Eq.symm (congrArg fn w)
              apply Eq.symm
              rw lem2 
              apply dropAtShift
              done
      )

structure ProvedUpdate{α : Type}(value : α) (n: Nat)(fn : Fin (n + 1) →  α) (k j: Fin (n + 1)) where
  result : α
  check : Not (k = j) → result = fn j
  checkDiag : k = j → result = value

def provedUpdate{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn: Fin (n + 1) →  α)  →  ( j: Fin (Nat.succ n)) → 
        ProvedUpdate value n fn ⟨k, lt⟩ j := 
      fun n k lt fn j =>
      match shiftIsSection n ⟨k, lt⟩ j with
      | SectionCase.diagonal eql =>
        let result := value 
        let check : Not (⟨k, lt⟩ = j) → result = fn j := fun c =>  absurd eql c 
        ⟨result, check, fun _ => rfl⟩
      | SectionCase.image i eql =>
        let lem1 := shiftSkipsEq n k lt i
        let lem : Not (⟨k, lt⟩ = j) := 
          fun hyp =>
            let lem2 := Eq.trans eql (Eq.symm hyp)
            lem1 lem2 
        ⟨fn j, fun _ => rfl, fun c => absurd c lem⟩

def update{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn: Fin (n + 1) →  α)  →  ( j: Fin (Nat.succ n)) → 
        α := 
      fun n k lt fn j => (provedUpdate value n k lt fn j).result

def updateEq{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn: Fin (n + 1) →  α)  →  ( j: Fin (Nat.succ n)) →
      Not (⟨k ,lt⟩ = j) → (update value n k lt fn j) = fn j := 
      fun n k lt fn j w =>
        (provedUpdate value n k lt fn j).check w        

def updateEqDiag{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (fn: Fin (n + 1) →  α)  → 
      (update value n k lt fn ⟨k, lt⟩) = value := 
      fun n k lt fn   =>
        (provedUpdate value n k lt fn ⟨k, lt⟩).checkDiag rfl

-- transpose index j in tail with initial element (actually not used)
def transposeZero{α: Type}{n: Nat} :(j: Nat) → j < n + 1 →  (Fin (n + 2)→ α) → Fin (n + 2) → α := 
  fun j lt seq =>
    let tail := dropHead _ seq 
    let head := seq ⟨0, zeroLtSucc _⟩
    let elem := tail ⟨j, lt⟩
    prepend _ elem (update head n j lt tail)

def transpJ{α: Type}{n: Nat}: (j: Nat) → (lt :j < n + 1) → (seq : Fin (n + 2)→ α) → 
  transposeZero j lt seq ⟨j + 1, succ_lt_succ lt⟩ = seq ⟨0, zeroLtSucc _⟩ := 
    fun j lt seq =>
      let tail := dropHead _ seq 
      let head := seq ⟨0, zeroLtSucc _⟩
      let elem := tail ⟨j, lt⟩
      let lem1 : transposeZero j lt seq ⟨j + 1, succ_lt_succ lt⟩ =
        update head n j lt tail ⟨j, lt⟩ := by rfl
          -- prependPlusOne _ elem (update head n j lt tail) ⟨j, lt⟩
      let lem2 : update head n j lt tail ⟨j, lt⟩ = head := 
        updateEqDiag head n j lt tail
      by
        rw lem1
        rw lem2
        done

def transpNotJ{α: Type}{n: Nat}: (j: Nat) → (lt :j < n + 1) → (seq : Fin (n + 2)→ α) → 
  (i: Nat) → (wi : i < n + 1) → Not (Fin.mk  j lt =Fin.mk i wi) → 
  transposeZero j lt seq ⟨i + 1, succ_lt_succ wi⟩ = seq  ⟨i + 1, succ_lt_succ wi⟩ := 
    fun j lt seq i wi neq =>
      let tail := dropHead _ seq 
      let head := seq ⟨0, zeroLtSucc _⟩
      let elem := tail ⟨j, lt⟩
      let lem1 : transposeZero j lt seq  ⟨i + 1, succ_lt_succ wi⟩ =
        update head n j lt tail ⟨i, wi⟩ := 
          prependPlusOne _ elem (update head n j lt tail) ⟨i, wi⟩
      let lem2  := 
        updateEq head n j lt tail ⟨i, wi⟩ neq
      by
        rw lem1
        rw lem2
        rfl
        done

theorem involuteTrans{α: Type}(n: Nat): (j: Nat) → (lt :j < n + 1) →
  (seq : Fin (n + 2)→ α) → 
    transposeZero j lt (transposeZero j lt seq)  = seq  := 
    fun j lt seq =>
      let tSeq := transposeZero j lt seq
      let transpTail := dropHead _ tSeq
      let tHead := tSeq ⟨0, zeroLtSucc _⟩
      funext (
        fun k => 
        match k with
        | ⟨0, w⟩ => 
          let lem1 : transposeZero j lt (transposeZero j lt seq) ⟨0, w⟩ =
                tSeq ⟨j + 1, succ_lt_succ lt⟩ := by rfl
          let lem2 := dropOnePrepend _ tHead transpTail ⟨j, lt⟩
          by
            rw lem1
            exact (transpJ j lt seq)
            done
        | ⟨l + 1, w⟩ => 
           if c : l = j then
            let lem0 : l +1 = j + 1 := congrArg (. + 1) c
            let lem1 : (⟨l + 1, w⟩ : Fin (n + 2)) = ⟨j + 1, succ_lt_succ lt⟩ := 
              by 
                apply Fin.eqOfVeq
                exact lem0
                done
            let lem2 := congrArg (transposeZero j lt (transposeZero j lt seq)) lem1
            let lem3 := transpJ j lt (transposeZero j lt seq)
            let lem4 : transposeZero j lt seq ⟨0, zeroLtSucc _⟩ =
                          seq ⟨j + 1, succ_lt_succ lt⟩ := by rfl
            by
              rw lem2
              rw lem3
              rw lem4
              apply (congrArg seq)
              apply Fin.eqOfVeq
              exact (Eq.symm lem0)
              done
           else
            let lem0 : Not (Fin.mk j lt = Fin.mk l w) := 
              fun hyp =>
                c (Eq.symm (congrArg Fin.val hyp))
            let lem1 := transpNotJ j lt (transposeZero j lt seq) l w lem0
            let lem2 := transpNotJ j lt seq l w lem0
            by
              rw lem1
              rw lem2
              done
           )

def shiftIsSectionProp (n: Nat): (k j: Fin (n + 1)) →  
     (k = j) ∨ (∃ i : Fin n, (shiftAt n k.val k.isLt i) = j) :=
      fun k j =>  getProof (shiftIsSection n k j)


-- theorems with old style finite sequences


structure ClauseSat{n: Nat}(clause : Clause n)(valuat: Valuat n) where
  coord : Fin n
  witness: varSat (clause coord) (valuat coord)

def clauseSat {n: Nat}(clause : Clause n)(valuat: Valuat n) := 
  ∃ (k : Fin n), varSat (clause k) (valuat k)

instance {n: Nat}(clause : Clause n)(valuat: Valuat n): Prover (ClauseSat clause valuat) where 
  statement := fun cs => ∃ (k : Fin n), varSat (clause k) (valuat k)
  proof := fun cs => ⟨cs.coord, cs.witness⟩


theorem contradictionFalse (n: Nat) : ∀ valuat : Valuat n, Not (clauseSat (contradiction n) valuat) :=
  fun valuat => fun ⟨k, p⟩ => 
    let lem1 : (contradiction n) (k) = none := by rfl
    let lem2 := congrArg varSat lem1
    let lem3 : varSat (contradiction n k) (valuat k) = 
                varSat none (valuat k) := congr lem2 rfl
    let lem4 : (varSat none (valuat k)) = (none = some (valuat k)) := rfl
    let lem5 : (none = some (valuat k)) := by
      rw (Eq.symm lem4)
      rw lem4
      assumption
      done 
    Option.noConfusion lem5


def isUnit{n: Nat}(k: Fin (n + 1))(b: Bool)(cl: Clause (n + 1)) :=
  (cl k = some b) &&
  ((dropAt n k.val k.isLt cl) =  contradiction n)



def unitClause(n : Nat)(b : Bool)(k : Fin (n + 1)):   Clause (n + 1):=
  liftAt (some b) n k.val k.isLt (contradiction n) 

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Fin (n + 1)
  parity: Bool
  equality : clause = unitClause n parity index

def clauseUnit{n: Nat}(clause: Clause (n + 1)) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) → Option (IsUnitClause clause) := 
    fun k =>
      match deqClause _ clause  (unitClause n true k) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k true pf 
        some (cl)
      | isFalse _ => 
        match deqClause _ clause  (unitClause n false k) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k false pf 
        some (cl)
      | isFalse _ => none  
  let seq : Fin (n + 1) → Fin (n + 1) := fun x => x
  findSome? f seq

def someUnitClause {l : Nat} : (n : Nat) →  (clauses : Fin l → (Clause (n + 1))) →  
  Option (Σ k : Fin l, IsUnitClause (clauses k))  := 
    match l with 
    | 0 => fun _ _ =>  none
    | m + 1 => 
      fun n cls =>
        match clauseUnit (cls ⟨0, zeroLtSucc m⟩) with
        | some u => some ⟨⟨0, zeroLtSucc m⟩, u⟩ 
        | none => 
          let tcls := dropHead _ cls
          let tail := someUnitClause n tcls
          match tail with
          | some ⟨⟨i, w⟩, u⟩ => 
            some ⟨⟨i + 1, leOfSuccLeSucc w⟩, u⟩
          | none => none

structure HasPureVar{dom n : Nat}(clauses : Fin dom → Clause n) where
  index : Fin n
  parity : Bool
  evidence : (k : Fin dom) → (clauses k index = none) ∨  (clauses k index = some parity)

structure IsPureVar{dom n : Nat}(clauses : Fin dom → Clause n)
                      (index: Fin n)(parity : Bool) where
  evidence : (k : Fin dom) → (clauses k index = none) ∨  (clauses k index = some parity)

def varIsPure{n : Nat}(index: Fin n)(parity : Bool) : 
  (dom: Nat) →  (clauses : Fin dom → Clause n) → Option (IsPureVar clauses index parity) :=
  fun dom =>
  match dom with
  | 0 => 
    fun clauses =>
      let evidence : (k : Fin 0) → 
         (clauses k index = none) ∨ (clauses k index = some parity) := 
          fun k => nomatch k
      some ⟨evidence⟩
  | m + 1 => 
      fun clauses =>
        let head := clauses ⟨0, zeroLtSucc _⟩ index
        if c :  (head = none) ∨ (head = some parity) then
          let tail : Fin m → Clause n := dropHead _ clauses
          (varIsPure index parity _ tail).map (
            fun ⟨ tpf ⟩ =>
              let pf : (j :Fin (m +1)) → 
                (clauses j index = none) ∨ (clauses j index = some parity) := 
                fun j =>
                  match j with 
                  | ⟨0, w⟩ => c
                  | ⟨i + 1, w⟩ =>
                    let tailWit : i < m := leOfSuccLeSucc w 
                    tpf (⟨i, tailWit⟩)
              ⟨ pf ⟩
          )
        else none

def findPureAux{n : Nat} : (dom: Nat) →  (clauses : Fin dom → Clause (n +1)) → 
  (ub: Nat) → (lt : ub < n + 1) → 
      Option (HasPureVar clauses) :=
      fun dom clauses ub => 
        match ub with
        | 0 =>
          fun lt =>
           ((varIsPure ⟨0, lt⟩ true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk ⟨0, lt⟩ true evidence
              )).orElse (
                (varIsPure ⟨0, lt⟩ false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk ⟨0, lt⟩ false evidence
              )
              )
        | l + 1 =>
          fun lt =>
            ((findPureAux dom clauses l (leStep lt)).orElse (              
              (varIsPure ⟨l, leStep lt⟩ true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk ⟨l, leStep lt⟩ true evidence
              )
              )).orElse (              
              (varIsPure ⟨l, leStep lt⟩ false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk ⟨l, leStep lt⟩ false evidence
              )
              )
            
def hasPure{n : Nat}(dom: Nat)(clauses : Fin dom → Clause (n +1)) 
            (ub: Nat)(lt : ub < n + 1) : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.leRefl _)
