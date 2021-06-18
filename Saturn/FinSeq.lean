import Saturn.Basic
open Nat

macro_rules
  | `(scowl) => `(sorry)

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

def skipPlusOne {n k j : Nat} : j < n → skip k j < n + 1 := 
  fun h =>
    Nat.leTrans (skipBound k j) h


def FinSeq (n: Nat) (α : Type) : Type := (k : Nat) → k < n → α

def FinSeq.cons {α : Type}{n: Nat}(head : α)(tail : FinSeq n α) : FinSeq (n + 1) α :=
  fun k =>
  match k with
  | 0 => fun _ => head
  | j + 1 => 
    fun w =>
      tail j (leOfSuccLeSucc w)

infixr:66 ":::" => FinSeq.cons

def tail {α : Type}{n: Nat}(seq : FinSeq (n + 1) α): FinSeq n α := 
  fun k w =>
      seq (k + 1) (succ_lt_succ w)

def head{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): α :=
  seq 0 (zeroLtSucc _)

theorem headTail{α : Type}{n: Nat}(seq : FinSeq (n + 1) α): 
      (head seq) ::: (tail seq) = seq := 
        funext (
          fun k => 
            match k with
            | 0 => by rfl 
            | i + 1 => by rfl
        )

def delete{α : Type}{n: Nat}(k : Nat) (kw : k < (n + 1)) (seq : FinSeq (n + 1) α): FinSeq n α := 
  fun j w =>
    seq (skip k j) (skipPlusOne w)

structure ProvedInsert{α : Type}{n: Nat}(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n)(j: Nat) (jw : j < n + 1) where
  result : α
  checkImage : (i : Nat) → (iw : i < n) → (skip  k i = j) → result = seq i iw
  checkFocus : j= k → result = value

def provedInsert{α : Type}{n: Nat}(value : α) (seq : FinSeq n α)
                (k : Nat)(kw : k < n)(j: Nat) (jw : j < n + 1) : 
                  ProvedInsert value seq k kw j jw := 
          match skipImageCase k j with
          | SkipImageCase.diag eqn => 
            let result := value
            sorry
          | SkipImageCase.image i eqn => sorry

class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 


-- theorems about old style finite sequences 

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

-- More specific to SAT

def varSat (clVal: Option Bool)(sectVal : Bool) : Prop := clVal = some sectVal

structure ClauseSat{n: Nat}(clause : Clause n)(sect: Sect n) where
  coord : Fin n
  witness: varSat (clause coord) (sect coord)

def clauseSat {n: Nat}(clause : Clause n)(sect: Sect n) := 
  ∃ (k : Fin n), varSat (clause k) (sect k)

instance {n: Nat}(clause : Clause n)(sect: Sect n): Prover (ClauseSat clause sect) where 
  statement := fun cs => ∃ (k : Fin n), varSat (clause k) (sect k)
  proof := fun cs => ⟨cs.coord, cs.witness⟩


theorem contradictionFalse (n: Nat) : ∀ sect : Sect n, Not (clauseSat (contradiction n) sect) :=
  fun sect => fun ⟨k, p⟩ => 
    let lem1 : (contradiction n) (k) = none := by rfl
    let lem2 := congrArg varSat lem1
    let lem3 : varSat (contradiction n k) (sect k) = 
                varSat none (sect k) := congr lem2 rfl
    let lem4 : (varSat none (sect k)) = (none = some (sect k)) := rfl
    let lem5 : (none = some (sect k)) := by
      rw (Eq.symm lem4)
      rw lem4
      assumption
      done 
    Option.noConfusion lem5


def isUnit{n: Nat}(k: Fin (n + 1))(b: Bool)(cl: Clause (n + 1)) :=
  (cl k = some b) &&
  ((dropAt n k.val k.isLt cl) =  contradiction n)

inductive SectionCase (n: Nat) (k j: Fin (n + 1)) where
  | diagonal : k = j → SectionCase n k j
  | image : (i : Fin n) →  (shiftAt n k.val k.isLt i) = j → SectionCase n k j

instance {n: Nat} {k j: Fin (n + 1)}: Prover (SectionCase n k j) where
  statement := fun s => 
    Or (k = j) (∃ i : Fin n, (shiftAt n k.val k.isLt i) = j)
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
    Or (k = j) (∃ i : Fin n, (shiftAt n k.val k.isLt i) = j) :=
      fun k j =>  getProof (shiftIsSection n k j)

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
  evidence : (k : Fin dom) → Or (clauses k index = none) (clauses k index = some parity)

structure IsPureVar{dom n : Nat}(clauses : Fin dom → Clause n)
                      (index: Fin n)(parity : Bool) where
  evidence : (k : Fin dom) → Or (clauses k index = none) (clauses k index = some parity)

def varIsPure{n : Nat}(index: Fin n)(parity : Bool) : 
  (dom: Nat) →  (clauses : Fin dom → Clause n) → Option (IsPureVar clauses index parity) :=
  fun dom =>
  match dom with
  | 0 => 
    fun clauses =>
      let evidence : (k : Fin 0) → 
        Or (clauses k index = none) (clauses k index = some parity) := 
          fun k => nomatch k
      some ⟨evidence⟩
  | m + 1 => 
      fun clauses =>
        let head := clauses ⟨0, zeroLtSucc _⟩ index
        if c : Or (head = none) (head = some parity) then
          let tail : Fin m → Clause n := dropHead _ clauses
          (varIsPure index parity _ tail).map (
            fun ⟨ tpf ⟩ =>
              let pf : (j :Fin (m +1)) → 
                Or (clauses j index = none) (clauses j index = some parity) := 
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
