import Saturn.Basic
open Nat

class Prover(α: Type) where
  statement : (x : α) → Prop
  proof : (x : α) → statement x

-- theorems about finite sequences

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

def deqClause {α : Type}[DecidableEq α] (n: Nat) : (c1 : Fin n → α) → (c2: Fin n → α) → Decidable (c1 = c2) := 
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

def shiftAtNat : Nat → Nat → Nat :=
    fun k =>
      match k with
      | 0 => 
          fun i =>
            i + 1
      | l+1 => 
          fun j =>
            match j with
            | 0 => 0
            | i + 1 => 
                (shiftAtNat l i) + 1

theorem shiftBound: (k j: Nat) →  shiftAtNat k j < j + 2 :=
    fun k =>
      match k with
      | 0 => 
          fun i =>
            let unfold : shiftAtNat 0 i = i + 1 := by rfl
            by
              rw unfold
              apply Nat.leRefl
              done
      | l+1 => 
          fun j =>
            match j with
            | 0 => 
              let isZero : shiftAtNat (l + 1) 0 = 0 := by rfl
              by
                rw isZero
                exact zeroLtSucc 0
                done 
            | i + 1 => 
              let  unfold : shiftAtNat (l + 1) (i + 1) = (shiftAtNat  l  i) + 1 := by rfl
              let base : shiftAtNat l i < i + 2  :=  shiftBound l i
              let baseP1 : succ (shiftAtNat l i) < succ (i + 2) := succ_lt_succ base
              by
                rw unfold
                exact baseP1
                done

def shiftInheritBound (n k j : Nat) : j < n → shiftAtNat k j < n + 1 := 
  fun h =>
    Nat.leTrans (shiftBound k j) h

def shiftAt : (n : Nat) →  (k: Nat) → (lt : k < succ n) → 
    Fin n → Fin (n + 1) :=
      fun n k lt =>
        fun ⟨i, w⟩ => 
          ⟨shiftAtNat k i, (shiftInheritBound n k i w)⟩

theorem seqShiftNatLemma: (l: Nat) → (i : Nat) →   
    (shiftAtNat (l + 1)  (i + 1)) = (shiftAtNat  l  i) + 1 := 
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

def getProof{α : Type}[pr : Prover α](x: α) := pr.proof x 

def getProp{α : Type}[pr : Prover α](x: α) : Prop := pr.statement x 

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

def liftAtSwitch{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (Fin n →  α) →  
      (j : Fin (Nat.succ n)) → SectionCase n ⟨k, lt⟩ j → α := 
  fun n k lt fn j switch =>  
    match switch with
    | SectionCase.diagonal _ => value
    | SectionCase.image i _ => fn i

def liftAt{α : Type}(value: α) : (n : Nat) →  (k: Nat) → 
    (lt : k < succ n) → (Fin n →  α) →  (Fin (Nat.succ n) → α) := 
  fun n k lt fn j =>  
    let switch := shiftIsSection n ⟨k, lt⟩ j
    match switch with
    | SectionCase.diagonal _ => value
    | SectionCase.image i _ => fn i

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

