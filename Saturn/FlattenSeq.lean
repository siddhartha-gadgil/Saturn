import Saturn.FinSeq
import Saturn.Clause 
open Nat

-- Unused code due to change of approach.


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



structure FlattenSeq{α : Type}{n: Nat}(lengths : (j : Nat) → j < n → Nat)
                                    (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) where
          length : Nat
          seq : FinSeq length α
          forward: (j : Nat) → (jw : j < length) → Σ (i : Nat), (iw : i < n) → 
                      ElemInSeq (seqs i iw) (seq j jw)
          reverse: (i : Nat) → (iw : i < n) → (j : Nat) → (jw : j < lengths i iw) → 
                      ElemInSeq seq (seqs i iw j jw)

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
                            let lem : i < n ∨ (i = n ∧ 
                              j < lengths n (Nat.leRefl (succ n))) :=
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
                              let q1 : i = gp := q.left
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
                                  
                                let goal : seqs gp gpBound k maxBound = seqs i iw j jw := 
                                    match i, q1, j, mc, iw, jw with  
                                    | .(gp), rfl, .(k), rfl, iww, jww => rfl 
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

def partFlatOrigin{α : Type}{n: Nat} : (lengths : (j : Nat) → j < n → Nat) → 
                          (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) → 
                          (gpBound : 0 < n) → 
                            (PartialFlattenSeq lengths seqs 0 gpBound 0 (Nat.zeroLe _)) :=
              match n with
              | 0 => fun _ _ w => nomatch w
              | m + 1 =>
                fun lengths seqs gpBound =>
                  let seqN : FinSeq 0 α := FinSeq.empty
                  let forwardN : (j : Nat) → (jw : j < 0) → Σ (i : Nat), (iw : i < m + 1) → 
                      ElemInSeq (seqs i iw) (seqN j jw) := fun j jw => nomatch jw 
                  let reverseN : (i : Nat) → (iw : i < m + 1) → (j : Nat) → (jw : j < lengths i iw) → 
                    i < 0 ∨ (i = 0 ∧ j < 0)  → 
                      ElemInSeq seqN (seqs i iw j jw) :=   
                        fun i iw j jw p => 
                          let q : ¬(i < 0 ∨ i = 0 ∧ j < 0) := 
                            match p with
                            | Or.inl p1 => nomatch p1
                            | Or.inr p2 => nomatch p2
                          absurd p q 
                  ⟨0, seqN, forwardN, reverseN⟩

def partFlatZeroBound{α : Type}{n: Nat}(lengths : (j : Nat) → j < n + 1 → Nat)
                                    (seqs : (j : Nat) → (jw : j < n + 1) → FinSeq (lengths j jw) α) :                
            (gp : Nat) → (gpBound : gp < n + 1) → 
                            PartialFlattenSeq lengths seqs gp gpBound 0 (Nat.zeroLe _) :=
              fun gp => 
                match gp with
                | 0 => by 
                          intro gpBound
                          apply partFlatOrigin
                          done
                | l + 1 => 
                  fun gpBound => 
                    let base := partFlatZeroBound lengths seqs l (leStep gpBound)
                    let pfs := partFlatInGp lengths seqs l (leStep gpBound) base
                                  (lengths l (leStep gpBound)) (Nat.leRefl _)
                    let reverseN : (i : Nat) → (iw : i < (n +1)) → 
                        (j : Nat) → (jw : j < lengths i iw) → 
                        i < l + 1 ∨ (i = l + 1 ∧ j < 0)  →
                        ElemInSeq pfs.seq (seqs i iw j jw) := 
                          fun i iw j jw p0 =>
                            let lem : i < l ∨ (i = l ∧ 
                              j < lengths l (leStep gpBound)) := 
                               match p0 with
                               | Or.inr pw => 
                                      let w := pw.right
                                      nomatch w
                               | Or.inl pw => 
                                let switch := Nat.eqOrLtOfLe pw
                                match switch with 
                                | Or.inl p => 
                                  let p1 : i = l := by
                                    injection p
                                    assumption
                                  let lem : lengths l (leStep gpBound) =
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

def flattenSeq{α : Type}{n: Nat} : 
    (lengths : (j : Nat) → j < n → Nat) → 
      (seqs : (j : Nat) → (jw : j < n) → FinSeq (lengths j jw) α) → 
      FlattenSeq lengths seqs := 
        match n with
        | 0 => fun _ _ => ⟨0, FinSeq.empty, 
                            fun j jw => nomatch jw, 
                            fun i iw => nomatch iw⟩ 
        | m + 1 => 
          fun lengths seqs => 
            let base := partFlatZeroBound lengths seqs m (Nat.leRefl _) 
            let pfs := partFlatInGp lengths seqs m (Nat.leRefl _) base 
                          (lengths m (Nat.leRefl _)) (Nat.leRefl _)
            partToFullFlatten lengths seqs pfs

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
