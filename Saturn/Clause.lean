import Saturn.FinSeq
open Nat

def Clause(n : Nat) : Type := FinSeq n (Option Bool)

def Valuation(n: Nat) : Type := FinSeq n  Bool

structure ClauseSat{n: Nat}(clause : Clause n)(valuation: Valuation n) where
  coord : Nat
  bound : coord < n  
  witness: varSat (clause coord bound) (valuation coord bound)

def clauseSat {n: Nat}(clause : Clause n)(valuation: Valuation n) := 
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuation k b)

instance {n: Nat}(clause : Clause n)(valuation: Valuation n): Prover (ClauseSat clause valuation) where 
  statement := fun cs => ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuation k b)
  proof := fun cs => ⟨cs.coord, ⟨cs.bound, cs.witness⟩⟩

def contradiction(n: Nat) : Clause n :=
  fun _ _ => none

theorem contradictionFalse (n: Nat) : ∀ valuation : Valuation n, Not (clauseSat (contradiction n) valuation) :=
  fun valuation => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : (contradiction n) k b = none := by rfl
    let lem2 := congrArg varSat lem1
    let lem3 : varSat (contradiction n k b) (valuation k b) = 
                varSat none (valuation k b) := congr lem2 rfl
    let lem4 : (varSat none (valuation k b)) = (none = some (valuation k b)) := rfl
    let lem5 : (none = some (valuation k b)) := by
      rw (Eq.symm lem4)
      rw lem4
      assumption
      done 
    Option.noConfusion lem5

theorem contradictionInsNone{n : Nat} (focus: Nat)(focusLt : focus < n + 1) :
      insert none n focus focusLt (contradiction n) =
                            contradiction (n + 1) :=
      let lem0 : (j: Nat) → (jw : j < n + 1) →  
            insert none n focus focusLt (contradiction n) j jw  =
                      contradiction (n + 1) j jw := 
                      fun j jw =>
                      let lem0 : contradiction (n + 1) j jw = none := by rfl
                      match skipImageCase focus j with
                      | SkipImageCase.diag eqn => 
                        match focus, eqn, focusLt with
                        | .(j), rfl, .(jw) =>
                          by
                            apply insertAtFocus 
                            done                                
                      | SkipImageCase.image i eqn => 
                        let iw := skipPreImageBound focusLt jw eqn
                        match j, eqn, jw, lem0 with
                        | .(skip focus i), rfl, .(skipPlusOne iw), lem1 =>  
                          by
                            rw lem1
                            apply insertAtImage
                            exact iw
                            done                               
                 by
                    apply funext
                    intro j
                    apply funext
                    intro jw
                    apply lem0
                    done



def varContains (v1 v2 : Option Bool) : Prop :=
  ∀ b : Bool, v2 = some b → v1  = some b

infix:65 "≥" => varContains

def varDomDecide : (v1 : Option Bool) → (v2 : Option Bool) → Decidable (v1 ≥  v2) :=
  fun v1 v2 =>
  match v2 with 
  | none => 
     let lem : v1 ≥  none := 
      fun b =>
        fun hyp =>
          Option.noConfusion hyp
     isTrue lem
  | some b2 => 
    match v1  with
    | none => 
      let lem : Not (none ≥  (some b2)) := 
         fun hyp => 
          Option.noConfusion (hyp b2 rfl)
      isFalse lem
    | some b1 => 
          if c : b1 = b2 then 
            isTrue (fun b => 
                      fun hyp =>
                       by
                        rw c
                        exact hyp
                        done)
          else 
            isFalse (
              fun hyp =>
                  let lem1 := hyp b2 rfl
                  let lem2 : b1 = b2 := by
                      injection lem1
                      assumption
                      done
                  c (lem2) 
            )



def contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, ∀ b : Bool, cl2 k kw = some b → cl1 k kw = some b

def contains.self{n: Nat} (cl : Clause n) : contains cl cl :=
  fun k kw b hyp => hyp

infix:65 " ⊇  " => contains

def containsBeyond(cl1 cl2 : Clause n)(m: Nat) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, m ≤ k →  ∀ b : Bool, cl2 k kw = some b → cl1 k kw = some b

theorem containsImpliesContainsBeyond {n: Nat} (cl1 cl2 : Clause n) (m: Nat) :
  contains cl1 cl2 → containsBeyond cl1 cl2 m := by
    intro h
    intro k
    intro kw
    intro ineq
    intro b
    exact h k kw b
    done
  
theorem containsBeyondZero {n: Nat} (cl1 cl2 : Clause n) :
  containsBeyond cl1 cl2 0 → contains cl1 cl2 := by
    intro h
    intro k
    intro kw
    intro b
    exact h k kw (Nat.zeroLe _) b
    done

def containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊇  cl2 → (valuation : Valuation n) → ClauseSat cl2 valuation → ClauseSat cl1 valuation :=
    fun dom valuation  =>
      fun ⟨j, jw, vs⟩ =>
        let lem0 :  cl2 j jw = some (valuation j jw) := vs 
        let lem1 := dom j jw (valuation j jw) lem0
        ⟨j, jw, lem1⟩

def containsPrepend{n: Nat}(v1 v2 : Option Bool)(cl1 cl2 : Clause n) :
          v1 ≥  v2 → cl1 ⊇  cl2 → 
                (v1 +: cl1) ⊇ (v2 +: cl2) := 
           fun hyp1 hyp2 =>
            fun k =>
            match k with
            | 0 => fun w b =>
              fun hb => 
                hyp1 b hb
            | j + 1  =>  
              fun  kw b =>
                fun hb =>
                  hyp2 j  (leOfSuccLeSucc kw) b hb

def containsTail{n: Nat} (cl1 cl2 : Clause (n + 1)) :
        cl1 ⊇  cl2 → (tail cl1) ⊇ (tail cl2) :=
        fun hyp =>
          fun k w b =>
            fun dHyp =>
              hyp (k + 1) (succ_lt_succ w) b dHyp

def containsRefl{n: Nat} (cl : Clause n) :   
  cl ⊇ cl :=
    fun k w b => 
      fun hyp =>
        hyp

def containsTrans{n: Nat} (cl1 cl2 cl3 : Clause n) :
        cl1 ⊇  cl2 → cl2 ⊇ cl3 →  cl1 ⊇ cl3 :=
        fun hyp1 hyp2 => 
          fun k w b =>
            fun dHyp =>
              by
                apply hyp1
                apply hyp2
                apply dHyp
                done

#check Nat.eqOrLtOfLe
#check Nat.ltIrrefl

def containsBeyondVacuous{n: Nat} (cl1 cl2 : Clause n)(m: Nat) :
    (n ≤ m) → containsBeyond cl1 cl2 m := by
      intro h
      intro k
      intro kw
      intro ineq
      let inq := Nat.leTrans h ineq
      let inq2 := Nat.ltOfLtOfLe kw inq
      exact (False.elim (Nat.ltIrrefl k inq2))
      done

def decideContainsRec{n: Nat} (cl1 cl2 : Clause n) :
        (m: Nat) → Decidable (containsBeyond cl1 cl2 m) → Decidable (contains cl1 cl2) :=
        fun m dContainsBeyond => 
          match m, dContainsBeyond with
          | m, isFalse contra => isFalse (
              by
                intro hyp
                let h := containsImpliesContainsBeyond cl1 cl2 m hyp
                exact contra h
                done)
          | 0, isTrue pf => isTrue (containsBeyondZero cl1 cl2 pf)
          | l + 1, isTrue pf => 
            if lw : l < n then
              match varDomDecide (cl1 l lw) (cl2 l lw) with
              | isTrue pfHead => 
                  let accum: Decidable (containsBeyond cl1 cl2 l) := 
                    isTrue (
                      by
                        intro k 
                        intro kw
                        intro ineq
                        intro b
                        cases Nat.eqOrLtOfLe ineq with
                        | inl eql =>
                          let lem0 := pfHead b
                          let lem1 : cl1 l lw = cl1 k kw := by
                            apply witnessIndependent
                            exact eql
                            done
                          let lem2 : cl2 l lw = cl2 k kw := by
                            apply witnessIndependent
                            exact eql
                          rw ← lem1
                          rw ← lem2
                          exact lem0
                          done
                        | inr l2 => 
                          exact pf k kw l2 b
                          done                      
                    )
                  decideContainsRec cl1 cl2 l accum
              | isFalse contra => isFalse (fun hyp =>
                            contra ( 
                              fun b => 
                                hyp l lw b 
                              )                           
                              )
            else
              let overshoot : n ≤ l := by
                cases Nat.ltOrGe l n with
                | inl l1 => exact absurd l1 lw
                | inr l2 => exact l2
              let accum: Decidable (containsBeyond cl1 cl2 l) := 
                isTrue (containsBeyondVacuous cl1 cl2 l overshoot)
              decideContainsRec cl1 cl2 l accum


def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊇   cl2) :=
    fun cl1 cl2 => decideContainsRec cl1 cl2 n 
        (isTrue (containsBeyondVacuous cl1 cl2 n (Nat.leRefl _)))
    -- match n with
    -- | 0 => 
    --     fun cl1 cl2 => isTrue (fun i iw => nomatch iw)
    -- | m + 1 => 
    --   fun cl1 cl2 =>
    --   match decideContains m (tail cl1) (tail cl2) with
    --   | isFalse contra =>
    --       isFalse (fun hyp =>
    --                   contra (containsTail cl1 cl2 hyp))
    --   | isTrue pfTail =>
    --       match varDomDecide (cl1 0 (zeroLtSucc _)) (cl2 0 (zeroLtSucc _)) with
    --       | isTrue pfHead =>
    --           let lem0 := 
    --             (containsPrepend (cl1 0 (zeroLtSucc _)) (cl2 0 (zeroLtSucc _)) 
    --                 (tail cl1) (tail cl2) pfHead) pfTail 
    --           let lem1b : (cl1 0 (zeroLtSucc _)) +:  (tail cl1)  = cl1  := 
    --             funext (fun j =>
    --                       match j with
    --                       | 0 => funext (fun jw => rfl)
    --                       | i + 1 => funext (fun jw => rfl)
    --                       )
    --           let lem2b : (cl2 0 (zeroLtSucc _)) +:  (tail cl2)  = cl2  := 
    --             funext (fun j =>
    --                       match j with
    --                       | 0 => funext (fun jw => rfl)
    --                       | i + 1 => funext (fun jw => rfl)
    --                       )
    --           let lem : cl1 ⊇   cl2 := by
    --             rw (Eq.symm lem1b)
    --             rw (Eq.symm lem2b)
    --             exact lem0
    --             done
    --           isTrue (
    --             lem
    --           )
    --       | isFalse contra => 
    --         isFalse (fun hyp =>
    --                     contra ( 
    --                       fun b => 
    --                          hyp 0 (zeroLtSucc _) b 
    --                       )                           
    --                       )


instance {n: Nat}{cl: Clause n} : DecidablePred (contains cl) :=
  decideContains n cl

def subClause?{l n: Nat}(cl : Clause n)(seq : FinSeq l (Clause n)) :
                    Option (ElemSeqPred seq (contains cl)) := 
              find? (contains cl) seq

structure Containment{dom n : Nat}(base: FinSeq dom (Clause n)) where
    codom: Nat
    imageSeq : FinSeq codom (Clause n)
    forward : (j : Nat) → (jw : j < dom) → ElemSeqPred imageSeq (contains (base j jw))
    reverse : (j : Nat) → (jw : j < codom) → ElemInSeq base (imageSeq j jw) 

def Containment.identity{dom n : Nat}(base: FinSeq dom (Clause n)) : Containment base :=
    ⟨dom, base, fun j jw => ⟨j, jw, contains.self (base j jw)⟩, 
          fun j jw => ⟨j, jw, rfl⟩⟩

def prependContainment{dom n : Nat}{base: FinSeq dom (Clause n)}(pred: Containment base)
        (cl : Clause n) : Containment (cl +: base) := 
            match subClause? cl (pred.imageSeq) with
            | none =>
              let codomN := pred.codom + 1
              let imageSeqN := cl +: (pred.imageSeq)
              let domN := dom + 1
              let baseN := cl +: base
              let forwardN : (j : Nat) → (jw : j < domN) → 
                  ElemSeqPred imageSeqN (contains (baseN j jw)) := 
                  fun j => 
                  match j with 
                  | 0 => fun jw => 
                    ⟨0, zeroLtSucc _, containsRefl cl⟩
                  | i + 1 =>
                    fun jw => 
                    let iw := leOfSuccLeSucc jw 
                    let ⟨ind, bd, ctn⟩ := pred.forward i iw
                    ⟨ ind + 1, succ_lt_succ bd, by 
                          exact ctn
                          done⟩
              let reverseN : (j : Nat) → (jw : j < codomN) → 
                  ElemInSeq baseN (imageSeqN j jw) := 
                  fun j => 
                  match j with 
                  | 0 => fun jw => 
                    ⟨0, zeroLtSucc _, rfl⟩
                  | i + 1 =>
                    fun jw => 
                    let iw := leOfSuccLeSucc jw 
                    let ⟨ind, bd, ctn⟩ := pred.reverse i iw
                    ⟨ ind + 1, succ_lt_succ bd, by 
                          exact ctn
                          done⟩
              ⟨codomN, imageSeqN, forwardN, reverseN⟩
            | some ⟨zi, zb, zc⟩ => 
              let codomN := pred.codom
              let imageSeqN := pred.imageSeq
              let domN := dom + 1
              let baseN := cl +: base
              let forwardN : (j : Nat) → (jw : j < domN) → 
                  ElemSeqPred imageSeqN (contains (baseN j jw)) := 
                  fun j => 
                  match j with 
                  | 0 => fun jw => 
                    ⟨zi, zb, zc⟩
                  | i + 1 =>
                    fun jw => 
                    let iw := leOfSuccLeSucc jw 
                    let ⟨ind, bd, ctn⟩ := pred.forward i iw
                    ⟨ ind, bd, by 
                          exact ctn
                          done⟩
              let reverseN : (j : Nat) → (jw : j < codomN) → 
                  ElemInSeq baseN (imageSeqN j jw) := 
                  fun i =>
                    fun iw => 
                    let ⟨ind, bd, ctn⟩ := pred.reverse i iw
                    ⟨ ind + 1, succ_lt_succ bd, by 
                          exact ctn
                          done⟩
              ⟨codomN, imageSeqN, forwardN, reverseN⟩

def initialContainment{dom n : Nat}: (clauses : FinSeq dom (Clause n)) → 
                              Containment clauses := 
                    match dom with
                    |0 => fun _ => 
                      ⟨0, FinSeq.empty, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => 
                        fun clauses =>
                        let ht := 
                          prependContainment (initialContainment (tail clauses)) (head clauses)
                        Eq.mp (congrArg Containment (headTail clauses)) ht

def simplifyNonEmptyContainment{d n : Nat}: (cursorBound : Nat) →  
      (base : FinSeq (d + 1) (Clause n)) → 
      Containment (base) → Containment (base) := 
      fun cursorBound =>
      match cursorBound with
      | 0 => fun _ => id
      | k + 1 =>
        fun base contn =>
          let ⟨j, (ineq : j < contn.codom), _⟩ := contn.forward 0 (zeroLtSucc _)      
          let neZero : Not (0 = contn.codom) := fun hyp => 
          let l0 : j < 0 := by
            rw hyp
            exact ineq
            done
         Nat.notLtZero k l0
        let ⟨l, leqn⟩ := posSucc contn.codom neZero
        match contn.codom, leqn, contn.imageSeq, contn.forward, contn.reverse with
        | .(l + 1), rfl, imageSeq, forward, reverse =>
         if lt : k < (l + 1) then
          let focus := imageSeq k lt
          let rest := delete k lt imageSeq
          match subClause? focus rest with 
          | none => 
            simplifyNonEmptyContainment k base 
               ⟨l + 1, imageSeq, forward, reverse⟩
          | some ⟨zi, zb, zc⟩ => 
            let codomN := l
            let imageSeqN := rest
            let domN := d + 1
            let forwardN : (j : Nat) → (jw : j < domN) → 
                  ElemSeqPred imageSeqN (contains (base j jw)) := 
                  fun j jw => 
                    let ⟨i, iw , ict⟩ := forward j jw
                    match skipImageCase k i with
                    | SkipImageCase.diag eqn => 
                        let lem1 : imageSeq i iw = imageSeq k lt := by
                              apply witnessIndependent
                              apply eqn
                              done
                        let lem2 : imageSeq i iw ⊇ imageSeqN zi zb := by
                              rw lem1 
                              exact zc
                              done    
                        ⟨zi, zb, containsTrans _ _ _ ict lem2⟩
                    | SkipImageCase.image ii eqn => 
                      let iiw := skipPreImageBound lt iw eqn
                      let lem1 : imageSeqN ii iiw = imageSeq (skip k ii) (skipPlusOne iiw)  := by rfl
                      let lem2 : imageSeq (skip k ii) (skipPlusOne iiw) = imageSeq i iw := by
                                      apply witnessIndependent
                                      apply eqn
                                      done 
                      ⟨ii, iiw, by 
                                rw lem1
                                rw lem2
                                exact ict
                                done⟩
            let reverseN : (j : Nat) → (jw : j < codomN) → 
                  ElemInSeq base (imageSeqN j jw) := 
                  fun i =>
                    fun iw => 
                      let ⟨ind, bd, eqn⟩ := reverse (skip k i) (skipPlusOne iw)
                      ⟨ind, bd, by 
                          exact eqn
                          done⟩
            let step := ⟨codomN, imageSeqN, forwardN, reverseN⟩
            simplifyNonEmptyContainment k base step
        else ⟨l + 1, imageSeq, forward, reverse⟩

def simplifiedContainment{dom n : Nat}: (clauses : FinSeq dom (Clause n)) → 
                              Containment clauses := 
                    match dom with
                    |0 => fun _ => ⟨0, FinSeq.empty, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => fun clauses => 
                        simplifyNonEmptyContainment (m + 1) clauses (Containment.identity clauses)
