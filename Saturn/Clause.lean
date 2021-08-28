import Saturn.FinSeq
open Nat
open Vector

def Clause(n : Nat) : Type := Vector (Option Bool) n

def Valuation(n: Nat) : Type := Vector Bool n

def varSat (clVal: Option Bool)(valuationVal : Bool) : Prop := clVal = some valuationVal


structure ClauseSat{n: Nat}(clause : Clause n)(valuation: Valuation n) where
  coord : Nat
  bound : coord < n  
  witness: varSat (clause.at coord bound) (valuation.at coord bound)

def clauseSat {n: Nat}(clause : Clause n)(valuation: Valuation n) := 
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause.at k b) (valuation.at k b)

instance {n: Nat}(clause : Clause n)(valuation: Valuation n): Prover (ClauseSat clause valuation) where 
  statement := fun cs => ∃ (k : Nat), ∃ (b : k < n), varSat (clause.at k b) (valuation.at k b)
  proof := fun cs => ⟨cs.coord, ⟨cs.bound, cs.witness⟩⟩

def contradiction(n: Nat) : Clause n :=
  FinSeq.vec (fun _ _ => none)

theorem contraAt(n: Nat) : Vector.at (contradiction n) = (fun _ _ => none) := by apply seqAt


theorem contradictionFalse (n: Nat) : ∀ valuation : Valuation n, Not (clauseSat (contradiction n) valuation) :=
  fun valuation => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : Vector.at (contradiction n) k b = none := by (rw (contraAt n))
    let lem2 : varSat (Vector.at (contradiction n) k b) = varSat none := congrArg varSat lem1
    let lem3 : varSat (Vector.at (contradiction n) k b) (valuation.at k b) = 
                varSat none (valuation.at k b) := congr lem2 rfl
    let lem4 : (varSat none (valuation.at k b)) = (none = some (valuation.at k b)) := rfl
    let lem5 : (none = some (valuation.at k b)) := by
      rw ← lem4
      rw ← lem2
      exact p
      done 
    Option.noConfusion lem5

theorem contradictionInsNone{n : Nat} (focus: Nat)(focusLt : focus < n + 1) :
      insert none n focus focusLt (Vector.at (contradiction n)) =
                          Vector.at (contradiction (n + 1)) :=
      let lem0 : (j: Nat) → (jw : j < n + 1) →  
            insert none n focus focusLt (Vector.at (contradiction n)) j jw  =
                      Vector.at (contradiction (n + 1)) j jw := 
                      fun j jw =>
                      let lem0 : Vector.at (contradiction (n + 1)) j jw = none := by rw contraAt
                      if c : j= focus then 
                        match focus, c, focusLt with
                        | .(j), rfl, .(jw) =>
                          by
                            rw insertAtFocus 
                            rw contraAt
                            done                                
                      else  
                        let i := skipInverse focus j c 
                        let eqn : skip focus i = j := skipInverseEqn focus j c
                        let iw := skipPreImageBound focusLt jw eqn
                        match j, eqn, jw, lem0 with
                        | .(skip focus i), rfl, .(skipPlusOne iw), lem1 =>  
                          by
                            rw lem1
                            rw (insertAtImage 
                               none n focus focusLt (Vector.at (contradiction n))
                               i iw)
                            rw contraAt
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
  ∀ k : Nat, ∀ kw : k < n, ∀ b : Bool, cl2.at k kw = some b → cl1.at k kw = some b

def contains.self{n: Nat} (cl : Clause n) : contains cl cl :=
  fun k kw b hyp => hyp

infix:65 " ⊇  " => contains

def containsBeyond(cl1 cl2 : Clause n)(m: Nat) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, m ≤ k →  ∀ b : Bool, cl2.at k kw = some b → cl1.at k kw = some b

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
        let lem0 :  cl2.at j jw = some (valuation.at j jw) := vs 
        let lem1 := dom j jw (valuation.at j jw) lem0
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

-- def containsTail{n: Nat} (cl1 cl2 : Clause (n + 1)) :
--         cl1 ⊇  cl2 → (tail cl1) ⊇ (tail cl2) :=
--         fun hyp =>
--           fun k w b =>
--             fun dHyp =>
--               hyp (k + 1) (succ_lt_succ w) b dHyp

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
            let accum: Decidable (containsBeyond cl1 cl2 l) := 
              if lw : l < n then
                match varDomDecide (cl1.at l lw) (cl2.at l lw) with
                | isTrue pfHead =>                       
                      isTrue (
                        by
                          intro k 
                          intro kw
                          intro ineq
                          intro b
                          cases Nat.eqOrLtOfLe ineq with
                          | inl eql =>
                            let lem0 := pfHead b
                            let lem1 : cl1.at l lw = cl1.at k kw := by
                              apply witnessIndependent
                              exact eql
                              done
                            let lem2 : cl2.at l lw = cl2.at k kw := by
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
                  | isFalse contra => isFalse (fun hyp =>
                              contra ( 
                                fun b => 
                                  hyp l lw (Nat.leRefl _) b 
                                )                           
                                )
            else
                let overshoot : n ≤ l := by
                  cases Nat.ltOrGe l n with
                  | inl l1 => exact absurd l1 lw
                  | inr l2 => exact l2
                isTrue (containsBeyondVacuous cl1 cl2 l overshoot)
        decideContainsRec cl1 cl2 l accum


def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊇   cl2) :=
    fun cl1 cl2 => decideContainsRec cl1 cl2 n 
        (isTrue (containsBeyondVacuous cl1 cl2 n (Nat.leRefl _)))

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
          let step  : Containment base :=
            match subClause? focus rest with 
            | none =>  
                ⟨l + 1, imageSeq, forward, reverse⟩
            | some ⟨zi, zb, zc⟩ => 
              let codomN := l
              let imageSeqN := rest
              let domN := d + 1
              let forwardN : (j : Nat) → (jw : j < domN) → 
                    ElemSeqPred imageSeqN (contains (base j jw)) := 
                    fun j jw => 
                      let ⟨i, iw , ict⟩ := forward j jw
                      if c : i = k then 
                          let lem1 : imageSeq i iw = imageSeq k lt := by
                                apply witnessIndependent
                                apply c
                                done
                          let lem2 : imageSeq i iw ⊇ imageSeqN zi zb := by
                                rw lem1 
                                exact zc
                                done    
                          ⟨zi, zb, containsTrans _ _ _ ict lem2⟩
                      else 
                        let ii := skipInverse k i c 
                        let eqn := skipInverseEqn k i c
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
             ⟨codomN, imageSeqN, forwardN, reverseN⟩
          simplifyNonEmptyContainment k base step
        else ⟨l + 1, imageSeq, forward, reverse⟩

def simplifiedContainment{dom n : Nat}: (clauses : FinSeq dom (Clause n)) → 
                              Containment clauses := 
                    match dom with
                    |0 => fun _ => ⟨0, FinSeq.empty, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => fun clauses => 
                        simplifyNonEmptyContainment (m + 1) clauses (Containment.identity clauses)
