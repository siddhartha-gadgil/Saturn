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

instance {n: Nat}(clause : Clause n)(valuation: Valuation n): 
    Prover (ClauseSat clause valuation) where 
  statement := fun cs => ∃ (k : Nat), ∃ (b : k < n), varSat (clause.at k b) (valuation.at k b)
  proof := fun cs => ⟨cs.coord, ⟨cs.bound, cs.witness⟩⟩

def contradiction(n: Nat) : Clause n :=
  FinSeq.vec (fun _ _ => none)

theorem contraAt(n: Nat) : Vector.at (contradiction n) = (fun _ _ => none) := by apply seqAt


theorem contradictionFalse (n: Nat) : ∀ valuation : Valuation n, 
          Not (clauseSat (contradiction n) valuation) :=
  fun valuation => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : Vector.at (contradiction n) k b = none := by rw [contraAt n]
    let lem2 : varSat (Vector.at (contradiction n) k b) = varSat none := congrArg varSat lem1
    let lem3 : varSat (Vector.at (contradiction n) k b) (valuation.at k b) = 
                varSat none (valuation.at k b) := congr lem2 rfl
    let lem4 : (varSat none (valuation.at k b)) = (none = some (valuation.at k b)) := rfl
    let lem5 : (none = some (valuation.at k b)) := by
      rw [← lem4]
      rw [← lem2]
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
                      let lem0 : Vector.at (contradiction (n + 1)) j jw = none := 
                          by rw [contraAt]
                      if c : j= focus then 
                        match focus, c, focusLt with
                        | .(j), rfl, .(jw) =>
                          by
                            rw [insertAtFocus] 
                            rw [contraAt]
                            done                                
                      else  
                        let i := skipInverse focus j c 
                        let eqn : skip focus i = j := skipInverseEqn focus j c
                        let iw := skipPreImageBound focusLt jw eqn
                        match j, eqn, jw, lem0 with
                        | .(skip focus i), rfl, .(skipPlusOne iw), lem1 =>  
                          by
                            rw [lem1]
                            rw [insertAtImage 
                               none n focus focusLt (Vector.at (contradiction n))
                               i iw]
                            rw [contraAt]
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
                        rw [c]
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
  containsBeyond cl1 cl2 zero → contains cl1 cl2 := by
    intro h
    intro k
    intro kw
    intro b
    exact h k kw (Nat.zero_le _) b
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
            | zero => fun w b =>
              fun hb => 
                hyp1 b hb
            | j + 1  =>  
              fun  kw b =>
                fun hb =>
                  hyp2 j  (le_of_succ_le_succ kw) b hb

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

#check Nat.eq_or_lt_of_le
#check Nat.lt_irrefl

def containsBeyondVacuous{n: Nat} (cl1 cl2 : Clause n)(m: Nat) :
    (n ≤ m) → containsBeyond cl1 cl2 m := by
      intro h
      intro k
      intro kw
      intro ineq
      let inq := Nat.le_trans h ineq
      let inq2 := Nat.lt_of_lt_of_le kw inq
      exact (False.elim (Nat.lt_irrefl k inq2))
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
          | zero, isTrue pf => isTrue (containsBeyondZero cl1 cl2 pf)
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
                          cases Nat.eq_or_lt_of_le ineq with
                          | inl eql =>
                            let lem0 := pfHead b
                            let lem1 : cl1.at l lw = cl1.at k kw := by
                              apply witnessIndependent
                              exact eql
                              done
                            let lem2 : cl2.at l lw = cl2.at k kw := by
                              apply witnessIndependent
                              exact eql
                            rw [← lem1]
                            rw [← lem2]
                            exact lem0
                            done
                          | inr l2 => 
                            exact pf k kw l2 b
                            done                      
                      )
                  | isFalse contra => isFalse (fun hyp =>
                              contra ( 
                                fun b => 
                                  hyp l lw (Nat.le_refl _) b 
                                )                           
                                )
            else
                let overshoot : n ≤ l := by
                  cases Nat.lt_or_ge l n with
                  | inl l1 => exact absurd l1 lw
                  | inr l2 => exact l2
                isTrue (containsBeyondVacuous cl1 cl2 l overshoot)
        decideContainsRec cl1 cl2 l accum


def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊇   cl2) :=
    fun cl1 cl2 => decideContainsRec cl1 cl2 n 
        (isTrue (containsBeyondVacuous cl1 cl2 n (Nat.le_refl _)))

instance {n: Nat}{cl: Clause n} : DecidablePred (contains cl) :=
  decideContains n cl

def subClause?{l n: Nat}(cl : Clause n)(seq : FinSeq l (Clause n)) :
                    Option (ElemSeqPred seq (contains cl)) := 
              find? (contains cl) seq

def parityCount{n: Nat}  (b: Bool) (cl : Clause n) : Nat :=
    let p : Option Bool →  Bool :=
      fun bo =>
        match bo with
        | some bb => bb = b
        | none => false
    cl.count p

def countBelow (p1 n1 p2 n2 : Nat) : Bool :=
  (p1 ≤ p2) ∧ (n1 ≤ n2) ∧ ((p1 < p2) ∨ (n1 < n2)) 

structure Containment{dom n : Nat}(base: Vector (Clause n) dom) where
    codom: Nat
    imageSeq : Vector (Clause n) codom
    forwardVec : Vector Nat dom
    forwardBound : (j : Nat) →  (jw : j < dom) → forwardVec.at j jw < codom
    forwardEq : (j : Nat) →  (jw : j < dom) → 
              contains (base.at j jw) (imageSeq.at (forwardVec.at j jw) (forwardBound j jw))
    reverseVec : Vector Nat codom
    reverseBound : (j : Nat) →  (jw : j < codom) → reverseVec.at j jw < dom
    reverseEq : (j : Nat) →  (jw : j < codom) →
             base.at (reverseVec.at j jw) (reverseBound j jw) = imageSeq.at j jw
    -- forward : (j : Nat) → (jw : j < dom) → ElemSeqPred imageSeq.at (contains (base.at j jw))
    -- reverse : (j : Nat) → (jw : j < codom) → ElemInSeq base.at (imageSeq.at j jw) 

def Containment.forward {dom n : Nat}{base: Vector (Clause n) dom}
      (cntn : Containment base) (j : Nat) (jw : j < dom) : 
                  ElemSeqPred cntn.imageSeq.at (contains (base.at j jw)) :=
                ⟨cntn.forwardVec.at j jw, cntn.forwardBound j jw, 
                    cntn.forwardEq j jw⟩
                

def Containment.reverse {dom n : Nat}{base: Vector (Clause n) dom}
      (cntn : Containment base) (j : Nat) (jw : j < cntn.codom) :
                  ElemInSeq base.at (cntn.imageSeq.at j jw) :=
                ⟨cntn.reverseVec.at j jw, cntn.reverseBound j jw,
                    cntn.reverseEq j jw⟩

def Containment.identity{dom n : Nat}(base: Vector (Clause n) dom) : Containment base :=
    let idVec : Vector Nat dom := FinSeq.vec (fun j jw => j)
    let idAt : (j : Nat) → (jw : j < dom) → idVec.at j jw = j := by
      intro j
      intro jw
      rw [seqAt]
      done
    let idBound : (j : Nat) → (jw : j < dom) → idVec.at j jw < dom := by
      intro j
      intro jw
      rw [idAt]
      exact jw
      done

    let idEqn : (j : Nat) → (jw : j < dom) → 
          idVec.at (idVec.at j jw) (idBound j jw) = j := by
          intro j
          intro jw
          rw [idAt]
          rw [idAt]
          done

    let baseEqn : (j : Nat) → (jw : j < dom) →
          base.at (idVec.at j jw) (idBound j jw) = base.at j jw := by
          intro j
          intro jw
          apply witnessIndependent
          rw [idAt]
          done
    let baseContains : (j : Nat) → (jw : j < dom) →
          contains (base.at j jw) (base.at (idVec.at j jw) (idBound j jw)) := by
          intro j
          intro jw
          rw [baseEqn]
          exact contains.self (base.at j jw)
          done
    ⟨dom, base, idVec, idBound, baseContains, idVec, idBound, 
      by 
      intro j
      intro jw
      apply witnessIndependent
      rw [idAt]
      done⟩


def simplifyNonEmptyContainment{d n : Nat}: (cursorBound : Nat) →  
      (base : Vector (Clause n) (d + 1)) → Vector Nat (d + 1) → Vector Nat (d + 1) → 
      Containment (base) → Containment (base) := 
      fun cursorBound =>
      match cursorBound with
      | zero => fun _ _ _ => id
      | k + 1 =>
        fun base posCount negCount contn =>
          let ⟨j, (ineq : j < contn.codom), _⟩ := contn.forward zero (zero_lt_succ _)      
          let neZero : Not (0 = contn.codom) := fun hyp => 
          let l0 : j < 0 := by
            rw [hyp]
            exact ineq
            done
          Nat.not_lt_zero j l0
        let ⟨l, leqn⟩ := posSucc contn.codom neZero
        match contn.codom, leqn, contn.imageSeq, contn.forward, contn.reverse,
            contn.forwardVec, contn.forwardBound, contn.forwardEq,
            contn.reverseVec, contn.reverseBound, contn.reverseEq with
        | .(l + 1), rfl, imageSeq, forward, reverse, 
            forwardVec, forwardBound, forwardEq, 
            reverseVec, reverseBound, revereseEq =>
         if lt : k < (l + 1) then
          let focus := imageSeq.at k lt
          let rest := delete k lt imageSeq.at
          let posFocus := posCount.at (reverseVec.at k lt) (reverseBound k lt)
          let negFocus := negCount.at (reverseVec.at k lt) (reverseBound k lt)
          let filter : FinSeq l Bool := 
              delete k lt (fun j jw =>
                countBelow (posCount.at (reverseVec.at j jw) (reverseBound j jw))
                  (negCount.at (reverseVec.at j jw) (reverseBound j jw)) 
                    posFocus negFocus)
          let step  : Containment base :=
            match findFiltered? filter (contains focus) rest with 
            | none =>  
                ⟨l + 1, imageSeq, forwardVec, forwardBound, forwardEq,
                   reverseVec, reverseBound, revereseEq⟩
            | some ⟨zi, zb, zc⟩ => 
              let codomN := l
              let imageSeqN := rest
              let domN := d + 1
              let forwardN : (j : Nat) → (jw : j < domN) → 
                    ElemSeqPred imageSeqN (contains (base.at j jw)) := 
                    fun j jw => 
                      let ⟨i, iw , ict⟩ := forward j jw
                      if c : i = k then 
                          let lem1 : imageSeq.at i iw = imageSeq.at k lt := by
                                apply witnessIndependent
                                apply c
                                done
                          let lem2 : imageSeq.at i iw ⊇ imageSeqN zi zb := by
                                rw [lem1] 
                                exact zc
                                done    
                          ⟨zi, zb, containsTrans _ _ _ ict lem2⟩
                      else 
                        let ii := skipInverse k i c 
                        let eqn := skipInverseEqn k i c
                        let iiw := skipPreImageBound lt iw eqn
                        let lem1 : imageSeqN ii iiw = imageSeq.at (skip k ii) (skipPlusOne iiw)  := by rfl
                        let lem2 : imageSeq.at (skip k ii) (skipPlusOne iiw) = imageSeq.at i iw := by
                                        apply witnessIndependent
                                        apply eqn
                                        done 
                        ⟨ii, iiw, by 
                                  rw [lem1]
                                  rw [lem2]
                                  exact ict
                                  done⟩
              let forwardNVec := FinSeq.vec (fun j jw => (forwardN j jw).index)
              have forwardNAt : (j : Nat) → (jw : j < domN) → 
                      forwardNVec.at j jw = (forwardN j jw).index := 
                      by
                        intro j
                        intro jw
                        rw [seqAt] 
                        done
              have forwardNBound : (j : Nat) → (jw : j < domN) →
                      forwardNVec.at j jw < codomN := by
                        intro j
                        intro jw
                        rw [forwardNAt]
                        exact (forwardN j jw).bound
                        done
              have forwardNEq : (j : Nat) → (jw : j < domN) → 
                  (imageSeqN (forwardNVec.at j jw) (forwardNBound j jw)) =
                      imageSeqN (forwardN j jw).index (forwardN j jw).bound := 
                        by 
                          intro j
                          intro jw
                          apply witnessIndependent
                          rw [forwardNAt]
                          done
              have forwardNPred : (j : Nat) → (jw : j < domN) →
                    contains (base.at j jw) 
                          (imageSeqN.vec.at (forwardNVec.at j jw) (forwardNBound j jw)) := 
                        by 
                          intro j
                          intro jw
                          have se : 
                            (imageSeqN.vec.at (forwardNVec.at j jw) (forwardNBound j jw)) =
                            (imageSeqN (forwardNVec.at j jw) (forwardNBound j jw)) := by
                              rw [seqAt]
                          rw [se, forwardNEq j jw]
                          exact (forwardN j jw).equation
                          done
              let reverseN : (j : Nat) → (jw : j < codomN) → 
                    ElemInSeq base.at (imageSeqN j jw) := 
                    fun i =>
                      fun iw => 
                        let ⟨ind, bd, eqn⟩ := reverse (skip k i) (skipPlusOne iw)
                        ⟨ind, bd, by 
                            exact eqn
                            done⟩
              let reverseNVec := FinSeq.vec (fun j jw => (reverseN j jw).index)
              have reverseNAt : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.at j jw = (reverseN j jw).index :=
                      by
                        intro j
                        intro jw
                        rw [seqAt]
                        done
              have reverseNBound : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.at j jw < domN := by
                        intro j
                        intro jw
                        rw [reverseNAt]
                        exact (reverseN j jw).bound
                        done
              have reverseNAtImage : (j : Nat) → (jw : j < l) →
                      imageSeqN.vec.at j jw = imageSeqN j jw :=
                      by
                        intro j
                        intro jw
                        rw [seqAt]
                        done
              have reverseNEq : (j : Nat) → (jw : j < codomN) →
                  (base.at (reverseNVec.at j jw) (reverseNBound j jw)) =
                    base.at (reverseN j jw).index (reverseN j jw).bound := by
                        intro j
                        intro jw
                        apply witnessIndependent
                        rw [reverseNAt]
                        done
              have reverseNPred : (j : Nat) → (jw : j < codomN) →
                  base.at (reverseNVec.at j jw) (reverseNBound j jw) =
                    imageSeqN.vec.at j jw := by
                        intro j
                        intro jw
                        rw [reverseNAtImage j jw]
                        rw [reverseNEq j jw]
                        exact (reverseN j jw).equation
                        done
             ⟨codomN, imageSeqN.vec, forwardNVec, forwardNBound, forwardNPred,
                reverseNVec, reverseNBound, reverseNPred⟩
          simplifyNonEmptyContainment k base posCount negCount step
        else ⟨l + 1, imageSeq, forwardVec, forwardBound, forwardEq,
                   reverseVec, reverseBound, revereseEq⟩

def simplifiedContainment{dom n : Nat}: (clauses : Vector (Clause n) dom) → 
                             Vector Nat dom → Vector Nat dom → 
                              Containment clauses := 
                    match dom with
                    |zero => fun _ _ _ => 
                      ⟨zero, Vector.Nil, Vector.Nil, fun j jw => nomatch jw, fun j jw => nomatch jw,
                        Vector.Nil, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => fun clauses posCount negCount =>                                                          
                        simplifyNonEmptyContainment (m + 1) clauses
                            posCount negCount (Containment.identity clauses)
