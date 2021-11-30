import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
open Nat
open Vector
open FinSeq

/-
Containment of clauses and basic properties
-/

abbrev varContains (v1 v2 : Option Bool) : Prop :=
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

abbrev contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, ∀ b : Bool, cl2.coords k kw = some b → cl1.coords k kw = some b

infix:65 " ⊇  " => contains

theorem contains_refl{n: Nat} (cl : Clause n) :   
  cl ⊇ cl :=
    fun k w b => 
      fun hyp =>
        hyp

theorem contains_trans{n: Nat} (cl1 cl2 cl3 : Clause n) :
        cl1 ⊇  cl2 → cl2 ⊇ cl3 →  cl1 ⊇ cl3 :=
        fun hyp1 hyp2 => 
          fun k w b =>
            fun dHyp =>
              by
                apply hyp1
                apply hyp2
                apply dHyp
                done

theorem contains_prepend{n: Nat}(v1 v2 : Option Bool)(cl1 cl2 : Clause n) :
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

/-
Implementation of checking for containment; tail-call optimized
-/

abbrev containsBeyond(cl1 cl2 : Clause n)(m: Nat) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, m ≤ k →  ∀ b : Bool, cl2.coords k kw = some b → cl1.coords k kw = some b

theorem contains_implies_contains_beyond {n: Nat} (cl1 cl2 : Clause n) (m: Nat) :
  contains cl1 cl2 → containsBeyond cl1 cl2 m := by
    intro h
    intro k
    intro kw
    intro ineq
    intro b
    exact h k kw b
    done
  
theorem contains_beyond_zero_implies_contains {n: Nat} (cl1 cl2 : Clause n) :
  containsBeyond cl1 cl2 zero → contains cl1 cl2 := by
    intro h
    intro k
    intro kw
    intro b
    exact h k kw (Nat.zero_le _) b
    done

def containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊇  cl2 → (valuation : Valuation n) → clauseSat cl2 valuation → clauseSat cl1 valuation :=
    fun dom valuation  =>
      fun ⟨j, jw, vs⟩ =>
        let lem0 :  cl2.coords j jw = some (valuation.coords j jw) := vs 
        let lem1 := dom j jw (valuation.coords j jw) lem0
        ⟨j, jw, lem1⟩


theorem contains_beyond_vacuously{n: Nat} (cl1 cl2 : Clause n)(m: Nat) :
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
                let h := contains_implies_contains_beyond cl1 cl2 m hyp
                exact contra h
                done)
          | zero, isTrue pf => isTrue (contains_beyond_zero_implies_contains cl1 cl2 pf)
          | l + 1, isTrue pf => 
            let accum: Decidable (containsBeyond cl1 cl2 l) := 
              if lw : l < n then
                match varDomDecide (cl1.coords l lw) (cl2.coords l lw) with
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
                            let lem1 : cl1.coords l lw = cl1.coords k kw := by
                              apply witness_independent
                              exact eql
                              done
                            let lem2 : cl2.coords l lw = cl2.coords k kw := by
                              apply witness_independent
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
                isTrue (contains_beyond_vacuously cl1 cl2 l overshoot)
        decideContainsRec cl1 cl2 l accum


def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊇   cl2) :=
    fun cl1 cl2 => decideContainsRec cl1 cl2 n 
        (isTrue (contains_beyond_vacuously cl1 cl2 n (Nat.le_refl _)))

instance {n: Nat}{cl: Clause n} : DecidablePred (contains cl) :=
  decideContains n cl

def parityCount{n: Nat}  (b: Bool) (cl : Clause n) : Nat :=
    let p : Option Bool →  Bool :=
      fun bo =>
        match bo with
        | some bb => bb = b
        | none => false
    cl.count p

abbrev countBelow (p1 n1 p2 n2 : Nat) : Bool :=
  (p1 ≤ p2) ∧ (n1 ≤ n2) ∧ ((p1 < p2) ∨ (n1 < n2)) 

-- Simplification removing clauses that contain other clauses.

structure Containment{dom n : Nat}(base: Vector (Clause n) dom) where
    codom: Nat
    imageSeq : Vector (Clause n) codom
    forwardVec : Vector Nat dom
    forwardBound : (j : Nat) →  (jw : j < dom) → forwardVec.coords j jw < codom
    forwardEq : (j : Nat) →  (jw : j < dom) → 
              contains (base.coords j jw) (imageSeq.coords (forwardVec.coords j jw) (forwardBound j jw))
    reverseVec : Vector Nat codom
    reverseBound : (j : Nat) →  (jw : j < codom) → reverseVec.coords j jw < dom
    reverseEq : (j : Nat) →  (jw : j < codom) →
             base.coords (reverseVec.coords j jw) (reverseBound j jw) = imageSeq.coords j jw

namespace Containment
abbrev forward {dom n : Nat}{base: Vector (Clause n) dom}
      (cntn : Containment base) (j : Nat) (jw : j < dom) : 
                  ElemSeqPred cntn.imageSeq.coords (contains (base.coords j jw)) :=
                ⟨cntn.forwardVec.coords j jw, cntn.forwardBound j jw, 
                    cntn.forwardEq j jw⟩
                

abbrev reverse {dom n : Nat}{base: Vector (Clause n) dom}
      (cntn : Containment base) (j : Nat) (jw : j < cntn.codom) :
                  ElemInSeq base.coords (cntn.imageSeq.coords j jw) :=
                ⟨cntn.reverseVec.coords j jw, cntn.reverseBound j jw,
                    cntn.reverseEq j jw⟩

def identity{dom n : Nat}(base: Vector (Clause n) dom) : Containment base :=
    let idVec : Vector Nat dom := FinSeq.vec (fun j jw => j)
    let idAt : (j : Nat) → (jw : j < dom) → idVec.coords j jw = j := by
      intro j
      intro jw
      rw [seq_to_vec_coords]
      done
    let idBound : (j : Nat) → (jw : j < dom) → idVec.coords j jw < dom := by
      intro j
      intro jw
      rw [idAt]
      exact jw
      done

    let idEqn : (j : Nat) → (jw : j < dom) → 
          idVec.coords (idVec.coords j jw) (idBound j jw) = j := by
          intro j
          intro jw
          rw [idAt]
          rw [idAt]
          done

    let baseEqn : (j : Nat) → (jw : j < dom) →
          base.coords (idVec.coords j jw) (idBound j jw) = base.coords j jw := by
          intro j
          intro jw
          apply witness_independent
          rw [idAt]
          done
    let baseContains : (j : Nat) → (jw : j < dom) →
          contains (base.coords j jw) (base.coords (idVec.coords j jw) (idBound j jw)) := by
          intro j
          intro jw
          rw [baseEqn]
          exact contains_refl (base.coords j jw)
          done
    ⟨dom, base, idVec, idBound, baseContains, idVec, idBound, 
      by 
      intro j
      intro jw
      apply witness_independent
      rw [idAt]
      done⟩
end Containment

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
          let focus := imageSeq.coords k lt
          let rest := delete k lt imageSeq.coords
          let posFocus := posCount.coords (reverseVec.coords k lt) (reverseBound k lt)
          let negFocus := negCount.coords (reverseVec.coords k lt) (reverseBound k lt)
          let filter : FinSeq l Bool := 
              delete k lt (fun j jw =>
                countBelow (posCount.coords (reverseVec.coords j jw) (reverseBound j jw))
                  (negCount.coords (reverseVec.coords j jw) (reverseBound j jw)) 
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
                    ElemSeqPred imageSeqN (contains (base.coords j jw)) := 
                    fun j jw => 
                      let ⟨i, iw , ict⟩ := forward j jw
                      if c : i = k then 
                          let lem1 : imageSeq.coords i iw = imageSeq.coords k lt := by
                                apply witness_independent
                                apply c
                                done
                          let lem2 : imageSeq.coords i iw ⊇ imageSeqN zi zb := by
                                rw [lem1] 
                                exact zc
                                done    
                          ⟨zi, zb, contains_trans _ _ _ ict lem2⟩
                      else 
                        let ii := skipInverse k i c 
                        let eqn := skip_inverse_eq k i c
                        let iiw := skip_preimage_lt lt iw eqn
                        let lem1 : imageSeqN ii iiw = imageSeq.coords (skip k ii) (skip_le_succ iiw)  := by rfl
                        let lem2 : imageSeq.coords (skip k ii) (skip_le_succ iiw) = imageSeq.coords i iw := by
                                        apply witness_independent
                                        apply eqn
                                        done 
                        ⟨ii, iiw, by 
                                  rw [lem1]
                                  rw [lem2]
                                  exact ict
                                  done⟩
              let forwardNVec := FinSeq.vec (fun j jw => (forwardN j jw).index)
              have forwardNAt : (j : Nat) → (jw : j < domN) → 
                      forwardNVec.coords j jw = (forwardN j jw).index := 
                      by
                        intro j
                        intro jw
                        rw [seq_to_vec_coords] 
                        done
              have forwardNBound : (j : Nat) → (jw : j < domN) →
                      forwardNVec.coords j jw < codomN := by
                        intro j
                        intro jw
                        rw [forwardNAt]
                        exact (forwardN j jw).bound
                        done
              have forwardNEq : (j : Nat) → (jw : j < domN) → 
                  (imageSeqN (forwardNVec.coords j jw) (forwardNBound j jw)) =
                      imageSeqN (forwardN j jw).index (forwardN j jw).bound := 
                        by 
                          intro j
                          intro jw
                          apply witness_independent
                          rw [forwardNAt]
                          done
              have forwardNPred : (j : Nat) → (jw : j < domN) →
                    contains (base.coords j jw) 
                          (imageSeqN.vec.coords (forwardNVec.coords j jw) (forwardNBound j jw)) := 
                        by 
                          intro j
                          intro jw
                          have se : 
                            (imageSeqN.vec.coords (forwardNVec.coords j jw) (forwardNBound j jw)) =
                            (imageSeqN (forwardNVec.coords j jw) (forwardNBound j jw)) := by
                              rw [seq_to_vec_coords]
                          rw [se, forwardNEq j jw]
                          exact (forwardN j jw).equation
                          done
              let reverseN : (j : Nat) → (jw : j < codomN) → 
                    ElemInSeq base.coords (imageSeqN j jw) := 
                    fun i =>
                      fun iw => 
                        let ⟨ind, bd, eqn⟩ := reverse (skip k i) (skip_le_succ iw)
                        ⟨ind, bd, by 
                            exact eqn
                            done⟩
              let reverseNVec := FinSeq.vec (fun j jw => (reverseN j jw).index)
              have reverseNAt : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.coords j jw = (reverseN j jw).index :=
                      by
                        intro j
                        intro jw
                        rw [seq_to_vec_coords]
                        done
              have reverseNBound : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.coords j jw < domN := by
                        intro j
                        intro jw
                        rw [reverseNAt]
                        exact (reverseN j jw).bound
                        done
              have reverseNAtImage : (j : Nat) → (jw : j < l) →
                      imageSeqN.vec.coords j jw = imageSeqN j jw :=
                      by
                        intro j
                        intro jw
                        rw [seq_to_vec_coords]
                        done
              have reverseNEq : (j : Nat) → (jw : j < codomN) →
                  (base.coords (reverseNVec.coords j jw) (reverseNBound j jw)) =
                    base.coords (reverseN j jw).index (reverseN j jw).bound := by
                        intro j
                        intro jw
                        apply witness_independent
                        rw [reverseNAt]
                        done
              have reverseNPred : (j : Nat) → (jw : j < codomN) →
                  base.coords (reverseNVec.coords j jw) (reverseNBound j jw) =
                    imageSeqN.vec.coords j jw := by
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
                      ⟨zero, Vector.nil, Vector.nil, fun j jw => nomatch jw, fun j jw => nomatch jw,
                        Vector.nil, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => fun clauses posCount negCount =>                                                          
                        simplifyNonEmptyContainment (m + 1) clauses
                            posCount negCount (Containment.identity clauses)