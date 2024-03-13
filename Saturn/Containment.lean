import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
open Nat
open Vector
open FinSeq

/-!
## Containment of collections of clauses

Containment of clauses and basic properties
-/

abbrev varContains (v1 v2 : Option Bool) : Prop :=
  ∀ b : Bool, v2 = some b → v1  = some b


instance : LE (Option Bool) :=
  ⟨fun v₁ v₂ => varContains v₂ v₁⟩

def varDomDecide : (v1 : Option Bool) → (v2 : Option Bool) → Decidable (v1 ≥  v2) :=
  fun v1 v2 =>
  match v2 with
  | none =>
     isTrue $ fun b hyp =>
          Option.noConfusion hyp
  | some b2 =>
    match v1  with
    | none =>
      isFalse $ fun hyp =>
          Option.noConfusion (hyp b2 rfl)
    | some b1 =>
          if c : b1 = b2 then
            isTrue (by
                        intro b hyp
                        rw [c]
                        exact hyp)
          else
            isFalse (
              fun hyp =>
                  let lem1 := hyp b2 rfl
                  let lem2 : b1 = b2 := by
                      injection lem1

                  c (lem2)
            )

def contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, ∀ b : Bool, cl2.get' k kw = some b → cl1.get' k kw = some b

infix:65 "⊇" => contains

theorem contains_refl{n: Nat} (cl : Clause n) :
  cl ⊇ cl := fun _ _ _ hyp => hyp

theorem contains_trans{n: Nat} (cl1 cl2 cl3 : Clause n) :
        cl1 ⊇  cl2 → cl2 ⊇ cl3 →  cl1 ⊇ cl3 := by
                intro hyp1 hyp2  k w b dHyp
                apply hyp1
                apply hyp2
                apply dHyp

theorem contains_prepend{n: Nat}(v1 v2 : Option Bool)(cl1 cl2 : Clause n) :
          v1 ≥  v2 → cl1 ⊇  cl2 →
                (v1 +: cl1) ⊇ (v2 +: cl2) := by
            intro hyp1 hyp2 k
            match k with
            | zero =>
              intro w b hb
              exact hyp1 b hb
            | j + 1  =>
              intro kw b hb
              have w : j < n := by
                  apply le_of_succ_le_succ
                  exact kw
              exact hyp2 j w b hb

/-
Implementation of checking for containment; tail-call optimized
-/
abbrev containsBeyond(cl1 cl2 : Clause n)(m: Nat) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, m ≤ k →  ∀ b : Bool, cl2.get' k kw = some b → cl1.get' k kw = some b

theorem contains_implies_contains_beyond {n: Nat} (cl1 cl2 : Clause n) (m: Nat) :
  cl1 ⊇ cl2 → containsBeyond cl1 cl2 m := by
    intro h k kw _ b
    exact h k kw b

theorem contains_beyond_zero_implies_contains {n: Nat} (cl1 cl2 : Clause n) :
  containsBeyond cl1 cl2 zero → cl1 ⊇ cl2 := by
    intro h k kw b
    exact h k kw (Nat.zero_le _) b

theorem containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊇  cl2 → (valuation : Valuation n) → clauseSat cl2 valuation → clauseSat cl1 valuation := by
    intro num_clauses valuation
    intro ⟨j, jw, vs⟩
    let lem0 :  cl2.get' j jw = some (valuation.get' j jw) := vs
    let lem1 : get' cl1 j jw = some (get' valuation j jw) := num_clauses j jw (valuation.get' j jw) lem0
    exact ⟨j, jw, lem1⟩


theorem contains_beyond_vacuously{n: Nat} (cl1 cl2 : Clause n)(m: Nat) :
    (n ≤ m) → containsBeyond cl1 cl2 m := by
      intro h k kw ineq
      let inq := Nat.le_trans h ineq
      let inq2 := Nat.lt_of_lt_of_le kw inq
      exact (False.elim (Nat.lt_irrefl k inq2))

def decideContainsRec{n: Nat} (cl1 cl2 : Clause n) :
        (m: Nat) → Decidable (containsBeyond cl1 cl2 m) → Decidable (cl1 ⊇ cl2) :=
        fun m dContainsBeyond =>
          match m, dContainsBeyond with
          | m, isFalse contra => isFalse (
              by
                intro hyp
                apply contra
                apply contains_implies_contains_beyond cl1 cl2 m hyp
                )
          | zero, isTrue pf => isTrue (contains_beyond_zero_implies_contains cl1 cl2 pf)
          | l + 1, isTrue pf =>
            let accum: Decidable (containsBeyond cl1 cl2 l) :=
              if lw : l < n then
                match varDomDecide (cl1.get' l lw) (cl2.get' l lw) with
                | isTrue pfHead =>
                      isTrue (
                        by
                          intro k kw ineq b
                          cases Nat.eq_or_lt_of_le ineq with
                          | inl eql =>
                            let lem1 : cl1.get' l lw = cl1.get' k kw := by
                              apply witness_independent
                              exact eql
                            let lem2 : cl2.get' l lw = cl2.get' k kw := by
                              apply witness_independent
                              exact eql
                            rw [← lem1]
                            rw [← lem2]
                            exact pfHead b
                          | inr l2 =>
                            exact pf k kw l2 b
                      )
                | isFalse contra =>
                    isFalse (fun hyp => contra (fun b => hyp l lw (Nat.le_refl _) b))
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

structure Containment{num_clauses n : Nat}(baseClauses: Vector (Clause n) num_clauses) where
    num_reducedClauses: Nat
    reducedClauses : Vector (Clause n) num_reducedClauses
    forwardVec : Vector Nat num_clauses
    forwardBound : (j : Nat) →  (jw : j < num_clauses) → forwardVec.get' j jw < num_reducedClauses
    forwardEq : (j : Nat) →  (jw : j < num_clauses) →
              baseClauses.get' j jw ⊇ reducedClauses.get' (forwardVec.get' j jw) (forwardBound j jw)
    reverseVec : Vector Nat num_reducedClauses
    reverseBound : (j : Nat) →  (jw : j < num_reducedClauses) → reverseVec.get' j jw < num_clauses
    reverseEq : (j : Nat) →  (jw : j < num_reducedClauses) →
             baseClauses.get' (reverseVec.get' j jw) (reverseBound j jw) = reducedClauses.get' j jw

namespace Containment
abbrev forward {num_clauses n : Nat}{base: Vector (Clause n) num_clauses}
      (cntn : Containment base) (j : Nat) (jw : j < num_clauses) :
                  ElemSeqPred cntn.reducedClauses.get' (contains (base.get' j jw)) :=
                ⟨cntn.forwardVec.get' j jw, cntn.forwardBound j jw,
                    cntn.forwardEq j jw⟩


abbrev reverse {num_clauses n : Nat}{base: Vector (Clause n) num_clauses}
      (cntn : Containment base) (j : Nat) (jw : j < cntn.num_reducedClauses) :
                  ElemInSeq base.get' (cntn.reducedClauses.get' j jw) :=
                ⟨cntn.reverseVec.get' j jw, cntn.reverseBound j jw,
                    cntn.reverseEq j jw⟩

def identity{num_clauses n : Nat}(base: Vector (Clause n) num_clauses) : Containment base :=
    let idVec : Vector Nat num_clauses := Vector.ofFn' (fun j _ => j)
    let idAt : (j : Nat) → (jw : j < num_clauses) → idVec.get' j jw = j := by
      intro j jw
      rw [Vector.of_Fn'_get']
    let idBound : (j : Nat) → (jw : j < num_clauses) → idVec.get' j jw < num_clauses := by
      intro j jw
      rw [idAt]
      exact jw
    let baseEqn : (j : Nat) → (jw : j < num_clauses) →
          base.get' (idVec.get' j jw) (idBound j jw) = base.get' j jw := by
          intro j jw
          apply witness_independent
          rw [idAt]
    let baseContains : (j : Nat) → (jw : j < num_clauses) →
          (base.get' j jw) ⊇ (base.get' (idVec.get' j jw) (idBound j jw)) := by
          intro j jw
          rw [baseEqn]
          exact contains_refl (base.get' j jw)
    ⟨num_clauses, base, idVec, idBound, baseContains, idVec, idBound,
      by
      intro j jw
      apply witness_independent
      rw [idAt]⟩

end Containment

def simplifyNonEmptyContainment{d n : Nat}: (cursorBound : Nat) →
      (base : Vector (Clause n) (d + 1)) → Vector Nat (d + 1) → Vector Nat (d + 1) →
      Containment (base) → Containment (base) :=
      fun cursorBound =>
      match cursorBound with
      | zero => fun _ _ _ => id
      | k + 1 =>
        fun base posCount negCount contn =>
          let ⟨j, (ineq : j < contn.num_reducedClauses), _⟩ := contn.forward zero (zero_lt_succ _)
          let neZero : Not (0 = contn.num_reducedClauses) := fun hyp =>
          let l0 : j < 0 := by
            rw [hyp]
            exact ineq
            done
          Nat.not_lt_zero j l0
        let ⟨l, leqn⟩ := posSucc contn.num_reducedClauses neZero
        match contn.num_reducedClauses, leqn, contn.reducedClauses, contn.forward, contn.reverse,
            contn.forwardVec, contn.forwardBound, contn.forwardEq,
            contn.reverseVec, contn.reverseBound, contn.reverseEq with
        | .(l + 1), rfl, reducedClauses, forward, reverse,
            forwardVec, forwardBound, forwardEq,
            reverseVec, reverseBound, revereseEq =>
         if lt : k < (l + 1) then
          let focus := reducedClauses.get' k lt
          let rest := delete k lt reducedClauses.get'
          let posFocus := posCount.get' (reverseVec.get' k lt) (reverseBound k lt)
          let negFocus := negCount.get' (reverseVec.get' k lt) (reverseBound k lt)
          let filter : FinSeq l Bool :=
              delete k lt (fun j jw =>
                countBelow (posCount.get' (reverseVec.get' j jw) (reverseBound j jw))
                  (negCount.get' (reverseVec.get' j jw) (reverseBound j jw))
                    posFocus negFocus)
          let step  : Containment base :=
            match findFiltered? filter (contains focus) rest with
            | none =>
                ⟨l + 1, reducedClauses, forwardVec, forwardBound, forwardEq,
                   reverseVec, reverseBound, revereseEq⟩
            | some ⟨zi, zb, zc⟩ => -- clause at k contains clause at index zi in deleted sequence
              let codomN := l
              let imageSeqN := rest
              let domN := d + 1
              let forwardN : (j : Nat) → (jw : j < domN) →
                    ElemSeqPred imageSeqN (contains (base.get' j jw)) :=
                    fun j jw =>
                      let ⟨i, iw , ict⟩ := forward j jw
                      if c : i = k then -- index i redirected
                          let lem1 : reducedClauses.get' i iw = reducedClauses.get' k lt := by
                                apply witness_independent
                                apply c
                          let lem2 : reducedClauses.get' i iw ⊇ imageSeqN zi zb := by
                                rw [lem1]
                                exact zc
                          ⟨zi, zb, contains_trans _ _ _ ict lem2⟩
                      else
                        let ii := skipInverse k i c -- index in sequence before deletion
                        let eqn := skipInverse_eq k i c
                        let iiw := skip_preimage_lt lt iw eqn
                        let lem1 : imageSeqN ii iiw = reducedClauses.get' (skip k ii) (skip_le_succ iiw)  :=
                                by rfl
                        let lem2 : reducedClauses.get' (skip k ii) (skip_le_succ iiw) = reducedClauses.get' i iw :=
                                by
                                    apply witness_independent
                                    apply eqn
                                    done
                        ⟨ii, iiw, by
                                  rw [lem1]
                                  rw [lem2]
                                  exact ict⟩
              let forwardNVec := Vector.ofFn' (fun j jw => (forwardN j jw).index)
              have forwardNAt : (j : Nat) → (jw : j < domN) →
                      forwardNVec.get' j jw = (forwardN j jw).index :=
                      by
                        intro j jw
                        rw [Vector.of_Fn'_get']
              have forwardNBound : (j : Nat) → (jw : j < domN) →
                      forwardNVec.get' j jw < codomN := by
                        intro j jw
                        rw [forwardNAt]
                        exact (forwardN j jw).bound
              have forwardNEq : (j : Nat) → (jw : j < domN) →
                  (imageSeqN (forwardNVec.get' j jw) (forwardNBound j jw)) =
                      imageSeqN (forwardN j jw).index (forwardN j jw).bound :=
                        by
                          intro j jw
                          apply witness_independent
                          rw [forwardNAt]
              have forwardNPred : (j : Nat) → (jw : j < domN) →
                    (base.get' j jw) ⊇
                          ((Vector.ofFn' imageSeqN).get' (forwardNVec.get' j jw) (forwardNBound j jw)) :=
                        by
                          intro j jw
                          have se :
                            ((Vector.ofFn' imageSeqN).get' (forwardNVec.get' j jw) (forwardNBound j jw)) =
                            (imageSeqN (forwardNVec.get' j jw) (forwardNBound j jw)) := by
                              rw [Vector.of_Fn'_get']
                          rw [se, forwardNEq j jw]
                          exact (forwardN j jw).equation
              let reverseN : (j : Nat) → (jw : j < codomN) →
                    ElemInSeq base.get' (imageSeqN j jw) :=
                    fun i iw =>
                        let ⟨ind, bd, eqn⟩ := reverse (skip k i) (skip_le_succ iw)
                        ⟨ind, bd, by exact eqn⟩
              let reverseNVec := Vector.ofFn' (fun j jw => (reverseN j jw).index)
              have reverseNAt : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.get' j jw = (reverseN j jw).index :=
                      by
                        intro j jw
                        rw [Vector.of_Fn'_get']
              have reverseNBound : (j : Nat) → (jw : j < codomN) →
                      reverseNVec.get' j jw < domN := by
                        intro j jw
                        rw [reverseNAt]
                        exact (reverseN j jw).bound
              have reverseNAtImage : (j : Nat) → (jw : j < l) →
                      (Vector.ofFn' imageSeqN).get' j jw = imageSeqN j jw :=
                      by
                        intro j jw
                        rw [Vector.of_Fn'_get']
              have reverseNEq : (j : Nat) → (jw : j < codomN) →
                  (base.get' (reverseNVec.get' j jw) (reverseNBound j jw)) =
                    base.get' (reverseN j jw).index (reverseN j jw).bound := by
                        intro j jw
                        apply witness_independent
                        rw [reverseNAt]
              have reverseNPred : (j : Nat) → (jw : j < codomN) →
                  base.get' (reverseNVec.get' j jw) (reverseNBound j jw) =
                    (Vector.ofFn' imageSeqN).get' j jw := by
                        intro j jw
                        rw [reverseNAtImage j jw]
                        rw [reverseNEq j jw]
                        exact (reverseN j jw).equation
             ⟨codomN, (Vector.ofFn' imageSeqN), forwardNVec, forwardNBound, forwardNPred,
                reverseNVec, reverseNBound, reverseNPred⟩
          simplifyNonEmptyContainment k base posCount negCount step
        else ⟨l + 1, reducedClauses, forwardVec, forwardBound, forwardEq,
                   reverseVec, reverseBound, revereseEq⟩

def simplifiedContainment{num_clauses n : Nat}: (clauses : Vector (Clause n) num_clauses) →
                             Vector Nat num_clauses → Vector Nat num_clauses →
                              Containment clauses :=
                    match num_clauses with
                    |zero => fun _ _ _ =>
                      ⟨zero, Vector.nil, Vector.nil, fun _ jw => nomatch jw, fun _ jw => nomatch jw,
                        Vector.nil, fun _ jw => nomatch jw, fun _ jw => nomatch jw⟩
                    | m + 1 => fun clauses posCount negCount =>
                        simplifyNonEmptyContainment (m + 1) clauses
                            posCount negCount (Containment.identity clauses)
