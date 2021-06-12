import Saturn.Basic
import Saturn.FinSeq 
open Nat

theorem liftSatHead {n: Nat}(clause : Clause (n + 1))(sect: Sect (n + 1)) :
  ClauseSat (dropHead n clause) (dropHead n sect) → ClauseSat clause sect := 
    fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropHead n clause ⟨k, w⟩ = clause (⟨k+1, _⟩) := by rfl
      let l2 : dropHead n sect ⟨k, w⟩ = sect ⟨k+1, _⟩ := by rfl
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause ⟨k+1, _⟩) (sect ⟨k+1, _⟩) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨⟨k+1, _⟩, pf⟩


theorem liftSatAt {n: Nat}(clause : Clause (n + 1))(sect: Sect (n + 1)) :
  (j : Nat) → (lt : j < n + 1) → 
  ClauseSat (dropAt n j lt clause) (dropAt n j lt sect) → ClauseSat clause sect := 
    fun j =>
    fun lt =>
     fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropAt n j lt clause ⟨k, w⟩ = clause (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt clause ⟨k, w⟩
      let l2 : dropAt n j lt sect ⟨k, w⟩ = sect (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt sect ⟨k, w⟩
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause (shiftAt n j lt ⟨k, w⟩)) (sect (shiftAt n j lt ⟨k, w⟩)) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨(shiftAt n j lt ⟨k, w⟩), pf⟩

structure RestrictionClauses{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)) where
  codom : Nat
  restClauses : Fin codom → Clause n
  forward : Fin dom → Option (Fin codom)
  dropped : (k : Fin dom) → forward k = none → clauses k focus = some branch
  reverse : Fin codom → Fin dom
  composition: (k : Fin codom) → forward (reverse k) = some k
  relation : (k : Fin codom) → 
    restClauses k = dropAt _ focus.val focus.isLt (clauses (reverse k))
  pure : (k : Fin codom) → Not (clauses (reverse k) (focus) = some branch)



def addPositiveClause{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) → 
            RestrictionClauses branch focus (prepend _ head clauses) := 
          fun rc head pos =>
            let domN := dom + 1
            let codomN := rc.codom
            let clausesN := prepend _ head clauses
            let forwardN := prepend _ none rc.forward
            let reverseN := fun (k : Fin codomN) => plusOne _ (rc.reverse k) 
            let droppedN : 
              (k : Fin domN) → forwardN k = none → clausesN k focus = some branch := 
                fun k =>
                  match k with
                  | ⟨0, w⟩ => fun _ => pos
                  | ⟨l + 1, w⟩ => 
                    fun nw =>
                      let lem1 : forwardN ⟨l + 1, w⟩ = 
                        rc.forward ⟨l, leOfSuccLeSucc w⟩ := by rfl
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := rc.dropped ⟨l, leOfSuccLeSucc w⟩ lem2
                      let lem4 : clausesN ⟨l + 1, w⟩ = 
                        clauses ⟨l, leOfSuccLeSucc w⟩ := by rfl
                      by
                        rw lem4
                        exact lem3
                        done
            let compositionN: (k : Fin codomN) → forwardN (reverseN k) = some k := 
              fun k =>
                let lem1 : forwardN (reverseN k) = rc.forward (rc.reverse k) := 
                  prependPlusOne _ none rc.forward (rc.reverse k)
                by 
                  rw lem1
                  exact (rc.composition k)
                  done
            let restClausesN := rc.restClauses 
            let relationN : (k : Fin codomN) → 
                  restClausesN k = 
                    dropAt _ focus.val focus.isLt (clausesN (reverseN k)) := 
                  fun k =>
                  let lem1 : clausesN (reverseN k) =
                    clauses (rc.reverse k) :=  
                      prependPlusOne _ head clauses (rc.reverse k)
                    by
                      rw lem1
                      exact rc.relation k
                      done
            let pureN : (k : Fin codomN) → 
              Not (clausesN (reverseN k) (focus) = some branch) :=
                  fun k =>
                  let lem1 : clausesN (reverseN k) =
                    clauses (rc.reverse k) :=  
                      prependPlusOne _ head clauses (rc.reverse k)
                    by
                      rw lem1
                      exact rc.pure k
                      done 
            RestrictionClauses.mk codomN restClausesN forwardN droppedN 
                reverseN compositionN relationN pureN
