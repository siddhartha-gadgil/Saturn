import Saturn.Basic
import Saturn.FinSeq 
open Nat

set_option maxHeartbeats 200000

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

def boundOpt(n: Nat) : Option (Nat) → Prop
  | none => True
  | some b => b < n

def boundOptSucc(n: Nat)(p: Option Nat) : boundOpt n p → boundOpt (n + 1) (p.map (. + 1)) :=
  match p with
  | none => fun h => True.intro
  | some a => fun h : a < n => succ_lt_succ h

structure RestrictionClauses{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)) where
  codom : Nat
  restClauses : Fin codom → Clause n
  forward : (k: Nat) → k < dom → Option Nat
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forward k w)
  dropped : (k : Nat) → (w: k < dom) → forward k w = none → 
    clauses ⟨k, w⟩ focus = some branch
  reverse : (k : Nat) → (k < codom) → Nat
  reverseWit : (k : Nat) → (w : k < codom) → reverse k w < dom
  composition: (k : Nat) → (w : k < codom) → (ww : reverse k w < dom) → 
    forward (reverse k w) ww = some k
  relation : (k : Nat) → (w: k < codom) → 
    restClauses ⟨k, w⟩ = dropAt _ focus.val focus.isLt (clauses (⟨reverse k w, reverseWit k w⟩))
  pure : (k : Nat) → (w: k < codom)  → 
    Not (clauses (⟨reverse k w, reverseWit k w⟩) (focus) = some branch)



def addPositiveClause{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (pos : head focus = some branch) → 
            RestrictionClauses branch focus (prepend _ head clauses) := 
          fun rc head pos =>
            let domN := dom + 1
            let codomN := rc.codom
            let clausesN := prepend _ head clauses
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | 0 => fun _ => none
              | l + 1 => 
                fun w : l + 1 < domN   =>  rc.forward l (leOfSuccLeSucc w)
            let forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | 0 => fun w => 
                let lem1 : forwardN 0 w = none := by rfl
                by
                  rw lem1
                  exact True.intro
                  done
              | l + 1 => 
                fun w : l + 1 < domN   => 
                  let lem : forwardN (l + 1) w = rc.forward l (leOfSuccLeSucc w) := by rfl 
                  by
                    rw lem
                    exact (rc.forwardWit l (leOfSuccLeSucc w))
                    done
            let reverseN : (k : Nat) →  k < codomN → Nat := 
              fun k w => (rc.reverse k w) + 1
            let reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
              fun k w => (rc.reverseWit k w)
            let droppedN : 
              (k : Nat) → (w: k < domN) → forwardN k w = none → 
                  clausesN ⟨k, w⟩ focus = some branch :=
                fun k =>
                  match k with
                  | 0 => fun _ _ => pos
                  | l + 1 => 
                    fun w nw =>
                      let lem1 : forwardN (l + 1) w = 
                        rc.forward l (leOfSuccLeSucc w) := by rfl
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := rc.dropped l (leOfSuccLeSucc w) lem2
                      by
                        exact lem3
                        done
            let compositionN: (k : Nat) → (w : k < codomN) → (ww : reverseN k w < domN) → 
                  forwardN (reverseN k w) ww = some k := 
              fun k w ww =>
                let lem1 : forwardN (reverseN k w) ww = rc.forward (rc.reverse k w) ww := by rfl                  
                by 
                  rw lem1
                  exact rc.composition k w ww
                  done
            let restClausesN := rc.restClauses 
            let relationN : (k : Nat) → (w: k < codomN) → 
                 restClausesN ⟨k, w⟩ = 
                  dropAt _ focus.val focus.isLt (clausesN (⟨reverseN k w, reverseWitN k w⟩)) := 
                  fun k w =>
                  let lem1 : clausesN (⟨reverseN k w, reverseWitN k w⟩) =
                    clauses (⟨rc.reverse k w, rc.reverseWit k w⟩ ) :=  by rfl
                    by
                      rw lem1
                      exact rc.relation k w
                      done
            let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (⟨reverseN k w, reverseWitN k w⟩) (focus) = some branch) :=
                  fun k w =>
                  let lem1 : clausesN (⟨reverseN k w, reverseWitN k w⟩) =
                    clauses (⟨rc.reverse k w, rc.reverseWit k w⟩) :=  by rfl
                    by
                      rw lem1
                      exact rc.pure k w
                      done 
            RestrictionClauses.mk codomN restClausesN forwardN forwardWitN droppedN 
                reverseN reverseWitN compositionN relationN pureN

theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none :=
  fun x =>
  match x with
  | none => fun _ => by rfl
  | some a => 
    fun eq : some (fn a) = none => Option.noConfusion eq


def prependClause{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1)):
      (rc: RestrictionClauses branch focus clauses) → 
        (head : Clause (n + 1)) → (neg : Not (head focus = some branch)) → 
            RestrictionClauses branch focus (prepend _ head clauses) := 
          fun rc head neg =>
            let headImage := dropAt _ focus.val focus.isLt head
            let domN := dom + 1
            let codomN := rc.codom + 1
            let clausesN := prepend _ head clauses
            let restClausesN := prepend _ headImage rc.restClauses
            let forwardN: (k : Nat) →  k < domN → Option Nat  := 
              fun k  => 
              match k with 
              | 0 => fun _ => some 0
              | l + 1 => 
                fun w : l + 1 < domN   =>  (rc.forward l (leOfSuccLeSucc w)).map (. + 1)
            let forwardWitN : (k: Nat) → (w: k < domN) → boundOpt codomN (forwardN k w) := 
              fun k  => 
              match k with 
              | 0 => fun w => 
                let lem1 : forwardN 0 w = some 0 := by rfl
                by
                  rw lem1
                  apply zeroLtSucc
                  done
              | l + 1 => 
                fun w : l + 1 < domN   => 
                  let lem : forwardN (l + 1) w = 
                    (rc.forward l (leOfSuccLeSucc w)).map (. + 1) := by rfl 
                  let lem2 := boundOptSucc rc.codom 
                            (rc.forward l (leOfSuccLeSucc w))
                            (rc.forwardWit l (leOfSuccLeSucc w))
                  by
                    rw lem
                    exact lem2
                    done
            let reverseN : (k : Nat) →  k < codomN → Nat :=             
              fun k =>
              match k with
              | 0 => fun _ => 0
              | l + 1 => fun w => (rc.reverse l w) + 1
            let reverseWitN : (k : Nat) → (w : k < codomN) → reverseN k w < domN :=
              fun k =>
              match k with
              | 0 => fun _ => zeroLtSucc _ 
              | l + 1 => fun w => 
                rc.reverseWit l w
            let droppedN : 
              (k : Nat) → (w: k < domN) → forwardN k w = none → 
                  clausesN ⟨k, w⟩ focus = some branch :=
                fun k =>
                  match k with
                  | 0 => fun w wf => 
                    let lem1 : forwardN 0 w = some (0) := by rfl
                    let lem2 := Eq.trans (Eq.symm wf) lem1
                    Option.noConfusion lem2
                  | l + 1 => 
                    fun w nw =>
                      let lem1 : forwardN (l + 1) w = 
                        (rc.forward l (leOfSuccLeSucc w)).map (. + 1)  := by rfl
                      let lem2 := Eq.trans (Eq.symm lem1) nw
                      let lem3 := mapNoneIsNone _ _ lem2
                      let lem4 := rc.dropped l (leOfSuccLeSucc w) lem3
                      lem4
                      
            let compositionN: (k : Nat) → (w : k < codomN) → (ww : reverseN k w < domN) → 
                  forwardN (reverseN k w) ww = some k := 
              fun k =>
              match k with
              | 0 => 
                fun w wf => by rfl
              | l + 1 => 
                fun w =>
                  fun ww  =>
                  let lhs := forwardN (reverseN (l + 1) w) (reverseWitN (l + 1) w)
                  let lem1 : reverseN (l + 1) w = (rc.reverse l w) + 1 := by rfl
                  let lem2 : forwardN ((rc.reverse l w) + 1) ww = 
                        (rc.forward (rc.reverse l w) ww).map (. + 1) := by rfl
                  let lem3 : lhs =
                                (rc.forward (rc.reverse l w) ww).map (. + 1) := by rfl
                  let lem4 :=
                    congrArg (fun (n : Option Nat) => n.map (. + 1)) (
                      rc.composition l w ww
                    )
                  let lem5 : lhs = some (l + 1) := Eq.trans lem3 lem4
                  by
                    exact lem5
                    done
            let relationN : (k : Nat) → (w: k < codomN) → 
                 restClausesN ⟨k, w⟩ = 
                  dropAt _ focus.val focus.isLt (clausesN (⟨reverseN k w, reverseWitN k w⟩)) := 
                    fun k =>
                    match k with
                    | 0 => 
                      fun w  => by rfl
                    | l + 1 => 
                      fun w =>
                        let lem1 : restClausesN ⟨l + 1, w⟩ = 
                              rc.restClauses ⟨l, leOfSuccLeSucc w ⟩ := by rfl
                        let lem2 := rc.relation l (leOfSuccLeSucc w) 
                        let lem3 : clausesN ⟨reverseN (l + 1) w, reverseWitN (l + 1) w⟩ = 
                          clauses ⟨rc.reverse l w, rc.reverseWit l w⟩ := by rfl
                        let lem4 := congrArg (dropAt n focus.val focus.isLt)
                          lem3
                        by
                          rw lem1
                          rw lem4
                          exact lem2
                          done
            let pureN : (k : Nat) → (w: k < codomN)  → 
                Not (clausesN (⟨reverseN k w, reverseWitN k w⟩) (focus) = some branch) :=
                fun k =>
                match k with
                | 0 => 
                  fun w  => 
                    fun hyp =>
                      let lem : 
                        clausesN (⟨reverseN 0 w, reverseWitN 0 w⟩) focus = head focus := by rfl
                      let lem2 := Eq.trans (Eq.symm lem) hyp
                      neg lem2
                | l + 1 => 
                  fun w hyp =>
                    let lem : 
                        clausesN (⟨reverseN (l + 1) w, reverseWitN (l + 1) w⟩) focus =
                          clauses ⟨rc.reverse l w, rc.reverseWit l w⟩ focus := by rfl
                    let lem2 := Eq.trans (Eq.symm lem) hyp
                    rc.pure l w lem2
            RestrictionClauses.mk codomN restClausesN forwardN forwardWitN droppedN 
                reverseN reverseWitN compositionN relationN pureN
