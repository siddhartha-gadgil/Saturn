import Saturn.Basic
import Saturn.FinSeq 
open Nat

set_option maxHeartbeats 500000

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
  forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  forward k w = some j →
    (jw : j < codom) →  dropAt _ focus.val focus.isLt (clauses (⟨k, w⟩) ) = 
      restClauses ⟨j, jw⟩
  reverse : (k : Nat) → (k < codom) → Nat
  reverseWit : (k : Nat) → (w : k < codom) → reverse k w < dom
  composition: (k : Nat) → (w : k < codom) → (ww : reverse k w < dom) → 
    forward (reverse k w) ww = some k
  relation : (k : Nat) → (w: k < codom) → 
    restClauses ⟨k, w⟩ = dropAt _ focus.val focus.isLt (clauses (⟨reverse k w, reverseWit k w⟩))
  pure : (k : Nat) → (w: k < codom)  → 
    Not (clauses (⟨reverse k w, reverseWit k w⟩) (focus) = some branch)




theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none :=
  fun x =>
  match x with
  | none => fun _ => by rfl
  | some a => 
    fun eq : some (fn a) = none => Option.noConfusion eq


