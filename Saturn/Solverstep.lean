import Saturn.FinSeq
import Saturn.Clause 
open Nat

def boundOpt(n: Nat) : Option (Nat) → Prop
  | none => True
  | some b => b < n

def boundOptSucc(n: Nat)(p: Option Nat) : boundOpt n p → boundOpt (n + 1) (p.map (. + 1)) :=
  match p with
  | none => fun h => True.intro
  | some a => fun h : a < n => succ_lt_succ h

theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none :=
  fun x eqn =>
  match x, eqn with
  | none, rfl => by rfl

inductive OptCase{α: Type} (opt: Option α) where
  | noneCase : opt = none → OptCase opt
  | someCase : (x : α) → (opt = some x) → OptCase opt

def optCase{α: Type} : (opt: Option α) →  OptCase opt :=
    fun x =>
    match x with
    | none =>  
      OptCase.noneCase rfl
    | some j => 
      OptCase.someCase j rfl


theorem mapPlusOneZero{n: Option Nat} : Not (n.map (. + 1) = some 0) :=
  match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some 0 =>
    let lem : j + 1 = 0 := by
      injection hyp
      assumption
    Nat.noConfusion lem

theorem mapPlusOneShift{n : Option Nat}{m : Nat} : n.map (. + 1) = some (m + 1) → 
  n = some m :=
    match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some (m + 1) => 
      let lem1 : j + 1 = m + 1 := by
        injection hyp
        assumption
      let lem2 : j = m := by
        injection lem1
        assumption 
    congrArg some lem2

structure RestrictionClauses{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))) where
  codom : Nat
  restClauses : FinSeq codom  (Clause n)
  forward : (k: Nat) → k < dom → Option Nat
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forward k w)
  reverse : (k : Nat) → (k < codom) → Nat
  reverseWit : (k : Nat) → (w : k < codom) → reverse k w < dom
  
structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: FinSeq dom (Clause (n + 1))}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (clauses k w focus focusLt = some branch)

structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: FinSeq dom (Clause (n + 1))}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  delete focus focusLt (clauses k w) = 
      rc.restClauses j jw

structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: FinSeq dom (Clause (n + 1))}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      rc.restClauses k w = delete focus focusLt 
        (clauses (rc.reverse k w) (rc.reverseWit k w))

structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: FinSeq dom (Clause (n + 1))}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not ((clauses (rc.reverse k w) (rc.reverseWit k w)) focus focusLt = some branch)

structure RestrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))) where
    restrictionClauses : RestrictionClauses branch focus focusLt clauses
    droppedProof : DroppedProof restrictionClauses
    forwardRelation : ForwardRelation restrictionClauses
    reverseRelation : ReverseRelation restrictionClauses
    nonPosReverse : NonPosReverse restrictionClauses 


def pullBackSolution{dom n: Nat}(branch: Bool)(focus : Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (valuation : Valuation n) → 
        ((j : Nat) → (jw : j < rc.codom) → ClauseSat (rc.restClauses j jw) valuation) → 
        (j : Nat) → (jw : j < dom) →  
          ClauseSat (clauses j jw) (insert branch n focus focusLt valuation) := 
        fun valuation pf =>
          fun k w => 
            let splitter := optCase (rc.forward k w)
            match splitter with
            | OptCase.noneCase eqn => 
              let lem1 : clauses k w focus focusLt = some branch := dp.dropped k w eqn
              let lem2 : insert branch n focus focusLt valuation focus focusLt = branch := by 
                apply insertAtFocus
                done
              let lem3 : clauses k w focus focusLt = 
                some (insert branch n focus focusLt valuation focus focusLt) := 
                by
                  rw lem1
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
              ⟨focus, focusLt, lem3⟩
            | OptCase.someCase j eqn => 
              let bound := rc.forwardWit k w 
              let jWitAux : boundOpt rc.codom (some j) := by
                rw (Eq.symm eqn)
                exact bound
                done
              let jWit : j < rc.codom := jWitAux
              let lem1 := fr.forwardRelation k w j eqn jWit
              let ⟨i, iw, vs⟩ := pf j jWit
              let lem2 : rc.restClauses j jWit i iw = some (valuation i iw) := vs
              let lem3 : delete focus focusLt (clauses k w) i iw =
                  some (valuation i iw) := 
                    by
                    rw (Eq.symm lem2)
                    rw lem1
                    done
              let lem4 : delete focus focusLt (clauses k w) i iw =
                clauses k w (skip focus i) (skipPlusOne iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuation 
                              (skip focus i) (skipPlusOne iw) =
                                  valuation i iw := by
                                    apply insertAtImage
                                    done
              let lem6 : clauses k w (skip focus i) (skipPlusOne iw) =
                          some (insert branch n focus focusLt valuation 
                              (skip focus i) (skipPlusOne iw)) := by
                              rw (Eq.symm lem4)
                              rw lem3
                              rw lem5
                              done
              ⟨skip focus i, skipPlusOne iw, lem6⟩



