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
  reverse : (k : Nat) → (k < codom) → Nat
  reverseWit : (k : Nat) → (w : k < codom) → reverse k w < dom
  
structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Fin (n + 1)}
    {clauses: Fin dom →  Clause (n + 1)}(
        rc: RestrictionClauses branch focus clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (clauses ⟨k, w⟩ focus = some branch)

structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Fin (n + 1)}
    {clauses: Fin dom →  Clause (n + 1)}(
        rc: RestrictionClauses branch focus clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  dropAt _ focus.val focus.isLt (clauses (⟨k, w⟩) ) = 
      rc.restClauses ⟨j, jw⟩

def optCasesProp : (x : Option Nat) → Or (x = none) (∃ j, x = some j) :=
  fun x =>
    match x with
    | none =>  
      Or.inl rfl
    | some j => 
      Or.inr ⟨j, rfl⟩

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

structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Fin (n + 1)}
    {clauses: Fin dom →  Clause (n + 1)}(
        rc: RestrictionClauses branch focus clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      rc.restClauses ⟨k, w⟩ = dropAt _ focus.val focus.isLt 
        (clauses (⟨rc.reverse k w, rc.reverseWit k w⟩))

structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Fin (n + 1)}
    {clauses: Fin dom →  Clause (n + 1)}(
        rc: RestrictionClauses branch focus clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not (clauses (⟨rc.reverse k w, rc.reverseWit k w⟩) (focus) = some branch)

theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none :=
  fun x =>
  match x with
  | none => fun _ => by rfl
  | some a => 
    fun eq : some (fn a) = none => Option.noConfusion eq

def pullBackSolution{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1))(rc: RestrictionClauses branch focus clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (sect : Sect n) → 
        ((j : Fin rc.codom) → ClauseSat (rc.restClauses j) sect) → 
        (j : Fin dom) →  
          ClauseSat (clauses j) (liftAt branch n focus.val focus.isLt sect) := 
        fun sect pf =>
          fun ⟨k, w⟩ => 
            let splitter := optCase (rc.forward k w)
            match splitter with
            | OptCase.noneCase eqn => 
              let lem0 : ⟨focus.val, focus.isLt⟩ = focus := 
                by
                apply Fin.eqOfVeq
                rfl
                done
              let lem1 := dp.dropped k w eqn
              let lem2 := liftAtFocus branch n focus.val focus.isLt sect
              let lem3 : liftAt branch n focus.val focus.isLt sect focus = branch := 
                Eq.trans (congrArg (liftAt branch n focus.val focus.isLt sect) 
                  (Eq.symm lem0)) lem2
              let lem4 : clauses ⟨k, w⟩ focus = 
                some (liftAt branch n focus.val focus.isLt sect focus) := 
                Eq.trans lem1 (congrArg some (Eq.symm lem3))
              ⟨focus, lem4⟩
            | OptCase.someCase j eqn => 
              let bound := rc.forwardWit k w 
              let jWitAux : boundOpt rc.codom (some j) := by
                rw (Eq.symm eqn)
                exact bound
                done
              let jWit : j < rc.codom := jWitAux
              let lem1 := fr.forwardRelation k w j eqn jWit
              let ⟨i, vs⟩ := pf ⟨j, jWit⟩
              let lem2 : rc.restClauses ⟨j, jWit⟩ i = some (sect i) := vs
              let lem3 : dropAt _ focus.val focus.isLt (clauses ⟨k, w⟩) i =
                  some (sect i) := 
                    by
                    rw (Eq.symm lem2)
                    rw lem1
                    done
              let lem4 : dropAt _ focus.val focus.isLt (clauses ⟨k, w⟩) i =
                clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) := by
                  apply dropAtShift
                  done
              let lem5 : clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) =
                          some (sect i) := Eq.trans (Eq.symm lem4) lem3
              let lem6 : liftAt branch n focus.val focus.isLt sect 
                              (shiftAt n focus.val focus.isLt i) =
                                  sect i := by
                                    apply liftAtImage
                                    done
              let lem7 : clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) =
                          some (liftAt branch n focus.val focus.isLt sect 
                              (shiftAt n focus.val focus.isLt i)) := by
                              rw lem5
                              rw lem6
                              done
              ⟨shiftAt n focus.val focus.isLt i, lem7⟩

def contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ (k : Fin n), ∀ b : Bool, cl2 k = some b → cl1 k = some b

infix:65 " ⊃ " => contains

theorem containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊃  cl2 → (sect : Sect n) → ClauseSat cl2 sect → ClauseSat cl1 sect :=
    fun dom sect  =>
      fun ⟨j, vs⟩ =>
        let lem0 :  cl2 j = some (sect j) := vs 
        let lem1 := dom j (sect j) lem0
        ⟨j, lem1⟩

def varContains (v1 v2 : Option Bool) : Prop :=
  ∀ b : Bool, v2 = some b → v1  = some b

infix:65 " ≥ " => varContains

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

def containPrepend{n: Nat}(v1 v2 : Option Bool)(cl1 cl2 : Clause n) :
          v1 ≥  v2 → cl1 ⊃  cl2 → 
                (v1 ::: cl1) ⊃  (v2 ::: cl2) := 
           fun hyp1 hyp2 =>
            fun k =>
            match k with
            | ⟨0, w⟩ => fun b =>
              fun hb => 
                hyp1 b hb
            | ⟨j + 1, w⟩  =>  
              fun b =>
                fun hb =>
                  hyp2 ⟨j, leOfSuccLeSucc w⟩ b hb

structure DominateList{n dom codom : Nat}
      (l1 : Fin dom → Clause n)(l2 : Fin codom → Clause n) where
    incl : (j : Fin codom) → SigmaEqElem l1 (l2 j)
    proj : (j : Fin dom) → SigmaPredElem l2 ((l1 j) ⊃ .)
  
structure RelDominateList{n dom codom prev : Nat}
      (l1 : Fin dom → Clause n)(l2 : Fin codom → Clause n)
      (givens : Fin prev → Clause n) where
    incl : (j : Fin codom) → SigmaEqElem l1 (l2 j)
    proj : (j : Fin dom) → 
              Sum  
                (SigmaPredElem l2 ((l1 j) ⊃ .))
                (SigmaPredElem givens ((l1 j) ⊃ .))

def containsTail{n: Nat} (cl1 cl2 : Clause (n + 1)) :
        cl1 ⊃  cl2 → (dropHead n cl1) ⊃ (dropHead n cl2) :=
        fun hyp =>
          fun ⟨k, w⟩ b =>
            fun dHyp =>
              hyp ⟨k + 1, succ_lt_succ w⟩ b dHyp              

def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊃  cl2) :=
    match n with
    | 0 => 
        fun cl1 cl2 => isTrue (fun i => nomatch i)
    | m + 1 => 
      fun cl1 cl2 =>
      match decideContains m (dropHead m cl1) (dropHead m cl2) with
      | isFalse contra =>
          isFalse (fun hyp =>
                      contra (containsTail cl1 cl2 hyp))
      | isTrue pfTail =>
          match varDomDecide (cl1 ⟨0, zeroLtSucc _⟩) (cl2 ⟨0, zeroLtSucc _⟩) with
          | isTrue pfHead =>
              let lem0 := 
                (containPrepend (cl1 ⟨0, zeroLtSucc _⟩) (cl2 ⟨0, zeroLtSucc _⟩) 
                    (dropHead m cl1) (dropHead m cl2) pfHead) pfTail 
              let lem1a :
                (j: Fin (m + 1)) → 
                   ((cl1 ⟨0, zeroLtSucc _⟩) ::: (dropHead m cl1)) j = cl1 j := 
                   fun j =>
                   match j with 
                   | ⟨0, w⟩ => by rfl
                   | ⟨i + 1, w⟩ => by rfl
              let lem1b : (cl1 ⟨0, zeroLtSucc _⟩) ::: (dropHead m cl1)  = cl1  := 
                funext lem1a
              let lem2a :
                (j: Fin (m + 1)) → 
                   ((cl2 ⟨0, zeroLtSucc _⟩) ::: (dropHead m cl2)) j = cl2 j := 
                   fun j =>
                   match j with 
                   | ⟨0, w⟩ => by rfl
                   | ⟨i + 1, w⟩ => by rfl
              let lem2b : (cl2 ⟨0, zeroLtSucc _⟩) ::: (dropHead m cl2)  = cl2  := 
                funext lem2a
              let lem : cl1 ⊃  cl2 := by
                rw (Eq.symm lem1b)
                rw (Eq.symm lem2b)
                exact lem0
                done
              isTrue (
                lem
              )
          | isFalse contra => 
            isFalse (fun hyp =>
                        contra ( 
                          fun b => 
                             hyp ⟨0, zeroLtSucc _⟩ b 
                          )                           
                          )

instance {n: Nat}{cl: Clause n} : DecidablePred (contains cl) :=
  decideContains n cl
