import Saturn.Basic
import Saturn.FinSeq 
open Nat

def boundOpt(n: Nat) : Option (Nat) → Prop
  | none => True
  | some b => b < n

def boundOptSucc(n: Nat)(p: Option Nat) : boundOpt n p → boundOpt (n + 1) (p.map (. + 1)) :=
  match p with
  | none => fun h => True.intro
  | some a => fun h : a < n => succ_lt_succ h

theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none :=
  fun x =>
  match x with
  | none => fun _ => by rfl
  | some a => 
    fun eq : some (fn a) = none => Option.noConfusion eq

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


namespace leaner


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

def contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ k : Nat, ∀ kw : k < n, ∀ b : Bool, cl2 k kw = some b → cl1 k kw = some b

infix:65 " ⊇  " => contains

def containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊇  cl2 → (valuat : Valuat n) → ClauseSat cl2 valuat → ClauseSat cl1 valuat :=
    fun dom valuat  =>
      fun ⟨j, jw, vs⟩ =>
        let lem0 :  cl2 j jw = some (valuat j jw) := vs 
        let lem1 := dom j jw (valuat j jw) lem0
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

def decideContains(n: Nat) : (cl1: Clause n) →  (cl2 : Clause n) → 
                                          Decidable (cl1 ⊇   cl2) :=
    match n with
    | 0 => 
        fun cl1 cl2 => isTrue (fun i iw => nomatch iw)
    | m + 1 => 
      fun cl1 cl2 =>
      match decideContains m (tail cl1) (tail cl2) with
      | isFalse contra =>
          isFalse (fun hyp =>
                      contra (containsTail cl1 cl2 hyp))
      | isTrue pfTail =>
          match varDomDecide (cl1 0 (zeroLtSucc _)) (cl2 0 (zeroLtSucc _)) with
          | isTrue pfHead =>
              let lem0 := 
                (containsPrepend (cl1 0 (zeroLtSucc _)) (cl2 0 (zeroLtSucc _)) 
                    (tail cl1) (tail cl2) pfHead) pfTail 
              let lem1b : (cl1 0 (zeroLtSucc _)) +:  (tail cl1)  = cl1  := 
                funext (fun j =>
                          match j with
                          | 0 => funext (fun jw => rfl)
                          | i + 1 => funext (fun jw => rfl)
                          )
              let lem2b : (cl2 0 (zeroLtSucc _)) +:  (tail cl2)  = cl2  := 
                funext (fun j =>
                          match j with
                          | 0 => funext (fun jw => rfl)
                          | i + 1 => funext (fun jw => rfl)
                          )
              let lem : cl1 ⊇   cl2 := by
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
                             hyp 0 (zeroLtSucc _) b 
                          )                           
                          )


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
                    |0 => fun _ => ⟨0, FinSeq.empty, fun j jw => nomatch jw, fun j jw => nomatch jw⟩ 
                    | m + 1 => 
                        fun clauses =>
                        let ht := prependContainment (initialContainment (tail clauses)) (head clauses)
                        Eq.mp (congrArg Containment (headTail clauses)) ht

structure NatSucc (n: Nat) where
  pred: Nat
  eqn : n = succ (pred)

def posSucc : (n : Nat) → Not (0 = n) → NatSucc n :=
  fun n =>
  match n with
  | 0 => fun w => absurd rfl w
  | l + 1 => fun _ => ⟨l, rfl⟩

def simplifyNonEmptyContainment{d n : Nat}: (cursorBound : Nat) →  (base : FinSeq (d + 1) (Clause n)) → 
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
                        simplifyNonEmptyContainment (m + 1) clauses (initialContainment clauses)

-- this is not recursive
def simplifyContainmentHead{dom n : Nat}: (base : FinSeq dom (Clause n)) → 
      Containment (base) → Containment (base) :=
  match dom with
  | 0 => fun _  => id
  | m + 1 => 
    fun base contn =>
      let ⟨k, (ineq : k < contn.codom), _⟩ := contn.forward 0 (zeroLtSucc _)      
      let neZero : Not (0 = contn.codom) := fun hyp => 
        let l0 : k < 0 := by
          rw hyp
          exact ineq
          done
        Nat.notLtZero k l0
      let ⟨l, leqn⟩ := posSucc contn.codom neZero
      match contn.codom, leqn, contn.imageSeq, contn.forward, contn.reverse with
      | .(l + 1), rfl, imageSeq, forward, reverse =>
        match subClause? (head imageSeq) (tail imageSeq) with 
        | none => 
          ⟨l + 1, imageSeq, forward, reverse⟩
        | some ⟨zi, zb, zc⟩ => 
          let codomN := l
          let imageSeqN := tail imageSeq
          let domN := m + 1
          let forwardN : (j : Nat) → (jw : j < domN) → 
                  ElemSeqPred imageSeqN (contains (base j jw)) := 
                  fun j jw => 
                  match forward j jw with 
                  | ⟨0, _, (ctn : base j jw ⊇ head imageSeq)⟩ => 
                    let c := containsTrans _ _ _ ctn zc
                    ⟨zi, zb, c⟩
                  | ⟨i + 1, iw, ctn⟩ =>                    
                    ⟨i, leOfSuccLeSucc iw, ctn⟩
          let reverseN : (j : Nat) → (jw : j < codomN) → 
                  ElemInSeq base (imageSeqN j jw) := 
                  fun i =>
                    fun iw => 
                    let ⟨ind, bd, ctn⟩ := reverse (i + 1) iw
                    ⟨ ind, succ_lt_succ bd, by 
                          exact ctn
                          done⟩
          ⟨codomN, imageSeqN, forwardN, reverseN⟩


def pullBackSolution{dom n: Nat}(branch: Bool)(focus : Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1)))(rc: RestrictionClauses branch focus focusLt clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (valuat : Valuat n) → 
        ((j : Nat) → (jw : j < rc.codom) → ClauseSat (rc.restClauses j jw) valuat) → 
        (j : Nat) → (jw : j < dom) →  
          ClauseSat (clauses j jw) (insert branch n focus focusLt valuat) := 
        fun valuat pf =>
          fun k w => 
            let splitter := optCase (rc.forward k w)
            match splitter with
            | OptCase.noneCase eqn => 
              let lem1 : clauses k w focus focusLt = some branch := dp.dropped k w eqn
              let lem2 : insert branch n focus focusLt valuat focus focusLt = branch := by 
                apply insertAtFocus
                done
              let lem3 : clauses k w focus focusLt = 
                some (insert branch n focus focusLt valuat focus focusLt) := 
                by
                  rw lem1
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
                -- Eq.trans lem1 (congrArg some (Eq.symm lem3))
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
              let lem2 : rc.restClauses j jWit i iw = some (valuat i iw) := vs
              let lem3 : delete focus focusLt (clauses k w) i iw =
                  some (valuat i iw) := 
                    by
                    rw (Eq.symm lem2)
                    rw lem1
                    done
              let lem4 : delete focus focusLt (clauses k w) i iw =
                clauses k w (skip focus i) (skipPlusOne iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuat 
                              (skip focus i) (skipPlusOne iw) =
                                  valuat i iw := by
                                    apply insertAtImage
                                    done
              let lem6 : clauses k w (skip focus i) (skipPlusOne iw) =
                          some (insert branch n focus focusLt valuat 
                              (skip focus i) (skipPlusOne iw)) := by
                              rw (Eq.symm lem4)
                              rw lem3
                              rw lem5
                              done
              ⟨skip focus i, skipPlusOne iw, lem6⟩


end leaner

namespace clunky


theorem liftSatHead {n: Nat}(clause : Clause (n + 1))(valuat: Valuat (n + 1)) :
  ClauseSat (dropHead n clause) (dropHead n valuat) → ClauseSat clause valuat := 
    fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropHead n clause ⟨k, w⟩ = clause (⟨k+1, _⟩) := by rfl
      let l2 : dropHead n valuat ⟨k, w⟩ = valuat ⟨k+1, _⟩ := by rfl
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause ⟨k+1, _⟩) (valuat ⟨k+1, _⟩) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨⟨k+1, _⟩, pf⟩


theorem liftSatAt {n: Nat}(clause : Clause (n + 1))(valuat: Valuat (n + 1)) :
  (j : Nat) → (lt : j < n + 1) → 
  ClauseSat (dropAt n j lt clause) (dropAt n j lt valuat) → ClauseSat clause valuat := 
    fun j =>
    fun lt =>
     fun ⟨⟨k, w⟩, tpf⟩ => 
      let l1 : dropAt n j lt clause ⟨k, w⟩ = clause (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt clause ⟨k, w⟩
      let l2 : dropAt n j lt valuat ⟨k, w⟩ = valuat (shiftAt n j lt ⟨k, w⟩) := 
        dropAtShift n j lt valuat ⟨k, w⟩
      let l3 := congrArg varSat l1
      let l4 := congr l3 l2
      let pf : varSat (clause (shiftAt n j lt ⟨k, w⟩)) (valuat (shiftAt n j lt ⟨k, w⟩)) := by
        rw (Eq.symm l4)
        exact tpf
        done
      ⟨(shiftAt n j lt ⟨k, w⟩), pf⟩


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


def pullBackSolution{dom n: Nat}(branch: Bool)(focus: Fin (n + 1))
    (clauses: Fin dom →  Clause (n + 1))(rc: RestrictionClauses branch focus clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (valuat : Valuat n) → 
        ((j : Fin rc.codom) → ClauseSat (rc.restClauses j) valuat) → 
        (j : Fin dom) →  
          ClauseSat (clauses j) (liftAt branch n focus.val focus.isLt valuat) := 
        fun valuat pf =>
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
              let lem2 := liftAtFocus branch n focus.val focus.isLt valuat
              let lem3 : liftAt branch n focus.val focus.isLt valuat focus = branch := 
                Eq.trans (congrArg (liftAt branch n focus.val focus.isLt valuat) 
                  (Eq.symm lem0)) lem2
              let lem4 : clauses ⟨k, w⟩ focus = 
                some (liftAt branch n focus.val focus.isLt valuat focus) := 
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
              let lem2 : rc.restClauses ⟨j, jWit⟩ i = some (valuat i) := vs
              let lem3 : dropAt _ focus.val focus.isLt (clauses ⟨k, w⟩) i =
                  some (valuat i) := 
                    by
                    rw (Eq.symm lem2)
                    rw lem1
                    done
              let lem4 : dropAt _ focus.val focus.isLt (clauses ⟨k, w⟩) i =
                clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) := by
                  apply dropAtShift
                  done
              let lem5 : clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) =
                          some (valuat i) := Eq.trans (Eq.symm lem4) lem3
              let lem6 : liftAt branch n focus.val focus.isLt valuat 
                              (shiftAt n focus.val focus.isLt i) =
                                  valuat i := by
                                    apply liftAtImage
                                    done
              let lem7 : clauses ⟨k, w⟩ (shiftAt n focus.val focus.isLt i) =
                          some (liftAt branch n focus.val focus.isLt valuat 
                              (shiftAt n focus.val focus.isLt i)) := by
                              rw lem5
                              rw lem6
                              done
              ⟨shiftAt n focus.val focus.isLt i, lem7⟩

def contains{n: Nat} (cl1 cl2 : Clause n) : Prop :=
  ∀ (k : Fin n), ∀ b : Bool, cl2 k = some b → cl1 k = some b

infix:65 " ⊃ " => contains

theorem containsSat{n: Nat} (cl1 cl2 : Clause n) :
  cl1 ⊃  cl2 → (valuat : Valuat n) → ClauseSat cl2 valuat → ClauseSat cl1 valuat :=
    fun dom valuat  =>
      fun ⟨j, vs⟩ =>
        let lem0 :  cl2 j = some (valuat j) := vs 
        let lem1 := dom j (valuat j) lem0
        ⟨j, lem1⟩


def containsPrepend{n: Nat}(v1 v2 : Option Bool)(cl1 cl2 : Clause n) :
          v1 ≥  v2 → cl1 ⊃  cl2 → 
                (v1 ::::  cl1) ⊃  (v2 ::::  cl2) := 
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
                (containsPrepend (cl1 ⟨0, zeroLtSucc _⟩) (cl2 ⟨0, zeroLtSucc _⟩) 
                    (dropHead m cl1) (dropHead m cl2) pfHead) pfTail 
              let lem1a :
                (j: Fin (m + 1)) → 
                   ((cl1 ⟨0, zeroLtSucc _⟩) ::::  (dropHead m cl1)) j = cl1 j := 
                   fun j =>
                   match j with 
                   | ⟨0, w⟩ => by rfl
                   | ⟨i + 1, w⟩ => by rfl
              let lem1b : (cl1 ⟨0, zeroLtSucc _⟩) ::::  (dropHead m cl1)  = cl1  := 
                funext lem1a
              let lem2a :
                (j: Fin (m + 1)) → 
                   ((cl2 ⟨0, zeroLtSucc _⟩) ::::  (dropHead m cl2)) j = cl2 j := 
                   fun j =>
                   match j with 
                   | ⟨0, w⟩ => by rfl
                   | ⟨i + 1, w⟩ => by rfl
              let lem2b : (cl2 ⟨0, zeroLtSucc _⟩) ::::  (dropHead m cl2)  = cl2  := 
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


def optCasesProp : (x : Option Nat) → Or (x = none) (∃ j, x = some j) :=
  fun x =>
    match x with
    | none =>  
      Or.inl rfl
    | some j => 
      Or.inr ⟨j, rfl⟩



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
