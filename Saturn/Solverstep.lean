import Saturn.FinSeq
import Saturn.Clause 
open Nat
open Vector

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


theorem mapPlusOneZero{n: Option Nat} : Not (n.map (. + 1) = some zero) :=
  match n with
  | none => fun hyp => 
    Option.noConfusion hyp
  | some j => 
    fun hyp : some (j + 1) = some zero =>
    let lem : j + 1 = zero := by
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
    (clauses: Vector (Clause (n + 1)) dom) where
  codom : Nat
  restClauses : Vector  (Clause n) codom
  forward : (k: Nat) → k < dom → Option Nat
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forward k w)
  reverse : (k : Nat) → (k < codom) → Nat
  reverseWit : (k : Nat) → (w : k < codom) → reverse k w < dom
  
structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (Vector.at (clauses.at k w) focus focusLt = some branch)

structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  delete focus focusLt (Vector.at (clauses.at k w)) = 
      Vector.at (rc.restClauses.at j jw)

structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      Vector.at (rc.restClauses.at k w) = delete focus focusLt 
        (Vector.at (clauses.at (rc.reverse k w) (rc.reverseWit k w)))

structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not (
        Vector.at (clauses.at (rc.reverse k w) (rc.reverseWit k w)) focus focusLt = some branch)

structure RestrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom) where
    restrictionClauses : RestrictionClauses branch focus focusLt clauses
    droppedProof : DroppedProof restrictionClauses
    forwardRelation : ForwardRelation restrictionClauses
    reverseRelation : ReverseRelation restrictionClauses
    nonPosReverse : NonPosReverse restrictionClauses 


def pullBackSolution{dom n: Nat}(branch: Bool)(focus : Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) dom)(rc: RestrictionClauses branch focus focusLt clauses) 
    (dp : DroppedProof rc) (fr: ForwardRelation rc): 
      (valuation : Valuation n) → 
        ((j : Nat) → (jw : j < rc.codom) → ClauseSat (rc.restClauses.at j jw) valuation) → 
        (j : Nat) → (jw : j < dom) →  
          ClauseSat (clauses.at j jw) (FinSeq.vec (insert branch n focus focusLt valuation.at)) := 
        fun valuation pf =>
          fun k w => 
            let splitter := optCase (rc.forward k w)
            match splitter with
            | OptCase.noneCase eqn => 
              let lem1 : Vector.at (clauses.at k w) focus focusLt = some branch := dp.dropped k w eqn
              let lem2 : insert branch n focus focusLt valuation.at focus focusLt = branch := by 
                apply insertAtFocus
                done
              let lem3 : Vector.at (clauses.at k w) focus focusLt = 
                some (insert branch n focus focusLt valuation.at focus focusLt) := 
                by
                  rw lem1
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
              let lem4 : (Vector.at (Vector.at clauses k w) focus focusLt) = some (
                  (Vector.at 
                    (FinSeq.vec (insert branch n focus focusLt 
                      (Vector.at valuation))) focus focusLt)) := 
                      by 
                        rw (seqAt (insert branch n focus focusLt 
                      (Vector.at valuation)))
                        rw lem3
                        done
              ⟨focus, focusLt, lem4⟩
            | OptCase.someCase j eqn => 
              let bound := rc.forwardWit k w 
              let jWitAux : boundOpt rc.codom (some j) := by
                rw (Eq.symm eqn)
                exact bound
                done
              let jWit : j < rc.codom := jWitAux
              let lem1 := fr.forwardRelation k w j eqn jWit
              let ⟨i, iw, vs⟩ := pf j jWit
              let lem2 : Vector.at (rc.restClauses.at j jWit) i iw = 
                      some (valuation.at i iw) := vs
              let lem3 : delete focus focusLt (Vector.at (clauses.at k w)) i iw =
                  some (valuation.at i iw) := 
                    by
                    rw (Eq.symm lem2)
                    rw lem1
                    done
              let lem4 : delete focus focusLt (Vector.at (clauses.at k w)) i iw =
                (Vector.at (clauses.at k w)) (skip focus i) (skipPlusOne iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuation.at 
                              (skip focus i) (skipPlusOne iw) =
                                  valuation.at i iw := by
                                    apply insertAtImage
                                    done
              let lem6 : (Vector.at (clauses.at k w)) (skip focus i) (skipPlusOne iw) =
                          some (insert branch n focus focusLt valuation.at 
                              (skip focus i) (skipPlusOne iw)) := by
                              rw (Eq.symm lem4)
                              rw lem3
                              rw lem5
                              done
              let lem7 : (Vector.at (Vector.at clauses k w) (skip focus i) (skipPlusOne iw)) =
                some (
                  (Vector.at (FinSeq.vec (insert branch n focus focusLt (Vector.at valuation))) 
                    (skip focus i) (skipPlusOne iw))) := 
                      by
                        rw (seqAt (insert branch n focus focusLt (Vector.at valuation)))
                        rw lem6
                        done
              ⟨skip focus i, skipPlusOne iw, lem7⟩


def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  FinSeq.vec (insert (some b) n k w (Vector.at (contradiction n))) 

theorem unitDiag(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          Vector.at (unitClause n b k w) k w = b := by
            have resolve  : unitClause n b k w = 
                FinSeq.vec (insert (some b) n k w (Vector.at (contradiction n))) := rfl
            rw resolve
            rw seqAt
            apply insertAtFocus (some b) n k w (Vector.at (contradiction n))
            done

theorem unitSkip(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          (i: Nat) → (iw : i < n) →  Vector.at (unitClause n b k w) (skip k i) 
                  (skipPlusOne iw) = none := by 
                  intros i iw
                  have resolve  : unitClause n b k w = 
                        FinSeq.vec (insert (some b) n k w (Vector.at (contradiction n))) := rfl
                  rw resolve
                  rw seqAt 
                  let ins := insertAtImage (some b) n k w (Vector.at (contradiction n)) i iw
                  rw ins
                  rw contraAt
                  done

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1)) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) := 
    fun ⟨k, w⟩ =>
      match deqSeq _ clause.at (Vector.at (unitClause n true k w)) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w true (equalCoords pf) 
        some (cl)
      | isFalse _ => 
        match deqSeq _ clause.at (Vector.at (unitClause n false k w)) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w false (equalCoords pf) 
        some (cl)
      | isFalse _ => none  
  let seq : FinSeq (n + 1) (Fin (n + 1)) := fun k w => ⟨k, w⟩
  findSome? f seq

structure SomeUnitClause{l n : Nat}(clauses : FinSeq l  (Clause (n + 1))) where
  pos: Nat
  posBound : pos < l
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clauses pos posBound = unitClause n parity index bound

def someUnitClauseAux {l : Nat} {n : Nat}: (clauses : FinSeq l  (Clause (n + 1))) →  
  (cb: Nat) → (cbBound : cb ≤  l) → Option (SomeUnitClause clauses) → 
  Option (SomeUnitClause clauses)  :=
    fun clauses cb  => 
    match cb with 
    | zero => fun cbBound optCl => optCl
    | m + 1 =>
      fun cbBound optCl =>
      match optCl with
      | some scl => some scl
      | none => 
        match clauseUnit (clauses m cbBound) with
        | some u => some ⟨m, cbBound, u.index, u.bound, u.parity, u.equality⟩ 
        | none => 
          someUnitClauseAux clauses m (Nat.leTrans (Nat.leSucc m) cbBound) none
          


def someUnitClause {l : Nat} {n : Nat}: (clauses : FinSeq l  (Clause (n + 1))) →  
  Option (SomeUnitClause clauses)  := 
    fun clauses =>
     someUnitClauseAux clauses l (Nat.leRefl l) none

structure HasPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < dom) → 
          (Vector.at (clauses.at k lt) index bound = none) ∨  
            (Vector.at (clauses.at k lt) index bound = some parity)

structure IsPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < dom) → (Vector.at (clauses.at k lt) index bound = none) ∨ 
                                (Vector.at (clauses.at k lt) index bound = some parity)

def pureEvidence {dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool): Prop := 
                  (k : Nat) → (lt : k < dom) → 
          (Vector.at (clauses.at k lt) index bound = none) ∨  
          (Vector.at (clauses.at k lt) index bound = some parity)

def pureBeyond{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool)(m: Nat): Prop := 
                  (k : Nat) → (lt : k < dom) → (m ≤ k) → 
          (Vector.at (clauses.at k lt) index bound = none) ∨  
          (Vector.at (clauses.at k lt) index bound = some parity)

def pureBeyondZero{dom n : Nat}(clauses : Vector  (Clause n) dom)
                (index: Nat)(bound : index < n)(parity : Bool) : 
                  pureBeyond clauses index bound parity zero → 
                  pureEvidence clauses index bound parity := by
                    intro hyp
                    intro k
                    intro kw
                    exact hyp k kw  (Nat.zeroLe k)
                    done   

def pureBeyondVacuous{dom n : Nat}(clauses : Vector  (Clause n) dom)
            (index: Nat)(bound : index < n)(parity : Bool)(m: Nat)(le: dom ≤ m): 
            pureBeyond clauses index bound parity m := by
                  intro k
                  intro kw
                  intro ineq
                  let inq := Nat.leTrans le ineq
                  let inq2 := Nat.ltOfLtOfLe kw inq
                  exact (False.elim (Nat.ltIrrefl k inq2))
                  done

structure IsPureVarBeyond{dom n : Nat}(clauses : Vector  (Clause n) dom)
                      (index: Nat)(bound : index < n)(parity : Bool)(m: Nat) where
  evidence : pureBeyond clauses index bound parity m

def varIsPureRec{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) : 
  (dom: Nat) →  (clauses : Vector  (Clause n) dom) → 
    (m: Nat) → Option (IsPureVarBeyond clauses index bound parity m) →
    Option (IsPureVar clauses index bound parity) :=
    fun dom clauses m =>
    match m with
    | zero => fun opt => 
        opt.map (fun pb => ⟨pureBeyondZero clauses index bound parity pb.evidence⟩)
    | p + 1 => 
      fun opt => 
        match opt with 
        | none => none
        | some pureBeyondEv => 
          if pw : p < dom then
            let head := Vector.at (clauses.at p pw) index bound
              if pf : (head = none) ∨  (head = some parity) then
                let evidence : pureBeyond clauses index bound parity p := 
                  by
                    intro k 
                    intro kw
                    intro ineq
                    cases Nat.eqOrLtOfLe ineq with
                    | inl eql =>           
                      let lem1 : clauses.at p pw = clauses.at k kw := by
                        apply witnessIndependent
                        exact eql
                        done
                      rw ← lem1
                      exact pf
                      done
                    | inr l2 => 
                      exact pureBeyondEv.evidence k kw l2 
                      done   
                varIsPureRec index bound parity dom clauses p (some ⟨evidence⟩)
              else none
          else 
            none -- can recurse here but never called so making TCO easy

def varIsPure{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) : 
  (dom: Nat) →  (clauses : Vector  (Clause n) dom) → 
    Option (IsPureVar clauses index bound parity) :=
    fun dom clauses =>
      varIsPureRec index bound parity dom clauses dom 
        (some ⟨pureBeyondVacuous clauses index bound parity dom (Nat.leRefl _)⟩)

def findPureAux{n : Nat} : (dom: Nat) →  (clauses : Vector  (Clause (n +1)) dom) → 
  (ub: Nat) → (lt : ub < n + 1) → 
      Option (HasPureVar clauses) :=
      fun dom clauses ub => 
        match ub with
        | zero =>
          fun lt =>
           ((varIsPure zero lt true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk zero lt true evidence
              )).orElse (
                (varIsPure zero lt false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk zero lt false evidence
              )
              )
        | l + 1 =>
          fun lt =>
            let atCursor := 
                ((varIsPure l (leStep lt) true dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (leStep lt) true evidence
                )
                ).orElse (              
                (varIsPure l (leStep lt) false dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (leStep lt) false evidence
                ))
            match atCursor with
            | some res => some res
            |none =>
              findPureAux dom clauses l (leStep lt)
            
def hasPure{n : Nat}{dom: Nat}(clauses : Vector  (Clause (n +1)) dom) 
             : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.leRefl _)


