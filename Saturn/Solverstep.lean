import Saturn.FinSeq
import Saturn.Vector
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

theorem mapNoneIsNone{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none 
  | none, rfl => by rfl

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
  forwardVec : Vector (Option Nat) dom
  forwardWit : (k: Nat) → (w: k < dom) → boundOpt codom (forwardVec.coords k w)
  reverseVec : Vector Nat codom
  reverseWit : (k : Nat) → (w : k < codom) → reverseVec.coords k w < dom
  
def RestrictionClauses.forward{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: RestrictionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < dom) → Option Nat := rc.forwardVec.coords

def RestrictionClauses.reverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}
      (rc: RestrictionClauses branch focus focusLt clauses) :
        (j: Nat) → (jw : j < rc.codom) → Nat := rc.reverseVec.coords


structure DroppedProof{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    dropped : (k : Nat) → (w: k < dom) → rc.forward k w = 
        none → (Vector.coords (clauses.coords k w) focus focusLt = some branch)

structure ForwardRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    forwardRelation : (k : Nat) → (w: k < dom) → (j: Nat) →  rc.forward k w = some j →
    (jw : j < rc.codom) →  delete focus focusLt (Vector.coords (clauses.coords k w)) = 
      Vector.coords (rc.restClauses.coords j jw)

structure ReverseRelation{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    relation : (k : Nat) → (w: k < rc.codom) → 
      Vector.coords (rc.restClauses.coords k w) = delete focus focusLt 
        (Vector.coords (clauses.coords (rc.reverse k w) (rc.reverseWit k w)))

structure NonPosReverse{dom n: Nat}{branch: Bool}{focus: Nat}{focusLt : focus < n + 1}
    {clauses: Vector (Clause (n + 1)) dom}(
        rc: RestrictionClauses branch focus focusLt clauses)  where
    nonPosRev : (k : Nat) → (w: k < rc.codom)  → 
      Not (
        Vector.coords (clauses.coords (rc.reverse k w) (rc.reverseWit k w)) focus focusLt = some branch)

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
        ((j : Nat) → (jw : j < rc.codom) → ClauseSat (rc.restClauses.coords j jw) valuation) → 
        (j : Nat) → (jw : j < dom) →  
          ClauseSat (clauses.coords j jw) (FinSeq.vec (insert branch n focus focusLt valuation.coords)) := 
        fun valuation pf =>
          fun k w => 
            let splitter := (rc.forward k w)
            match eq:splitter with
            | none => 
              let lem1 : Vector.coords (clauses.coords k w) focus focusLt = some branch := dp.dropped k w eq
              let lem2 : insert branch n focus focusLt valuation.coords focus focusLt = branch := by 
                apply insertAtFocus
                done
              let lem3 : Vector.coords (clauses.coords k w) focus focusLt = 
                some (insert branch n focus focusLt valuation.coords focus focusLt) := 
                by
                  rw [lem1]
                  apply (congrArg some)
                  exact Eq.symm lem2
                  done
              let lem4 : (Vector.coords (Vector.coords clauses k w) focus focusLt) = some (
                  (Vector.coords 
                    (FinSeq.vec (insert branch n focus focusLt 
                      (Vector.coords valuation))) focus focusLt)) := 
                      by 
                        rw [seq_to_vec_coords (insert branch n focus focusLt 
                      (Vector.coords valuation))]
                        rw [lem3]
                        done
              ⟨focus, focusLt, lem4⟩
            | some j => 
              let bound := rc.forwardWit k w 
              let jWitAux : boundOpt rc.codom (some j) := by
                rw [←  eq]
                exact bound
                done
              let jWit : j < rc.codom := jWitAux
              let lem1 := fr.forwardRelation k w j eq jWit
              let ⟨i, iw, vs⟩ := pf j jWit
              let lem2 : Vector.coords (rc.restClauses.coords j jWit) i iw = 
                      some (valuation.coords i iw) := vs
              let lem3 : delete focus focusLt (Vector.coords (clauses.coords k w)) i iw =
                  some (valuation.coords i iw) := 
                    by
                    rw [←  lem2]
                    rw [lem1]
                    done
              let lem4 : delete focus focusLt (Vector.coords (clauses.coords k w)) i iw =
                (Vector.coords (clauses.coords k w)) (skip focus i) (skip_le_succ iw) := by
                  rfl
                  done
              let lem5 : insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw) =
                                  valuation.coords i iw := by
                                    apply insertAtImage
                                    done
              let lem6 : (Vector.coords (clauses.coords k w)) (skip focus i) (skip_le_succ iw) =
                          some (insert branch n focus focusLt valuation.coords 
                              (skip focus i) (skip_le_succ iw)) := by
                              rw [← lem4]
                              rw [lem3]
                              rw [lem5]
                              done
              let lem7 : (Vector.coords (Vector.coords clauses k w) (skip focus i) (skip_le_succ iw)) =
                some (
                  (Vector.coords (FinSeq.vec (insert branch n focus focusLt (Vector.coords valuation))) 
                    (skip focus i) (skip_le_succ iw))) := 
                      by
                        rw [seq_to_vec_coords (insert branch n focus focusLt (Vector.coords valuation))]
                        rw [lem6]
                        done
              ⟨skip focus i, skip_le_succ iw, lem7⟩


def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  FinSeq.vec (insert (some b) n k w (Vector.coords (contradiction n))) 

theorem unitDiag(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          Vector.coords (unitClause n b k w) k w = b := by
            have resolve  : unitClause n b k w = 
                FinSeq.vec (insert (some b) n k w (Vector.coords (contradiction n))) := rfl
            rw [resolve]
            rw [seq_to_vec_coords]
            apply insertAtFocus (some b) n k w (Vector.coords (contradiction n))
            done

theorem unitSkip(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          (i: Nat) → (iw : i < n) →  Vector.coords (unitClause n b k w) (skip k i) 
                  (skip_le_succ iw) = none := by 
                  intros i iw
                  have resolve  : unitClause n b k w = 
                        FinSeq.vec (insert (some b) n k w (Vector.coords (contradiction n))) := rfl
                  rw [resolve]
                  rw [seq_to_vec_coords] 
                  let ins := insertAtImage (some b) n k w (Vector.coords (contradiction n)) i iw
                  rw [ins]
                  rw [contraAt]
                  done

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1))(parity: Bool) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) := 
    fun ⟨k, w⟩ =>
      match deqSeq _ clause.coords (Vector.coords (unitClause n parity k w)) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w parity (coords_eq_implies_vec_eq pf) 
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
  Vector Nat l →  Vector Nat l →
  (cb: Nat) → (cbBound : cb ≤  l) → Option (SomeUnitClause clauses) → 
  Option (SomeUnitClause clauses)  :=
    fun clauses posCount negCount cb => 
    match cb with 
    | zero => fun cbBound optCl => optCl
    | m + 1 =>
      fun cbBound optCl =>
      match optCl with
      | some scl => some scl
      | none => 
        if (posCount.coords m cbBound) + (negCount.coords m cbBound) = 1 then
        let parity := (posCount.coords m cbBound) == 1
        match clauseUnit (clauses m cbBound) parity with
        | some u => some ⟨m, cbBound, u.index, u.bound, u.parity, u.equality⟩ 
        | none => 
          someUnitClauseAux clauses 
            posCount negCount m (Nat.le_trans (Nat.le_succ m) cbBound) none
        else none


def someUnitClause {l : Nat} {n : Nat}: (clauses : FinSeq l  (Clause (n + 1))) →  
  Vector Nat l → 
  Vector Nat l →
  Option (SomeUnitClause clauses)  := 
    fun clauses posCount negCount =>
     someUnitClauseAux clauses posCount negCount l (Nat.le_refl l) none

structure HasPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < dom) → 
          (Vector.coords (clauses.coords k lt) index bound = none) ∨  
            (Vector.coords (clauses.coords k lt) index bound = some parity)

structure IsPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < dom) → (Vector.coords (clauses.coords k lt) index bound = none) ∨ 
                                (Vector.coords (clauses.coords k lt) index bound = some parity)

def pureEvidence {dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool): Prop := 
                  (k : Nat) → (lt : k < dom) → 
          (Vector.coords (clauses.coords k lt) index bound = none) ∨  
          (Vector.coords (clauses.coords k lt) index bound = some parity)

def pureBeyond{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool)(m: Nat): Prop := 
                  (k : Nat) → (lt : k < dom) → (m ≤ k) → 
          (Vector.coords (clauses.coords k lt) index bound = none) ∨  
          (Vector.coords (clauses.coords k lt) index bound = some parity)

def pureBeyondZero{dom n : Nat}(clauses : Vector  (Clause n) dom)
                (index: Nat)(bound : index < n)(parity : Bool) : 
                  pureBeyond clauses index bound parity zero → 
                  pureEvidence clauses index bound parity := by
                    intro hyp
                    intro k
                    intro kw
                    exact hyp k kw  (Nat.zero_le k)
                    done   

def pureBeyondVacuous{dom n : Nat}(clauses : Vector  (Clause n) dom)
            (index: Nat)(bound : index < n)(parity : Bool)(m: Nat)(le: dom ≤ m): 
            pureBeyond clauses index bound parity m := by
                  intro k
                  intro kw
                  intro ineq
                  let inq := Nat.le_trans le ineq
                  let inq2 := Nat.lt_of_lt_of_le kw inq
                  exact (False.elim (Nat.lt_irrefl k inq2))
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
            let head := Vector.coords (clauses.coords p pw) index bound
              if pf : (head = none) ∨  (head = some parity) then
                let evidence : pureBeyond clauses index bound parity p := 
                  by
                    intro k 
                    intro kw
                    intro ineq
                    cases Nat.eq_or_lt_of_le ineq with
                    | inl eql =>           
                      let lem1 : clauses.coords p pw = clauses.coords k kw := by
                        apply witness_independent
                        exact eql
                        done
                      rw [← lem1]
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
        (some ⟨pureBeyondVacuous clauses index bound parity dom (Nat.le_refl _)⟩)

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
                ((varIsPure l (le_step  (le_of_succ_le_succ lt)) true dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) true evidence
                )
                ).orElse (              
                (varIsPure l (le_step (le_of_succ_le_succ lt)) false dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) false evidence
                ))
            match atCursor with
            | some res => some res
            |none =>
              findPureAux dom clauses l (le_step (le_of_succ_le_succ lt))
            
def hasPure{n : Nat}{dom: Nat}(clauses : Vector  (Clause (n +1)) dom) 
             : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.le_refl _)


