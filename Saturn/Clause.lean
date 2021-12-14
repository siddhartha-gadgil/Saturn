import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Prover
open Nat
open Vector
open FinSeq

/- A SAT problem is a set of clauses. Here we define structures corresponding to clauses, 
and prove their basic properties. 

Variables are assumed to correspond to integers. Literals correspond to associating to each variable
a term of type `Option Bool`, with `none` meaning absence of the variable in the clause, and 
`some b` meaning its presence with `b` a boolean indicating whether the variable or its negation 
is part of the clause. Thus, clauses correspond to `FinSeq n (Option Bool)`, with `n` the number
of variables. Similarly a valuation (assignment of `true` or `false` to each variable) is a
term of type `FinSeq n Bool`.

We also define unit clauses, which are clauses that have only one literal, and pure clauses.
We define functions that find unit clauses and pure variables in a finite sequence of clauses,
with proofs.
-/


/-
Contradictions and basic properties
-/
abbrev contradiction(n: Nat) : Clause n :=
  FinSeq.vec (fun _ _ => none)

theorem contra_at_none(n: Nat) : (contradiction n).coords = (fun _ _ => none) := 
              by apply seq_to_vec_coords


theorem contradiction_is_false (n: Nat) : ∀ valuation : Valuation n, 
          Not (clauseSat (contradiction n) valuation) :=
  fun valuation => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : (contradiction n).coords k b = none := by rw [contra_at_none n]
    let lem2 : varSat ((contradiction n).coords k b) = varSat none := congrArg varSat lem1
    let lem3 : varSat ((contradiction n).coords k b) (valuation.coords k b) = 
                varSat none (valuation.coords k b) := congr lem2 rfl
    let lem4 : (varSat none (valuation.coords k b)) = (none = some (valuation.coords k b)) := rfl
    let lem5 : (none = some (valuation.coords k b)) := by
      rw [← lem4]
      rw [← lem2]
      exact p
      done 
    Option.noConfusion lem5

theorem contradiction_insert_none{n : Nat} (focus: Nat)(focusLt : focus < n + 1) :
      insert none n focus focusLt ((contradiction n).coords) =
                          (contradiction (n + 1)).coords :=
      let lem0 : (j: Nat) → (jw : j < n + 1) →  
            insert none n focus focusLt ((contradiction n).coords) j jw  =
                      (contradiction (n + 1)).coords j jw := 
                      fun j jw =>
                      let lem0 : (contradiction (n + 1)).coords j jw = none := 
                          by rw [contra_at_none]
                      if c : j= focus then 
                        match focus, c, focusLt with
                        | .(j), rfl, .(jw) =>
                          by
                            rw [insert_at_focus] 
                            rw [contra_at_none]
                            done                                
                      else  
                        let i := skipInverse focus j c 
                        let eqn : skip focus i = j := skip_inverse_eq focus j c
                        let iw := skip_preimage_lt focusLt jw eqn
                        match j, eqn, jw, lem0 with
                        | .(skip focus i), rfl, .(skip_le_succ iw), lem1 =>  
                          by
                            rw [lem1]
                            rw [insert_at_image 
                               none n focus focusLt ((contradiction n).coords)
                               i iw]
                            rw [contra_at_none]
                            done                               
                 by
                    apply funext
                    intro j
                    apply funext
                    intro jw
                    apply lem0
                    done

def Clause.toString {n: Nat}: Clause n → String :=
  fun (cls : Clause n) => (cls.coords.list).toString

instance {n: Nat} : ToString (Clause n) := 
  ⟨fun (cls : Clause n) => (cls.coords.list).toString⟩

/-
Unit clauses: definitions and finding with proofs
-/

def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  FinSeq.vec (insert (some b) n k w ((contradiction n).coords)) 

theorem unitDiag(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          (unitClause n b k w).coords k w = b := by
            have resolve  : unitClause n b k w = 
                FinSeq.vec (insert (some b) n k w ((contradiction n).coords)) := rfl
            rw [resolve]
            rw [seq_to_vec_coords]
            apply insert_at_focus (some b) n k w ((contradiction n).coords)
            done

theorem unitSkip(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          (i: Nat) → (iw : i < n) → (unitClause n b k w).coords (skip k i) 
                  (skip_le_succ iw) = none := by 
                  intros i iw
                  have resolve  : unitClause n b k w = 
                        FinSeq.vec (insert (some b) n k w ((contradiction n).coords)) := rfl
                  rw [resolve]
                  rw [seq_to_vec_coords] 
                  let ins := insert_at_image (some b) n k w ((contradiction n).coords) i iw
                  rw [ins]
                  rw [contra_at_none]
                  done

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1))(parity: Bool) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) := 
    fun ⟨k, w⟩ =>
      match deqSeq _ clause.coords ((unitClause n parity k w).coords) with 
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

/-
Pure variables: definitions and finding with proofs
-/

structure HasPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < dom) → 
          ((clauses.coords k lt).coords index bound = none) ∨  
            ((clauses.coords k lt).coords index bound = some parity)

structure IsPureVar{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < dom) → ((clauses.coords k lt).coords index bound = none) ∨ 
                                ((clauses.coords k lt).coords index bound = some parity)

def pureEvidence {dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool): Prop := 
                  (k : Nat) → (lt : k < dom) → 
          ((clauses.coords k lt).coords index bound = none) ∨  
          ((clauses.coords k lt).coords index bound = some parity)

def pureBeyond{dom n : Nat}(clauses : Vector  (Clause n) dom) 
                  (index: Nat)(bound : index < n)(parity : Bool)(m: Nat): Prop := 
                  (k : Nat) → (lt : k < dom) → (m ≤ k) → 
          ((clauses.coords k lt).coords index bound = none) ∨  
          ((clauses.coords k lt).coords index bound = some parity)

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
            let head := (clauses.coords p pw).coords index bound
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
           match (varIsPure zero lt true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk zero lt true evidence
              ) with 
              | none => 
                (varIsPure zero lt false dom clauses).map (
                  fun ⟨evidence⟩ =>
                    HasPureVar.mk zero lt false evidence
                    )
              | some pv => some pv
        | l + 1 =>
          fun lt =>
            let atCursor := 
                match (varIsPure l (le_step  (le_of_succ_le_succ lt)) true dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) true evidence
                ) with 
                | none =>            
                (varIsPure l (le_step (le_of_succ_le_succ lt)) false dom clauses).map (
              fun ⟨evidence⟩ =>
                HasPureVar.mk l (le_step (le_of_succ_le_succ lt)) false evidence
                )
                | some pv => some pv
            match atCursor with
            | some res => some res
            |none =>
              findPureAux dom clauses l (le_step (le_of_succ_le_succ lt))
            
def hasPure{n : Nat}{dom: Nat}(clauses : Vector  (Clause (n +1)) dom) 
             : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.le_refl _)


