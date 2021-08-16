import Saturn.FinSeq
open Nat




def Clause(n : Nat) : Type := FinSeq n (Option Bool)

def Valuat(n: Nat) : Type := FinSeq n  Bool



structure ClauseSat{n: Nat}(clause : Clause n)(valuat: Valuat n) where
  coord : Nat
  bound : coord < n  
  witness: varSat (clause coord bound) (valuat coord bound)

def clauseSat {n: Nat}(clause : Clause n)(valuat: Valuat n) := 
  ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuat k b)

instance {n: Nat}(clause : Clause n)(valuat: Valuat n): Prover (ClauseSat clause valuat) where 
  statement := fun cs => ∃ (k : Nat), ∃ (b : k < n), varSat (clause k b) (valuat k b)
  proof := fun cs => ⟨cs.coord, ⟨cs.bound, cs.witness⟩⟩

def contrad(n: Nat) : Clause n :=
  fun _ _ => none

theorem contradFalse (n: Nat) : ∀ valuat : Valuat n, Not (clauseSat (contrad n) valuat) :=
  fun valuat => fun ⟨k, ⟨b, p⟩⟩ => 
    let lem1 : (contrad n) k b = none := by rfl
    let lem2 := congrArg varSat lem1
    let lem3 : varSat (contrad n k b) (valuat k b) = 
                varSat none (valuat k b) := congr lem2 rfl
    let lem4 : (varSat none (valuat k b)) = (none = some (valuat k b)) := rfl
    let lem5 : (none = some (valuat k b)) := by
      rw (Eq.symm lem4)
      rw lem4
      assumption
      done 
    Option.noConfusion lem5

theorem contradInsNone{n : Nat} (focus: Nat)(focusLt : focus < n + 1) :
      insert none n focus focusLt (contrad n) =
                            contrad (n + 1) :=
      let lem0 : (j: Nat) → (jw : j < n + 1) →  
            insert none n focus focusLt (contrad n) j jw  =
                      contrad (n + 1) j jw := 
                      fun j jw =>
                      let lem0 : contrad (n + 1) j jw = none := by rfl
                      match skipImageCase focus j with
                      | SkipImageCase.diag eqn => 
                        match focus, eqn, focusLt with
                        | .(j), rfl, .(jw) =>
                          by
                            apply insertAtFocus 
                            done                                
                      | SkipImageCase.image i eqn => 
                        let iw := skipPreImageBound focusLt jw eqn
                        match j, eqn, jw, lem0 with
                        | .(skip focus i), rfl, .(skipPlusOne iw), lem1 =>  
                          by
                            rw lem1
                            apply insertAtImage
                            exact iw
                            done                               
                 by
                    apply funext
                    intro j
                    apply funext
                    intro jw
                    apply lem0
                    done



def unitClause(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1):   Clause (n + 1):=
  insert (some b) n k w (contrad n) 

theorem unitDiag(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          unitClause n b k w k w = b :=
          insertAtFocus (some b) n k w (contrad n)

theorem unitSkip(n : Nat)(b : Bool)(k : Nat) (w : k < n + 1): 
          (i: Nat) → (iw : i < n) →  unitClause n b k w (skip k i) 
                  (skipPlusOne iw) = none := fun i iw => 
          insertAtImage (some b) n k w (contrad n) i iw

structure IsUnitClause{n: Nat}(clause: Clause (n +1)) where
  index: Nat 
  bound : index < n + 1
  parity: Bool
  equality : clause = unitClause n parity index bound

def clauseUnit{n: Nat}(clause: Clause (n + 1)) : Option (IsUnitClause clause) :=
  let f : Fin (n + 1) →   (Option (IsUnitClause clause)) := 
    fun ⟨k, w⟩ =>
      match deqSeq _ clause  (unitClause n true k w) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w true pf 
        some (cl)
      | isFalse _ => 
        match deqSeq _ clause  (unitClause n false k w) with 
      | isTrue pf => 
        let cl : IsUnitClause clause := IsUnitClause.mk k w false pf 
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

def someUnitClause {l : Nat} {n : Nat}: (clauses : FinSeq l  (Clause (n + 1))) →  
  Option (SomeUnitClause clauses)  := 
    match l with 
    | 0 => fun  _ =>  none
    | m + 1 => 
      fun  cls =>
        match clauseUnit (cls 0 (zeroLtSucc m)) with
        | some u => some ⟨0, zeroLtSucc _, u.index, u.bound, u.parity, u.equality⟩ 
        | none => 
          let tcls := tail cls
          let tail := someUnitClause  tcls
          match tail with
          | some ⟨i, w, index, bd, par, eql⟩ => 
            some ⟨i + 1, leOfSuccLeSucc w, index, bd, par, eql⟩
          | none => none

structure HasPureVar{dom n : Nat}(clauses : FinSeq dom  (Clause n)) where
  index : Nat
  bound : index < n
  parity : Bool
  evidence : (k : Nat) → (lt : k < dom) → 
          (clauses k lt index bound = none) ∨  (clauses k lt index bound = some parity)

structure IsPureVar{dom n : Nat}(clauses : FinSeq dom  (Clause n))
                      (index: Nat)(bound : index < n)(parity : Bool) where
  evidence : (k : Nat) → (lt : k < dom) → (clauses k lt index bound = none) ∨ 
                                (clauses k lt index bound = some parity)

def varIsPure{n : Nat}(index: Nat)(bound : index < n)(parity : Bool) : 
  (dom: Nat) →  (clauses : FinSeq dom  (Clause n)) → 
    Option (IsPureVar clauses index bound parity) :=
  fun dom =>
  match dom with
  | 0 => 
    fun clauses =>
      let evidence : (k : Nat) → (lt : k < 0) →  
        (clauses k lt index bound = none) ∨ (clauses k lt index bound = some parity) := 
          fun k lt => nomatch lt
      some ⟨evidence⟩
  | m + 1 => 
      fun clauses =>
        let head := clauses 0 (zeroLtSucc _) index bound
        if c : (head = none) ∨  (head = some parity) then
          let tailSeq  := tail clauses
          (varIsPure index bound parity _ tailSeq).map (
            fun ⟨ tpf ⟩ =>
              let pf : (j : Nat) → (w : j < (m +1)) → 
                (clauses j w index bound = none) ∨ (clauses j w index bound = some parity) := 
                fun j =>
                  match j with 
                  | 0 => fun w => c
                  | i + 1 => fun w =>
                    let tailWit : i < m := leOfSuccLeSucc w 
                    tpf i tailWit
              ⟨ pf ⟩
          )
        else none

def findPureAux{n : Nat} : (dom: Nat) →  (clauses : FinSeq dom (Clause (n +1))) → 
  (ub: Nat) → (lt : ub < n + 1) → 
      Option (HasPureVar clauses) :=
      fun dom clauses ub => 
        match ub with
        | 0 =>
          fun lt =>
           ((varIsPure 0 lt true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk 0 lt true evidence
              )).orElse (
                (varIsPure 0 lt false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk 0 lt false evidence
              )
              )
        | l + 1 =>
          fun lt =>
            ((findPureAux dom clauses l (leStep lt)).orElse (              
              (varIsPure l (leStep lt) true dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk l (leStep lt) true evidence
              )
              )).orElse (              
              (varIsPure l (leStep lt) false dom clauses).map (
            fun ⟨evidence⟩ =>
              HasPureVar.mk l (leStep lt) false evidence
              )
              )
            
def hasPure{n : Nat}{dom: Nat}(clauses : FinSeq dom  (Clause (n +1))) 
             : Option (HasPureVar clauses) :=
          findPureAux dom clauses n (Nat.leRefl _)

