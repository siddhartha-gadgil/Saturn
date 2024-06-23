import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.Solverstep
open Nat
open Vector
open FinSeq

/--
The inductive step for adding a new clause when it is not dropped. The new clauses and maps
are defined. All the witnesses for the relations between the old and new clauses are also
constructed.
-/
def prependClause{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
            ReductionClauses branch focus focusLt (head +: clauses) :=
          fun rc head _ =>
            let headImage := Vector.ofFn' (delete focus focusLt head.get')
            let domN := num_clauses + 1
            let codomN := rc.num_reducedClauses + 1
            let restClausesN := headImage +: rc.restClauses
            let forwardVecN := (some zero) +: (rc.forwardVec.map (fun nop => nop.map (. + 1)) )
            let forwardN: (k : Nat) →  k < domN → Option Nat  :=
              fun k  =>
              match k with
              | zero => fun _ => some zero
              | l + 1 =>
                fun w : l + 1 < domN   =>  (rc.forward l (le_of_succ_le_succ w)).map (. + 1)
            have forwardNEq : forwardVecN.get' = forwardN := by
                  apply funext
                  intro j
                  cases j with
                  | zero =>
                    apply funext
                    intro jw
                    rfl
                  | succ i =>
                    apply funext
                    intro jw
                    rw [get'_cons_succ (some zero) (rc.forwardVec.map (fun nop => nop.map (. + 1))),
                      get'_map]
            have forwardWitN : (k: Fin domN) →
                boundOpt codomN (forwardN k.val k.isLt) := by
              intro ⟨k, w⟩
              match k with
              | zero =>
                  simp [forwardN]
                  apply zero_lt_succ
              | l + 1 =>
                  simp [forwardN]
                  exact boundOptSucc rc.num_reducedClauses
                            (rc.forward l (le_of_succ_le_succ w))
                            (rc.forwardWit ⟨ l, (le_of_succ_le_succ w)⟩)
            let reverseVecN := zero +: (rc.reverseVec.map (. + 1))
            let reverseN : (k : Nat) →  k < codomN → Nat :=
              fun k =>
              match k with
              | zero => fun _ => zero
              | l + 1 => fun w => (rc.reverse l (Nat.le_of_succ_le_succ w)) + 1
            have reverseNEq : reverseVecN.get' = reverseN := by
                  apply funext
                  intro j
                  cases j with
                  | zero =>
                    apply funext
                    intro jw
                    rfl
                  | succ i =>
                    apply funext
                    intro jw
                    rw [get'_cons_succ zero (rc.reverseVec.map (. + 1)),
                        get'_map]
            have reverseWitN : (k : Fin codomN) →
                reverseN k.val k.isLt < domN :=
              fun ⟨k, w⟩ =>
              match k with
              | zero => zero_lt_succ _
              | l + 1 => by
                  apply succ_le_succ
                  exact rc.reverseWit ⟨l, (le_of_succ_le_succ w)⟩
                  done
            {
            num_reducedClauses := codomN,
            restClauses := restClausesN,
            forwardVec := forwardVecN,
            forwardWit :=  forwardNEq ▸ forwardWitN
            reverseVec :=  reverseVecN,
            reverseWit :=  reverseNEq ▸ reverseWitN
            }


theorem restClauses_prependClause{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses)(rc: ReductionClauses branch focus focusLt clauses)
        (head : Clause (n + 1))(neg : Not (head.get' focus focusLt = some branch)) :
    (prependClause branch focus focusLt clauses rc head neg).restClauses =
      (Vector.ofFn' (delete focus focusLt head.get')) +: rc.restClauses :=
          rfl

theorem reverseVec_prependClause{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses)(rc: ReductionClauses branch focus focusLt clauses)
        (head : Clause (n + 1))(neg : Not (head.get' focus focusLt = some branch)) :
    (prependClause branch focus focusLt clauses rc head neg).reverseVec =
      zero +: (rc.reverseVec.map (. + 1)) :=
          rfl

theorem none_mapsto_none{α β : Type}(fn: α → β): (x: Option α) → (x.map fn = none) → x = none
  | none, rfl => by rfl

theorem map_plusone_not_somezero{n: Option Nat} : Not (n.map (. + 1) = some zero) :=
  match n with
  | none => fun hyp =>
    Option.noConfusion hyp
  | some j =>
    fun hyp : some (j + 1) = some zero =>
    let lem : j + 1 = zero := by
      injection hyp

    Nat.noConfusion lem

theorem map_plusone_pred{n : Option Nat}{m : Nat} : n.map (. + 1) = some (m + 1) →
  n = some m :=
    match n with
  | none => fun hyp =>
    Option.noConfusion hyp
  | some j =>
    fun hyp : some (j + 1) = some (m + 1) =>
      let lem1 : j + 1 = m + 1 := by
        injection hyp

      let lem2 : j = m := by
        injection lem1

    congrArg some lem2


namespace PrependClause

theorem forwardResolve{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
        (l: Nat) → (w : l + 1 < num_clauses + 1) →
          (prependClause  branch focus focusLt clauses rc head neg).forward (l + 1) w =
            (rc.forward l (le_of_succ_le_succ w)).map (. + 1) := by
                  intro rc head _ l w
                  simp [ReductionClauses.forward, ReductionClauses.forwardVec, prependClause]
                  simp [Vector.get']
                  have s : { val := l + 1, isLt := w } = Fin.succ
                    ⟨l, le_of_succ_le_succ w⟩ := by rfl
                  rw [s]
                  rw [Vector.get_cons_succ, Vector.get_map]


def droppedProof{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
          DroppedProof rc →
          DroppedProof (prependClause  branch focus focusLt clauses rc head neg) :=
          fun rc head neg drc =>
            let rcN := prependClause  branch focus focusLt clauses rc head neg
            let domN := num_clauses + 1
            let clausesN := head +: clauses
            let droppedN :
              (k : Nat) → (w: k < domN) → rcN.forward k w = none →
                  (clausesN.get' k w).get' focus focusLt = some branch :=
                by
                  intro k
                  match k with
                  | zero =>
                    intro w wf
                    exact Option.noConfusion wf
                  | l + 1 =>
                    intro w nw
                    have clres: clausesN.get' (l + 1) w =
                        clauses.get' l (le_of_succ_le_succ w) := by rfl
                    rw [clres]
                    have prev := drc.dropped l (le_of_succ_le_succ w)
                    apply prev
                    rw [forwardResolve] at nw
                    apply none_mapsto_none (. + 1)
                    exact nw
            ⟨droppedN⟩

def forwardRelation{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
          ForwardRelation rc →
          ForwardRelation (prependClause  branch focus focusLt clauses rc head neg) :=
        fun rc head neg frc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg
          let domN := num_clauses + 1
          let codomN := rc.num_reducedClauses + 1
          let clausesN := head +: clauses
          have forwardRelationN : (k : Nat) → (w: k < domN) → (j: Nat) →  rcN.forward k w = some j →
              (jw : j < codomN) →  delete focus focusLt ((clausesN.get' k w).get') =
                (rcN.restClauses.get' j jw).get' := by
                intro k
                match k with
                | zero =>
                    intro w j sw
                    let lem1 : rcN.forward zero w = some zero := by rfl
                    let lem2 : some j = some zero := Eq.trans (Eq.symm sw) lem1
                    let lem3 : j = zero := by
                      injection lem2

                    rw [lem3]
                    intro jw
                    have hl1 : clausesN.get' zero w = head := by rfl
                    rw [hl1]
                    have hl2 : rcN.restClauses.get' zero jw =
                         Vector.ofFn' (delete focus focusLt (head.get')) := by rfl
                    rw [hl2]
                    apply Eq.symm
                    apply Vector.of_Fn'_get'
                | l + 1 =>
                    intro w
                    match c:rcN.forward (l + 1) w with
                    | none =>
                      intro j sw jw
                      simp at sw
                    | some zero =>
                      rw [forwardResolve] at c
                      have contra:= map_plusone_not_somezero c
                      contradiction
                    | some (j + 1) =>
                      intro j1 eq1
                      have eq2 : j + 1 = j1 := by
                        injection eq1
                      rw [← eq2]
                      intro jw
                      simp [Vector.get']
                      rw [forwardResolve] at c
                      let cc:= map_plusone_pred c
                      let rel := frc.forwardRelation l (le_of_succ_le_succ w) j cc
                            (le_of_succ_le_succ jw)
                      rw [Vector.get'] at rel
                      have s : { val := l + 1, isLt := w } =
                        Fin.succ ⟨l, le_of_succ_le_succ w⟩ := by rfl
                      rw [s, Vector.get_cons_succ]
                      rw [rel]
                      simp [Vector.get']
                      rfl
          ⟨forwardRelationN⟩


theorem reverseResolve{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
        (l: Nat) → (w : l + 1 < rc.num_reducedClauses + 1) →
          (prependClause  branch focus focusLt clauses rc head neg).reverse (l + 1) w =
            (rc.reverse l (le_of_succ_le_succ w)) + 1 := by
            intro rc head _ l w
            simp [ReductionClauses.reverse, ReductionClauses.reverseVec, prependClause, Vector.get', get'_map]
            have s : { val := l + 1, isLt := w } = Fin.succ
                    ⟨l, le_of_succ_le_succ w⟩ := by rfl
            rw [s, Vector.get_cons_succ, Vector.get_map]

theorem revrelAux (v : Vector Nat num_reducedClauses)(clauses: Vector (Clause (n + 1)) num_clauses)(head: Clause (n + 1))(l: Nat)(w: l < num_reducedClauses)(bd : v.get ⟨l, w⟩ < num_clauses):
    Vector.get clauses { val := Vector.get v { val := l, isLt := w }, isLt := bd } =
  Vector.get (head ::ᵥ clauses)
    { val := Vector.get (0 ::ᵥ map (fun x ↦ x + 1) v) (Fin.succ { val := l, isLt := w }), isLt :=
      by
        have l : Vector.get (0 ::ᵥ map (fun x ↦ x + 1) v) (Fin.succ { val := l, isLt := w }) =  v.get ⟨l, w⟩ + 1  := by
          rw [Vector.get_cons_succ]
          rw [Vector.get_map]
        rw [l]
        apply Nat.succ_lt_succ
        exact bd
      } := by
        symm
        let lem :=
          Vector.get_cons_succ 0 (map (fun x ↦ x + 1) v) ⟨l, w⟩
        rw [Vector.get_map] at lem
        let lem' : Fin.succ { val := Vector.get v { val := l, isLt := w }, isLt := bd } =
          ⟨ Vector.get (0 ::ᵥ map (fun x ↦ x + 1) v) (Fin.succ { val := l, isLt := w }), by
              rw [lem]
              apply Nat.succ_lt_succ
              exact bd
          ⟩  := by
            apply Fin.eq_of_val_eq
            simp
            symm
            exact lem
        let lem'' :=
          Vector.get_cons_succ head clauses ⟨Vector.get v { val := l, isLt := w }, bd⟩
        rw [lem'] at lem''
        exact lem''

def reverseRelation{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
          ReverseRelation rc →
          ReverseRelation (prependClause  branch focus focusLt clauses rc head neg) :=
        fun rc head pos rrc =>
          let rcN := prependClause  branch focus focusLt clauses rc head pos
          let codomN := rcN.num_reducedClauses
          let clausesN := head +: clauses
          have relationN : (k : Nat) → (w: k < codomN) →
                 (rcN.restClauses.get ⟨k, w⟩).get' =
                  delete focus focusLt
                      (clausesN.get' (rcN.reverse k w)
                      (rcN.reverseWit ⟨ k, w⟩ )).get' :=
                    by
                    intro k w
                    match k, w with
                    | zero, _ =>
                      simp [Vector.get', Vector.of_Fn'_get]
                      rw [restClauses_prependClause]
                      simp [reverseVec_prependClause]
                      apply Vector.of_Fn'_get'
                    | l + 1, w =>
                      let w' := (le_of_succ_le_succ w)
                      let lem2 := rrc.relation l w'
                      simp [Vector.get', ReverseRelation.relation]
                      rw [Vector.get'] at lem2
                      rw [restClauses_prependClause]
                      simp [rcN, reverseVec_prependClause]
                      show get' ((ofFn' (delete focus focusLt (get' head))+:rc.restClauses).get (⟨l, w'⟩ : Fin _).succ) = _
                      rw [Vector.get_cons_succ]
                      rw [lem2]
                      simp [ReductionClauses.reverse]
                      rw [Vector.get']
                      funext j jw
                      let fn (cl: Clause (n + 1))  :=
                        delete focus focusLt cl.get' j jw
                      apply congrArg fn
                      simp [Vector.get', Vector.get_cons_succ]
                      let v := rc.reverseVec
                      show Vector.get clauses
                        { val := Vector.get v { val := l, isLt := _ }, isLt := _ } =
                          Vector.get (head ::ᵥ clauses)
                            { val := Vector.get (0 ::ᵥ map (fun x ↦ x + 1) v) (
                              Fin.succ { val := l, isLt :=
                              Nat.le_of_succ_le_succ w }), isLt := _ }
                      apply
                        revrelAux v clauses head l (Nat.le_of_succ_le_succ w)
          ⟨relationN⟩

#check Vector.get_cons_succ

def pureReverse{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
      (rc: ReductionClauses branch focus focusLt clauses) →
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
          NonPosReverse rc →
          NonPosReverse (prependClause  branch focus focusLt clauses rc head neg) :=
        fun rc head neg prc =>
          let rcN := prependClause  branch focus focusLt clauses rc head neg
          let codomN := rc.num_reducedClauses + 1
          let clausesN := head +: clauses
          have pureN : (k : Nat) → (w: k < codomN)  →
                Not (
                  (clausesN.get' (rcN.reverse k w) (rcN.reverseWit ⟨k, w⟩)).get'
                    (focus) focusLt = some branch) := by
                intro k
                match k with
                | zero =>
                      intro w hyp
                      apply neg
                      let lem :
                         (clausesN.get' (rcN.reverse zero w) (rcN.reverseWit ⟨zero, w⟩ )).get'
                          focus focusLt = head.get' focus focusLt := by rfl
                      rw [← lem]
                      exact hyp
                | l + 1 =>
                    intro w hyp
                    have rs0 : clausesN.get' (rcN.reverse (l + 1) w)
                                (rcN.reverseWit ⟨ (l + 1), w⟩) =
                                  clausesN.get'
                                    (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                    (succ_le_succ
                                      (rc.reverseWit ⟨l, (Nat.le_of_succ_le_succ w)⟩ )) := by
                                    apply witness_independent
                                    apply reverseResolve
                    rw [rs0] at hyp
                    have rs1 : clausesN.get'
                                    (rc.reverse l (Nat.le_of_succ_le_succ w) + 1)
                                    (succ_le_succ
                                      (rc.reverseWit ⟨l, (Nat.le_of_succ_le_succ w)⟩)) =
                                        clauses.get' (rc.reverse l (Nat.le_of_succ_le_succ w))
                                        (rc.reverseWit ⟨l, (Nat.le_of_succ_le_succ w)⟩) := by rfl
                    rw [rs1] at hyp
                    let prev := prc.nonPosRev l (Nat.le_of_succ_le_succ w)
                    simp [hyp] at prev
          ⟨pureN⟩


def prependResData{num_clauses n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: Vector (Clause (n + 1)) num_clauses):
        (head : Clause (n + 1)) → (neg : Not (head.get' focus focusLt = some branch)) →
        (rd : ReductionData branch focus focusLt clauses) →
        ReductionData branch focus focusLt (head +: clauses) :=
          fun head neg rd =>
          let rc := prependClause branch focus focusLt clauses rd.restrictionClauses head neg
          ⟨rc,
          droppedProof branch focus focusLt clauses rd.restrictionClauses head neg rd.droppedProof,
          forwardRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.forwardRelation,
          reverseRelation branch focus focusLt clauses rd.restrictionClauses head neg rd.reverseRelation,
          pureReverse branch focus focusLt clauses rd.restrictionClauses head neg rd.nonPosReverse⟩

end PrependClause
