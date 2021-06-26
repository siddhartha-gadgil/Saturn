import Saturn.FinSeq 
import Saturn.Solverstep
import Saturn.Resolution
import Saturn.PosRestClause
import Saturn.PrependClause
import Saturn.ExistingClause

open Nat
open leaner

instance {n: Nat} : DecidableEq (Clause n) := fun c1 c2 => deqSeq _ c1 c2

def prependResData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1)
    (clauses: FinSeq dom (Clause (n + 1))): 
        (rd : RestrictionData branch focus focusLt clauses) → 
           (head : Clause (n + 1)) → 
        RestrictionData branch focus focusLt (head +: clauses) := 
        fun rd  head => 
        match findElem? (rd.restrictionClauses.restClauses) (delete focus focusLt head) with
        | some ⟨p, pLt, peqn⟩ =>
            ExistingClauses.prependResData branch focus focusLt clauses rd head p pLt peqn
        | none => 
          if c : head focus focusLt = some branch then
            PosResClause.prependResData branch focus focusLt clauses head c rd
          else
            PrependClause.prependResData branch focus focusLt clauses head c rd
         
def restrictionData{dom n: Nat}(branch: Bool)(focus: Nat)(focusLt : focus < n + 1):
    (clauses: FinSeq dom (Clause (n + 1))) →   
        RestrictionData branch focus focusLt clauses := 
      match dom with 
      | 0 => fun clauses =>  
        let eqn : clauses = FinSeq.empty := funext (fun j => funext (fun w => nomatch w))
        match clauses, eqn with
        | .(FinSeq.empty), rfl =>
          let rc : RestrictionClauses branch focus focusLt FinSeq.empty := 
              ⟨0, FinSeq.empty, 
                fun k w => nomatch w, 
                fun k w => nomatch w, fun k w => nomatch w, fun k w => nomatch w⟩
          ⟨rc,
          ⟨fun k w => nomatch w⟩,
          ⟨fun k w => nomatch w⟩,
          ⟨fun k w => nomatch w⟩, 
          ⟨fun k w => nomatch w⟩⟩
      | l + 1 => fun clauses => 
        let res := prependResData branch focus focusLt (tail clauses) 
          (restrictionData branch focus focusLt (tail clauses))
          (head clauses)
        let lem := headTail clauses
        by
          rw (Eq.symm lem)
          exact res

def containmentLift{dom n: Nat}(clauses : FinSeq dom (Clause (n + 1)))(cntn : Containment clauses):
          SatSolution (cntn.imageSeq) → SatSolution clauses := 
          fun sol =>
          match sol with
          | SatSolution.sat val pf => 
              SatSolution.sat val (
                fun k kw => 
                        let ⟨ind, bd, w⟩ := cntn.forward k kw
                        let ev := pf ind bd
                        let lem := containsSat (clauses k kw) (cntn.imageSeq ind bd) w val
                        lem ev)
              
          | SatSolution.unsat tree chk chkTop => 
                let rpf := 
                  transportResPf cntn.imageSeq clauses cntn.reverse (contradiction (n + 1))
                    tree chk chkTop
                SatSolution.unsat rpf.tree rpf.check rpf.checkTop