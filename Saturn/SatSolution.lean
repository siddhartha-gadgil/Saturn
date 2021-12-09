import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause 
import Saturn.Resolution

/-
Structured solution to a SAT problem. Either a valuation with evidence that it is satisfied
by all the given clauses, or a resolution tree starting with the given clauses.
-/
inductive SatSolution{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) where
  | unsat : (tree : ResolutionTree clauses (contradiction (n + 1))) → 
          SatSolution clauses
  | sat : (valuation : Valuation (n + 1)) → ((k : Nat) → (kw : k < dom) 
        → clauseSat (clauses.coords k kw) valuation) → SatSolution clauses 

def SatSolution.toString{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
        (sol: SatSolution clauses) →  String 
      | unsat tree => "unsat: " ++ tree.toString 
      | sat valuation _ => "sat: " ++ (valuation.coords.list).toString

def solutionProp{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
                  (sol : SatSolution clauses) →  Prop 
| SatSolution.unsat _  => isUnSat clauses
| SatSolution.sat _ _ => isSat clauses

def solutionProof{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  :(sol : SatSolution clauses) → solutionProp sol 
| SatSolution.unsat tree  => tree_unsat clauses tree
| SatSolution.sat valuation evidence => ⟨valuation, evidence⟩
