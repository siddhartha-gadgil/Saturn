import Saturn.Core
import Saturn.FinSeq
import Saturn.Vector
import Saturn.Clause
import Saturn.Resolution

/--
Structured solution to a SAT problem. Either a valuation with evidence that it is satisfied
by all the given clauses, or a resolution tree starting with the given clauses.
-/
inductive SatSolution{dom n: Nat}(clauses : Vector (Clause (n + 1)) dom) where
  | unsat : (tree : ResolutionTree clauses (contradiction (n + 1))) →
          SatSolution clauses
  | sat : (valuation : Vector Bool (n + 1)) → ((k : Nat) → (kw : k < dom)
        → clauseSat (clauses.get' k kw) valuation) → SatSolution clauses

instance {dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
  Repr (SatSolution clauses) where
  reprPrec := by
        intro satSoln m
        cases satSoln
        case unsat tree =>
          exact "UNSAT: " ++ .line ++ reprPrec tree m
        case sat valuation evidence =>
          let valFormat := reprPrec (valuation.toList) m
          let clauseList := clauses.toList.map (fun c => clauseSummary c)
          exact "SAT: " ++  valFormat ++ .line ++
                "Satisfying Clauses: " ++
                reprPrec (clauseList) m

def SatSolution.toString{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
        (sol: SatSolution clauses) →  String
      | soln => repr soln  |>.pretty

def solutionProp{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}:
                  (sol : SatSolution clauses) →  Prop
| SatSolution.unsat _  => isUnSat clauses
| SatSolution.sat _ _ => isSat clauses

def solutionProof{dom n: Nat}{clauses : Vector (Clause (n + 1)) dom}
                  :(sol : SatSolution clauses) → solutionProp sol
| SatSolution.unsat tree  => tree_unsat clauses tree
| SatSolution.sat valuation evidence => ⟨valuation, evidence⟩
