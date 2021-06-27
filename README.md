# SATurn : SAT Solver-prover in lean 4

__SATurn__ is a SAT solver-prover in lean 4 based on the DPLL algorithm. Given a SAT problem, we get either a solution or a resolution tree showing why there is no solution. Being written in Lean 4 allows:

* The program generates proofs in the foundations of the lean prover, so these are independently checked (both for existence and non-existence of solutions).
* The program itself is checked by lean, so guaranteed to terminate and give a correct answer.

Proofs can be obtained by using the methods `solve` and `proveOrDisprove` in the file `DPLL.lean`. The former gives an object in a type representing either verified solutions or resolution trees. The latter gives a proof of existence or non-existence verified by the _lean prover_. 

Many improvements are necessary, and some are forthcoming (including convenience is usability.)
