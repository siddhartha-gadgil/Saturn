# SATurn : SAT Solver-prover in lean 4

__SATurn__ is a SAT solver-prover in lean 4 based on the DPLL algorithm. Given a SAT problem, we get either a solution or a resolution tree showing why there is no solution. Being written in Lean 4 gives the following attractive features:

* The program generates proofs in the foundations of the lean prover, so these are independently checked (both for existence and non-existence of solutions).
* The program itself is checked by lean, so guaranteed to terminate and give a correct answer.

Proofs can be obtained by using the methods `solveSAT` and `proveOrDisprove` in the file `DPLL.lean`. The former gives an object in a type representing either verified solutions or resolution trees. The latter gives a proof of existence or non-existence verified by the _lean prover_. 

Alternatively, for a SAT problem, functions `isSat` and `isUnsat` give propositions corresponding to whether the problem is satisfiable or unsatisfiable. There are instances of `Decidable` for these functions (in `DPLL`), so one can simply `decide` where these hold, as for example 

```lean
#eval decide (isSat eg1Statement)
```

More details can be found in the related [blog post](https://siddhartha-gadgil.github.io/automating-mathematics/posts/sat-prover-lean/).

## Exploring and running

The file [Examples.lean](https://github.com/siddhartha-gadgil/Saturn/blob/main/Saturn/Examples.lean) illustrates, for some basic examples, both obtaining structured proofs and proofs or disproofs of propositions. However as this runs in interpreted mode, the examples are very simple.

One can run a compiled version in a command line. This solves the basic examples in the file [Examples.lean](https://github.com/siddhartha-gadgil/Saturn/blob/main/Saturn/Examples.lean) and also the [N-Queens problem](https://en.wikipedia.org/wiki/Eight_queens_puzzle) (if one chooses) for specified `N`. To run this assuming a recent version of the `lean` toolchain is installed using `elan`, one can do the following (in linux) for example:

```bash
$ lake build bin
$ build/bin/saturn 7
```

The above commands run the basic examples and the 7-queens problem. Without an argument (such as `7` in the above example) just the basic examples are run. 

Note that the performance is slow, to a large extent because the underlying collections used are not optimized for performance.
