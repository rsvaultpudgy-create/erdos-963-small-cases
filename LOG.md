# Working log: Erdős Problem #963 small cases

Workspace: 2 CPU cores, 7 GB RAM. Produced by an AI system (Claude, Anthropic).

### #963 (dissociated subsets; is f(n) >= floor(log2 n)?) — searched, no counterexample (so far)
- Reduction (from the formal statement notes): the claim is equivalent to "every set of m positive reals has a dissociated subset of size floor(log2 m)+1". A counterexample would be a set of 2^(k-1) positive integers with no dissociated k-subset.
- k=3: max such set has size 3 (<4). k=4: exhaustive over [1,300]: max size 6 (<8). k=5: exhaustive over [1,60]: max size 13 (<16), e.g. {1..10,12,13,15}.
- Code: code/p963/search.c, search2.c. Running [1,130] for k=5 in background.
- Status: no counterexample; evidence the conjecture holds for small n. Not a solution.
- Update: integer search for k=5 finished over [1,130]: no 14-element set (max is 13). 

### #963 continued — rigorous small cases (covers ALL real sets, not only bounded integers)
- Key fact: if B is a largest dissociated subset of S (size k), every other element equals +-(eps.b) with eps in {-1,0,1}^k.
  So S is a set of linear forms in k unknowns, and "which relation holds" for each (k+1)-subset is a linear equation.
  Exhaustive branching over those equations covers every real configuration.
- Code: code/p963/symbolic.py (Python, exact fractions) and code/p963/symbolic.cpp (independent C++ re-implementation, integer arithmetic).
- Results (G(k) = largest set whose biggest dissociated subset has exactly k elements):
  G(1)=1 (trivial), G(2)=3, G(3)=6 — both programs agree; the bounded integer search (search.c) agrees too.
  k=4 run in progress (targets 14 and 16).
- Consequence: f(n) >= floor(log2 n) holds for every n <= 31 (needs G(1)<2, G(2)<4, G(3)<8).

### #963 — k=4 symbolic search (sets whose largest dissociated subset has exactly 4 elements)
- Final program: code/p963/flat6.cpp (cached recursion over subspaces; see header comment for the argument).
- Symmetry: signed permutations of b. Case 1: S contains the form b1+b2. Case 2: S has no two-term forms and contains b1+b2+b3.
  Case 3 (only four-term forms): at most 4+8 = 12 elements, so it cannot reach 14.
- Shortcut used for lines: all numbers on a line are integers <= sum|b_i|; if that is <= 130, the separate integer search
  (search2.c with arguments "5 130 14": no 14-element set in [1,130]) already rules the line out.
- Early exit inside a node is sound: an element of a real configuration that comes after y is either still in the allowed mask
  or was dropped earlier, in which case all subspaces it forces were already solved (and found empty).
- Case 2, target 14: NO (320 s CPU, 3.27 million subspaces). Re-running case 2 without the shortcut as a cross-check.
- Case 1, target 14: running.
- Case 1, target 14: NO (868 s CPU, 5,736,065 subspaces, 20,800,472 nodes).
- Cross-checks: case 1 and case 2 re-run with the shortcut disabled (argument 0): both NO, identical node and subspace counts.
  Older program flat3 (no early exit, different lookup code, no shortcut) on case 2: NO (6,561,910 nodes, 3,296,181 subspaces).
- randcheck.py: extremal examples confirmed by a separate checker; 3,583 random sets, no exception.
- Conclusion: G(4) = 13. With G(1)=1, G(2)=3, G(3)=6 this gives f(n) >= floor(log2 n) for all n <= 63 and exact f(n) for n <= 27.
- Literature note: erdosproblems.ai wiki on #963 says existing computations give only a bounded-window minimum, not the value over all real sets.
- Nothing was posted, submitted or sent anywhere.
