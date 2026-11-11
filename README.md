# Erdős Problem #963: computer-assisted small cases

Produced entirely by an AI system (Claude, Anthropic). Not checked by a human. Released under CC0.

## Summary

A computer-assisted proof that the inequality asked about in Erdős Problem #963 holds for every set of up to 63 real numbers, with the exact answer for sets of up to 27 numbers. The general problem remains open.

## The result (Problem #963)

**The problem in plain English.** Take any collection of n different real numbers. Call a sub-collection "dissociated" if no two different selections from it add up to the same total. For example {1, 2, 4} is dissociated, but {1, 2, 3} is not, because 1 + 2 = 3. Let f(n) be the size of dissociated sub-collection you are always guaranteed to find, however the n numbers are chosen. Erdős asked whether f(n) is always at least log2(n) rounded down. This is open.

**What was proved.**

| Largest dissociated sub-collection has exactly | The whole collection of positive numbers has at most | Example reaching it |
|---|---|---|
| 2 numbers | 3 numbers | {1, 2, 3} |
| 3 numbers | 6 numbers | {1, 2, 3, 4, 5, 6} |
| 4 numbers | 13 numbers | {1, 2, ..., 10, 12, 13, 15} |

Consequences, for collections of any real numbers (positive, negative or zero):

- Erdős's inequality f(n) >= floor(log2 n) is true for every n up to 63.
- Exact values: f(n) = 1 for n = 2, 3; f(n) = 2 for n = 4 to 7; f(n) = 3 for n = 8 to 13; f(n) = 4 for n = 14 to 27; and f(n) >= 5 from n = 28.
- From n = 14 the true value is strictly larger than Erdős's bound requires.

**Why this is more than a spot check.** A search over whole numbers up to some limit cannot rule out a counterexample made of large or irrational numbers. The program avoids that. If B is a largest dissociated sub-collection, every other number must equal a sum of members of B with coefficients +1, -1 or 0. So the collection is described by algebra in a few unknowns, and each "these numbers are not dissociated" condition is a linear equation in those unknowns. The program follows every possible combination of such equations, which covers all real collections at once.

**How it was checked.**

- Rows 1 and 2 of the table: two separately written programs (Python with exact fractions, and C++) agree, and both agree with a plain whole-number search up to 300.
- Row 3: one C++ program, run in two symmetry cases. Both report that no collection of 14 exists. The three example collections in the table were confirmed by a separate short Python checker.
- Row 3 was first run with a shortcut that relies on the whole-number search (no 14-number collection exists among whole numbers up to 130). Both cases were then re-run without the shortcut and gave the same answer with identical work counts, so the result does not depend on it. An earlier, slower version of the program with different inner routines also agrees on case 2.
- A random test of about 3,600 collections found no exception.

**Confidence and the most likely way it is wrong.**

- Rows 1 and 2: high. Two independent programs and a third method agree.
- Row 3: fairly high, not certain. It rests on one program. The most likely failure would be a logic slip in the symmetry reduction or the caching, which would make the program skip a case. The argument for each is written in the program header and in LOG.md so it can be reviewed.
- Novelty: moderate confidence. A public AI-research wiki on this problem (erdosproblems.ai) states that an existing search over whole numbers up to 34 "proves only a bounded window minimum, not f(13)=4 over all real sets". This result closes exactly that gap. The all-real-sets statement was not found elsewhere, but the main erdosproblems.com discussion page for #963 could not be read by the AI system, so it may already have been posted there.

**What it is not.** It does not settle the problem. The inequality for all n remains open, and others have recent unrefereed claims of f(n) >= (1 - o(1)) log2 n.

## Files

- `LOG.md`: working log for the #963 computation.
- `code/p963/flat6.cpp`: the final exhaustive program. `code/p963/symbolic.py`: the independent Python version for the two small cases.
- `code/p963/search.c`, `search2.c`: whole-number searches. `code/p963/randcheck.py`: independent checker and random test.
- `results/`: raw output of every run.

To rerun the main checks:

```
cd code/p963
g++ -O2 -o flat6 flat6.cpp && gcc -O2 -o search2 search2.c
./flat6 3 7          # no 7-number collection with largest dissociated subset of size 3
./search2 5 130 14   # no 14 whole numbers up to 130 without a dissociated 5-subset
./flat6 4 14 1 130   # symmetry case 1 (about 15 minutes; use 0 in place of 130 to run without the shortcut, about 2 hours)
./flat6 4 14 2 130   # symmetry case 2 (about 6 minutes; without the shortcut about 1 hour)
python3 randcheck.py
```
