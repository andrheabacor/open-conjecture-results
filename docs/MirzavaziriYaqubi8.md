# Mirzavaziri–Yaqubi Conjecture 8

The proposed sign rule fails at **\(n=93\,312=2^7 3^6\)**. Its prime factorization has 13 factors counted with multiplicity, so the conjecture permits zero or a positive value. The Möbius function from the prime factorization to the one-factor factorization has value **\(-57\)**. This single counterexample disproves the universally quantified conjecture, including when its domain is restricted to integers greater than one.

## Statement and open-status check

Madjid Mirzavaziri and Daniel Yaqubi formulated Conjecture 8 on page 4 of *The Möbius function of factorizations with a simple prime factor*. The subject is the Möbius function of the refinement poset, evaluated between the prime factorization and \(n\). Their exact prediction reads “is either \(0\) or has the sign \((-1)^{\Omega(n)+1}\), and it vanishes for \(n=p^k\) with \(k\geq3\).” Their Theorem 1 covers a number with a prime divisor of multiplicity one. Both multiplicities of the witness exceed one. [Conjecture 8](https://arxiv.org/html/2611.18194v1#Thmtheorem8) · [Original PDF, page 4](https://arxiv.org/pdf/2611.18194v1#page=4)

The literature check on **27 November 2026** found the following.

- arXiv listed a single version, submitted on 13 November 2026. Its final section still stated the conjecture. The authors reported checking every exponent pattern with \(\Omega(n)\le8\), alongside other entries in Table 1. [Version history](https://arxiv.org/abs/2611.18194)
- The Semantic Scholar citations endpoint returned *offset 0, data empty*. OpenAlex identified the work as W7234028298, reported a cited-by count of zero, and returned zero results for a separate citing-works query. Google Scholar presented a verification screen. [Semantic Scholar citations](https://api.semanticscholar.org/graph/v1/paper/ARXIV:2611.18194/citations?fields=title,year,url&limit=100) · [OpenAlex citing works](https://api.openalex.org/works?filter=cites:W7234028298)
- Searches using the authors, arXiv identifier, conjecture number, sign rule, multiset-partition terminology, exponent pattern and numerical witness found no prior resolution of the bottom-to-top sign claim. The paper was two weeks old. Indexing delays limit the priority claim this search can support.
- Ziegler’s older result concerns sign behavior on intervals of the integer-partition poset. The endpoints matter here. Hersh and Kleinberg distinguish the ordinary Möbius function from their multiplicative deformation. Babson and Hersh ask a related question about the topology of the proper part of the multiset-partition poset and prove a result for hook-shaped multiplicities. None of those sources supplied the stated bottom-to-top counterexample. [Ziegler](https://doi.org/10.1016/0097-3165%2886%2990092-0) · [Hersh and Kleinberg](https://plhersh.math.ncsu.edu/muquestions.pdf) · [Babson and Hersh, Question 1.1](https://plhersh.math.ncsu.edu/lexmorse.pdf)

## Proof

Write a factorization as a nondecreasing list of factors greater than one. Choosing two entries and replacing them by their product is one coarsening step. Repeating this operation groups the factors in every possible way. Equal resulting lists represent one element of the poset, even when several choices produce them. Conversely, reversing those steps splits factors, as in the paper’s order definition.

Let \(b=[2,2,2,2,2,2,2,3,3,3,3,3,3]\) and \(t=[93312]\). Every factorization of \(93312\) can be split down to \(b\) and merged up to \(t\). For \(u(x)=\mu(b,x)\), the defining equations are \(u(b)=1\) and \(u(x)=-\sum_{b\le y<x}u(y)\) for \(x\ne b\).

The following exact totals group the terms by the number of factors in \(x\). Each row in the third column sums the ordinary Möbius values over the indicated factorizations.

| Factors in \(x\) | Factorizations | \(\sum_x \mu(b,x)\) |
|---:|---:|---:|
| 13 | 1 | 1 |
| 12 | 3 | −3 |
| 11 | 10 | 5 |
| 10 | 27 | −10 |
| 9 | 66 | 24 |
| 8 | 136 | −57 |
| 7 | 242 | 127 |
| 6 | 354 | −253 |
| 5 | 410 | 419 |
| 4 | 327 | −512 |
| 3 | 148 | 352 |
| 2 | 27 | −36 |
| 1 | 1 | **−57** |

The 12 rows below the top in the refinement order sum to \(57\). Thus \(\mu(b,t)=-57\), whereas \((-1)^{13+1}=+1\).

The independent divisor computation enumerates all nondecreasing multiplicative partitions by choosing the least factor \(d\) and recursing on \(n/d\) with lower bound \(d\). It obtains the strict lower set of each \(x\) by taking the union of the lower sets of its immediate splittings. A set union counts a given refinement once. This gives 1,752 factorizations and 229,706 comparable ordered pairs including the diagonal. A separate pair-merging computation starts at the prime factorization and uses \(\mu(x,t)\) in the opposite direction. Both return \(-57\). [Independent divisor calculation](../scripts/mirzavaziri_yaqubi_independent_check.py) · [Pair-merger discovery calculation](../scripts/mirzavaziri_yaqubi_mobius_search.py)

## Lean statement and verification

The standalone source imports Mathlib. It uses Mathlib’s incidence-algebra Möbius function with integer coefficients. The certificate checks the reverse recurrence, independently of the divisor calculation that produced the table above. [Standalone Lean source](../OpenConjectures/MirzavaziriYaqubi8.lean)

| Paper | Lean |
|---|---|
| Positive integer \(n\) | `∀ n : ℕ, 0 < n → ...` in `Conjecture8`. An additional theorem explicitly restricts the sign assertion to \(n\ge2\) and refutes it with the same witness. |
| Prime factorization and \(\Omega(n)\) | `bottomNode n` uses Mathlib’s `n.primeFactorsList`. Its length counts occurrences. `Witness.omega_witness` checks 13. |
| Trivial factorization \(n\) | `topNode n` uses the singleton `[n]` for \(n>1\) and the conventional empty product for \(n=1\). |
| Unordered factorizations under refinement | The endpoints are nondecreasing lists. `picks` chooses occurrences. `merges` replaces two factors by their product and reinserts it in order. `Relation.ReflTransGen Step` allows zero or more such coarsenings. Every list in the interval therefore consists of sorted factors greater than one with product \(n\). |
| Möbius function between the two endpoints | `factorMu n = IncidenceAlgebra.mu ℤ (bottomNode n) (topNode n)` by definition. The finite-interval instance follows from the decrease in list length under each strict merge. |
| Zero or the sign \((-1)^{\Omega(n)+1}\) | `factorMu n = 0 ∨ Int.sign (factorMu n) = (-1 : ℤ) ^ (n.primeFactorsList.length + 1)`. |
| Vanishing for a prime power \(p^k\) with \(k\ge3\) | The second conjunct quantifies over `p k : ℕ` with `p.Prime`, `3 ≤ k`, and `n = p ^ k`, and concludes `factorMu n = 0`. A contradiction to the first conjunct refutes the full proposition. |

For every row the checker verifies that the children are exactly the pair mergers, that each child has a smaller row index, and that the upper-set mask is the union of the children’s masks and the row itself. It verifies that decoding the index list reproduces the mask, that indices occur once, that all labels are distinct, and that the row’s Möbius sum is the required Kronecker delta. `certificate_correct` proves that each checked row value equals Mathlib’s `IncidenceAlgebra.mu` by applying `IncidenceAlgebra.sum_Icc_mu_left` and induction. Thus omissions, duplicated paths and values supplied by the generator are subject to kernel checking. The formal proof binds the two endpoint labels to `bottomNode 93312` and `topNode 93312`.

The small checks give \(\mu(5)=1\), \(\mu(8)=0\), and \(\mu([2,4],[8])=-1\). Merging \([2,2,3]\) produces exactly the two distinct lists \([2,6]\) and \([3,4]\).

## Candidate survey

The ordering records research priority. Multiple numbered conjectures from one paper are listed separately where their mathematical content differs. The status audit above applies to the selected result.

| Rank | Candidate | Decision |
|---:|---|---|
| 1 | Mirzavaziri–Yaqubi, Conjecture 8, signs in the factorization poset. [Paper](https://arxiv.org/abs/2611.18194) | Selected. The source’s small-pattern table provided controls for the search. |
| 2 | Mandal–Mohan, Conjecture 1.28, odd self-summable Fibonacci indices. [Paper](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem28) | Tested the modular criterion with \(m=rp\), odd \(r\le22\,001\) and primes \(5<p\le500\,000\), filtering \(5\nmid r\). It checked 11,614 candidates after the prime sieve and found no witness. A separate search used known prime factors of \(F_r\pm3\) or \(F_r\pm4\) through \(r=2501\). |
| 3 | Yaqubi–Mirzavaziri, Conjecture 6.2, exact dyadic divisibility for odd designated parts. [Paper](https://arxiv.org/html/2611.05623v1#S6.Thmtheorem2) | Compared the eight residue classes with Theorems 4.3–4.6 and the factorization of \(6B_k(3)\). Selected the factorization-poset witness before attempting a formal proof. |
| 4 | Conjecture 5.3 on degrees two and three of signed-path matching polynomials. [Paper](https://arxiv.org/abs/2611.28952) | The authors computed the relevant cases for path sizes 15, 31 and 63. Their remaining symmetry classes need a structural argument. |
| 5 | Yaqubi–Mirzavaziri, Conjecture 6.3, sharp divisibility by \(3^5\) on \(12n+10\). [Paper](https://arxiv.org/html/2611.05623v1#S6.Thmtheorem3) | The paper isolates a coefficient-vanishing problem modulo 81. |
| 6 | The same authors’ Conjecture 6.4 on higher divisibility in several progressions. [Paper](https://arxiv.org/html/2611.05623v1#S6.Thmtheorem4) | Five congruences occur across three clauses. No proof of their conjunction was attempted. |
| 7 | Mandal–Mohan, Conjecture 1.9 on two Fibonacci-square means. [Paper](https://arxiv.org/html/2611.32519v1#S1.Thmtheorem9) | The claim is finiteness for odd indices. Finding one odd solution would leave it open. |
| 8 | Common finite tiling by arbitrary arithmetic progressions in \(\mathbb Z^d\), Conjecture 8.1. [Paper](https://arxiv.org/abs/2611.33154) | The planar construction uses absorption. A general-dimensional lift or obstruction is needed. |
| 9 | Ternary Legendre pairs at every admissible length, Conjecture 10. [Paper](https://arxiv.org/abs/2611.31067) | The first lengths left open by the source are 35 and 38. One construction at either length would leave the universal existence claim open. |
| 10 | Mirzavaziri–Yaqubi, Conjecture 4.5 on single Gaussian quotients. [Paper](https://arxiv.org/abs/2610.19249) | Exact computations already cover eligible \(m\le300\). |
| 11 | The same authors’ Conjecture 4.4 on signs of double Gaussian quotients. [Paper](https://arxiv.org/abs/2610.19249) | The paper proves the claim for \(m\ge10^{30}\). Extending the finite range alone would leave a gap. |
| 12 | Vatter, Conjecture 2.6 on rank-unimodality of composition downsets. [Survey](https://arxiv.org/abs/2602.16355) | The survey reports tests through size 34. Later work treats one-descent ideals. [Later paper](https://arxiv.org/abs/2611.28619) |
| 13 | Ballantine–Beck–Feigon–Maurischat, Conjecture 3, the even part of the ordinary numerator. [Paper](https://arxiv.org/abs/2605.10512) | A subsequent paper retains this coefficient-shape problem. [Follow-up](https://arxiv.org/abs/2605.21718) |
| 14 | The same authors’ Conjecture 4 on denominator log-concavity. [Paper](https://arxiv.org/abs/2605.10512) | The statement has four specified exceptions. The later paper distinguishes it from the refuted binary log-concavity assertion. [Follow-up](https://arxiv.org/abs/2605.21718) |
| 15 | Allie et al., Conjecture 4.4 on remoteness-minimising trees with a fixed segment sequence. [Paper](https://arxiv.org/abs/2611.27685) | Excluded after finding a public counterexample claim. [Earlier counterexample report](https://aixiv.online/abs/2611.02875) |
| 16 | Benfield–Lippard, Conjecture 10.1, symmetry of stable Waring gaps. [Revised paper](https://arxiv.org/html/2404.08193v2) | Excluded. A public formalization reports counterexamples at exponents 64 and 128. [Resolution catalogue](https://itsdavis.com/solved-conjectures/catalogue/) |
| 17 | The same authors’ Conjecture 10.4 on the parity of the largest gap and the gap count. [Revised paper](https://arxiv.org/html/2404.08193v2) | Excluded after finding a public proof. [Resolution catalogue](https://itsdavis.com/solved-conjectures/catalogue/) |
| 18 | Yaqubi–Mirzavaziri, Conjecture 6.1 on all designated parts. [Paper](https://arxiv.org/abs/2611.05623) | Excluded after finding a public Lean resolution. [Formal proof record](https://www.trureturing.org/research/yaqubi-mirzavaziri-2026-designated-summands-conjecture-6-1/) |
| 19 | Mandal–Mohan, Conjecture 1.19 on powered harmonic means. [Paper](https://arxiv.org/abs/2611.32519) | Excluded after finding a public proof record. [Formal proof record](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S3/Arith/Recurrence/MandalMohanFibonacciPowerMean.html) |

## Reproduction

From the repository root:

~~~text
lake env lean OpenConjectures/MirzavaziriYaqubi8.lean
python scripts/mirzavaziri_yaqubi_independent_check.py
python scripts/mirzavaziri_yaqubi_mobius_search.py 7,6
python scripts/mirzavaziri_yaqubi_reviewer_check.py
~~~

Lean output (exit code 0, about 4 minutes):

~~~text
'MirzavaziriYaqubi.Factorizations.witness_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'MirzavaziriYaqubi.Factorizations.refutation' depends on axioms: [propext, Classical.choice, Quot.sound]
'MirzavaziriYaqubi.Factorizations.refutation_even_if_one_is_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
'MirzavaziriYaqubi.Factorizations.prime_cube_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
~~~

## Independent review

A reviewer wrote a third implementation separately from the two above (`scripts/mirzavaziri_yaqubi_reviewer_check.py`). It computes down-sets by splitting one factor at a time. It reproduces all 20 entries of the paper's Table 1 exactly, and the value 0 for 2^k with 3 ≤ k ≤ 10. It then gives μ = −57 for 2^7·3^6 over 1,752 factorizations.
