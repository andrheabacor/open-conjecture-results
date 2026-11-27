# A counterexample to van Berkel and Bosma’s Conjecture 4

**SOLVED — disproved.** For \(d=4\), the conjecture prescribes a repeating block of four gaps after seven initial gaps. In the strict greedy sequence with seeds \(1,3,7\), the eighth gap is \(6\) and the twelfth is \(1\). Lean proves the negation of the full universal conjecture. A second kernel-checked example at \(d=6\) contradicts the claimed modulus directly. [Conjecture 4, p. 3](https://arxiv.org/pdf/2609.16843v2#page=3) · [Lean proof](../OpenConjectures/VanBerkelBosma4.lean)

## Source and statement

Daan van Berkel and Wieb Bosma, *On \(t\)-sumfree sequences*, arXiv:2609.16843. The first submission was 15 September 2026. The 11 November revision explicitly withdraws the exceptional family from the scope of its earlier theorem and introduces Conjecture 4. It specifies the sequence \(S_{1,d-1,2d-1}\) for every integer \(d\ge3\), asserts eventual periodicity, and adds this exact qualification about its parameters. [Version history](https://arxiv.org/abs/2609.16843) · [Revised statement and authors’ explanation](https://arxiv.org/html/2609.16843v2#Thmtheorem4)

> “with the exception of \(d=3\) or \(d=5\), the preperiod length is \(d+3\) and the period length is \(d\) modulo \(8d-1\).”

The introduction defines each new term as the smallest integer above all earlier terms that is unavailable as a sum of three **distinct** earlier terms. It defines the gap sequence by \(D_i=s_{i+1}-s_i\) with \(i\) starting at 1. Preperiod \(k\) discards the first \(k\) gaps. A repeating block of \(p\) terms modulo \(m\) translates by \(m\) on each repetition. The authors use least lengths. [Definitions and worked example, pp. 1–2](https://arxiv.org/pdf/2609.16843v2#page=2)

## Proof

Set \(d=4\). The seeds are \(1,3,7\), and the prescribed preperiod, period and modulus are respectively \(7,4,31\). Starting from those seeds, the following table implements the greedy rule. In each row, the middle entry lists every skipped integer between the previous term and the accepted term. Each skipped integer is a sum of three distinct preceding terms. The accepted value has no such representation.

| Previous term | Skipped integers | Next accepted term |
|---:|:---|---:|
| 7 | none | 8 |
| 8 | none | 9 |
| 9 | none | 10 |
| 10 | 11–14 | 15 |
| 15 | 16–28 | 29 |
| 29 | 30–34 | 35 |
| 35 | none | 36 |
| 36 | 37–55 | 56 |
| 56 | 57–61 | 62 |
| 62 | none | 63 |

One way to check the entire table by hand is to maintain the sets \(A\), \(B\) and \(C\) of sums of one, two and three distinct entries. Start with \(A=\{1,3,7\}\), \(B=\{4,8,10\}\) and \(C=\{11\}\). After accepting \(x\), replace \(C\) by \(C\cup(x+B)\), then \(B\) by \(B\cup(x+A)\), then adjoin \(x\) to \(A\). Each new sum uses \(x\) exactly once. For example, immediately before accepting \(15\), the set of triple sums is \(\{11,12,13,14,16,17,18,19,20,21,22,24,25,26,27\}\).

With the authors’ one-based indices, \(s_8=29,\ s_9=35,\ s_{12}=62,\ s_{13}=63\). A period of four after seven gaps would give \(D_8=D_{12}\). But \(35-29=6\) and \(63-62=1\). Also \(s_{12}-s_8=33\), which fails even to be divisible by \(31\). Either contradiction refutes the universal statement. The proof requires only these forced terms because the conjecture specifies when the repeating pattern must start.

At \(d=6\), the proposed shift is \(47\) after nine gaps, across six terms. The same greedy rule gives \(s_{10}=55\) and \(s_{16}=100\). Their difference is \(45\). Lean certifies this second contradiction separately. The broader ultimate-periodicity question is Conjecture 5 in the source. [Second Lean proof](../OpenConjectures/VanBerkelBosma4.lean) · [Source](https://arxiv.org/html/2609.16843v2#Thmtheorem5)

## Paper–Lean correspondence

| Paper | Lean |
|---|---|
| Three distinct earlier entries summing to \(n\) | `IsTripleSum` requires \(a<b<c\), membership in the history, and \(a+b+c=n\). `forbidden_iff` proves the executable test equivalent. |
| Smallest positive larger eligible integer | `nextValue_isLeast` quantifies over all natural numbers. The implementation has a proved search bound. If \(M\) is the largest earlier entry, \(3M+1\) exceeds every possible triple sum. |
| The actual infinite sequence \(S_{f,g,h}\) | `history` starts with the three seeds and prepends each successive `nextValue`. `seq` reads the resulting sequence, with zero-based indices. |
| Ultimate periodicity, least preperiod and period, and translation by the modulus | `HasGapPeriod`, `UltimatelyPeriodic` and `ExactPeriod` express the repeating gaps, the two least lengths and the translation after each block. The first source gap is Lean gap 0. |
| Every \(d\ge3\), the exact seeds and both exceptions | `Conjecture4` quantifies over every such natural \(d\), includes ultimate periodicity for all of them, and imposes the exact parameters whenever \(d\ne3,5\). |
| Counterexample to that statement | `conjecture4_false : ¬ Conjecture4` and `conjecture4_false_by_modulus : ¬ Conjecture4` use independent parameter values. There is no bound in the conjecture definition. |

The transcript checker proves that each proposed term is the exact value obtained by the recurrence. Its Boolean computations reduce in Lean’s kernel. [Formal definitions](../OpenConjectures/VanBerkelBosma4.lean) · [Full conjecture](../OpenConjectures/VanBerkelBosma4.lean)

## Sanity checks and independent computations

The first three rows of Table 1 concern different seeds from the counterexample. The Lean sanity theorem recomputes genuine greedy prefixes and checks two full consecutive gap blocks per row. It checks the translation, rules out every shorter cyclic shift of the block, and checks that the preceding gap breaks the repetition. The Python checks use four blocks. These are finite sanity checks of the printed values. [Table 1, p. 21](https://arxiv.org/pdf/2609.16843v2#page=21) · [Lean sanity theorem](../OpenConjectures/VanBerkelBosma4.lean)

| Seeds | Printed \(k,p,m\) | Observed repeating gap block |
|---|---|---|
| \(1,2,6\) | \(6,6,28\) | \(5,6,5,1,5,6\) |
| \(1,2,7\) | \(8,8,44\) | \(7,6,6,6,1,6,6,6\) |
| \(1,3,8\) | \(8,6,38\) | \(7,1,7,8,7,8\) |

Two independent Python algorithms reproduce every listed sequence entry. One tests each candidate against all 3-subsets of the earlier entries. The other maintains three integer bitsets and finds the least admissible next term from the bitset of forbidden sums. The cross-check also finds \(s_{33}=285\) and \(s_{62}=514\) for \(d=29\), giving a shift of \(229\) in place of \(231\). That larger example is a computational cross-check. [Reproducible Python verifier](../scripts/vbb_verify_three_sumfree.py)

```text
python scripts/vbb_verify_three_sumfree.py
```

## Reproducing the Lean result

The project uses Lean 4.37.0-rc1, Lean commit `0b77e12952ad39077d80d8bd6b66d601f225c321`, and Mathlib commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. [Proof file](../OpenConjectures/VanBerkelBosma4.lean)

```bash
lake env lean OpenConjectures/VanBerkelBosma4.lean
```

Exit code 0. The complete output was

```text
'VanBerkelBosma4.conjecture4_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'VanBerkelBosma4.conjecture4_false_by_modulus' depends on axioms: [propext, Classical.choice, Quot.sound]
'VanBerkelBosma4.nextValue_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound]
'VanBerkelBosma4.witness_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
'VanBerkelBosma4.witness_gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
'VanBerkelBosma4.table1_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The file imports only Mathlib. It contains zero `sorry`, `admit`, new `axiom`, or `native_decide` declarations or uses.

## Open-status and priority checks

Checks were performed on **27 November 2026, Pacific/Auckland**. The authors explicitly present this family as an open conjecture in v2. I found no earlier public claim resolving Conjecture 4 in the sources below. The evidence establishes the search performed, with the usual limits of publication and citation indexing.

| Source checked | Finding |
|---|---|
| arXiv v1 and v2 | The 15 September version included the family in a headline periodicity theorem. The detailed v1 Theorem 19 requires \(f+g\ge d+1\), whereas these seeds give \(f+g=d\). The 11 November revision narrows the theorem and introduces the separate conjecture with specific parameters. [v1](https://arxiv.org/abs/2609.16843v1) · [v2](https://arxiv.org/abs/2609.16843v2) |
| OpenAlex and Semantic Scholar | Both returned zero indexed citing works for the source. Topic/title searches also located the authors’ distinct two-summand companion paper and Shtrezi’s different \(S_{1,g,g+1}\) family. [OpenAlex citing works](https://api.openalex.org/works?filter=cites:W7213401224) · [Semantic Scholar citing works](https://api.semanticscholar.org/graph/v1/paper/43f370ea3d55a1d71e7837bb5922f2a9e35e2f01/citations?limit=10) · [Shtrezi](https://arxiv.org/abs/2606.17447) |
| trureturing | The public two-summand counterexample concerns Conjecture 9 of a different paper. The three-summand formalization of v1 Theorem 19 covers the range \(f+g\ge d+1\). Repository issue searches using the authors, conjecture number, seeds and exceptional family located no claim for this Conjecture 4. [Conjecture 9 record](https://the-omega-institute.github.io/trureturing-mdbook/Problems/van-berkel-bosma-2026-conjecture-9.html) · [Scope of Theorem 19 formalization](https://github.com/the-omega-institute/trureturing/pull/26092) |
| Itsdavis | Checked the catalogue’s 19 November snapshot, then its repository index and history at `9587fe4`. No entry matched the authors, sumfree sequences or arXiv ID. [Catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Repository contents at the checked revision](https://github.com/1337isnot1337/solved-conjectures/blob/9587fe4fe9b8d0b8ffb5b158bbfb91361fe70e80/CONTENTS.md) |
| aiXiv and DataCite | Searched aiXiv by authors, arXiv ID and variants of “sumfree sequences”. Its search returned related terms but no matching resolution. DataCite searches for three-sumfree and sumfree sequences likewise located the source and neighbouring research. [aiXiv search](https://aixiv.online/search?q=t-sumfree%20sequences) · [DataCite search](https://api.datacite.org/dois?query=%223-sumfree%22) |
| Author code and prior computational certificates | The authors provide a general sequence generator. Hirotaka Shimizu’s repository lists seven explicitly identified seed triples. They belong to a different list of outstanding periodicity cases. [Authors’ implementation](https://github.com/fifth-postulate/subsumfree) · [Shimizu’s certificates](https://github.com/yygotm/sumfree3-certificates) |

## Other candidates surveyed

| Paper and candidate | Disposition |
|---|---|
| Dietz, Flowers and Lockard, Question 5.13 on the smallest nonsquare self-conjugate partition | Dropped after developing and kernel-checking a local proof. An OpenAlex **title** search found Ma and Zhang’s 24 November preprint explicitly resolving Questions 5.12–5.14, even though both citation indexes returned zero citing works for the original paper. [Original question](https://arxiv.org/abs/2609.08799) · [Prior resolution](https://doi.org/10.5281/zenodo.24488524) |
| Jaffe, two conjectures about the Frobenius problem | Both had public resolutions. Shimizu proved the factor-four bound and trureturing refuted the successor-ratio conjecture. [Paper](https://arxiv.org/abs/2610.17267) · [Factor-four result](https://aixiv.online/abs/2610.02223) · [Successor-ratio result](https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.html) |
| Finch, Conjecture 23 on quadratic recurrences | Dropped because a public record already gives the counterexample at \(k=2\). [Paper](https://arxiv.org/abs/2610.34300) · [Prior result](https://the-omega-institute.github.io/trureturing-mdbook/Library/Certificates/finch2026quadraticrecurrences.html) |
| Coons, growth of adjacent multiplicities | The upper adjacent-growth question has a public resolution. Lower-growth calculations also overlap older work on self-similar measures. [Paper](https://arxiv.org/abs/2611.08109) · [Upper-growth result](https://www.trureturing.org/research/coons-strict-adjacent-multiplicity-growth/) · [Hare, 2016 proceedings](https://km.fjfi.cvut.cz/jn16/_files/jn16_proc.pdf) |
| Huber, minimum width of divisor sums | Searched for explicit chain covers contradicting the proposed minimum. No counterexample was established. [Paper](https://arxiv.org/abs/2610.02264) |
| Cubic partition statistics and Diophantine tuples involving star numbers | Ran exploratory searches for violations. Neither supplied a disproof or a general proof. [Cubic partitions](https://arxiv.org/abs/2611.05196) · [Star tuples](https://arxiv.org/abs/2610.27033) |
| Van Berkel and Bosma’s two-summand period formula | Screened separately. Its published examples and a separate trureturing preperiod refutation make the interpretation of an apparent short mismatch important. The certified result delivered here concerns the three-summand Conjecture 4 of the other paper. [Two-summand paper](https://arxiv.org/abs/2609.18522) |


## Independent review

A reviewer recompiled the Lean file. There is no `sorry`, `admit`, `native_decide` or added axiom. They read the conjecture and the definitions from the arXiv v2 PDF. They wrote a separate bitset implementation (`scripts/vbb_reviewer_period_table.py`), checked it against brute force on the first 45 terms for d = 4, 6, 7, and confirmed that it reproduces the paper's worked example S_{1,2,3} (preperiod 6, period 5, modulus 23). Computing the exact least preperiod, period and modulus of S_{1,d−1,2d−1} for 3 ≤ d ≤ 20 gives the following.

| d | 3 | 4 | 5 | 6 … 20 |
|---|---|---|---|---|
| actual (k, p, m) | (5, 1, 5) | **(7, 3, 27)** | (13, 10, 104) | (d+3, d, **8d−3**) |
| Conjecture 4 | excepted | (7, 4, 31) | excepted | (d+3, d, 8d−1) |

Two observations follow.

1. **For every d ≥ 6 checked, only the modulus differs: 8d−3 instead of 8d−1.** This systematic difference of 2 looks like a misprint in the stated modulus. `conjecture4_false_by_modulus` (d = 6) refutes the conjecture as printed, but it would not survive that correction.
2. **d = 4 is a genuine exception the authors did not list.** Its gap sequence settles into the block (6, 1, 20), with period 3 and modulus 27. A period of 4 is impossible for any preperiod. The main theorem `conjecture4_false` uses exactly this: it shows the 8th and 12th gaps differ (6 ≠ 1). This refutes Conjecture 4 even with the modulus corrected to 8d−3. The exception list would need to be {3, 4, 5}.
