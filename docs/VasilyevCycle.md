# A counterexample to Vasilyev’s cycle inequality

**SOLVED.** The universal inequality in the first sentence of Vasilyev’s Question 7.1 is false. A simple cycle through 3 has least period 233, with 146 upward and 87 downward steps. Its largest vertex is 698. In exact arithmetic, \(2^{233}>3^{147}\). The witness gives the lower bound \(2^{233}/3^{146}\approx3.021939745162393\) for the supremum in the follow-up question. Its exact value remains undetermined here. [Question 7.1](https://arxiv.org/html/2611.20344v2#S7.Thmtheorem1) · [Lean proof](../OpenConjectures/VasilyevCycle.lean)

## Published statement

Oleg Vasilyev, *Up or down at every integer: Collatz-type maps of arbitrary sets and the up-down graph*, arXiv:2611.20344v2. The first submission was 16 November 2026. The latest version listed when checked was v2, dated 18 November. Its primary category is cs.DM and it is cross-listed in math.NT. [Version history](https://arxiv.org/abs/2611.20344)

> Does every cycle satisfy $2^\ell<3^{a+1}$, that is, $a=\lfloor\ell\log_3 2\rfloor$?

The author writes the statement as a yes/no question. Here \(\ell\) is the cycle length and \(a\) its number of upward steps. Vasilyev checked all cycles through length 30 and all 1,133,265,572 cycles whose vertices are at most 160. The witness exceeds both search limits. The proposed inequality and its equivalent floor formulation appear together in v2, and the counterexample uses the definitions in that same version. [Statement](https://arxiv.org/html/2611.20344v2#S7.Thmtheorem1) · [Paper’s census](https://arxiv.org/html/2611.20344v2#S4.T1)

## Proof

For a positive integer \(x\), set \(U(x)=\lceil3x/2\rceil\) and \(D(x)=\lceil x/2\rceil\). A subset \(S\) of the positive integers defines one map, using \(U\) on \(S\) and \(D\) elsewhere. Start at 3 and read these five blocks in order, applying one letter per step. The last value in a row is the first value in the next row. [Definition 1.1](https://arxiv.org/html/2611.20344v2#S1.Thmtheorem1)

| Steps | Start | End | Upward steps | Directions |
|---|---:|---:|---:|---|
| 1–48 | 3 | 90 | 33 | `UUUUUUUDUUUUUDUDUDUUUUUDDUUDDUUDDUUDUDDDUUUUUDUU` |
| 49–96 | 90 | 626 | 32 | `UUUUDDUUUDUDUUDUDUDUUDUUDUUUUDUUDUDUUDDUUDDUUUUU` |
| 97–144 | 626 | 171 | 29 | `DUDUUDDDDUDUUDUUUUUUUDUUDUDDUUUDDUUDUUUDUUUDDUDU` |
| 145–192 | 171 | 465 | 31 | `DUUUUUDUDUUDDUUDUUDDUUDUDDUDUDUDDUUUDUUUUUUUUUDU` |
| 193–233 | 465 | 3 | 21 | `UDUDUDUDUUDDUUDUUDUUUUDUDUUDUDDUDUDDDDUDD` |

Summing the block counts gives 146 upward steps. The last value is 3. The 233 source vertices in the word are distinct, so assigning each source its indicated branch defines a single set \(S\). Take \(S\) to consist of the sources of the 146 upward steps. This orbit of \(T_S\) returns for the first time at step 233. The following integer calculation checks the entire certificate. The ordered vertices are also available directly. [Vertex list](../scripts/vasilyev/cycle.json) · [Independent verifier](../scripts/vasilyev/verify_cycle.py)

```python
x, seen, a = 3, set(), 0
for letter in word:  # concatenate the five blocks above
    assert x > 0 and x not in seen
    seen.add(x)
    a += (letter == 'U')
    m = 3 if letter == 'U' else 1
    x = (m*x + 1) // 2
assert (x, len(seen), a, min(seen), max(seen)) == (3, 233, 146, 3, 698)
assert 2**233 > 3**147
```

The exact positive difference is

```text
2^233 − 3^147 = 100215470057906355436149411528249268366177189165848154207107510496805
```

Substituting \((\ell,a)=(233,146)\) contradicts the strict inequality. This settles the universal assertion.

## Two independent computations

1. **Directed graph search.** On the integers from 2 through 700, generate the two permitted outgoing edges, keeping edges whose target is in range. An OR-Tools CP-SAT circuit constraint selects one simple circuit through 3, with self-loops representing unused vertices. For an edge with multiplier \(m\in\{1,3\}\), the rounding term is \(\log(1+(x\bmod 2)/(mx))\). Around a closed cycle, these terms sum to \(\log(2^\ell/3^a)\), since the factors involving consecutive vertices telescope. Rounded weights guide the search for a circuit that exceeds \(\log 3\). Replaying the resulting finite set \(S\) and comparing the two integer powers certifies the result. A separate depth-first census reproduced the first four nonempty rows of the paper’s table before the witness search. [Search and replay code](../scripts/vasilyev/cycle_search.py)

2. **Enumeration of direction words.** Fix a word and let \(m_i\in\{1,3\}\) be its successive multipliers, starting at \(i=0\). The exact recurrence is \(2x_{i+1}=m_ix_i+e_i\), where \(e_i=x_i\bmod2\). Put \(B_0=0\), \(B_{i+1}=m_iB_i+2^i\). For any closed orbit of this word, \((2^\ell-3^a)x_0\le B_\ell\). For the witness word this gives \(1\le x_0\le5\). Trying every admissible start independently recovered this report’s vertex list, with 3 the sole start giving a simple cycle in least-first order. As an additional check, each edge satisfied the defining inverse inequality \(2y-2<mx\le2y\) for exactly one of \(m=1,3\). This verifier uses only the Python standard library and the fixed word. [Independent implementation](../scripts/vasilyev/verify_cycle.py)

Enumerating every direction word at each length also gives a check independent of the paper’s vertex ceilings. Nonempty census rows agree on all three quantities shown below. Both missing lengths 3 and 4 give zero cycles. The Lean census certifies the first four rows inside the author’s stated ceilings and confirms that lowering each ceiling by one removes a cycle. [Source table 4.1](https://arxiv.org/html/2611.20344v2#S4.T1)

| Cycle length | Cycles | Steps up per cycle | Largest vertex |
|---:|---:|---:|---:|
| 1 | 1 | 0 | 1 |
| 2 | 3 | 1 | 5 |
| 5 | 12 | 3 | 26 |
| 8 | 140 | 5 | 242 |
| 10 | 18 | 6 | 41 |

## Lean correspondence and build

| Paper | Lean representation |
|---|---|
| Positive integer vertices and arbitrary \(S\) | The public proposition quantifies over `S : Set ℕ` and requires `0 < x` for every vertex of the cycle. Membership of 0 has no effect. |
| \(U,D,T_S\) | `up` and `down` use natural-number division after adding 1 to the numerator. `step (characteristic S)` chooses the branch at each source. |
| A simple cycle written from its least vertex | `IsCycle` requires a nonempty list of distinct positive vertices, first vertex equal to its minimum, and `c.map (step inS) = c.rotate 1`. This equality includes the last-to-first edge. |
| \(\ell,a\) | `c.length` and `c.countP (characteristic S)` count the vertices and selected upward sources. |
| Entire proposed statement | `CycleBound` quantifies over every set and every such cycle. `cycleBound_false : ¬ CycleBound` supplies the explicit set and cycle. |
| Exact period | `witness_minimal_period` independently evaluates the 233rd iterate at 3 and uses primality of 233 and the first step \(3\mapsto5\) to certify Mathlib’s `Function.minimalPeriod`. |

The file contains the complete certificate and all sanity lemmas. The checker used Lean 4.37.0-rc1, commit `0b77e12952ad39077d80d8bd6b66d601f225c321`, with Mathlib revision `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The proof checks by kernel reduction. [Lean source](../OpenConjectures/VasilyevCycle.lean)

From the repository root:

```bash
lake env lean OpenConjectures/VasilyevCycle.lean
```

Exit status **0**. Complete standard output

```text
'VasilyevCycle.paper_cycles' does not depend on any axioms
'VasilyevCycle.paper_census' depends on axioms: [propext, Classical.choice, Quot.sound]
'VasilyevCycle.paper_census_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
'VasilyevCycle.witness_isCycle' does not depend on any axioms
'VasilyevCycle.witness_counts' does not depend on any axioms
'VasilyevCycle.witness_extrema' does not depend on any axioms
'VasilyevCycle.witness_minimal_period' depends on axioms: [propext, Classical.choice, Quot.sound]
'VasilyevCycle.exact_gap' depends on axioms: [propext]
'VasilyevCycle.cycleBound_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To replay the independent computation, run `python verify_cycle.py` in the report directory. The search can also be repeated there with `python cycle_search.py --limits 700 --focus 3 --seconds 10` using OR-Tools 9.15.6755.

## Public status checked 27 November 2026

| Source | Finding |
|---|---|
| arXiv | The author’s latest listed version, v2, still asks Question 7.1. The source archive SHA-256 is `46b81a95f4a24573f7f0eae379719c234695ebcb3ca7041cd8b8099b170a0542`. The `updown.tex` SHA-256 is `3ed8f00431e8ee11ccf0d0885254f38b44c33c33d82cdf6be7784daecebc0b57`. [Version history](https://arxiv.org/abs/2611.20344) · [Versioned source](https://arxiv.org/src/2611.20344v2) |
| OpenAlex | Work `W7234897498` had citation count 0. Its separate citing-works query also returned 0 results. [Work](https://openalex.org/W7234897498) · [Citing works](https://api.openalex.org/works?filter=cites:W7234897498) |
| Semantic Scholar | arXiv’s own link resolved to paper `312686d74560cfefcfc0aac7437b4a31f92da66b`. Its citing-works endpoint returned HTTP 200 and an empty data array. The alternative arXiv-ID metadata request was rate-limited and the DOI lookup did not locate a record. [Citing works](https://api.semanticscholar.org/graph/v1/paper/312686d74560cfefcfc0aac7437b4a31f92da66b/citations?fields=title,year&limit=100) |
| trureturing | Searched issues and PRs by arXiv ID, author and graph name, plus the complete default-branch `Problems` and `D5` path lists. The paper-specific result refutes Question 7.7 about force-divergent sets. No record located for the cycle inequality. [Problem record](https://the-omega-institute.github.io/trureturing-mdbook/Library/Asymptotics/vasilyev2026upordown.html) · [Issue 32194](https://github.com/the-omega-institute/trureturing/issues/32194) · [PR 32243](https://github.com/the-omega-institute/trureturing/pull/32243) |
| Solved Conjectures | Checked the dated public catalogue, current repository contents and complete path listing, and searched issues and PRs for the ID, author, and graph name. No corresponding claim was located. [Catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Repository contents](https://github.com/1337isnot1337/solved-conjectures/blob/main/CONTENTS.md) |
| aiXiv | Searches by arXiv ID, author and graph name returned the source paper. Its record summarizes the author’s results and gives no refutation of the cycle inequality. The returned search records contained no identifiable prior answer. [Source record](https://aixiv.online/abs/2611.01746) · [ID search](https://aixiv.online/search?q=2611.20344) |

Targeted searches for the title, author, question number, and cycle-ratio wording also found the source and mirrors. The available public evidence supports describing the question as open before this check. Unindexed work and independent discoveries can exist, so priority remains provisional.

## Candidate survey

The August–November 2026 announcement lists for math.NT, math.CO and math.RA yielded 8,585 distinct arXiv IDs after deduplication. Title searches guided a screen of 81 distinct source texts. The table records the main candidates and decisions. Source screening alone supplies no open-status conclusion about a dropped item. [Number theory listing](https://arxiv.org/list/math.NT/2026-11?show=2000) · [Combinatorics listing](https://arxiv.org/list/math.CO/2026-11?show=2000) · [Rings and algebras listing](https://arxiv.org/list/math.RA/2026-11?show=2000)

| Candidate | Decision and reason |
|---|---|
| Vasilyev, Question 7.1 | **Kept and disproved.** All graph, set, positivity and cycle-length conditions were realized in a single deterministic orbit. [Source](https://arxiv.org/abs/2611.20344) |
| Finch, capture offset | Dropped. The exact universal claim already has a public counterexample at \(k=2\). [Source](https://arxiv.org/abs/2610.34300) · [Resolution](https://www.trureturing.org/research/finch-2026-conjecture-23-capture-offset/) |
| Coons, Calkin–Wilf CW2 | Dropped. A public proof establishes the strict power bound below the proposed threshold. The separate adjacent upper-growth question also has a public refutation. [Source](https://arxiv.org/abs/2611.08109) · [CW2 solution](https://irsi.ai/notes/calkin-wilf-cw2/) · [Adjacent upper-growth result](https://www.trureturing.org/research/coons-strict-adjacent-multiplicity-growth/) |
| Shah–Kiselev, late-growing permutations | Dropped Conjecture 3.1 because its limit has a public solution. The companion valuation question was set aside. [Source](https://arxiv.org/abs/2610.08636) · [Resolution](https://www.trureturing.org/research/shah-kiselev-2026-late-growing-ratio-limit/) |
| Van Berkel–Bosma, greedy 2-sumfree sequences | Dropped the printed preperiod formula, Conjecture 9. The discrepancy with the authors’ example and its formal refutation are public. [Source](https://arxiv.org/abs/2609.18522) · [Resolution](https://the-omega-institute.github.io/trureturing-mdbook/Problems/van-berkel-bosma-2026-conjecture-9.html) |
| V-toothpick sequence | Set aside. The paper already certifies its proposed degree identity for dyadic \(q\le2^{266}\), and the remaining argument requires controlling all direct cones. [Source](https://arxiv.org/abs/2611.23172) |
| Generalized Hofstadter functions | Set aside. The general first-occurrence formula is explicitly qualified by sufficiently large \(k\). One value of \(k\) can test a listed threshold but cannot refute this asymptotic assertion. [Source](https://arxiv.org/abs/2610.35994) |
| Fibonacci and Lucas Smith numbers | Set aside. A second common index would answer its existence question, but certifying Smith numbers here requires complete prime factorizations. [Source](https://arxiv.org/abs/2609.01955) |
| Partial Petrial polynomials | Set aside the subcubic-tree log-concavity question after reading the distinction between the paper’s non-log-concave family and the smaller proposed class. [Source](https://arxiv.org/abs/2611.07503) |
| Narayana transforms | Set aside the real-rootedness and log-concavity questions on restricted polytopes and stack-sorting fibers. Transferring a candidate polynomial to an admissible fiber needs a separate certificate. [Source](https://arxiv.org/abs/2611.13479) |
| Finite linear Jaco graph degrees | Dropped. The short paper supplies proofs of the two proposed sequence relationships. [Source](https://arxiv.org/abs/2611.28060) |
| Kaprekar 2-cycles | Dropped. The authors report that Dolan had already obtained their full classification. [Source](https://arxiv.org/abs/2608.22564) |
| Type (2,3) finite endofunction identities | Dropped. The paper gives counting formulas for all sixteen listed forms. [Source](https://arxiv.org/abs/2611.19668) |
| Restricted partition minimum periods | Dropped. The paper itself gives counterexamples to the Beck–Sam–Woods conjecture it quotes. [Source](https://arxiv.org/abs/2608.02085) |

<details>
<summary>Other source texts screened and set aside at triage</summary>

These sources were screened for explicit questions and conjectural formulas. No result from them is claimed here.

**August.** [2608.00532](https://arxiv.org/abs/2608.00532), [2608.03243](https://arxiv.org/abs/2608.03243), [2608.04468](https://arxiv.org/abs/2608.04468), [2608.11012](https://arxiv.org/abs/2608.11012), [2608.12011](https://arxiv.org/abs/2608.12011), [2608.15992](https://arxiv.org/abs/2608.15992), [2608.22010](https://arxiv.org/abs/2608.22010), [2608.24476](https://arxiv.org/abs/2608.24476), [2608.27058](https://arxiv.org/abs/2608.27058).

**September.** [2609.05827](https://arxiv.org/abs/2609.05827), [2609.06332](https://arxiv.org/abs/2609.06332), [2609.08822](https://arxiv.org/abs/2609.08822), [2609.10234](https://arxiv.org/abs/2609.10234), [2609.13350](https://arxiv.org/abs/2609.13350), [2609.15146](https://arxiv.org/abs/2609.15146), [2609.15201](https://arxiv.org/abs/2609.15201), [2609.15554](https://arxiv.org/abs/2609.15554), [2609.15754](https://arxiv.org/abs/2609.15754), [2609.16596](https://arxiv.org/abs/2609.16596), [2609.22364](https://arxiv.org/abs/2609.22364), [2609.29484](https://arxiv.org/abs/2609.29484), [2609.30314](https://arxiv.org/abs/2609.30314), [2609.31336](https://arxiv.org/abs/2609.31336), [2609.35921](https://arxiv.org/abs/2609.35921).

**October.** [2610.00775](https://arxiv.org/abs/2610.00775), [2610.00966](https://arxiv.org/abs/2610.00966), [2610.01747](https://arxiv.org/abs/2610.01747), [2610.03070](https://arxiv.org/abs/2610.03070), [2610.03111](https://arxiv.org/abs/2610.03111), [2610.08965](https://arxiv.org/abs/2610.08965), [2610.09953](https://arxiv.org/abs/2610.09953), [2610.12237](https://arxiv.org/abs/2610.12237), [2610.14496](https://arxiv.org/abs/2610.14496), [2610.15770](https://arxiv.org/abs/2610.15770), [2610.18919](https://arxiv.org/abs/2610.18919), [2610.20028](https://arxiv.org/abs/2610.20028), [2610.37356](https://arxiv.org/abs/2610.37356).

**November.** [2611.00435](https://arxiv.org/abs/2611.00435), [2611.00912](https://arxiv.org/abs/2611.00912), [2611.01170](https://arxiv.org/abs/2611.01170), [2611.01243](https://arxiv.org/abs/2611.01243), [2611.01453](https://arxiv.org/abs/2611.01453), [2611.01919](https://arxiv.org/abs/2611.01919), [2611.02072](https://arxiv.org/abs/2611.02072), [2611.02389](https://arxiv.org/abs/2611.02389), [2611.06417](https://arxiv.org/abs/2611.06417), [2611.06599](https://arxiv.org/abs/2611.06599), [2611.07303](https://arxiv.org/abs/2611.07303), [2611.10200](https://arxiv.org/abs/2611.10200), [2611.10437](https://arxiv.org/abs/2611.10437), [2611.11056](https://arxiv.org/abs/2611.11056), [2611.15635](https://arxiv.org/abs/2611.15635), [2611.16834](https://arxiv.org/abs/2611.16834), [2611.17839](https://arxiv.org/abs/2611.17839), [2611.20221](https://arxiv.org/abs/2611.20221), [2611.20832](https://arxiv.org/abs/2611.20832), [2611.21657](https://arxiv.org/abs/2611.21657), [2611.22110](https://arxiv.org/abs/2611.22110), [2611.23536](https://arxiv.org/abs/2611.23536), [2611.23542](https://arxiv.org/abs/2611.23542), [2611.25331](https://arxiv.org/abs/2611.25331), [2611.26439](https://arxiv.org/abs/2611.26439), [2611.26962](https://arxiv.org/abs/2611.26962), [2611.28619](https://arxiv.org/abs/2611.28619), [2611.29782](https://arxiv.org/abs/2611.29782), [2611.33046](https://arxiv.org/abs/2611.33046), [2611.33216](https://arxiv.org/abs/2611.33216).

</details>


## Independent review

A reviewer recompiled the file and found no `sorry`, `admit`, `native_decide` or added axioms. They read Question 7.1 and Definitions 1.1 and 2.2 (U(x) = ⌈3x/2⌉, D(x) = ⌈x/2⌉, simple cycles of the up-down graph) in the arXiv v2 PDF. A separate script read the 233 vertices from the Lean file and checked the following:

- every consecutive pair, including the wrap-around, is an edge x → ⌈3x/2⌉ or x → ⌈x/2⌉;
- all vertices are distinct;
- there are exactly 146 up-edges;
- 2^233 ≥ 3^147, and 2^233/3^146 = 3.021939745…

The largest vertex is 698, beyond the paper's exhaustive search over cycles with all elements at most 160. The only related public record, [TruReTuring #32194](https://github.com/the-omega-institute/trureturing/issues/32194), concerns the paper's Question 7.7, not 7.1. No earlier answer to Question 7.1 was found in the solved-conjectures or TruReTuring catalogues, on aiXiv or on arXiv.

**Scope.** This refutes the first sentence of Question 7.1 (whether every cycle satisfies 2^ℓ < 3^(a+1)). It gives the lower bound 3.0219… for the follow-up question about the supremum of 2^ℓ/3^a, which remains open.
