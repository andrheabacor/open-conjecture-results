# A seven-element counterexample to Mou’s effective-barcode conjecture

**Disproof.** Let \(P\) be the disjoint union of a five-element chain and two isolated elements. Every barcode \(a\) of \(P\) has \(B_a(25)=0\). The order polytope has 24 vertices, and a set of 25 points contains a copy of all its vertices. Hence \(F_P(25)\geq 1\), which rules out every barcode of this poset.

Site Mou states Conjecture 1.4 as follows.

> Every finite poset with at least two elements admits an effective barcode.

The source is *Homothetic Copies of Polytopes and Binomial Barcodes*, arXiv:2611.32429v1, submitted 24 November 2026. Definition 4.5 requires \(F_P(N)\le B_a(N)\) for every nonnegative integer \(N\). [Conjecture 1.4](https://arxiv.org/html/2611.32429v1#S1.Thmtheorem4) · [Definition 4.5](https://arxiv.org/html/2611.32429v1#S4.Thmtheorem5)

## Proof

**1. The barcode value.** A strictly order-preserving map from \(P\) to \([q]\) chooses five distinct values in increasing order on the chain and chooses each isolated element’s value freely. Thus \(\Omega_P^\circ(q)=\binom q5 q^2\). This vanishes for \(0\le q<5\) and equals 25 at \(q=5\). By Mou’s Theorem 1.2, every barcode satisfies

\[
B_a(25)=B_a(\Omega_P^\circ(5))=\sum_{q=0}^{4}\Omega_P^\circ(q)=0.
\]

This argument uses only the order relation on \(P\), so the endpoint is independent of the natural labelling. [Theorem 1.2](https://arxiv.org/html/2611.32429v1#S1.Thmtheorem2)

**2. A configuration with a copy.** Label the chain coordinates \(0,\ldots,4\) in increasing order and the isolated coordinates \(5,6\). The polytope consists of points in the unit cube with \(x_0\le\cdots\le x_4\). Its vertices are exactly the feasible binary vectors. Each such vector is extreme coordinate by coordinate. Conversely, any feasible \(x\) with a fractional coordinate is the midpoint of the distinct feasible points given coordinatewise by \(x_i^2\) and \(1-(1-x_i)^2\). Both maps preserve the interval and its order.

The five binary chain coordinates have six possible cut positions between zeros and ones. The isolated coordinates give four independent choices. The vertex set \(V\) therefore has \(6\cdot4=24\) elements. Set \(S=V\cup\{(2,2,2,2,2,2,2)\}\). Then \(|S|=25\), and translation zero with scale one is a positive homothety sending every vertex into \(S\). Thus \(F_P(25)\geq1>0=B_a(25)\) for every \(a\). The paper counts copies by their vertices. [Definition of \(F_Q\)](https://arxiv.org/html/2611.32429v1#S1)

### Direct derivation of the endpoint from the definitions

The Lean proof checks the following argument directly, without importing Mou’s endpoint theorem. Each linear extension places the two isolated labels \(5,6\) in two ordered slots among seven. The five remaining slots hold the chain in increasing order. This gives 42 extensions. A descent must start with 5 or 6. Exactly one extension has zero descents. To have two descents, insert the isolated labels in two distinct gaps just before chain elements (20 choices), or put them together in the order \(6,5\) just before one chain element (5 choices). Thus the descent multiplicities at \(0,1,2\) are \(1,16,25\).

Every basic sequence permutes exactly those 42 labels. In periods \(t=0,\ldots,4\), a label \(a_i+t\) gives bar length \(\binom{a_i+t}{6}\) and full contribution \(\binom{a_i+t}{7}\). All tops are at most six. Only the 25 copies of label two in period four attain six, each supplying one unit of length. Every full contribution is zero. The first five periods therefore end at total length 25 with value zero, in every ordering. [Definition 4.4 and equation (4.4)](https://arxiv.org/html/2611.32429v1#S4.Thmtheorem4)

## Correspondence between the source and Lean

All names below belong to the namespace `MouBarcode` in the [Lean source](../OpenConjectures/MouBarcode.lean).

| Paper object | Lean object | Correspondence |
| --- | --- | --- |
| Finite poset of size \(d\), naturally labelled | `Poset d` | A Mathlib `PartialOrder (Fin d)`, a decision procedure for its order, and the implication from poset order to numeric label order. Adding one to labels recovers the paper’s \([d]\). Every finite poset admits a natural labelling by a linear extension. |
| \(\mathrm{LE}(P)\), descents, \(\mu_P\), eq. (4.1) | `descentData`, `descents` | Enumerates the permutations of all labels. An extension passes exactly when no later label lies below an earlier one. Adjacent descents are counted with their multiplicities. |
| All barcodes of \(P\), Definition 4.4 | `IsBarcode P a` | Mathlib `List.Perm` says the basic sequence is any ordering of the descent multiset. The basic sequence uniquely determines the integer-indexed barcode. Its positive-indexed part, used by \(B_a\), has entries \(a_i+t\) in period \(t\). |
| Bar lengths, full and partial contributions | `periodWeight`, `prefixWeight`, `upperShift`, `BarcodeValue` | The relation records the graph \((N,B_a(N))\) by counting full periods, a prefix of the next period, and the residual fill. Zero residual includes every endpoint and \(N=0\). Positive residual must be less than the next bar length. Zero-length bars also give zero full contribution. |
| \(K_k(r)\), eqs. (2.1)–(2.2) | `upperShift k r` | At each positive rank \(s\), take the largest \(m\) with \(\binom ms\le r\), add \(\binom m{s+1}\), and recurse on the remainder at rank \(s-1\). The search bound \(r+s-1\) suffices since \(\binom ms\ge m-s+1\) for \(m\ge s\). This is the greedy canonical expansion. |
| \(O(P)\) and its vertices, Definition 4.1 | `orderPolytope`, Mathlib `Set.extremePoints ℝ` | Uses real coordinates in \([0,1]\) and the paper’s order inequalities. `vertices_eq` proves for every such poset that the actual extreme points equal its monotone binary vectors. |
| \(F_P(N)\) | `copies`, `extremal`, `extremal_le_iff` | Counts distinct pairs of a real translation vector and a positive real scale taking every vertex into an \(N\)-point real set. The cardinal supremum expresses the paper’s maximum. The checked equivalence says its upper bound is precisely an upper bound on every such configuration. For \(d\ge2\), an image of the zero and all-ones vertices fixes the homothety, so each count is bounded by \(N^2\) and a maximum exists. |
| Effectiveness and Conjecture 1.4 | `Effective`, `MouConjecture`, `mou_conjecture_false` | Quantifies over all sizes \(d\ge2\), all naturally labelled \(d\)-element posets, all possible basic sequences, and every \(N\). The final Lean theorem proves `¬ MouConjecture`. |

The proof constructs the specific finite set `witnessPoints`. It proves its cardinality, proves membership of the identity homothety in the set of copies, and derives the contradiction. [Order polytope and descents](https://arxiv.org/html/2611.32429v1#S4.Thmtheorem1) · [Canonical binomial expansion](https://arxiv.org/html/2611.32429v1#S2)

## Source sanity checks and independent verification

| Source check | Result verified in Lean |
| --- | --- |
| Theorem 1.3, chain family at \(d=3\) | `table_chain` gives one extension and the basic multiset \((0)\). |
| Theorem 1.3, one antichain pair, with both outer chains empty | `table_antichain` gives two extensions and \((0,1)\). |
| Theorem 1.3, two successive antichain pairs, with both outer chains empty | `table_ordinal_sum` gives four extensions and \((0,1,1,2)\). |
| Square example, Figure 4, \(n=4\) and \(r=3,6\) | `square_at_nineteen` and `square_at_twenty_two` give \(B(19)=17\) and \(B(22)=21\), including partial-bar evaluation. These numerical values follow from the source’s displayed square formula for the illustrated inputs. |

[Theorem 1.3 table](https://arxiv.org/html/2611.32429v1#S1.Thmtheorem3) · [Square example](https://arxiv.org/html/2611.32429v1#S6.Thmtheorem2) · [Figure 4](https://arxiv.org/html/2611.32429v1#S6.F4)

The independent Python check ran with `python scripts/mou_verify_barcode.py`. It enumerated all strict maps into \([q]\) for \(0\le q\le5\) and compared each count with the product formula. Separately, it accumulated the five periods from the descent histogram, obtaining the same endpoint \((25,0)\). It compared the complete sets of linear extensions from two algorithms (filter all \(7!\) permutations, or insert the two isolated labels into ordered slots), and the complete vertex sets from two algorithms (test all \(2^7\) bit strings, or form the product of cut positions and free bits). Finally it checked all candidate images of the zero and all-ones vertices in the displayed \(S\). The identity is the unique copy in this particular \(S\). The disproof needs only its existence. [Verification script](../scripts/mou_verify_barcode.py)

## Public status checked on 27 November 2026

| Source | Observation |
| --- | --- |
| arXiv | The version history lists only v1, submitted 24 November at 11:31:13 UTC. The text presents Conjecture 1.4 as open. [Version history](https://arxiv.org/abs/2611.32429) |
| OpenAlex | Record `W7239845458` reports zero citations. The separate citing-works query returned zero results. [Work](https://openalex.org/W7239845458) · [Citing works](https://api.openalex.org/works?filter=cites:W7239845458) |
| Semantic Scholar | The public paper-detail endpoint returned this title with `citationStats.numCitations = 0`. The Graph API was rate limited. [Paper-detail record](https://www.semanticscholar.org/api/1/paper/00ee785e8921a4f19ae402c3431eb9f7eb3cdbe1) |
| Davis solved-conjectures catalogue | Searches found no match for the identifier, “binomial barcode”, “effective barcode”, or the title fragment. The directly served catalogue displayed a 19 November snapshot, so I also searched the 27 November repository revision’s contents page, history, README and complete tree of 19,918 paths. The history covers entries dated 26 November. [Catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Repository revision](https://github.com/1337isnot1337/solved-conjectures/tree/9587fe4fe9b8d0b8ffb5b158bbfb91361fe70e80) · [History at that revision](https://github.com/1337isnot1337/solved-conjectures/blob/9587fe4fe9b8d0b8ffb5b158bbfb91361fe70e80/HISTORY.md) |
| TrureTuring | The public discovery manifest reported 45,152 records. The complete release index matched its published SHA-256. Searches of that index found none of the four identifier/title/term strings above. [Discovery manifest](https://www.trureturing.org/api/v1/manifest.json) · [Release index](https://the-omega-institute.github.io/trureturing-pages/api/v1/index.json) |
| aiXiv | Four searches covered the arXiv identifier, “barcode”, “binomial barcodes” and “effective barcode”. The search returns ranked results, including unrelated papers. No displayed result matched Mou’s paper or conjecture. [Identifier search](https://aixiv.online/search?q=2611.32429) · [Effective-barcode search](https://aixiv.online/search?q=%22effective%20barcode%22) |

I found no prior public resolution or claim in these checks. Recent, privately held, or unindexed work may escape discovery.

## Other candidates surveyed

I screened titles from the September, October and November math.CO listings and fetched primary TeX for 124 selected papers. The following candidates received closer attention. [September](https://arxiv.org/list/math.CO/2026-09) · [October](https://arxiv.org/list/math.CO/2026-10) · [November](https://arxiv.org/list/math.CO/2026-11)

| Candidate | Disposition |
| --- | --- |
| Mou, effective barcodes of posets | Selected. The endpoint and a geometric witness yield the full disproof above. [Paper](https://arxiv.org/abs/2611.32429) |
| Mu–Welker, Conjecture 3.9 on Dyck valleys and bargraphs | Dropped after locating the existing TrureTuring record and its linked bijection work. [Paper](https://arxiv.org/abs/2609.14054) · [Public record](https://www.trureturing.org/knowledge/node/a469ae4ab0c1ee4345e9e5238e79e61bfe55d0720a7e1422c78f6701e72a0bbc/) |
| Verkama, Conjecture 6.2 on inversion graphs | Dropped. TrureTuring records a proof of the full bound. [Paper](https://arxiv.org/abs/2611.17237) · [Proof dossier](https://the-omega-institute.github.io/trureturing-mdbook/Problems/verkama-2026-conjecture-62.html) |
| Shlyk, eventual existence of partition convexity indices | Dropped. The existing public result addresses eventual existence. [Paper](https://arxiv.org/abs/2611.24835) · [Proof dossier](https://www.trureturing.org/research/shlyk-convexity-index-eventual-existence/) |
| Mirzavaziri–Yaqubi, Latin Eulerian numbers | The separate positivity assertion has a public proof. For interior unimodality, independent row and column enumerations agreed for orders 3 through 6. The order-six distribution covers 812,851,200 Latin squares and gives no counterexample. [Paper](https://arxiv.org/abs/2609.25100) · [Positivity dossier](https://the-omega-institute.github.io/trureturing-mdbook/Problems/mirzavaziri-yaqubi-latin-eulerian-multiples.html) |
| Partition inequalities for missing integers | Dropped. The source paper proves the three cited parity inequalities. [Paper](https://arxiv.org/abs/2611.07908) |
| Reflection length and cycle type in pattern-avoiding permutations | Reserve candidate. The authors report checking length through ten. I did not extend their search. [Paper](https://arxiv.org/abs/2611.33575) |
| Coefficientwise question in permutation Penney games | Reserve candidate. The manuscript proves the originally cited winning-strategy conjecture and leaves a coefficientwise strengthening as a question. [Paper](https://arxiv.org/abs/2611.28063) |
| Equalities for pattern-avoiding flattened partitions | Reserve candidate. The paper reports checking the \(2431/3241\) equality through 14 and the separate OEIS equality through 15. [Paper](https://arxiv.org/abs/2610.11271) |
| Hall’s condition for adjacent levels of the permutohedron | Reviewed the partial results and numerical bounds. I did not obtain a proof or obstruction for the full statement. [Paper](https://arxiv.org/abs/2611.34537) |

## Lean reproduction

From the repository root (Lean `v4.37.0-rc1`, Mathlib `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`):

```bash
lake env lean OpenConjectures/MouBarcode.lean
```

The command exits 0 and prints the following.

```text
'MouBarcode.table_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.table_antichain' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.table_ordinal_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.square_at_nineteen' depends on axioms: [propext, Classical.choice]
'MouBarcode.square_at_twenty_two' depends on axioms: [propext, Classical.choice]
'MouBarcode.vertices_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.witness_vertex_count' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'MouBarcode.mou_conjecture_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Independent review

A reviewer recompiled the file and found no `sorry`, `admit`, `native_decide` or added axioms. They compared the Lean definitions with the paper's Definitions 4.1, 4.4 and 4.5 and equation (4.4), read from the arXiv v1 PDF. The bar lengths are C(a_i + t, d − 1), full bars contribute C(a_i + t, d), and the endpoint convention matches. Effectiveness means F_P(N) ≤ B_a(N) for all N, and copies are counted as pairs (v, λ) with λ > 0 and v + λ·vert(O(P)) ⊆ S, as in the paper's definition of F_X.

The disproof does not depend on the formal barcode machinery. The paper's own Theorem 1.2 gives B_a(Ω°_P(5)) = Σ_{q<5} Ω°_P(q) = 0 for every barcode, while Ω°_P(5) = 25. Any 25-point set containing the 24 vertices has at least one copy. The same reasoning gives a counterexample whenever the number of strict maps into a chain of the poset's height is at least the number of vertices of its order polytope.
