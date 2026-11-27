# A unicyclic counterexample to connected zero forcing log-concavity

**SOLVED.** The log-concavity question in Mukherjee and Ray, Problem 6.2, has a negative answer. Attach a two-edge path to a pentagon. The resulting connected zero forcing polynomial has coefficients 5, 7, and 10 at degrees 2, 3, and 4. They violate log-concavity because $7^2=49<50=5\cdot10$. Lean verified the full coefficient vector and the negation of the universal statement. [Paper, v2, Problem 6.2](https://arxiv.org/html/2611.10985v2#S6.Thmtheorem2) · [Lean proof](../OpenConjectures/UnicyclicLogConcavity.lean)

## Source and scope

Sanjay Mukherjee and Papi Ray pose the question on page 25 of *On the connected zero forcing polynomial of finite trees*, arXiv:2611.10985v2. The first two sentences of Problem 6.2 read

> Determine the connected zero forcing polynomial of a unicyclic graph. Is this polynomial always log-concave?

The result resolves the second sentence for the full class of finite unicyclic graphs. The same numbered problem asks separately for a general polynomial formula and for coefficientwise extrema at fixed order and leaf count. Those questions have their own public work records. The authors proved log-concavity for trees in Theorem 4.6. [Typeset statement](https://arxiv.org/pdf/2611.10985v2#page=25) · [Tree theorem](https://arxiv.org/html/2611.10985v2#S4.Thmtheorem6)

## Proof by counting cycle arcs

Use vertices 0 through 6, with the six edges joining consecutive integers and one extra edge joining 0 to 4. Deleting that edge leaves a spanning path. Adding it back creates exactly the cycle $0,1,2,3,4,0$. The path $4,5,6$ is attached to the cycle at vertex 4.

A connected initial set forces the whole graph exactly when it contains a cycle edge. To see sufficiency, its initially colored cycle vertices form either the whole cycle or a consecutive arc of at least two vertices. While the arc is proper, its two endpoints are distinct. At least one endpoint differs from vertex 4 and has exactly one white neighbor. Extend the arc from that end. Once the cycle is colored, vertex 4 and then vertex 5 can finish the tail as needed.

For necessity, a connected set with no cycle edge meets the cycle in at most one vertex. If it contains a cycle vertex away from 4, it consists of that singleton and cannot make a move. Every other such set lies in the path $4,5,6$. Even after the whole path is colored, vertex 4 has two white cycle neighbors, so neither can be forced.

For a proper cycle arc of size $r=2,3,4$, there are five starting positions. Exactly $r$ arcs contain vertex 4. An initial set that includes tail vertices must contain 4, and its tail portion is either $\{5\}$ or $\{5,6\}$. The full cycle contributes one choice in each tail case.

| Initially colored tail vertices | Size 2 | Size 3 | Size 4 | Size 5 | Size 6 | Size 7 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| None | 5 | 5 | 5 | 1 | 0 | 0 |
| Vertex 5 | 0 | 2 | 3 | 4 | 1 | 0 |
| Vertices 5 and 6 | 0 | 0 | 2 | 3 | 4 | 1 |
| **Total** | **5** | **7** | **10** | **8** | **5** | **1** |

The empty set and all singletons fail. Therefore

$$
Z_C^G(x)=5x^2+7x^3+10x^4+8x^5+5x^6+x^7.
$$

The same count gives an infinite family. Replace the pentagon by a cycle of length $m\ge5$, keeping the two-edge tail. The coefficients in degrees 2, 3, and 4 are $m,m+2,m+5$. The gap $m(m+5)-(m+2)^2=m-4$ is positive. This gives a hand proof for all $m\ge5$. The Lean theorem uses the seven-vertex witness, which suffices to disprove the universal claim.

## Independent computational checks

The first Python algorithm represents subsets by bit masks, applies a legal single-vertex force and looks up the resulting larger subset, and tests induced connectivity by a graph traversal. It can choose any legal force because extra colored vertices preserve any successful continuation after skipping targets already colored. [Search implementation](../scripts/unicyclic/search_unicyclic.py)

The second algorithm uses unordered pairs and ordinary sets. It enumerates all nonempty *forts*, sets $F$ such that no vertex outside $F$ has exactly one neighbor in $F$. A disjoint fort can never receive a first force. Conversely, when a forcing process stalls before completion, its remaining white set is a disjoint fort. The algorithm tests whether each initial set intersects every fort and whether each of its proper nonempty cuts has a crossing edge. A third calculation counts the arcs and initial tail segments in the proof above. [Independent checker](../scripts/unicyclic/check_counts.py)

Both graph algorithms reproduced the three complete source vectors below. Lean checked both four-vertex vectors and the published coefficients 5, 13, and 12 in degrees 5, 6, and 7 of the nine-vertex example. [Four-vertex examples, page 11](https://arxiv.org/pdf/2611.10985v2#page=11) · [Example 5.17, Case I, page 22](https://arxiv.org/html/2611.10985v2#S5.Thmtheorem17)

| Graph | Coefficients from degree zero |
| --- | --- |
| Four-vertex path | 0, 2, 3, 2, 1 |
| Three-leaf star | 0, 0, 0, 3, 1 |
| Uniform starlike tree $T'$, with arm lengths 2, 2, 2, 1, 1 | 0, 0, 0, 0, 0, 5, 13, 12, 5, 1 |
| Pentagon with a two-edge tail | 0, 0, 5, 7, 10, 8, 5, 1 |

Run `python scripts/unicyclic/check_counts.py`. It exited 0. The two algorithms also agreed with the arc count for every cycle length from 5 through 9.

## Correspondence between the paper and Lean

| Paper definition | Lean declaration and meaning |
| --- | --- |
| Finite simple undirected graph | Mathlib's `SimpleGraph W` on an arbitrary `Fintype W`. The finite-set operations use decidable vertex equality, available classically for every such type. |
| A colored vertex with exactly one uncolored neighbor colors that neighbor | `LegalForce G s u w` requires $u\in s$, $w\notin s$, adjacency, and equality to $w$ for every white neighbor of $u$. |
| Repeated legal forces eventually color every vertex | `Finishes` records a chronological sequence of single legal additions ending at `Finset.univ`. `ZeroForces` allows any sequence length. `finishes_card` proves that a successful sequence has exactly the number of initially white vertices as its length. |
| The initially colored set induces a connected graph | `(G.induce (s : Set W)).Connected` is Mathlib's induced-graph connectedness predicate on the original subset. |
| $Z_C(G,k)$ counts qualifying initial subsets of size $k$ | `paperCoefficient` takes `Nat.card` of exactly that subtype. `paperCoefficient_eq` proves equality with `coefficient`, the executable filtered powerset count. Each initial subset contributes once regardless of how many forcing orders it permits. |
| $Z_C^G(x)=\sum_k Z_C(G,k)x^k$ | `connectedForcingPolynomial` is a Mathlib polynomial over the naturals. `polynomial_coeff` proves its coefficient equals `paperCoefficient` for every degree, including degrees above the graph order. |
| Connected graph with one undirected cycle | `Unicyclic` asks for connectedness and a present edge whose deletion yields a Mathlib tree. A tree has a unique path between the ends of the restored edge, and every cycle must use that edge. Conversely, deleting a cycle edge from a connected graph with exactly one cycle preserves connectedness and removes its only cycle. |
| Log-concavity for every coefficient index | `LogConcave` requires $a_k a_{k+2}\le a_{k+1}^2$ for every natural $k$. The quantified assertion is `UniversalClaim`. Its negation is `not_unicyclic_log_concavity`. |

The full vector is checked from the graph by kernel reduction. The final proof specializes the universal claim to the witness and reads the degree-2, degree-3, and degree-4 counts from that vector. [Lean source](../OpenConjectures/UnicyclicLogConcavity.lean)

## Replaying Lean

The project uses Lean 4.37.0-rc1 and Mathlib revision `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. From the repository root:

```bash
lake env lean OpenConjectures/UnicyclicLogConcavity.lean
```

Lean exited with code 0 and printed the following six axiom checks.

```text
'MukherjeeRay.UnicyclicLogConcavity.paper_path4' depends on axioms: [propext, Classical.choice, Quot.sound]
'MukherjeeRay.UnicyclicLogConcavity.paper_star4' depends on axioms: [propext, Classical.choice, Quot.sound]
'MukherjeeRay.UnicyclicLogConcavity.paper_example_5_17' depends on axioms: [propext, Classical.choice, Quot.sound]
'MukherjeeRay.UnicyclicLogConcavity.tadpole_unicyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'MukherjeeRay.UnicyclicLogConcavity.tadpole_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound]
'MukherjeeRay.UnicyclicLogConcavity.not_unicyclic_log_concavity' depends on axioms: [propext, Classical.choice, Quot.sound]
```



## Public status checked on 27 November 2026

- **arXiv versions.** V1 was submitted on 7 November. Its Problem 5.2 asked for the unicyclic polynomial and extrema. V2 was submitted on 25 November at 12:50 UTC. It adds the log-concavity question in Problem 6.2. The version history listed v2 as current at the check. [Submission history](https://arxiv.org/abs/2611.10985) · [V1](https://arxiv.org/html/2611.10985v1#S5.Thmtheorem2) · [V2](https://arxiv.org/html/2611.10985v2#S6.Thmtheorem2)
- **Citation indexes.** OpenAlex work W7225736249 reported zero citations. Its citing-works endpoint returned zero records, and a title search for “connected zero forcing polynomial” returned the source paper alone. The OpenAlex record's update timestamp precedes v2. Semantic Scholar's bulk title search independently matched the title and arXiv identifier (Corpus ID 295732426) and reported zero citations. Its separate citations endpoint was rate-limited. DataCite also reported zero. [OpenAlex citing works](https://api.openalex.org/works?filter=cites%3AW7225736249) · [Semantic Scholar exact title query](https://api.semanticscholar.org/graph/v1/paper/search/bulk?query=%22On%20the%20connected%20zero%20forcing%20polynomial%20of%20finite%20trees%22&fields=title%2CcitationCount%2CexternalIds&year=2026) · [DataCite](https://api.datacite.org/dois/10.48550/arxiv.2611.10985)
- **TrureTuring.** The indexed source record concerns v1's ordered coefficient-crossing question. GitHub searches by paper ID, authors, forcing, unicyclicity, tadpole, and log-concavity identified the adjacent registrations. Issue 30379 reports a mathematical counterexample to coefficientwise extrema on five vertices. Issue 33479 gives a proposed general formula and reports small-graph checks. Both precede v2 and target different propositions. A search of the default branch's Problems, Library, and Blueprint path indexes, supplemented by issue searches, found no record claiming the unicyclic log-concavity answer. [Repository snapshot](https://github.com/the-omega-institute/trureturing/tree/0ab3edce883d165b87f2d0ace6431d8bc026ea3e) · [Ordered crossing](https://www.trureturing.org/research/mukherjee-ray-2026-ordered-connected-forcing-crossing/) · [Extrema registration and comments](https://github.com/the-omega-institute/trureturing/issues/30379) · [Formula registration](https://github.com/the-omega-institute/trureturing/issues/33479)
- **Solved Conjectures.** The published catalogue was dated 19 November. I also searched the repository's current contents index, README, aliases, complete path index, and GitHub issue searches. The related Boyer et al. issue concerns the ordinary zero forcing polynomial. No matching claim surfaced. [Catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Current contents at checked snapshot](https://github.com/1337isnot1337/solved-conjectures/blob/9587fe4fe9b8d0b8ffb5b158bbfb91361fe70e80/CONTENTS.md) · [Boyer et al. issue](https://github.com/1337isnot1337/solved-conjectures/issues/323)
- **aiXiv and Hexagon.** Searches used the paper ID, author names, forcing-polynomial terms, and the combined unicyclic log-concavity wording. aiXiv returned related claims about ordinary zero forcing and unrelated log-concavity problems. Hexagon returned zero works for the combined graph-polynomial terms. No prior resolution of the specific universal assertion was located. The short interval since v2 limits what indexing can establish about priority. [aiXiv search](https://aixiv.online/search?q=unicyclic%20connected%20zero%20forcing%20polynomial%20log-concavity) · [Hexagon search](https://hexagonmath.org/search?q=unicyclic%20connected%20zero%20forcing%20polynomial)

## Other candidates screened

| Candidate | Disposition |
| --- | --- |
| Mukherjee–Ray, unicyclic log-concavity | **Kept and disproved.** A seven-vertex witness satisfies the definitions in the revised source. [Problem 6.2](https://arxiv.org/html/2611.10985v2#S6.Thmtheorem2) |
| Mukherjee–Ray, ordered crossing | Dropped. TrureTuring had already recorded the four-vertex path/star refutation of v1 Problem 5.3, retained as v2 Problem 6.3. [Paper](https://arxiv.org/html/2611.10985v2#S6.Thmtheorem3) · [Prior refutation](https://www.trureturing.org/research/mukherjee-ray-2026-ordered-connected-forcing-crossing/) |
| Mukherjee–Ray, log-concavity for arbitrary graphs | Dropped. Newton and Brimkov already constructed connected forcing polynomials that fail unimodality on graphs made from joins. The positive support has no gaps because extending a connected forcing set by an adjacent vertex preserves both properties. Their result therefore already gives failure of general log-concavity. [Newton–Brimkov construction](https://arxiv.org/html/2611.11352v1#S2) |
| Cazenave, spectral graph conjectures | Dropped the two inspected targets after locating prior claims for Conjecture 4 and Conjecture 6(iii). [Source](https://arxiv.org/abs/2611.03879) · [Conjecture 4 record](https://the-omega-institute.github.io/trureturing-mdbook/Library/Eigenstructure/cazenave2026spectralgraphconjectures.html) · [Proposed proof of 6(iii)](https://hexagonmath.org/2611.01102v1) |
| Dvořáková–Mol–Pelantová, minimally repetitive rich words | Deferred. The all-alphabet assertion concerns infinite words and morphism languages. The paper already proves the four-letter case. A finite-word search alone would not settle the assertion. [Source](https://arxiv.org/abs/2611.13676) |
| Shukla, small five-chromatic unit-distance graphs in disks | Dropped. The three constructions in the paper already have exact certificates. A smaller construction at the listed radii would improve a bound while leaving the optimum undetermined. [Source](https://arxiv.org/abs/2611.06269) |

## Independent review

A reviewer recompiled the file and found no `sorry`, `admit`, `native_decide` or added axioms. They read Problem 6.2 and the definitions in the arXiv v2 PDF. They confirmed that the log-concavity question is absent from v1 (where the problem is 5.2, with two parts) and first appears in v2 (25 Nov 2026). A separate brute-force program (`scripts/unicyclic/reviewer_check.py`) reproduces the coefficient vector 0, 0, 5, 7, 10, 8, 5, 1. The TruReTuring records #30379 and #33479 cover the other two parts of the problem (the extremal graphs and the general formula), not log-concavity. No earlier answer to the log-concavity question was found. Newton–Brimkov (arXiv:2611.11352) show that connected forcing polynomials of general graphs need not be unimodal, but their graphs contain a universal vertex and are not unicyclic.

**Scope.** Problem 6.2 asks three things: a formula for the polynomial, whether it is always log-concave, and whether extremal graphs U_min and U_max exist. This result answers only the second question, negatively.
