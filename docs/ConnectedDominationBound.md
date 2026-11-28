# A degree-sensitive disk for connected domination roots

**Answered — the root-bound question in Shao and Zhao’s Open Problem 4, with a linear, degree-sensitive bound.** Let \(G\) be any finite connected simple graph, \(n=|V(G)|\), and \(\delta\) its minimum degree. Put \(k=\max\{1,2\delta+2-n\}\). Every complex zero \(z\) of its connected domination polynomial satisfies

\[
\boxed{\quad |z+1|\le \frac{4n}{k}.\quad}
\]

For example, minimum degree at least \(3n/4\) gives the uniform radius \(8\). The Lean proof also establishes the finer bound \(|z+1|\le(1+t)/(t^{k/n}-1)\) for every real \(t>1\). [Lean file](../OpenConjectures/ConnectedDominationBound.lean)

## The source question

Pingping Shao and Chengye Zhao pose the following question in *On the Roots of Connected Domination Polynomials*, arXiv:2609.06569v5, section 5.2, page 14. They explicitly allow dependence on graph order and minimum degree. [Open Problem 4, printed page 14](https://arxiv.org/pdf/2609.06569v5#page=14)

> is there an explicit bound for connected domination roots analogous to Oboudi’s?

Definitions 1.1–1.3 specify finite undirected simple graphs, require \(G\) to be connected for \(D_c\), and count vertex subsets \(S\) which dominate \(G\) and induce a connected subgraph. The theorem above answers this entire root-bound question. The coefficient and limit-curve questions in the same paragraph have separate scopes. [Definitions](https://arxiv.org/html/2609.06569v5#S1.SS1) · [Problem statement](https://arxiv.org/html/2609.06569v5#S5.SS2)

The degree dependence matters. Monicity and the elementary bounds \(d_c(G,i)\le\binom ni\) alone give an order-only estimate. Indeed, with \(r=|z|\), the root equation implies \(2r^n\le(1+r)^n\). The proof below uses the graph structure to give a bounded radius even as \(n\) grows when \(\delta/n\) stays above \(1/2\) by a fixed positive amount. At the other extreme, the paper’s cycle formula gives a root \(z=(-n-\sqrt{n^2-4n})/2\) for \(n\ge5\). At fixed minimum degree two, \(|z+1|/n\to1\), so the worst-case order of growth in \(n\) is linear. [Cycle formula, Lemma 3.1](https://arxiv.org/pdf/2609.06569v5#page=7)

## Proof

Write \(N[u]\) for the closed neighbourhood of a vertex and \(R=|1+z|\).

1. **Deleting fewer than \(k\) vertices leaves a connected dominating set.** With zero deletions the claim follows from connectedness. Otherwise let \(r\ge1\) be the number removed and suppose \(r<k\). Then \(r<2\delta+2-n\). For any vertices \(u,v\), the two closed neighbourhoods have at least \(2(\delta+1)-n>r\) vertices in common. Pick a surviving common vertex. Taking \(u=v\) proves domination. Taking any two surviving endpoints proves they are joined within the surviving set by a walk of length at most two. The same argument gives a surviving vertex, including when \(G\) has one vertex. Thus every subset \(S\) which fails connected domination has \(n-|S|\ge k\).

2. **Compare the polynomial at its zero with the full subset sum.** Since the qualifying subsets contribute \(D_c(G,z)=0\), the sum over all subsets leaves
   \[
   (1+z)^n=\sum_{S\ \mathrm{failing}} z^{|S|}.
   \]
   For \(t\ge1\), each failing subset satisfies \(t^k\le t^{n-|S|}\). Take absolute values, use \(|z|\le R+1\), and include all subsets in the final nonnegative sum. This gives
   \[
   t^k R^n
    \le \sum_{S\ \mathrm{failing}}(R+1)^{|S|}t^{n-|S|}
    \le (R+1+t)^n .
   \]

3. **Extract the radius.** Connectedness gives \(n\ge1\), and \(k\ge1\) by definition. For \(t>1\), taking an \(n\)-th root and rearranging gives \(R\le(1+t)/(t^{k/n}-1)\). At \(t=3\), use \(3^a\ge e^a\ge1+a\) for \(a=k/n>0\) to obtain \(R\le4n/k\). This proof applies to every complex root, including zero. [Graph lemma](../OpenConjectures/ConnectedDominationBound.lean) · [Binomial comparison](../OpenConjectures/ConnectedDominationBound.lean)

## Lean correspondence

| Paper or proof object | Formal object |
|---|---|
| Finite undirected simple connected graph | `G : SimpleGraph V`, `[Fintype V]` and `hG : G.Connected`. Decidable equality and adjacency support finite enumeration and are available classically for every such graph. |
| Connected dominating subset | `ConnectedDominating G s` checks every vertex outside `s` has a neighbour in `s` and asks Mathlib for connectedness of the induced graph `G.induce (s : Set V)`. Each labelled subset occurs once. |
| \(D_c(G,x)=\sum_s x^{|s|}\) | `connectedDominationPolynomial` is a Mathlib `Polynomial ℂ`. The theorem `coeff_eq` proves its coefficient in every natural degree is the count `coefficient G j`. |
| Root and radius | `Polynomial.IsRoot` is ordinary evaluation at a complex number. `‖z + 1‖` is the complex modulus. `G.minDegree` and `Fintype.card V` are Mathlib’s graph degree and order. |
| Positive-part convention | Natural subtraction in `threshold` truncates at zero. The outer maximum with one makes it exactly \(\max(1,2\delta+2-n)\) under either natural or integer arithmetic. |
| Full result | `radius_at` quantifies over every \(t>1\). `explicit_disk` states the simple bound directly in terms of order and minimum degree. |

[Definitions and coefficient theorem](../OpenConjectures/ConnectedDominationBound.lean) · [Explicit disk](../OpenConjectures/ConnectedDominationBound.lean)

## Independent computations

Both algorithms reproduced the paper’s examples before the exhaustive small-graph check. The entries below are coefficients in increasing degree, beginning with the constant coefficient. Lean separately checked all four vectors with kernel reduction. [Example 2.2, page 5](https://arxiv.org/pdf/2609.06569v5#page=5) · [Lemma 3.1, page 7](https://arxiv.org/pdf/2609.06569v5#page=7) · [Lean sanity lemmas](../OpenConjectures/ConnectedDominationBound.lean)

| Graph | Complete coefficient vector |
|---|---|
| \(P_3\) | \(0,1,2,1\) |
| \(P_3[K_2]\) | \(0,2,9,16,14,6,1\) |
| \(C_4\) | \(0,0,4,4,1\) |
| \(C_5\) | \(0,0,0,5,5,1\) |

Algorithm A grows the reachable set within each vertex subset and then checks domination by the graph neighbourhoods. Algorithm B enumerates spanning trees by testing candidate edges for cycles, takes each tree’s internal vertices, and forms all supersets. For \(n\ge3\), the internal vertices of a tree induce a connected dominating set; conversely, any connected dominating set supports a tree to which each outside vertex can be added as a single leaf. Orders one and two are handled directly.

The programs agreed on the actual subset families for **all 33,867 labelled graphs of orders one through six**. Of these, **27,476 were connected**. Every connected graph also passed two exact checks, one for the deletion threshold and one for containment of its actual roots in the disk. The latter applies the Schur recursion to the integer polynomial \(k^n D_c(G,4nw/k-1)\). It uses integer arithmetic throughout. [Reproducible Python algorithms](../scripts/shao_zhao/verify.py)

## Open-status and priority checks

Checks on **28 November 2026 UTC** located no earlier proof or preregistration of the degree-sensitive root-bound clause. The strongest dated public scope evidence is a **26 November** update by the investigators of the adjacent coefficient questions explicitly identifying the order-dependent root bound as open in their work. Public indexes can miss recent or unpublished work. [Dated scope statement](https://github.com/the-omega-institute/trureturing/issues/34367#issuecomment-7181774900)

| Source checked | Result |
|---|---|
| arXiv versions | The version history records v1 on 6 September and v5 on 23 September. I inspected all five texts. The explicit-bound question appears in v1 and persists through v5. [Version history](https://arxiv.org/abs/2609.06569) |
| Citation indexes | OpenAlex work W7212026642 reported zero citations and its separate citing-works query returned zero. Semantic Scholar matched both title and identifier, reporting zero citing papers; its citations endpoint returned an empty list. DataCite also recorded zero. An additional OpenAlex title search returned 31 records, including the source, earlier family computations and several other domination variants. [OpenAlex citing works](https://api.openalex.org/works?filter=cites:W7212026642) · [Semantic Scholar citations](https://api.semanticscholar.org/graph/v1/paper/ARXIV:2609.06569/citations?fields=title,year,url) |
| TrureTuring | Searches by identifier, both surnames, invariant, root-bound wording, and the authors with “Problem 4” found the relevant issue bodies. Issue 34367 covers the two coefficient questions. I also read its three comments. Issues 22954 and 23313 cover independent-domination and total-domination root density. None claims the bound proved here. The paper ID alone failed to surface issue 34367 in `gh search issues`. [Coefficient registration](https://github.com/the-omega-institute/trureturing/issues/34367) · [Independent domination](https://github.com/the-omega-institute/trureturing/issues/22954) · [Total domination](https://github.com/the-omega-institute/trureturing/issues/23313) |
| Solved Conjectures | I checked the published catalogue, issues, code search, and the repository snapshot at `a8cbf1807910d8d49b6c96ce0a1eac84d9ef7540`. The `results/` tree contained 2,352 files. Full-text screening covered 2,344 text files including the top-level indexes, with zero matches for the identifier or targeted invariant-and-root wording. A looser code search hit a heading about disconnected domination hypergraphs in an unrelated oriented-graph proof. [Published catalogue](https://itsdavis.com/solved-conjectures/catalogue/) · [Pinned results](https://github.com/1337isnot1337/solved-conjectures/tree/a8cbf1807910d8d49b6c96ce0a1eac84d9ef7540/results) |
| aiXiv | Read-only full-text queries covered the arXiv identifier, exact invariant, root wording, and authors with problem number. Related hits concern ordinary-domination coefficient valleys. I also screened all 9,598 public corpus records available at the check. [Full-text API search](https://aixiv.online/api/v1/papers?q=%22connected%20domination%20polynomial%22&limit=100) · [Corpus](https://aixiv.online/api/v1/corpus.jsonl) |
| Earlier literature | Oboudi bounds ordinary domination roots, and Alikhani–Jafari bound total domination roots. Omar’s degree estimate also counts ordinary dominating sets. Earlier work on connected domination computes polynomials and roots for particular graph families. These results use different counting families or narrower graph hypotheses. The degree-sensitive estimate above uses the connected-domination definition in the current source. [Oboudi](https://doi.org/10.1016/j.dam.2015.12.010) · [Total domination](https://arxiv.org/abs/1605.02222) · [Omar](https://arxiv.org/abs/2601.14494) · [Mojdeh and Emadi](https://fasciculi-mathematici.put.poznan.pl/artykuly/60/FM60%282018%29-MojdehDA-EmadiAS.pdf) · [Connected domination roots for particular graphs](https://www.iosrjournals.org/iosr-jm/papers/Vol12-issue4/Version-3/C1204031316.pdf) |

## Other candidates surveyed

The title screen used September–November math.CO listings. I retrieved 27 primary problem texts for the initial screen. The following affected candidate selection. 

| Candidate | Disposition |
|---|---|
| Shao–Zhao, Italian domination on paths and cycles, arXiv:2610.00108 | Existing registrations cover path-and-cycle coefficient unimodality, the cycle recurrence, and the all-deficits formula. [Paper](https://arxiv.org/abs/2610.00108) · [Unimodality](https://github.com/the-omega-institute/trureturing/issues/25413) · [Recurrence](https://github.com/the-omega-institute/trureturing/issues/12435) · [Coefficient formula](https://github.com/the-omega-institute/trureturing/issues/23882) |
| Chen–He–Lai–Li, local mean order of dominating sets | The precise conjecture about stems already had a public proof registration. [Paper](https://arxiv.org/abs/2610.11446) · [Registration](https://github.com/the-omega-institute/trureturing/issues/14740) |
| Zhou–Chen–Li–Fan, spectral minimizers at fixed dissociation number | The odd-parity branch of Conjecture 1 already had a public counterexample registration. [Paper](https://arxiv.org/abs/2610.38539) · [Registration](https://github.com/the-omega-institute/trureturing/issues/24250) |
| Cycle-basis bounds for reliability coefficients | The paper itself proves the displayed Colbourn problem. [Paper](https://arxiv.org/abs/2611.12302) |
| Tree independence polynomials with a perfect matching | The paper itself constructs counterexamples to the cited Ramos–Sun implication at arbitrary prescribed positive distances. [Paper](https://arxiv.org/abs/2610.18340) |
| Barrier log-concavity of forests | The source proves an eventual theorem and formulates separate all-size questions. A finite extension in graph order would leave their universal assertions open. [Paper](https://arxiv.org/abs/2610.22098) |
| Acyclic polynomials of orientations | The authors ask for classifications by root and coefficient shape. A single small orientation would supply one member of such a class. [Paper](https://arxiv.org/abs/2609.02249) |

## Reproducing the kernel check

Git Bash on Windows, Lean `4.37.0-rc1` at `0b77e12952ad39077d80d8bd6b66d601f225c321`, Mathlib at `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`. The project used its installed dependencies. The final Lean command exited **0** with the exact output below. The source SHA-256 was `649eac5c45a5f10c6acf37947e7aae9d6a1c0b90d9f0aff2f49c9e70f57871d5`. [Lean source](../OpenConjectures/ConnectedDominationBound.lean)

```bash
lake env lean OpenConjectures/ConnectedDominationBound.lean
```

```text
'ShaoZhao.ConnectedDominationBound.coeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.path_three_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.double_path_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.cycle_four_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.cycle_five_sanity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.root_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.radius_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.shao_zhao_root_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ShaoZhao.ConnectedDominationBound.explicit_disk' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The local `master` checkout contains the new proof as an untracked file in `LeanProofs/AgentP/`. The report, search receipts, and computation logs are in the assigned `work/AgentP/` directory. No commit or publication was made.

## Independent review

A reviewer recompiled the file and found no `sorry`, `admit`, `native_decide` or added axioms. They read Open Problem 4 in the arXiv v5 PDF. The Lean definitions match Definitions 1.1–1.3: a subset dominates when every outside vertex has a neighbour in it, it must induce a connected subgraph, and D_c = Σ x^|S|. A separate floating-point test (`scripts/shao_zhao/reviewer_roots.py`) covered all connected labelled graphs on up to 6 vertices and 3,000 random graphs on 7 to 12 vertices, 29,589 graphs in all. The largest observed ratio max|z+1| / (4n/k) was 0.25.

**How to read this result.** Taken literally, the question ("is there an explicit bound depending on the order?") has an easy answer. D_c is monic with coefficients at most C(n, i), so Cauchy's classical root bound already gives an exponential bound in n, as the report notes above. The content here is the quality of the bound: it is linear in n, which is the correct order because the paper's own cycle roots have |z+1| ≈ n, and it is bounded (radius 8) whenever δ ≥ 3n/4. That is the sense in which it is "analogous to Oboudi's". TruReTuring #34367 (26 Nov 2026) settled the separate coefficient questions in the same paragraph and explicitly left the root bound open. The limit-curve question also remains open.
