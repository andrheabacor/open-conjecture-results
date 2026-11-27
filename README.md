# Open conjectures resolved with Lean 4 proofs

This repository contains six machine-checked resolutions of previously unresolved, publicly stated conjectures. Every theorem is checked by Lean 4 (`v4.37.0-rc1`) with Mathlib. There is no `sorry`, `admit`, `native_decide` or added `axiom`. `#print axioms` on every main theorem reports only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

| Result | Source | Type | Lean | Write-up |
|---|---|---|---|---|
| The conjecture is **proved**: the selected sequence c(n) is a subsequence of OEIS A110978 | [MathOverflow 464360](https://mathoverflow.net/questions/464360) (Feb 2024, unanswered) | Proof | [`OpenConjectures/MO464360.lean`](OpenConjectures/MO464360.lean) | [`docs/MO464360.md`](docs/MO464360.md) |
| The conjecture is **disproved**: A046385 has terms at indices 14, 17 and 21, which the conjecture says do not exist | [OEIS A046385](https://oeis.org/A046385), conjecture by H. Pfoertner (Aug 2019) | Counterexample | [`OpenConjectures/A046385.lean`](OpenConjectures/A046385.lean) | [`docs/A046385.md`](docs/A046385.md) |
| Conjecture 8 is **disproved**: the Möbius value for n = 2^7·3^6 is −57, but the conjecture allows only 0 or a positive value | [Mirzavaziri–Yaqubi, arXiv:2611.18194](https://arxiv.org/abs/2611.18194), Conjecture 8 (Nov 2026) | Counterexample | [`OpenConjectures/MirzavaziriYaqubi8.lean`](OpenConjectures/MirzavaziriYaqubi8.lean) | [`docs/MirzavaziriYaqubi8.md`](docs/MirzavaziriYaqubi8.md) |
| Hamilton's family is **proved**: every k whose binary expansion is `10`, then j > 1 ones, then `010` is a term, so the sequence is infinite | [OEIS A179697](https://oeis.org/A179697), conjecture in the original 2010 entry | Proof | [`OpenConjectures/A179697.lean`](OpenConjectures/A179697.lean) | [`docs/A179697.md`](docs/A179697.md) |
| Conjecture 1.4 is **disproved**: the poset made of a 5-element chain plus 2 isolated points has no effective barcode | [Mou, arXiv:2611.32429](https://arxiv.org/abs/2611.32429), Conjecture 1.4 (Nov 2026) | Counterexample | [`OpenConjectures/MouBarcode.lean`](OpenConjectures/MouBarcode.lean) | [`docs/MouBarcode.md`](docs/MouBarcode.md) |
| Conjecture 4 is **disproved**: at d = 4 the sequence repeats every 3 gaps, not every 4 as predicted | [van Berkel–Bosma, arXiv:2609.16843v2](https://arxiv.org/abs/2609.16843), Conjecture 4 (Nov 2026) | Counterexample | [`OpenConjectures/VanBerkelBosma4.lean`](OpenConjectures/VanBerkelBosma4.lean) | [`docs/VanBerkelBosma4.md`](docs/VanBerkelBosma4.md) |

## 1. MathOverflow 464360 — a carry-free subsequence (proved)

Let b(n) start at A = n and repeatedly apply A := A + min(2^tr(A), A / 2^tr(A)) while A < 2n, where tr(A) is the number of trailing binary zeros. Let c(n) list the odd k with b((k−1)/2) = k. The question conjectured that c(n) is a subsequence of [A110978](https://oeis.org/A110978), the odd composite numbers that factor as u·v with u, v > 1 where binary long multiplication needs no carry.

**Proof idea.** Look at the last step x → k = 2n+1, where x = 2^t·d with d odd. The step s = min(2^t, d) is at least 2, so x is even. If s = 2^t, then k would be even. So s = d < 2^t and k = d·(2^t + 1). Multiplying d by 2^t+1 places two copies of d into disjoint binary blocks, so the multiplication has no carry. Lean also proves c is infinite (it contains every 3·2^t + 3 with t ≥ 2) and gives a strictly increasing index map between the two increasing enumerations:

```lean
theorem mathOverflow464360 :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, Nat.nth inC i = Nat.nth inA (g i)
```

## 2. OEIS A046385 — the exhaustiveness conjecture (disproved)

A046385(k) is the smallest palindrome with exactly k palindromic prime factors (counted with multiplicity) and no other prime factors. The entry lists terms for k = 0..13, 15, 16 and 20 and states: *"Conjecture: The sequence is finite and has no other terms than those shown here."*

**Counterexample.** p = 10^46 + 10^33 + 10^23 + 10^13 + 1 is a palindromic prime. Lean certifies this with a Lucas (Pratt) certificate that the kernel checks. Multiplying a palindrome of at most 9 digits by p writes five symmetric, non-overlapping copies of it, so the product is again a palindrome:

| k | witness | factorization |
|---|---|---|
| 14 | 2977792 · p | 2^12 · 727 · p |
| 17 | 40955904 · p | 2^12 · 3^2 · 11 · 101 · p |
| 21 | 677707776 · p | 2^16 · 3^3 · 383 · p |

These witnesses give upper bounds on a(14), a(17) and a(21), not their exact values. **Scope:** this refutes the conjecture as stated, specifically its "no other terms" clause. Whether the sequence is finite is still open.

## 3. Mirzavaziri–Yaqubi Conjecture 8 — Möbius signs on the factorization poset (disproved)

Order the unordered factorizations of n by refinement. The prime factorization is at the bottom and [n] is at the top. [Mirzavaziri and Yaqubi](https://arxiv.org/abs/2611.18194) conjectured that μ(prime factorization, n) *"is either 0 or has the sign (−1)^(Ω(n)+1), and it vanishes for n=p^k with k≥3"*. They checked every n with Ω(n) ≤ 8.

**Counterexample.** n = 93312 = 2^7·3^6 has Ω(n) = 13, so the conjecture allows only 0 or a positive value. The actual value is **μ = −57**, computed over the 1,752 factorizations of n. The Lean proof checks a certificate of the whole interval against Mathlib's `IncidenceAlgebra.mu`. Three separate programs agree, and the reviewer's program reproduces all 20 entries of the paper's Table 1.

```lean
theorem refutation : ¬ Conjecture8
```

## 4. OEIS A179697 — Hamilton's infinite family (proved)

A179697 lists k such that, with R the binary reversal, |k + R(k) − R(k + R(k))| = |k − R(k)| + R(|k − R(k)|) = k. The 2010 entry states: *"All numbers whose binary representation is of the form 10(j 1s)010, where j>1, appear to be terms of this sequence."*

**Proof idea.** Write k = 2q, where q = `10 1^j 01` is a binary palindrome, so R(k) = q. With t = j − 2, the binary words of 3q and 5q are `1000 1^t 0111` and `1110 1^t 0001`, which are reversals of each other. Then k + R(k) = 3q, its reversal is 5q, and |3q − 5q| = 2q = k. Also |k − q| + R(q) = 2q = k. Each such k equals 6(2^(j+2) − 1), so the sequence is infinite.

```lean
theorem hamilton_family {k j : ℕ} (hj : 1 < j)
    (hw : (Nat.digits 2 k).reverse = hamiltonWord j) : Member k
```

The same file also proves Branicky's 2026 conjecture that every term starts with `1011` and ends with `11010`. That result is **not** claimed as new: a complete argument already appeared in [TruReTuring issue 29105](https://github.com/the-omega-institute/trureturing/issues/29105), which explicitly leaves Hamilton's family open.

## 5. Mou's Conjecture 1.4 — effective barcodes for order polytopes (disproved)

[Mou](https://arxiv.org/abs/2611.32429) defines binomial barcodes a of a poset P and a function B_a. A barcode is *effective* if F_P(N) ≤ B_a(N) for every N, where F_P(N) is the largest number of positive homothetic copies of the order polytope's vertex set that fit in an N-point set. Conjecture 1.4: *"Every finite poset with at least two elements admits an effective barcode."*

**Counterexample.** Let P be a 5-element chain plus 2 isolated elements. Its strict order polynomial is Ω°(q) = C(q,5)·q², which is 0 for q < 5 and 25 at q = 5. By the paper's Theorem 1.2, every barcode has B_a(25) = Σ_{q<5} Ω°(q) = 0. The order polytope has 6·4 = 24 vertices, so the vertices plus any one extra point form a 25-point set with at least one copy. So F_P(25) ≥ 1 > 0 = B_a(25), and no barcode of P is effective. Lean derives B_a(25) = 0 directly from the barcode definitions, without assuming Theorem 1.2.

```lean
theorem mou_conjecture_false : ¬ MouConjecture
```

## 6. van Berkel–Bosma Conjecture 4 — periods of 3-sumfree sequences (disproved)

S_{f,g,h} starts f < g < h. Each next term is the least integer larger than all previous terms that is not a sum of three distinct previous terms. [Conjecture 4](https://arxiv.org/abs/2609.16843) (added in v2): *"For every d ≥ 3 the 3-sumfree sequence S_{1,d−1,2d−1} is ultimately periodic, and, with the exception of d = 3 or d = 5, the preperiod length is d + 3 and the period length is d modulo 8d − 1."*

**Counterexample.** For d = 4, S_{1,3,7} = 1, 3, 7, 8, 9, 10, 15, 29, 35, 36, 56, 62, 63, 83, … Its gaps are 2, 4, 1, 1, 1, 5, 14, then (6, 1, 20) repeating, so the period is 3 (modulus 27), not 4. Lean certifies the first 13 terms against the greedy definition and shows that the 8th and 12th gaps differ (6 ≠ 1). A period of 4 after a preperiod of 7 is therefore impossible.

```lean
theorem conjecture4_false : ¬ Conjecture4
```

*Note.* For every d from 6 to 20 the actual modulus is 8d−3, not 8d−1, which is probably a misprint. The file's second theorem (d = 6) uses that discrepancy. The d = 4 result does not: it still refutes the conjecture after the misprint is corrected. See [`docs/VanBerkelBosma4.md`](docs/VanBerkelBosma4.md).

## Verifying

Install [elan](https://github.com/leanprover/elan), then run:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build           # checks all files; prints the #print axioms lines
```

## Provenance and caveats

These results were found and formalized by AI agents (OpenAI GPT‑6.2 Astra, coordinated by Claude) and reviewed before publication. "Previously unresolved" is based on searches done on 27 Nov 2026: the MathOverflow question had no answers or comments; the OEIS entry, its revision history and the literature showed no refutation. See each write-up for the search details. Priority beyond the sources searched cannot be guaranteed. All are modest results on lightly studied problems. They are not famous conjectures.
