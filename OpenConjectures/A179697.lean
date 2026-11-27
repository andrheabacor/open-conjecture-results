import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Binary reversal and Dylan Hamilton's infinite family in OEIS A179697

Michael S. Branicky conjectured on November 8, 2026 that the listed terms
begin with 1011 and end with 11010 in base two. The defining equations also
hold at zero, which the OEIS table omits. A November 11, 2026 public proof
outline for the prefix and suffix already appeared in TruReTuring issue 29105.
The second part proves Hamilton's separate conjecture from 2010 that every
binary word consisting of 10, then j > 1 ones, then 010 gives a term.
-/

namespace OEIS.A179697

/-- Reverse the ordinary binary digits, interpreting the result as a natural number. -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digits 2 n).reverse

/-- Absolute difference on naturals. One of the two summands is always zero. -/
def gap (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- The two equalities in the OEIS definition, with no domain restriction. -/
def Equations (k : ℕ) : Prop :=
  gap (k + rev k) (rev (k + rev k)) = k ∧
  gap k (rev k) + rev (gap k (rev k)) = k

instance (k : ℕ) : Decidable (Equations k) := by unfold Equations; infer_instance

/-- Membership in the positive sequence tabulated by OEIS. -/
def Member (k : ℕ) : Prop := 0 < k ∧ Equations k

instance (k : ℕ) : Decidable (Member k) := by unfold Member; infer_instance

/-- Mathlib stores digits least significant first, so the second clause reads
the specified suffix backwards. The first clause uses ordinary display order. -/
def HasEnds (k : ℕ) : Prop :=
  (Nat.digits 2 k).reverse.take 4 = [1, 0, 1, 1] ∧
  (Nat.digits 2 k).take 5 = [0, 1, 0, 1, 1]

instance (k : ℕ) : Decidable (HasEnds k) := by unfold HasEnds; infer_instance

theorem listed_examples :
    Member 90 ∧ Member 186 ∧ Member 378 ∧ Member 762 ∧ Member 1530 ∧
    Member 23130 := by decide

set_option maxRecDepth 8192 in
theorem first_three :
    (List.range 400).filter (fun k => decide (Member k)) = [90, 186, 378] := by decide

theorem first_example_digits :
    (Nat.digits 2 90).reverse = [1, 0, 1, 1, 0, 1, 0] ∧
    rev 90 = 45 ∧ rev (90 + rev 90) = 225 ∧ HasEnds 90 := by decide

theorem zero_boundary : Equations 0 ∧ ¬ HasEnds 0 ∧ ¬ Member 0 := by decide

private theorem rev_zero : rev 0 = 0 := by decide

private theorem rev_odd {n : ℕ} (hn : 0 < n) : rev n % 2 = 1 := by
  have hd : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  have hnz := Nat.getLast_digit_ne_zero 2 hn.ne'
  have hlt := Nat.digits_lt_base (by decide : 1 < 2) (List.getLast_mem hd)
  have hlast : (Nat.digits 2 n).getLast hd = 1 := by omega
  have hs : Nat.digits 2 n = (Nat.digits 2 n).dropLast ++ [1] := by
    simpa only [hlast] using (List.dropLast_append_getLast hd).symm
  unfold rev
  rw [hs, List.reverse_append]
  simp [Nat.ofDigits]

private theorem digits_rev_odd {n : ℕ} (hn : n % 2 = 1) :
    Nat.digits 2 (rev n) = (Nat.digits 2 n).reverse := by
  apply Nat.digits_ofDigits 2 (by decide)
  · intro d hd
    exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)
  · have hs := Nat.digits_eq_cons_digits_div (by decide : 1 < 2)
        (show n ≠ 0 by omega)
    rw [hn] at hs
    rw [hs]
    simp

private theorem rev_invol {n : ℕ} (hn : n % 2 = 1) : rev (rev n) = n := by
  change Nat.ofDigits 2 (Nat.digits 2 (rev n)).reverse = n
  rw [digits_rev_odd hn, List.reverse_reverse, Nat.ofDigits_digits]

private theorem rev_pow_mul (e : ℕ) {q : ℕ} (hq : 0 < q) :
    rev (2 ^ e * q) = rev q := by
  simp [rev, Nat.digits_base_pow_mul (by decide : 1 < 2) hq,
    List.reverse_append, Nat.ofDigits_append_replicate_zero]

private theorem rev_lt_twice {n : ℕ} (hn : 0 < n) : rev n < 2*n := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 2) (l := (Nat.digits 2 n).reverse)
    (by decide) (fun _ hd => Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd))
  rw [List.length_reverse] at h
  exact h.trans_le (Nat.base_pow_length_digits_le 2 n (by decide) hn.ne')

private theorem rev_even_lt {n : ℕ} (hn : 0 < n) (he : n % 2 = 0) : rev n < n := by
  have hq : 0 < n / 2 := by omega
  have hs : n = 2 ^ 1 * (n / 2) := by omega
  calc rev n = rev (2 ^ 1 * (n / 2)) := congrArg rev hs
    _ = rev (n / 2) := rev_pow_mul 1 hq
    _ < 2 * (n / 2) := rev_lt_twice hq
    _ = n := by omega

private theorem rev_preimage {m n : ℕ} (hm : 0 < m) (hn : n % 2 = 1)
    (h : rev m = rev n) : ∃ e : ℕ, m = 2 ^ e * n := by
  obtain ⟨e, q, hq, he⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hqo : q % 2 = 1 := Nat.odd_iff.mp hq
  have hqp : 0 < q := by omega
  rw [he, rev_pow_mul e hqp] at h
  have hqn := congrArg rev h
  rw [rev_invol hqo, rev_invol hn] at hqn
  exact ⟨e, he.trans (congrArg (fun u => 2 ^ e * u) hqn)⟩

private theorem only_double {b n : ℕ} (hlo : n < b*n) (hhi : b*n < 3*n) :
    b = 2 := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := Nat.mul_le_mul_right n (show b ≤ 1 by omega)
    omega
  · have := Nat.mul_le_mul_right n (show 3 ≤ b by omega)
    omega

/-- A positive solution must be twice an odd palindrome q. Its remaining
reversal equation is exactly rev (3*q) = 5*q. -/
theorem necessary_structure {k : ℕ} (hk : Member k) :
    ∃ q : ℕ, 0 < q ∧ q % 2 = 1 ∧ k = 2*q ∧ rev q = q ∧ rev (3*q) = 5*q := by
  obtain ⟨hkpos, hsum, hdiff⟩ := hk
  have hr := rev_odd hkpos
  have hrpos : 0 < rev k := by omega
  have hrbound := rev_lt_twice hkpos
  have heven : k % 2 = 0 := by
    by_contra! h
    have ho : k % 2 = 1 := by omega
    have hspos : 0 < k + rev k := by omega
    have hlt := rev_even_lt hspos (by omega)
    have heq : rev (k + rev k) = rev k := by unfold gap at hsum; omega
    obtain ⟨e, he⟩ := rev_preimage hspos ho heq
    have hp : 2 ^ e = 2 := only_double (n := k) (by omega) (by omega)
    rw [hp] at he
    have hrk : rev k = k := by omega
    rw [hrk] at hdiff
    simp [gap, rev_zero] at hdiff
    omega
  have hrlt := rev_even_lt hkpos heven
  obtain ⟨e, q, hqo', he⟩ := Nat.exists_eq_two_pow_mul_odd hkpos.ne'
  have hqo := Nat.odd_iff.mp hqo'
  have hqp : 0 < q := by omega
  have hrq : rev k = rev q := by rw [he, rev_pow_mul e hqp]
  have hdval : gap k (rev k) = k - rev k := by unfold gap; omega
  have hdodd : gap k (rev k) % 2 = 1 := by omega
  have hrd : rev (gap k (rev k)) = rev q := by omega
  have hdq := congrArg rev hrd
  rw [rev_invol hdodd, rev_invol hqo] at hdq
  have hqbound := rev_lt_twice hqp
  have hp : 2 ^ e = 2 := only_double (n := q) (by omega) (by omega)
  rw [hp] at he
  have hpal : rev q = q := by omega
  have hsum3 : k + rev k = 3*q := by omega
  rw [hsum3] at hsum
  have h35 : rev (3*q) = 5*q := by
    by_contra h
    have h31 : rev (3*q) = q := by unfold gap at hsum; omega
    have bad := congrArg rev h31
    rw [rev_invol (by omega), hpal] at bad
    omega
  exact ⟨q, hqp, hqo, he, hpal, h35⟩

/-- Conversely, every palindrome with the indicated reversal gives a term. -/
theorem member_iff_structure (k : ℕ) :
    Member k ↔ ∃ q : ℕ, 0 < q ∧ q % 2 = 1 ∧ k = 2*q ∧ rev q = q ∧ rev (3*q) = 5*q := by
  constructor
  · exact necessary_structure
  · rintro ⟨q, hq, _, rfl, hpal, h35⟩
    have hr : rev (2*q) = q := by simpa only [pow_one] using (rev_pow_mul 1 hq).trans hpal
    refine ⟨by omega, ?_, ?_⟩
    · rw [hr, show 2*q+q = 3*q by omega, h35]; unfold gap; omega
    · rw [hr, show gap (2*q) q = q by unfold gap; omega, hpal]; omega

/-- Reversal of a block of exactly four bits, including any zero padding. -/
private def flip4 (r : ℕ) : ℕ := Nat.ofDigits 2 (Nat.digitsAppend 2 4 r).reverse

private theorem take_four {n : ℕ} (h : 4 ≤ (Nat.digits 2 n).length) :
    (Nat.digits 2 n).take 4 = Nat.digitsAppend 2 4 (n % 16) := by
  apply Nat.ofDigits_inj_of_len_eq (b := 2) (by decide)
  · rw [List.length_take_of_le h, Nat.length_digitsAppend (by decide) 4 (by omega)]
  · exact fun _ hd => Nat.digits_lt_base (by decide) (List.mem_of_mem_take hd)
  · exact fun d hd => Nat.lt_of_mem_digitsAppend (by decide) 4 d hd
  · rw [← Nat.self_mod_pow_eq_ofDigits_take 4 n (by decide : 2 ≤ 2)]
    simp [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/-- The low four bits of n determine the high four places of its reversal.
This is an interval statement, so it also handles leading zeros in the reversed word. -/
private theorem top_four_bounds {n : ℕ} (h : 4 ≤ (Nat.digits 2 n).length) :
    let d := 2 ^ ((Nat.digits 2 n).length - 4)
    flip4 (n % 16) * d ≤ rev n ∧ rev n < (flip4 (n % 16) + 1) * d := by
  let L := Nat.digits 2 n
  let tailVal := Nat.ofDigits 2 (L.drop 4).reverse
  have htail : tailVal < 2 ^ (L.length - 4) := by
    have ht := Nat.ofDigits_lt_base_pow_length (b := 2) (l := (L.drop 4).reverse)
      (by decide) (fun _ hd => Nat.digits_lt_base (by decide)
        (List.mem_of_mem_drop (List.mem_reverse.mp hd)))
    simpa [tailVal] using ht
  have hsplit : rev n = tailVal + 2 ^ (L.length - 4) * flip4 (n % 16) := by
    calc rev n = Nat.ofDigits 2 (L.take 4 ++ L.drop 4).reverse := by simp [rev, L]
      _ = _ := by
        rw [List.reverse_append, Nat.ofDigits_append, List.length_reverse, List.length_drop]
        change _ + _ * Nat.ofDigits 2 ((Nat.digits 2 n).take 4).reverse = _
        rw [take_four h]
        rfl
  change flip4 (n % 16) * 2 ^ (L.length - 4) ≤ rev n ∧
    rev n < (flip4 (n % 16) + 1) * 2 ^ (L.length - 4)
  rw [hsplit, Nat.mul_comm (2 ^ _) (flip4 _), Nat.add_mul, Nat.one_mul]
  omega

private theorem four_bit_cases : ∀ r : Fin 16,
    flip4 r.val ≤ 9 ∨ 13 ≤ flip4 r.val ∨
    (flip4 r.val = 10 ∧ flip4 (3*r.val % 16) = 15) ∨
    (flip4 r.val = 12 ∧ flip4 (3*r.val % 16) = 9) ∨ r.val = 13 := by decide

private theorem small_exclusion : ∀ q : Fin 8, 0 < q.val → rev (3*q.val) ≠ 5*q.val := by
  decide

private theorem low_four_of_palindrome {q : ℕ} (hq : 0 < q) (ho : q % 2 = 1)
    (hpal : rev q = q) (h35 : rev (3*q) = 5*q) :
    4 ≤ (Nat.digits 2 q).length ∧ q % 16 = 13 := by
  have h8 : 8 ≤ q := by
    by_contra! h
    exact small_exclusion ⟨q, h⟩ hq h35
  have hlen : 4 ≤ (Nat.digits 2 q).length :=
    (Nat.lt_digits_length_iff (k := 3) (by decide) q).mpr h8
  let e := (Nat.digits 2 q).length - 4
  let d := 2 ^ e
  have hL : (Nat.digits 2 q).length = e + 4 := by dsimp [e]; omega
  have hd : 0 < d := by dsimp [d]; positivity
  have hp4 : 2 ^ (e + 4) = 16*d := by rw [pow_add]; dsimp [d]; ring
  have hp5 : 2 ^ (e + 5) = 32*d := by rw [pow_add]; dsimp [d]; ring
  have hp6 : 2 ^ (e + 6) = 64*d := by rw [pow_add]; dsimp [d]; ring
  have qhi := Nat.lt_base_pow_length_digits (m := q) (by decide : 1 < 2)
  have qlo := Nat.base_pow_length_digits_le 2 q (by decide) hq.ne'
  rw [hL, hp4] at qhi qlo
  have hsame : (Nat.digits 2 (5*q)).length = (Nat.digits 2 (3*q)).length := by
    rw [← h35, digits_rev_odd (by omega), List.length_reverse]
  have lenHi : (Nat.digits 2 (3*q)).length ≤ e + 6 :=
    (Nat.digits_length_le_iff (by decide) _).mpr (by rw [hp6]; omega)
  have lenLo : e + 5 < (Nat.digits 2 (5*q)).length :=
    (Nat.lt_digits_length_iff (by decide) _).mpr (by rw [hp5]; omega)
  have len3 : (Nat.digits 2 (3*q)).length = e + 6 := by omega
  have lo3 : 32*d ≤ 3*q := by
    rw [← hp5]
    exact (Nat.lt_digits_length_iff (by decide) _).mp (by omega)
  have hi5 : 5*q < 64*d := by
    rw [← hp6]
    exact (Nat.digits_length_le_iff (by decide) _).mp (by omega)
  have bq := top_four_bounds (n := q) hlen
  change flip4 (q % 16) * d ≤ rev q ∧ rev q < (flip4 (q % 16) + 1) * d at bq
  rw [hpal] at bq
  have b3 := top_four_bounds (n := 3*q) (by omega)
  dsimp only at b3
  have hscale : 2 ^ (e + 6 - 4) = 4*d := by
    rw [show e+6-4 = e+2 by omega, pow_add]; dsimp [d]; ring
  rw [h35, len3, hscale, show 3*q % 16 = 3*(q % 16) % 16 by omega] at b3
  refine ⟨hlen, ?_⟩
  rcases four_bit_cases ⟨q % 16, by omega⟩ with hlo | hhi | h | h | h
  · change flip4 (q % 16) ≤ 9 at hlo
    have := Nat.mul_le_mul_right d (show flip4 (q % 16) + 1 ≤ 10 by omega)
    omega
  · change 13 ≤ flip4 (q % 16) at hhi
    have := Nat.mul_le_mul_right d hhi
    omega
  · obtain ⟨h1, h2⟩ := h
    change flip4 (q % 16) = 10 at h1
    change flip4 (3*(q % 16) % 16) = 15 at h2
    rw [h1] at bq
    rw [h2] at b3
    omega
  · obtain ⟨h1, h2⟩ := h
    change flip4 (q % 16) = 12 at h1
    change flip4 (3*(q % 16) % 16) = 9 at h2
    rw [h1] at bq
    rw [h2] at b3
    omega
  · exact h

/-- Branicky's full conjecture for every positive member of OEIS A179697. -/
theorem branicky_ends {k : ℕ} (hk : Member k) : HasEnds k := by
  obtain ⟨q, hq, ho, rfl, hpal, h35⟩ := necessary_structure hk
  obtain ⟨hlen, h13⟩ := low_four_of_palindrome hq ho hpal h35
  have hbits : (Nat.digits 2 q).take 4 = [1,0,1,1] := by
    rw [take_four hlen, h13]; decide
  have hsymm : (Nat.digits 2 q).reverse = Nat.digits 2 q := by
    rw [← digits_rev_odd ho, hpal]
  unfold HasEnds
  rw [Nat.digits_base_mul (by decide) hq, List.reverse_cons, hsymm]
  constructor
  · rw [List.take_append_of_le_length hlen]; exact hbits
  · simpa only [List.take_succ_cons] using congrArg (List.cons 0) hbits

/-- If the equations are read over all naturals, zero is the unique exception. -/
theorem unique_exception (k : ℕ) : (Equations k ∧ ¬ HasEnds k) ↔ k = 0 := by
  constructor
  · rintro ⟨heq, hbad⟩
    by_contra h
    exact hbad (branicky_ends ⟨Nat.pos_of_ne_zero h, heq⟩)
  · rintro rfl
    exact ⟨zero_boundary.1, zero_boundary.2.1⟩

/-! ## Hamilton's conjectured family -/

/-- Canonical binary word specified by Hamilton, in reading order. -/
def hamiltonWord (j : ℕ) : List ℕ := [1, 0] ++ List.replicate j 1 ++ [0, 1, 0]

/-- Read a finite binary word most significant digit first. -/
def wordValue (w : List ℕ) : ℕ := Nat.ofDigits 2 w.reverse

private theorem wordValue_append (p s : List ℕ) :
    wordValue (p ++ s) = wordValue s + 2^s.length * wordValue p := by
  simp [wordValue, List.reverse_append, Nat.ofDigits_append]

private theorem ones_value (j : ℕ) : wordValue (List.replicate j 1) + 1 = 2^j := by
  suffices h : ∀ n : ℕ, Nat.ofDigits 2 (List.replicate n 1) + 1 = 2^n by
    simpa [wordValue] using h j
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Nat.ofDigits, pow_succ]
    omega

private theorem block_value (p s : List ℕ) (j : ℕ) :
    wordValue (p ++ List.replicate j 1 ++ s) + 2^s.length =
      wordValue s + 2^s.length * 2^j * (wordValue p + 1) := by
  rw [wordValue_append, wordValue_append, List.length_replicate]
  calc
    _ = wordValue s + 2^s.length *
        ((wordValue (List.replicate j 1) + 1) + 2^j * wordValue p) := by ring
    _ = _ := by rw [ones_value]; ring

private theorem canonical_word (s : List ℕ) (hs : ∀ d ∈ s, d < 2) :
    (Nat.digits 2 (wordValue (1 :: s))).reverse = 1 :: s := by
  have h : Nat.digits 2 (wordValue (1 :: s)) = (1 :: s).reverse := by
    apply Nat.digits_ofDigits 2 (by decide)
    · intro d hd
      rcases List.mem_cons.mp (List.mem_reverse.mp hd) with h | h
      · omega
      · exact hs d h
    · simp
  rw [h, List.reverse_reverse]

private theorem canonical_block (p s : List ℕ) (j : ℕ)
    (hp : ∀ d ∈ p, d < 2) (hs : ∀ d ∈ s, d < 2) :
    (Nat.digits 2 (wordValue ((1 :: p) ++ List.replicate j 1 ++ s))).reverse =
      (1 :: p) ++ List.replicate j 1 ++ s := by
  apply canonical_word
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · exact hp d hd
    · have := List.mem_replicate.mp hd
      omega
  · exact hs d hd

private theorem rev_wordValue {w : List ℕ}
    (hw : (Nat.digits 2 (wordValue w)).reverse = w) :
    rev (wordValue w) = wordValue w.reverse := by
  unfold rev
  rw [hw]
  simp [wordValue]

private def halfWord (j : ℕ) : List ℕ := [1, 0] ++ List.replicate j 1 ++ [0, 1]

private def tripleWord (t : ℕ) : List ℕ :=
  [1, 0, 0, 0] ++ List.replicate t 1 ++ [0, 1, 1, 1]

private def quintupleWord (t : ℕ) : List ℕ :=
  [1, 1, 1, 0] ++ List.replicate t 1 ++ [0, 0, 0, 1]

/-- Actual members, their canonical words, and their closed form for every run length. -/
theorem hamilton_construction (t : ℕ) :
    let k := wordValue (hamiltonWord (t + 2))
    Member k ∧ (Nat.digits 2 k).reverse = hamiltonWord (t + 2) ∧ k + 6 = 96 * 2^t := by
  let q := wordValue (halfWord (t + 2))
  let k := wordValue (hamiltonWord (t + 2))
  have kd : k = 2*q := by
    have hw : hamiltonWord (t+2) = halfWord (t+2) ++ [0] := by
      simp [hamiltonWord, halfWord, List.append_assoc]
    change wordValue (hamiltonWord (t+2)) = _
    rw [hw, wordValue_append]
    change 0 + 2*q = 2*q
    omega
  have vq := block_value [1,0] [0,1] (t+2)
  change q + 4 = 1 + 4 * 2^(t+2) * (2+1) at vq
  rw [pow_add] at vq
  have v3 := block_value [1,0,0,0] [0,1,1,1] t
  change wordValue (tripleWord t) + 16 = 7 + 16 * 2^t * (8+1) at v3
  have v5 := block_value [1,1,1,0] [0,0,0,1] t
  change wordValue (quintupleWord t) + 16 = 1 + 16 * 2^t * (14+1) at v5
  have hp : 0 < 2^t := Nat.two_pow_pos t
  have qp : 0 < q := by omega
  have qpal : rev q = q := by
    have hc := canonical_block [0] [0,1] (t+2) (by simp) (by simp)
    have hr := rev_wordValue hc
    change rev q = wordValue (halfWord (t+2)).reverse at hr
    have hpal : (halfWord (t+2)).reverse = halfWord (t+2) := by
      simp [halfWord, List.reverse_append, List.append_assoc]
    rw [hpal] at hr
    exact hr
  have r3 : rev (3*q) = 5*q := by
    have hc := canonical_block [0,0,0] [0,1,1,1] t (by simp) (by simp)
    have hr := rev_wordValue hc
    have hrw : (tripleWord t).reverse = quintupleWord t := by
      simp [tripleWord, quintupleWord, List.reverse_append, List.append_assoc]
    change rev (wordValue (tripleWord t)) = wordValue (tripleWord t).reverse at hr
    rw [hrw] at hr
    rwa [show wordValue (tripleWord t) = 3*q by omega,
      show wordValue (quintupleWord t) = 5*q by omega] at hr
  have rk : rev k = q := by
    rw [kd]
    simpa only [pow_one] using (rev_pow_mul 1 qp).trans qpal
  change Member k ∧ _ ∧ k + 6 = 96 * 2^t
  refine ⟨⟨by omega, ?_, ?_⟩, canonical_block [0] [0,1,0] (t+2) (by simp) (by simp), by omega⟩
  · rw [rk, show k + q = 3*q by omega, r3]
    unfold gap
    omega
  · rw [rk, show gap k q = q by unfold gap; omega, qpal]
    omega

/-- Hamilton's 2010 OEIS assertion, stated for every k with the specified binary expansion. -/
theorem hamilton_family {k j : ℕ} (hj : 1 < j)
    (hw : (Nat.digits 2 k).reverse = hamiltonWord j) : Member k := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
  have hk : wordValue (hamiltonWord (t + 2)) = k := by
    rw [← hw]
    simp [wordValue, Nat.ofDigits_digits]
  exact hk ▸ (hamilton_construction t).1

/-- The family supplies a sequence member above every prescribed bound. -/
theorem hamilton_unbounded (bound : ℕ) : ∃ k, bound < k ∧ Member k := by
  obtain ⟨hm, _, hval⟩ := hamilton_construction bound
  exact ⟨_, by have := bound.lt_two_pow_self; omega, hm⟩

theorem hamilton_examples :
    (List.range 6).map (fun t => wordValue (hamiltonWord (t + 2))) =
      [90, 186, 378, 762, 1530, 3066] := by decide

#print axioms hamilton_family
#print axioms hamilton_construction
#print axioms hamilton_unbounded
#print axioms branicky_ends
#print axioms unique_exception
#print axioms member_iff_structure

end OEIS.A179697
