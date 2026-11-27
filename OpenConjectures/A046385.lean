import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Primality

/-!
# The exhaustiveness conjecture in OEIS A046385

At each index `k`, the entry takes the least positive decimal palindrome having
exactly `k` prime factors, counted with multiplicity, all decimal palindromes.
The 2019 conjecture says that the sequence is finite and has no terms beyond
those shown in the entry's data and comment. Three omitted indices have terms.
-/

namespace OEIS.A046385

set_option maxRecDepth 8192

/-- Mathlib lists digits least significant first. Equality with the reverse
tests the same decimal palindrome condition in either order. -/
def DecimalPalindrome (n : ℕ) : Prop :=
  Nat.digits 10 n = (Nat.digits 10 n).reverse

instance (n : ℕ) : Decidable (DecimalPalindrome n) :=
  inferInstanceAs (Decidable (Nat.digits 10 n = (Nat.digits 10 n).reverse))

/-- The prime factor list is complete and retains repeated factors. -/
def Qualifies (k n : ℕ) : Prop :=
  0 < n ∧ DecimalPalindrome n ∧ n.primeFactorsList.length = k ∧
    ∀ p ∈ n.primeFactorsList, DecimalPalindrome p

instance (k n : ℕ) : Decidable (Qualifies k n) := by
  unfold Qualifies
  infer_instance

/-- `none` means there is no qualifying integer. Otherwise take the minimum. -/
noncomputable def a (k : ℕ) : Option ℕ := by
  classical
  exact if h : ∃ n, Qualifies k n then some (Nat.find h) else none

theorem value_of_least {k n : ℕ} (hn : Qualifies k n)
    (hmin : ∀ i : Fin n, ¬Qualifies k i.val) : a k = some n := by
  classical
  have h : ∃ m, Qualifies k m := ⟨n, hn⟩
  unfold a
  rw [dite_eq_left h, (Nat.find_eq_iff h).2 ⟨hn, fun i hi ↦ hmin ⟨i, hi⟩⟩]

-- Exact values, including minimality, from the offset-zero OEIS data.
theorem first_terms : a 0 = some 1 ∧ a 1 = some 2 ∧ a 2 = some 4 ∧
    a 3 = some 8 ∧ a 4 = some 88 ∧ a 5 = some 252 := by
  repeat' constructor
  all_goals apply value_of_least <;> decide +kernel

/-- A five-term decimal multiplier with gaps of at least ten digit positions. -/
def p : ℕ := 10000000000001000000000100000000010000000000001

theorem p_expansion : p = 10^46 + 10^33 + 10^23 + 10^13 + 1 := by decide

theorem p_prime : p.Prime := by
  unfold p
  primality (cert := .witnesses [
    .lucas { root := 6, primeFactors := [2, 5, 17, 1229, 5030702572783, 9514162267188379] },
    .lucas { root := 2, primeFactors := [2, 307] },
    .lucas { root := 3, primeFactors := [2, 3, 41269, 20316713] },
    .lucas { root := 2, primeFactors := [2, 3, 19, 181] },
    .lucas { root := 5, primeFactors := [2, 13, 195353] },
    .lucas { root := 3, primeFactors := [2, 24419] },
    .lucas { root := 2, primeFactors := [2, 29, 421] },
    .lucas { root := 2, primeFactors := [2, 3, 67, 3454901, 6850289] },
    .lucas { root := 2, primeFactors := [2, 5, 34549] },
    .lucas { root := 2, primeFactors := [2, 3, 2879] },
    .lucas { root := 7, primeFactors := [2, 1439] },
    .lucas { root := 7, primeFactors := [2, 719] },
    .lucas { root := 3, primeFactors := [2, 428143] },
    .lucas { root := 3, primeFactors := [2, 3, 11, 13, 499] }])

theorem p_palindrome : DecimalPalindrome p := by decide

private theorem qualifies_product {k n : ℕ} (s : List ℕ) (hn : 0 < n)
    (hpal : DecimalPalindrome n) (hprod : s.prod * p = n) (hlen : s.length + 1 = k)
    (hs : ∀ q ∈ s, q.Prime) (hdigits : ∀ q ∈ s, DecimalPalindrome q) :
    Qualifies k n := by
  have hprime : ∀ q ∈ s ++ [p], Nat.Prime q := by
    intro q hq
    rcases List.mem_append.mp hq with h | h
    · exact hs q h
    · exact (List.mem_singleton.mp h) ▸ p_prime
  have factors := Nat.primeFactorsList_unique (l := s ++ [p])
    (by simpa using hprod) hprime
  refine ⟨hn, hpal, ?_, ?_⟩
  · simpa using factors.length_eq.symm.trans (by simpa using hlen)
  · intro q hq
    have hq' := factors.mem_iff.mpr hq
    rcases List.mem_append.mp hq' with h | h
    · exact hdigits q h
    · exact (List.mem_singleton.mp h) ▸ p_palindrome

theorem witness14 : Qualifies 14 (2977792 * p) := by
  apply qualifies_product (List.replicate 12 2 ++ [727]) <;> decide

theorem witness17 : Qualifies 17 (40955904 * p) := by
  apply qualifies_product (List.replicate 12 2 ++ [3, 3, 11, 101]) <;> decide

theorem witness21 : Qualifies 21 (677707776 * p) := by
  apply qualifies_product (List.replicate 16 2 ++ [3, 3, 3, 383]) <;> decide

/-- A qualifying witness bounds the true least value at its index. -/
theorem term_le_of_witness {k n : ℕ} (hn : Qualifies k n) :
    ∃ m ≤ n, a k = some m := by
  classical
  have h : ∃ m, Qualifies k m := ⟨n, hn⟩
  exact ⟨Nat.find h, Nat.find_min' h hn, by simp [a, h]⟩

theorem three_new_indices :
    (∃ m ≤ 2977792 * p, a 14 = some m) ∧
    (∃ m ≤ 40955904 * p, a 17 = some m) ∧
    (∃ m ≤ 677707776 * p, a 21 = some m) :=
  ⟨term_le_of_witness witness14, term_le_of_witness witness17,
    term_le_of_witness witness21⟩

/-- The full table shown in OEIS at the time of the conjecture. The comments
give the last three displayed values. All other slots are left empty. -/
def displayed : ℕ → Option ℕ
  | 0 => some 1
  | 1 => some 2
  | 2 => some 4
  | 3 => some 8
  | 4 => some 88
  | 5 => some 252
  | 6 => some 2772
  | 7 => some 82728
  | 8 => some 2112
  | 9 => some 4224
  | 10 => some 8448
  | 11 => some 236989632
  | 12 => some 48384
  | 13 => some 2977792
  | 15 => some 405504
  | 16 => some 40955904
  | 20 => some 677707776
  | _ => none

/-- The two clauses of Hugo Pfoertner's conjecture dated August 13, 2019. -/
def PfoertnerConjecture : Prop :=
  {k : ℕ | a k ≠ none}.Finite ∧ ∀ k, a k = displayed k

theorem pfoertnerConjecture_false : ¬PfoertnerConjecture := by
  rintro ⟨_, hall⟩
  obtain ⟨m, _, hm⟩ := term_le_of_witness witness21
  rw [hall 21] at hm
  change none = some m at hm
  cases hm

#print axioms first_terms
#print axioms p_prime
#print axioms three_new_indices
#print axioms pfoertnerConjecture_false

end OEIS.A046385
