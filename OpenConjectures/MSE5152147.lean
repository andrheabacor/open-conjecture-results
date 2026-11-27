import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq

/-!
# A square sum of remainders over divisors

Math Stack Exchange question 5152147, posted by pie on 18 October 2026.
For each natural number x > 13 there is a positive y < x such that the sum
of x mod d over all positive divisors d of y is a square k² with k ≥ 2.
-/

namespace MathStackExchange.Q5152147

/-- The source's S(x,y), with each positive divisor of y counted once. -/
def remainderSum (x y : ℕ) : ℕ := ∑ d ∈ y.divisors, x % d

/-- The first displayed witness in the source has an arithmetic error. -/
theorem first_example_value : remainderSum 7 6 = 3 := by decide

/-- The same input has this valid witness. -/
theorem corrected_first_example : remainderSum 7 4 = 2 ^ 2 := by decide

theorem second_example : remainderSum 11 4 = 2 ^ 2 := by decide

private theorem sum_eq_of_dvd_sub {x y : ℕ} (hx : 4 ≤ x) (hy : y ∣ x - 4) :
    remainderSum x y = remainderSum 4 y := by
  apply Finset.sum_congr rfl
  intro d hd
  exact ((Nat.modEq_iff_dvd' hx).2 ((Nat.dvd_of_mem_divisors hd).trans hy)).symm

private theorem prime_sum {p : ℕ} (hp : p.Prime) (h : 4 < p) :
    remainderSum 4 p = 4 := by
  have hne : 1 ≠ p := by omega
  simp [remainderSum, hp.divisors, hne, Nat.mod_eq_of_lt h]

/-- If m has neither of the two prime cubes nor a prime above 3 as a
divisor, then its factorization is bounded by that of 2² · 3² = 36. -/
private theorem divides_36 {m : ℕ} (hm : m ≠ 0) (h8 : ¬8 ∣ m) (h27 : ¬27 ∣ m)
    (small : ∀ p : ℕ, p.Prime → p ∣ m → p ≤ 4) : m ∣ 36 := by
  apply (Nat.factorization_le_iff_dvd hm (by decide)).1
  intro p
  by_cases hp : p.Prime
  · by_cases hd : p ∣ m
    · have hle := small p hp hd
      have hge := hp.two_le
      have hn4 : p ≠ 4 := fun e => (by decide : ¬ Nat.Prime 4) (e ▸ hp)
      have h23 : p = 2 ∨ p = 3 := by omega
      rcases h23 with rfl | rfl
      · have h : ¬3 ≤ m.factorization 2 :=
          fun he => h8 ((Nat.prime_two.pow_dvd_iff_le_factorization hm).2 he)
        have h36 : 2 ≤ (36 : ℕ).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by decide)).1 (by decide)
        change m.factorization 2 ≤ (36 : ℕ).factorization 2
        omega
      · have h : ¬3 ≤ m.factorization 3 :=
          fun he => h27 ((Nat.prime_three.pow_dvd_iff_le_factorization hm).2 he)
        have h36 : 2 ≤ (36 : ℕ).factorization 3 :=
          (Nat.prime_three.pow_dvd_iff_le_factorization (by decide)).1 (by decide)
        change m.factorization 3 ≤ (36 : ℕ).factorization 3
        omega
    · simp [Nat.factorization_eq_zero_of_not_dvd hd]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The witness can always be chosen so that its sum is exactly 4 or 9. -/
theorem four_or_nine (x : ℕ) (hx : 13 < x) :
    ∃ y : ℕ, 1 ≤ y ∧ y < x ∧ (remainderSum x y = 4 ∨ remainderSum x y = 9) := by
  have hx4 : 4 ≤ x := by omega
  have hm : 0 < x - 4 := by omega
  by_cases h8 : 8 ∣ x - 4
  · have hle := Nat.le_of_dvd hm h8
    refine ⟨8, by decide, by omega, Or.inl ?_⟩
    exact (sum_eq_of_dvd_sub hx4 h8).trans (by decide)
  by_cases h27 : 27 ∣ x - 4
  · have hle := Nat.le_of_dvd hm h27
    refine ⟨27, by decide, by omega, Or.inr ?_⟩
    exact (sum_eq_of_dvd_sub hx4 h27).trans (by decide)
  by_cases large : ∃ p : ℕ, p.Prime ∧ p ∣ x - 4 ∧ 4 < p
  · obtain ⟨p, hp, hd, hgt⟩ := large
    have hle := Nat.le_of_dvd hm hd
    exact ⟨p, by omega, by omega,
      Or.inl ((sum_eq_of_dvd_sub hx4 hd).trans (prime_sum hp hgt))⟩
  have small (p : ℕ) (hp : p.Prime) (hd : p ∣ x - 4) : p ≤ 4 :=
    le_of_not_gt fun hgt => large ⟨p, hp, hd, hgt⟩
  have hd := divides_36 hm.ne' h8 h27 small
  have hmem : x - 4 ∈ (36 : ℕ).divisors := Nat.mem_divisors.2 ⟨hd, by decide⟩
  have hlist : (36 : ℕ).divisors = {1, 2, 3, 4, 6, 9, 12, 18, 36} := by decide
  rw [hlist] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hcases : x = 16 ∨ x = 22 ∨ x = 40 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact ⟨12, by decide, by decide, Or.inr (by decide)⟩
  · exact ⟨13, by decide, by decide, Or.inr (by decide)⟩
  · exact ⟨12, by decide, by decide, Or.inr (by decide)⟩

/-- The full, unbounded conjecture, using exactly its original quantifiers. -/
theorem mse_5152147 (x : ℕ) (hx : 13 < x) :
    ∃ y : ℕ, 1 ≤ y ∧ y < x ∧ ∃ k : ℕ, 2 ≤ k ∧ remainderSum x y = k ^ 2 := by
  obtain ⟨y, hy, hyx, h⟩ := four_or_nine x hx
  refine ⟨y, hy, hyx, ?_⟩
  rcases h with h | h
  · exact ⟨2, by decide, h⟩
  · exact ⟨3, by decide, h⟩

/-- The exceptional set reported in the question is exact on its domain x ≥ 2. -/
theorem exact_exceptions (x : ℕ) (hx : 2 ≤ x) :
    (¬ ∃ y : ℕ, 1 ≤ y ∧ y < x ∧ ∃ k : ℕ, 2 ≤ k ∧ remainderSum x y = k ^ 2) ↔
      x ∈ ({2, 3, 4, 5, 6, 13} : Finset ℕ) := by
  constructor
  · intro noWitness
    by_contra outside
    have hx13 : x ≤ 13 := le_of_not_gt (fun h => noWitness (mse_5152147 x h))
    simp only [Finset.mem_insert, Finset.mem_singleton] at outside
    have tab : ∀ a : Fin 14, 7 ≤ a.val → a.val ≤ 12 →
        ∃ b : Fin 14, 1 ≤ b.val ∧ b.val < a.val ∧ remainderSum a b = 4 := by decide
    obtain ⟨b, hb, hbx, h⟩ := tab ⟨x, by omega⟩ (by change 7 ≤ x; omega)
      (by change x ≤ 12; omega)
    exact noWitness ⟨b.val, hb, hbx, 2, by decide, h⟩
  · rintro hex ⟨y, _, hyx, k, hk, hs⟩
    have hx14 : x < 14 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hex
      omega
    have tab : ∀ a b : Fin 14, a.val ∈ ({2, 3, 4, 5, 6, 13} : Finset ℕ) →
        b.val < a.val → remainderSum a b < 9 ∧ remainderSum a b ≠ 4 := by decide
    obtain ⟨hlt, hne⟩ := tab ⟨x, hx14⟩ ⟨y, by omega⟩ hex hyx
    change remainderSum x y < 9 at hlt
    change remainderSum x y ≠ 4 at hne
    by_cases hk2 : k = 2
    · subst k
      exact hne hs
    · have h9 : 3 ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega

#print axioms mse_5152147
#print axioms four_or_nine
#print axioms exact_exceptions

end MathStackExchange.Q5152147
