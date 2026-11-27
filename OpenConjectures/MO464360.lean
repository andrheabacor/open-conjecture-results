import Mathlib.Data.Nat.PadicValNat
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Tactic

/-!
# A carry-free subsequence (MathOverflow 464360)

The source defines `b n` by starting at `n` and increasing the current value until
it reaches or exceeds `2*n`. Both sequences in the question list their elements
in increasing order. A multiplication is carry-free exactly when no two distinct
pairs of set bits contribute to the same output column.
-/

namespace MathOverflow.Q464360

/-- The smaller of the maximal power of two dividing `x` and the complementary factor. -/
def increment (x : ℕ) : ℕ :=
  min (2 ^ padicValNat 2 x) (x.divMaxPow 2)

theorem increment_eq_source (x : ℕ) :
    increment x = min (2 ^ padicValNat 2 x) (x / 2 ^ padicValNat 2 x) := by
  have h := congrArg (fun y : ℕ => y / 2 ^ padicValNat 2 x)
    (Nat.divMaxPow_mul_pow_padicValNat 2 x)
  simpa only [increment, Nat.mul_div_cancel _ (Nat.two_pow_pos _)] using
    congrArg (min (2 ^ padicValNat 2 x)) h

private theorem increment_pos {x : ℕ} (hx : 0 < x) : 0 < increment x := by
  have hd : 0 < x.divMaxPow 2 := by
    by_contra! hz
    have h := Nat.divMaxPow_mul_pow_padicValNat 2 x
    simp [Nat.eq_zero_of_le_zero hz] at h
    omega
  exact lt_min (Nat.two_pow_pos _) hd

/-- Stop at the first value at least `target`, executing at most `fuel` steps. -/
def run (target : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | fuel + 1, x => if x < target then run target fuel (x + increment x) else x

/-- A positive state advances by at least one per active step, so this budget suffices. -/
theorem run_reaches {target fuel x : ℕ} (hx : 0 < x) (h : target ≤ x + fuel) :
    target ≤ run target fuel x := by
  induction fuel generalizing x with
  | zero => simpa [run] using h
  | succ fuel ih =>
    rw [run]
    split_ifs with hlt
    · have hi := increment_pos hx
      exact ih (by omega) (by omega)
    · omega

def b (n : ℕ) : ℕ := run (2*n) n n

theorem b_reaches (n : ℕ) : 2*n ≤ b n := by
  cases n with
  | zero => decide
  | succ n => exact run_reaches (by omega) (by omega)

private theorem run_eq_start_or_step (target fuel x : ℕ) :
    run target fuel x = x ∨
      ∃ y, y < target ∧ run target fuel x = y + increment y := by
  induction fuel generalizing x with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    rw [run]
    split_ifs with h
    · rcases ih (x + increment x) with hret | hret
      · exact Or.inr ⟨x, h, hret⟩
      · exact Or.inr hret
    · exact Or.inl rfl

/-- Every column of the binary long multiplication receives at most one set-bit pair. -/
def CarryFree (u v : ℕ) : Prop :=
  ∀ i j i' j' : ℕ, u.testBit i = true → v.testBit j = true →
    u.testBit i' = true → v.testBit j' = true →
    i + j = i' + j' → i = i' ∧ j = j'

/-- The membership test for the increasing sequence c in the post. -/
def inC (k : ℕ) : Prop := Odd k ∧ b ((k-1)/2) = k

/-- OEIS A110978, with both factors required to be nontrivial. -/
def inA (k : ℕ) : Prop :=
  Odd k ∧ ¬ Nat.Prime k ∧
    ∃ u v : ℕ, 1 < u ∧ 1 < v ∧ k = u*v ∧ CarryFree u v

private theorem one_bit (i : ℕ) : (1 : ℕ).testBit i = decide (0 = i) := by
  simpa only [pow_zero] using (Nat.testBit_two_pow (n := 0) (m := i))

private theorem bit_below {d t i : ℕ} (hd : d < 2^t) (hbit : d.testBit i = true) :
    i < t := by
  by_contra! hi
  have h := Nat.testBit_lt_two_pow (hd.trans_le (Nat.pow_le_pow_right (by decide) hi))
  simp [h] at hbit

private theorem two_bits {t j : ℕ} (ht : 1 < 2^t)
    (h : (2^t + 1).testBit j = true) : j = 0 ∨ j = t := by
  have blocks := Nat.testBit_two_pow_mul_add 1 ht j
  rw [Nat.mul_one] at blocks
  rw [blocks] at h
  split_ifs at h with hj <;> simp only [one_bit, decide_eq_true_eq] at h <;> omega

/-- The two copies of `d` in the binary product fit in separate blocks of `t` digits. -/
private theorem block_carryFree {d t : ℕ} (hd : d < 2^t) (ht : 1 < 2^t) :
    CarryFree d (2^t + 1) := by
  intro i j i' j' hi hj hi' hj' hcol
  have := bit_below hd hi
  have := bit_below hd hi'
  rcases two_bits ht hj with h | h <;> rcases two_bits ht hj' with h' | h' <;> omega

private theorem odd_final_step {n x : ℕ} (hx : x < 2*n)
    (hstep : 2*n+1 = x + increment x) : inA (2*n+1) := by
  let t := padicValNat 2 x
  let d := x.divMaxPow 2
  have hxprod : d * 2^t = x := Nat.divMaxPow_mul_pow_padicValNat 2 x
  change 2*n+1 = x + min (2^t) d at hstep
  have hmin : 1 < min (2^t) d := by omega
  have ht : 1 < 2^t := hmin.trans_le (min_le_left ..)
  have hd : 1 < d := hmin.trans_le (min_le_right ..)
  have hsmall : d < 2^t := by
    by_contra! hle
    rw [min_eq_left hle] at hstep
    have ht0 : t ≠ 0 := Nat.one_lt_two_pow_iff.mp ht
    have hpEven : 2 ∣ 2^t := dvd_pow_self 2 ht0
    have hxEven : 2 ∣ x := hxprod ▸ dvd_mul_of_dvd_right hpEven d
    omega
  rw [min_eq_right hsmall.le] at hstep
  have hfactor : 2*n+1 = d * (2^t + 1) := by
    simpa only [Nat.mul_add, Nat.mul_one, hxprod] using hstep
  refine ⟨⟨n, rfl⟩, ?_, d, 2^t+1, hd, by omega, hfactor, block_carryFree hsmall ht⟩
  rw [hfactor]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- Every odd integer selected by the posted loop belongs to A110978. -/
theorem term_inclusion (k : ℕ) (hk : inC k) : inA k := by
  obtain ⟨⟨n, rfl⟩, h⟩ := hk
  have hdiv : (2*n+1-1)/2 = n := by omega
  rw [hdiv] at h
  change run (2*n) n n = 2*n+1 at h
  rcases run_eq_start_or_step (2*n) n n with hstart | ⟨x, hx, hlast⟩
  · omega
  · exact odd_final_step hx (h.symm.trans hlast)

/-! The sequence in the question is infinite. The following family supplies explicit
terms and makes the final subsequence statement unconditional for the two actual
increasing enumerations. -/

private theorem run_stopped {target x : ℕ} (hx : target ≤ x) (fuel : ℕ) :
    run target fuel x = x := by
  cases fuel <;> simp [run, Nat.not_lt_of_ge hx]

/-- No positive starting value below three times a power of two can jump past it. -/
private theorem stays_below_three_pow {t x : ℕ} (hpos : 0 < x) (hx : x < 3*2^t) :
    x + increment x ≤ 3*2^t := by
  let e := padicValNat 2 x
  have hxd : 2^e ∣ x := ⟨x.divMaxPow 2, by
    rw [Nat.mul_comm]; exact (Nat.divMaxPow_mul_pow_padicValNat 2 x).symm⟩
  by_cases he : e ≤ t
  · have hd : 2^e ∣ 3*2^t := dvd_mul_of_dvd_right (pow_dvd_pow 2 he) 3
    have hgap := Nat.le_of_dvd (Nat.sub_pos_of_lt hx) (Nat.dvd_sub hd hxd)
    have hi : increment x ≤ 2^e := min_le_left ..
    omega
  · have hd : 2^(t+1) ∣ x := (pow_dvd_pow 2 (show t+1 ≤ e by omega)).trans hxd
    obtain ⟨m, hm⟩ := hd
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      omega
    have hm1 : m = 1 := by
      by_contra! h
      have hm2 : 2 ≤ m := by omega
      have hmul := Nat.mul_le_mul_left (2^(t+1)) hm2
      rw [← hm, pow_succ] at hmul
      omega
    have hxp : x = 2^(t+1) := by simpa [hm1] using hm
    have hsmall : increment x ≤ 1 := calc
      increment x ≤ x.divMaxPow 2 := min_le_right ..
      _ = 1 := hxp ▸ Nat.divMaxPow_base_pow (by decide) (t+1)
    omega

private theorem increment_three_pow {t : ℕ} (ht : 2 ≤ t) :
    increment (3*2^t) = 3 := by
  have hpow : 3 ≤ (2:ℕ)^t := (show 3 ≤ (2:ℕ)^2 by decide).trans
    (Nat.pow_le_pow_right (by decide) ht)
  have h3 : (3:ℕ).divMaxPow 2 = 3 := by cbv
  have hval : multiplicity 2 (3:ℕ) = 0 := by rw [← Nat.padicValNat_def]; cbv
  rw [increment, Nat.mul_comm 3, Nat.padicValNat_def, multiplicity_base_pow_mul (by decide)
    (by decide), Nat.divMaxPow_base_pow_mul (by decide), hval, h3, zero_add, min_eq_right hpow]

private theorem run_to_three_pow {t fuel x : ℕ} (ht : 2 ≤ t) (hx : 0 < x)
    (hbound : x ≤ 3*2^t) (hbudget : 3*2^t+2 ≤ x+fuel) :
    run (3*2^t+2) fuel x = 3*2^t+3 := by
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    rw [run, ite_eq_left (show x < 3*2^t+2 by omega)]
    rcases lt_or_eq_of_le hbound with hlt | rfl
    · have hi := increment_pos hx
      exact ih (by omega) (stays_below_three_pow hx hlt) (by omega)
    · rw [increment_three_pow ht]
      exact run_stopped (by omega) fuel

/-- The terms 15, 27, 51, 99, ... all belong to c. -/
theorem family_inC (m : ℕ) : inC (3*2^(m+2)+3) := by
  let n := 3*2^(m+1)+1
  have htarget : 2*n = 3*2^(m+2)+2 := by
    dsimp [n]
    rw [pow_succ (2:ℕ) (m+1)]
    omega
  have hpos : 0 < n := by dsimp [n]; omega
  have hbound : n ≤ 3*2^(m+2) := by
    have := Nat.two_pow_pos (m+1)
    dsimp [n]
    rw [pow_succ (2:ℕ) (m+1)]
    omega
  refine ⟨⟨n, by omega⟩, ?_⟩
  have hdiv : (3*2^(m+2)+3-1)/2 = n := by omega
  rw [hdiv, b, htarget]
  exact run_to_three_pow (by omega) hpos hbound (by omega)

theorem c_infinite : (Set.ofPred inC).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro m
  refine ⟨_, family_inC m, ?_⟩
  have := Nat.lt_two_pow_self (n := m+2)
  omega

/-- The increasing enumeration of c is a subsequence of the increasing enumeration
of A110978, through a strictly increasing map on indices. -/
theorem mathOverflow464360 :
    ∃ g : ℕ → ℕ, StrictMono g ∧ ∀ i, Nat.nth inC i = Nat.nth inA (g i) := by
  have ha : (Set.ofPred inA).Infinite := c_infinite.mono fun k hk => term_inclusion k hk
  have hmem (i : ℕ) : Nat.nth inC i ∈ Set.range (Nat.nth inA) := by
    rw [Nat.range_nth_of_infinite ha]
    exact term_inclusion _ (Nat.nth_mem_of_infinite c_infinite i)
  choose g hg using hmem
  refine ⟨g, ?_, fun i => (hg i).symm⟩
  intro i j hij
  apply (Nat.nth_lt_nth ha).mp
  rw [hg, hg]
  exact Nat.nth_strictMono c_infinite hij

theorem sanity_zero : b 0 = 0 := by decide
theorem sanity_first : inC 15 := ⟨⟨7, rfl⟩, by cbv⟩
theorem sanity_second : inC 27 := ⟨⟨13, rfl⟩, by cbv⟩
theorem sanity_prime_not_selected : ¬ inC 7 := fun h => (by cbv : b 3 ≠ 7) h.2
theorem sanity_genuine_carry : ¬ CarryFree 3 3 := by
  intro h
  have := h 0 1 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  omega

#print axioms term_inclusion
#print axioms c_infinite
#print axioms mathOverflow464360

end MathOverflow.Q464360
