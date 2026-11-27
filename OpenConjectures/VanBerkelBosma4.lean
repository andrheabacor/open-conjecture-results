import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# A counterexample to van Berkel and Bosma, Conjecture 4
The number-theory preprint arXiv:2609.16843v2 defines strict greedy
three-sumfree sequences. The finite computations below reduce in Lean's kernel.
All sequence indices in this file start at zero.
-/

namespace VanBerkelBosma4

/-- Three distinct values from the available entries, put in increasing order. -/
def IsTripleSum (xs : List ℕ) (n : ℕ) : Prop :=
  ∃ a ∈ xs, ∃ b ∈ xs, ∃ c ∈ xs, a < b ∧ b < c ∧ a + b + c = n

/-- Test the first two summands and recover the third by subtraction. -/
def forbidden (xs : List ℕ) (n : ℕ) : Bool :=
  xs.any fun a => xs.any fun b =>
    decide (a < b ∧ a + b + b < n) && xs.contains (n - a - b)

theorem forbidden_iff (xs : List ℕ) (n : ℕ) :
    forbidden xs n = true ↔ IsTripleSum xs n := by
  simp only [forbidden, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.contains_iff_mem, IsTripleSum]
  constructor
  · rintro ⟨a, ha, b, hb, ⟨hab, hlt⟩, hc⟩
    exact ⟨a, ha, b, hb, n-a-b, hc, hab, by omega, by omega⟩
  · rintro ⟨a, ha, b, hb, c, hc, hab, hbc, rfl⟩
    exact ⟨a, ha, b, hb, ⟨hab, by omega⟩, by rwa [show a+b+c-a-b = c by omega]⟩

private def top (xs : List ℕ) := xs.toFinset.sup id

private theorem le_top {xs : List ℕ} {a : ℕ} (ha : a ∈ xs) : a ≤ top xs :=
  Finset.le_sup (f := id) (List.mem_toFinset.mpr ha)

private def choices (xs : List ℕ) : Finset ℕ :=
  (Finset.Icc (top xs + 1) (3 * top xs + 1)).filter (fun n => forbidden xs n = false)

private theorem endpoint_mem (xs : List ℕ) : 3 * top xs + 1 ∈ choices xs := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hsum
  obtain ⟨a, ha, b, hb, c, hc, _, _, h⟩ := (forbidden_iff xs _).mp hsum
  have := le_top ha
  have := le_top hb
  have := le_top hc
  omega

/-- The next entry of the strict greedy sequence. A candidate always exists. -/
def nextValue (xs : List ℕ) : ℕ := (choices xs).min' ⟨_, endpoint_mem xs⟩

/-- The finite search gives exactly the least eligible integer in the unbounded definition. -/
theorem nextValue_isLeast (xs : List ℕ) :
    IsLeast {n : ℕ | (∀ a ∈ xs, a < n) ∧ ¬ IsTripleSum xs n ∧ 0 < n} (nextValue xs) := by
  have hx := Finset.mem_filter.mp ((choices xs).min'_mem ⟨_, endpoint_mem xs⟩)
  have hr := Finset.mem_Icc.mp hx.1
  change top xs + 1 ≤ nextValue xs ∧ nextValue xs ≤ 3 * top xs + 1 at hr
  have hnot : ¬ IsTripleSum xs (nextValue xs) := by
    rw [← forbidden_iff]
    exact Bool.eq_false_iff.mp hx.2
  refine ⟨⟨fun a ha => lt_of_le_of_lt (le_top ha) (by omega), hnot, by omega⟩, ?_⟩
  rintro n ⟨ha, hn, hpos⟩
  by_cases hh : n ≤ 3 * top xs + 1
  · apply Finset.min'_le
    apply Finset.mem_filter.mpr
    have ht : top xs < n := by
      have ht' : top xs ≤ n - 1 := Finset.sup_le (fun a h => by
        have h' := ha a (List.mem_toFinset.mp h)
        change a ≤ n - 1
        omega)
      omega
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hh⟩, Bool.eq_false_iff.mpr ((forbidden_iff xs n).not.mpr hn)⟩
  · omega

/-- Most recent entry first, after k choices beyond the three seeds. -/
def history (f g h : ℕ) : ℕ → List ℕ
  | 0 => [h,g,f]
  | k+1 => let xs := history f g h k; nextValue xs :: xs

/-- Zero-indexed sequence with the three specified initial entries. -/
def seq (f g h : ℕ) : ℕ → ℕ
  | 0 => f
  | 1 => g
  | 2 => h
  | k+3 => nextValue (history f g h k)

def gap (s : ℕ → ℕ) (i : ℕ) := s (i+1) - s i

def HasGapPeriod (s : ℕ → ℕ) (k p : ℕ) : Prop :=
  0 < p ∧ ∀ i ≥ k, gap s (i+p) = gap s i

def UltimatelyPeriodic (s : ℕ → ℕ) : Prop := ∃ k p, HasGapPeriod s k p

/-- Preperiod and period are least lengths. The period in values is the translation
of each entry in the repeating block, as explained in the authors' introduction. -/
def ExactPeriod (s : ℕ → ℕ) (k p modulus : ℕ) : Prop :=
  HasGapPeriod s k p ∧
  IsLeast {j | ∃ r, HasGapPeriod s j r} k ∧
  IsLeast {r | ∃ j, HasGapPeriod s j r} p ∧
  ∀ i ≥ k, s (i+p) = s i + modulus

/-- Conjecture 4 in full, including the exceptional parameters and the translation. -/
def Conjecture4 : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    let s := seq 1 (d-1) (2*d-1)
    UltimatelyPeriodic s ∧ (d ≠ 3 → d ≠ 5 → ExactPeriod s (d+3) d (8*d-1))

/-- A finite transcript can certify a proposed move by checking only the skipped integers. -/
private def validNext (xs : List ℕ) (n : ℕ) : Bool :=
  decide (top xs < n) && !forbidden xs n &&
    (List.range n).all (fun j => decide (j ≤ top xs) || forbidden xs j)

private theorem next_of_valid {xs : List ℕ} {n : ℕ} (hn : validNext xs n = true) :
    nextValue xs = n := by
  simp only [validNext, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true, Bool.or_eq_true, List.mem_range] at hn
  obtain ⟨⟨ht, hnfree⟩, hskips⟩ := hn
  have hl := nextValue_isLeast xs
  have hfree : ¬ IsTripleSum xs n := (forbidden_iff ..).not.mp (Bool.eq_false_iff.mp hnfree)
  have hle := hl.2 (show n ∈ {v : ℕ | (∀ a ∈ xs, a < v) ∧ ¬ IsTripleSum xs v ∧ 0 < v} from
    ⟨fun a ha => (le_top ha).trans_lt ht, hfree, by omega⟩)
  apply le_antisymm hle
  by_contra! hbad
  rcases hskips _ hbad with h | h
  · have htop : top xs < nextValue xs := by
      exact (Finset.mem_Icc.mp ((Finset.mem_filter.mp
        ((choices xs).min'_mem ⟨_, endpoint_mem xs⟩)).1)).1
    omega
  · exact hl.1.2.1 ((forbidden_iff ..).mp h)

private def validTranscript (xs : List ℕ) : List ℕ → Bool
  | [] => true
  | y :: ys => validNext xs y && validTranscript (y :: xs) ys

private theorem transcript_history {f g h k : ℕ} {xs : List ℕ}
    (xs_eq : history f g h k = xs) (ys : List ℕ) (cert : validTranscript xs ys = true)
    (i : ℕ) (hi : i ≤ ys.length) :
    history f g h (k+i) = (ys.take i).reverse ++ xs := by
  induction ys generalizing k xs i with
  | nil =>
    have : i = 0 := by simpa using hi
    simpa [this] using xs_eq
  | cons y ys ih =>
    cases i with
    | zero => simpa using xs_eq
    | succ i =>
      change (validNext xs y && validTranscript (y::xs) ys) = true at cert
      simp only [Bool.and_eq_true] at cert
      obtain ⟨hy, htail⟩ := cert
      have hnext : history f g h (k+1) = y::xs := by
        simp only [history, xs_eq, next_of_valid hy]
      have hh := ih hnext htail i (by simpa using hi)
      rw [show k + i.succ = k+1+i by omega]
      simpa only [List.take_succ_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hh

private theorem certifiedTerm {f g h : ℕ} {ys : List ℕ}
    (cert : validTranscript [h,g,f] ys = true) (i : ℕ) (hi : i ≤ ys.length) :
    seq f g h (i+2) = ((ys.take i).reverse ++ [h,g,f]).headD 0 := by
  have hw := transcript_history (k := 0) (f := f) (g := g) (h := h) rfl ys cert i hi
  simp only [Nat.zero_add] at hw
  cases i with
  | zero => rfl
  | succ i => exact congrArg (fun l : List ℕ => l.headD 0) hw

private def witnessTail : List ℕ := [8,9,10,15,29,35,36,56,62,63]

private theorem witness_valid : validTranscript [7,3,1] witnessTail = true := by decide +kernel

/-- The literal greedy recurrence at the counterexample seeds, in source order. -/
theorem witness_prefix :
    history 1 3 7 10 = [63,62,56,36,35,29,15,10,9,8,7,3,1] := by
  exact transcript_history (k := 0) rfl witnessTail witness_valid 10 (by decide)

private theorem gap_of_terms {s : ℕ → ℕ} {i a b : ℕ}
    (hi : s i = a) (hn : s (i+1) = b) : gap s i = b-a :=
  congrArg₂ Nat.sub hn hi

/-- Zero-indexed gaps 7 and 11, four gaps apart. -/
theorem witness_gaps : gap (seq 1 3 7) 7 = 6 ∧ gap (seq 1 3 7) 11 = 1 := by
  have hs (i : ℕ) (hi : i ≤ 10) := certifiedTerm witness_valid i hi
  have h7 : seq 1 3 7 7 = 29 := hs 5 (by decide)
  have h8 : seq 1 3 7 8 = 35 := hs 6 (by decide)
  have h11 : seq 1 3 7 11 = 62 := hs 9 (by decide)
  have h12 : seq 1 3 7 12 = 63 := hs 10 (by decide)
  exact ⟨gap_of_terms (i := 7) h7 h8, gap_of_terms (i := 11) h11 h12⟩

/-- The entire, universally quantified Conjecture 4 is false. -/
theorem conjecture4_false : ¬ Conjecture4 := by
  intro H
  have hp := ((H 4 (by decide)).2 (by decide) (by decide)).1.2 7 (by decide)
  change gap (seq 1 3 7) 11 = gap (seq 1 3 7) 7 at hp
  rw [witness_gaps.1, witness_gaps.2] at hp
  contradiction

/-- A second failure, this time reading the modulus clause directly. -/
theorem second_witness : seq 1 5 11 9 = 55 ∧ seq 1 5 11 15 = 100 := by
  let ys := [12,13,14,15,16,23,55,56,57,58,59,60,100]
  have hc : validTranscript [11,5,1] ys = true := by decide +kernel
  exact ⟨certifiedTerm hc 7 (by decide), certifiedTerm hc 13 (by decide)⟩

theorem conjecture4_false_by_modulus : ¬ Conjecture4 := by
  intro H
  have hmod := ((H 6 (by decide)).2 (by decide) (by decide)).2.2.2 9 (by decide)
  change seq 1 5 11 15 = seq 1 5 11 9 + 47 at hmod
  rw [second_witness.1, second_witness.2] at hmod
  contradiction

/-- A finite check of Table 1. It reads two complete gap blocks starting at k,
tests all shorter cyclic shifts, checks the previous gap, and checks the translation. -/
def checkTableWindow (xs : List ℕ) (k p modulus : ℕ) : Bool :=
  let delta := fun i : ℕ => xs[i+1]! - xs[i]!
  decide (0 < k ∧ 0 < p ∧ k+2*p < xs.length) &&
    (List.range p).all (fun i => delta (k+i) == delta (k+i+p)) &&
    (List.range' 1 (p-1)).all (fun r =>
      (List.range p).any (fun i => delta (k+i) != delta (k+i+r))) &&
    (delta (k-1) != delta (k-1+p)) &&
    (xs[k+p]! == xs[k]! + modulus)

private theorem checked_window (f g h k p m : ℕ) (ys : List ℕ)
    (cert : validTranscript [h,g,f] ys = true)
    (w : checkTableWindow ((ys.reverse ++ [h,g,f]).reverse) k p m = true) :
    checkTableWindow ((history f g h ys.length).reverse) k p m = true := by
  have hh : history f g h ys.length = ys.reverse ++ [h,g,f] := by
    simpa using transcript_history (k := 0) (f := f) (g := g) (h := h) (xs := [h,g,f]) rfl
      ys cert ys.length le_rfl
  exact (congrArg (fun xs : List ℕ => checkTableWindow xs.reverse k p m) hh).trans w

/-- Reproduce the first three numerical rows on p. 21, using genuine greedy prefixes. -/
theorem table1_sanity :
    checkTableWindow ((history 1 2 6 16).reverse) 6 6 28 = true ∧
    checkTableWindow ((history 1 2 7 22).reverse) 8 8 44 = true ∧
    checkTableWindow ((history 1 3 8 18).reverse) 8 6 38 = true := by
  refine ⟨checked_window 1 2 6 6 6 28
    [7,8,12,13,18,24,29,30,35,41,46,52,57,58,63,69] ?_ ?_,
    checked_window 1 2 7 8 8 44
    [8,9,13,14,15,20,27,33,39,45,46,52,58,64,71,77,83,89,90,96,102,108] ?_ ?_,
    checked_window 1 3 8 8 6 38
    [9,10,11,16,17,32,39,40,47,55,62,70,77,78,85,93,100,108] ?_ ?_⟩ <;>
    decide +kernel

#print axioms conjecture4_false
#print axioms conjecture4_false_by_modulus
#print axioms nextValue_isLeast
#print axioms witness_prefix
#print axioms witness_gaps
#print axioms table1_sanity

end VanBerkelBosma4
