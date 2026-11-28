import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An explicit disk for the connected domination roots

Shao and Zhao, arXiv:2609.06569v5, §5.2, Open Problem 4, root-bound question.
If a connected simple graph has order n and minimum degree δ, put
k = max(1, 2δ+2−n). Every complex root z of its connected domination
polynomial satisfies k |z+1| ≤ 4n.
-/

namespace ShaoZhao.ConnectedDominationBound

open Finset SimpleGraph Polynomial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the family from Definitions 1.1–1.3 of the paper. -/
def ConnectedDominating (G : SimpleGraph V) (s : Finset V) : Prop :=
  (∀ v, v ∉ s → ∃ u ∈ s, G.Adj v u) ∧ (G.induce (s : Set V)).Connected

instance (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Decidable (ConnectedDominating G s) := by
  unfold ConnectedDominating
  infer_instance

def family (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  univ.filter (ConnectedDominating G)

def coefficient (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) : ℕ :=
  ((family G).filter fun s => s.card = j).card

noncomputable def connectedDominationPolynomial (G : SimpleGraph V) [DecidableRel G.Adj] :
    Polynomial ℂ := ∑ s ∈ family G, X ^ s.card

theorem coeff_eq (G : SimpleGraph V) [DecidableRel G.Adj] (j : ℕ) :
    (connectedDominationPolynomial G).coeff j = (coefficient G j : ℂ) := by
  simp only [connectedDominationPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow,
    @eq_comm ℕ j, Finset.sum_boole, coefficient]

def threshold (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  max 1 (2 * G.minDegree + 2 - Fintype.card V)

private def closedN (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (G.neighborFinset v)

private theorem card_closedN (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedN G v).card = G.degree v + 1 := by
  simp [closedN, G.notMem_neighborFinset_self]

private theorem closedN_mem (G : SimpleGraph V) [DecidableRel G.Adj] {u w : V} :
    w ∈ closedN G u ↔ w = u ∨ G.Adj u w := by
  simp [closedN]

omit [DecidableEq V] in
private theorem univ_good (G : SimpleGraph V) (hG : G.Connected) :
    ConnectedDominating G univ := by
  refine ⟨by simp, ?_⟩
  rw [Finset.coe_univ]
  exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hG

/-- Every deletion of fewer than k vertices leaves a connected dominating set. -/
theorem good_of_few_deleted (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (s : Finset V) (hs : Fintype.card V - s.card < threshold G) : ConnectedDominating G s := by
  by_cases hfull : s = univ
  · simpa [hfull] using univ_good G hG
  have hcard : s.card < Fintype.card V := (Finset.card_lt_iff_ne_univ s).mpr hfull
  have hlarge : sᶜ.card + Fintype.card V < 2 * G.minDegree + 2 := by
    rw [Finset.card_compl]
    unfold threshold at hs
    omega
  have shared (u v : V) : ∃ w ∈ s, w ∈ closedN G u ∧ w ∈ closedN G v := by
    by_contra! h
    have sub : closedN G u ∩ closedN G v ⊆ sᶜ := by
      intro w hw
      exact Finset.mem_compl.mpr fun hws =>
        h w hws (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
    have hi := Finset.card_le_card sub
    have hu := Finset.card_le_univ (closedN G u ∪ closedN G v)
    have hsum := Finset.card_union_add_card_inter (closedN G u) (closedN G v)
    rw [card_closedN, card_closedN] at hsum
    have hdu := G.minDegree_le_degree u
    have hdv := G.minDegree_le_degree v
    omega
  constructor
  · intro v hv
    obtain ⟨w, hw, hwv, _⟩ := shared v v
    refine ⟨w, hw, (closedN_mem G).mp hwv |>.resolve_left ?_⟩
    exact fun he => hv (he ▸ hw)
  · have step (u w : (s : Set V)) (h : w.val ∈ closedN G u.val) :
        (G.induce (s : Set V)).Reachable u w := by
      rcases (closedN_mem G).mp h with he | ha
      · obtain rfl : w = u := Subtype.ext he
        exact SimpleGraph.Reachable.refl _
      · exact (show (G.induce (s : Set V)).Adj u w from ha).reachable
    refine (SimpleGraph.connected_iff _).mpr ⟨fun u v => ?_, ?_⟩
    · obtain ⟨w, hw, hwu, hwv⟩ := shared u v
      exact (step u ⟨w, hw⟩ hwu).trans (step v ⟨w, hw⟩ hwv).symm
    · obtain ⟨v⟩ := hG.nonempty
      obtain ⟨w, hw, _, _⟩ := shared v v
      exact ⟨⟨w, hw⟩⟩

/-- The binomial comparison at a complex zero. Every excluded set gets weight
at least t^k when each deleted vertex contributes a factor t ≥ 1. -/
theorem root_power_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {z : ℂ} (hz : (connectedDominationPolynomial G).IsRoot z) (t : ℝ) (ht : 1 ≤ t) :
    t ^ threshold G * ‖z + 1‖ ^ Fintype.card V ≤
      (‖z + 1‖ + 1 + t) ^ Fintype.card V := by
  have ht₀ : 0 ≤ t := le_trans zero_le_one ht
  let bad := (univ : Finset (Finset V)).filter fun s => ¬ ConnectedDominating G s
  have zero : ∑ s ∈ family G, z ^ s.card = 0 := by
    simpa only [Polynomial.IsRoot, connectedDominationPolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_X_pow] using hz
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Finset V))
    (ConnectedDominating G) (fun s => z ^ s.card)
  change (∑ s ∈ family G, z ^ s.card) + (∑ s ∈ bad, z ^ s.card) = _ at hsplit
  rw [zero, zero_add] at hsplit
  have hall : (∑ s : Finset V, z ^ s.card) = (z + 1) ^ Fintype.card V := by
    simpa using Fintype.sum_pow_mul_eq_add_pow V z (1 : ℂ)
  have hn : ‖z + 1‖ ^ Fintype.card V ≤ ∑ s ∈ bad, ‖z‖ ^ s.card := by
    calc
      ‖z + 1‖ ^ Fintype.card V = ‖∑ s ∈ bad, z ^ s.card‖ := by
        rw [hsplit, hall, norm_pow]
      _ ≤ _ := by simpa only [norm_pow] using norm_sum_le bad (fun s => z ^ s.card)
  have hnorm : ‖z‖ ≤ ‖z + 1‖ + 1 := by
    simpa using norm_sub_le (z + 1) (1 : ℂ)
  calc
    _ ≤ t ^ threshold G * ∑ s ∈ bad, ‖z‖ ^ s.card :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ∑ s ∈ bad, t ^ threshold G * ‖z‖ ^ s.card := Finset.mul_sum ..
    _ ≤ ∑ s ∈ bad, (‖z + 1‖ + 1) ^ s.card * t ^ (Fintype.card V - s.card) := by
      refine Finset.sum_le_sum fun s hs => ?_
      have hbad := (Finset.mem_filter.mp hs).2
      have hk : threshold G ≤ Fintype.card V - s.card := by
        by_contra! h
        exact hbad (good_of_few_deleted G hG s h)
      rw [mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _)
        (pow_right_mono₀ ht hk) (by positivity) (by positivity)
    _ ≤ ∑ s : Finset V, (‖z + 1‖ + 1) ^ s.card * t ^ (Fintype.card V - s.card) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ = _ := Fintype.sum_pow_mul_eq_add_pow V _ _

/-- Taking an n-th root gives a family of explicit radii for the same disk centre. -/
theorem radius_at (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {z : ℂ} (hz : (connectedDominationPolynomial G).IsRoot z) (t : ℝ) (ht : 1 < t) :
    ‖z + 1‖ ≤ (1 + t) / (t ^ ((threshold G : ℝ) / Fintype.card V) - 1) := by
  let n := Fintype.card V
  let k := threshold G
  let R := ‖z + 1‖
  have hn : 0 < n := Fintype.card_pos_iff.mpr hG.nonempty
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hden := Real.one_lt_rpow ht (div_pos hkr hnr)
  have hp : (t ^ ((k : ℝ) / n)) ^ n = t ^ k := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ t), div_mul_cancel₀ _ hnr.ne',
      Real.rpow_natCast]
  have hs : (t ^ ((k : ℝ) / n) * R) ^ n ≤ (R + 1 + t) ^ n := by
    rw [mul_pow, hp]
    exact root_power_bound G hG hz t ht.le
  have hRt : t ^ ((k : ℝ) / n) * R ≤ R + 1 + t :=
    le_of_pow_le_pow_left₀ hn.ne' (by dsimp [R]; positivity) hs
  apply (le_div_iff₀ (sub_pos.mpr hden)).mpr
  change R * (t ^ ((k : ℝ) / n) - 1) ≤ 1 + t
  linarith

/-- The root-bound clause of Open Problem 4, uniformly for all finite connected graphs. -/
theorem shao_zhao_root_bound (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {z : ℂ} (hz : (connectedDominationPolynomial G).IsRoot z) :
    (threshold G : ℝ) * ‖z + 1‖ ≤ 4 * Fintype.card V := by
  let R := ‖z + 1‖
  let k := threshold G
  let n := Fintype.card V
  have hpower : (3 : ℝ) ^ k * R ^ n ≤ (R + 4) ^ n := by
    simpa only [add_assoc, show (1 : ℝ) + 3 = 4 by norm_num] using
      root_power_bound G hG hz 3 (by norm_num)
  change (k : ℝ) * R ≤ 4 * n
  by_contra! h
  have hR : 0 < R := by
    by_contra! hh
    have heq : R = 0 := le_antisymm hh (norm_nonneg _)
    simp [heq] at h
    exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ 4 * n)) h
  have hratio : (3 : ℝ)^k ≤ (1 + 4/R)^n := by
    rw [add_div' (4 : ℝ) 1 R hR.ne', one_mul, div_pow]
    exact (le_div_iff₀ (pow_pos hR _)).mpr hpower
  have hy : (1 + 4/R)^n ≤ Real.exp ((n : ℝ) * (4/R)) := by
    rw [Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (4/R)]) _
  have harg : (n : ℝ) * (4 / R) < k := by
    rw [← mul_div_assoc, div_lt_iff₀ hR]
    linarith
  have he : Real.exp (k : ℝ) ≤ (3 : ℝ)^k := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _
  exact (not_lt_of_ge (hratio.trans hy)) ((Real.exp_lt_exp.mpr harg).trans_le he)

/-- The explicit disk radius expressed solely in terms of order and minimum degree. -/
theorem explicit_disk (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    {z : ℂ} (hz : (connectedDominationPolynomial G).IsRoot z) :
    ‖z + 1‖ ≤ 4 * (Fintype.card V : ℝ) /
      ((max 1 (2 * G.minDegree + 2 - Fintype.card V) : ℕ) : ℝ) := by
  have hk : 0 < threshold G := lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..)
  apply (le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < threshold G)).mpr
  simpa [mul_comm] using shao_zhao_root_bound G hG hz

private instance pathAdj (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff' _ pathGraph_adj

/-- P₃[K₂] on its lexicographic-product vertex type, as in Definition 1.4. -/
def doublePath : SimpleGraph (Fin 3 × Fin 2) where
  Adj p q := (pathGraph 3).Adj p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)
  symm := ⟨by
    intro p q h
    rcases h with ha | ⟨hb, hc⟩
    · exact Or.inl ha.symm
    · exact Or.inr ⟨hb.symm, Ne.symm hc⟩⟩
  loopless := ⟨fun p h => h.elim (fun ha => (pathGraph 3).loopless.irrefl p.1 ha)
    (fun hq => hq.2 rfl)⟩

instance : DecidableRel doublePath.Adj := fun p q =>
  inferInstanceAs (Decidable ((pathGraph 3).Adj p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 ≠ q.2)))

set_option maxHeartbeats 1200000 in
/-- The complete coefficient vector in the first computation of Example 2.2. -/
theorem path_three_sanity :
    (List.range 4).map (coefficient (pathGraph 3)) = [0, 1, 2, 1] := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem double_path_sanity :
    (List.range 7).map (coefficient doublePath) = [0, 2, 9, 16, 14, 6, 1] := by decide +kernel

set_option maxHeartbeats 1200000 in
/-- Lemma 3.1 at order four, including the leading zero coefficients. -/
theorem cycle_four_sanity :
    (List.range 5).map (coefficient (cycleGraph 4)) = [0, 0, 4, 4, 1] := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem cycle_five_sanity :
    (List.range 6).map (coefficient (cycleGraph 5)) = [0, 0, 0, 5, 5, 1] := by decide +kernel

#print axioms coeff_eq
#print axioms path_three_sanity
#print axioms double_path_sanity
#print axioms cycle_four_sanity
#print axioms cycle_five_sanity
#print axioms root_power_bound
#print axioms radius_at
#print axioms shao_zhao_root_bound
#print axioms explicit_disk

end ShaoZhao.ConnectedDominationBound
