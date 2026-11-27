import Mathlib

/-! A counterexample to Conjecture 1.4 in Site Mou, arXiv:2611.32429v1.
The definitions follow Sections 2 and 4, including the rank-dependent partial bar. -/
namespace MouBarcode

structure Poset (d : ℕ) where
  order : PartialOrder (Fin d)
  decLe : DecidableRel order.le
  natural : ∀ i j, order.le i j → i ≤ j

variable {d : ℕ}

def descents (w : List (Fin d)) : ℕ :=
  (w.zip (w.drop 1)).countP (fun p => decide (p.2 < p.1))

def descentData (P : Poset d) : List ℕ :=
  letI : DecidableRel P.order.le := P.decLe
  let ws := (List.finRange d).permutations'
  (ws.filter (fun w => decide (w.Pairwise (fun i j => ¬ P.order.le j i)))).map descents

def IsBarcode (P : Poset d) (a : List ℕ) : Prop := a.Perm (descentData P)

/-- Greedy binomial expansion at rank k, with the binomial lower indices raised by one. -/
def upperShift : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k+1, r =>
    if r = 0 then 0 else
      let m := Nat.findGreatest (fun i => i.choose (k+1) ≤ r) (r+k)
      m.choose (k+2) + upperShift k (r - m.choose (k+1))

def periodWeight (k t : ℕ) (a : List ℕ) : ℕ :=
  (a.map (fun x => (x+t).choose k)).sum

def prefixWeight (k : ℕ) (a : List ℕ) (t j : ℕ) : ℕ :=
  ((List.range t).map (fun u => periodWeight k u a)).sum + periodWeight k t (a.take j)

/-- At a boundary r=0. Otherwise r is strictly inside the next nonempty bar. -/
def BarcodeValue (k : ℕ) (a : List ℕ) (N value : ℕ) : Prop :=
  ∃ t j r : ℕ, j ≤ a.length ∧
    (r=0 ∨ ∃ x, a[j]? = some x ∧ r < (x+t).choose k) ∧
    N = prefixWeight k a t j + r ∧ value = prefixWeight (k+1) a t j + upperShift k r

abbrev Point (d : ℕ) := Fin d → ℝ

def orderPolytope (P : Poset d) : Set (Point d) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∀ i j, P.order.le i j → x i ≤ x j}

def copies (P : Poset d) (S : Finset (Point d)) : Set (Point d × ℝ) :=
  {h | 0 < h.2 ∧ ∀ x ∈ (orderPolytope P).extremePoints ℝ, h.1 + h.2 • x ∈ S}

noncomputable def extremal (P : Poset d) (N : ℕ) : ℕ∞ :=
  ⨆ (S : Finset (Point d)) (_ : S.card = N), (copies P S).encard

/-- The upper bound on the extremal number is precisely the bound on every configuration. -/
theorem extremal_le_iff (P : Poset d) (N v : ℕ) :
    extremal P N ≤ (v : ℕ∞) ↔
      ∀ S : Finset (Point d), S.card = N → (copies P S).encard ≤ (v : ℕ∞) := by
  simp only [extremal, iSup_le_iff]

def Effective (P : Poset d) (a : List ℕ) : Prop :=
  ∀ N v, BarcodeValue (d-1) a N v → extremal P N ≤ (v : ℕ∞)

def MouConjecture : Prop :=
  ∀ d, 2 ≤ d → ∀ P : Poset d, ∃ a, IsBarcode P a ∧ Effective P a

def fromStrict (r : Fin d → Fin d → Bool)
    (trans : ∀ i j k, r i j = true → r j k = true → r i k = true)
    (lt : ∀ i j, r i j = true → i < j) : Poset d where
  order := {
    le := fun i j => i = j ∨ r i j = true
    lt := fun i j => (i = j ∨ r i j = true) ∧ ¬ (j = i ∨ r j i = true)
    le_refl := fun _ => Or.inl rfl
    le_trans := by
      intro i j k hij hjk
      rcases hij with rfl | hij
      · exact hjk
      rcases hjk with rfl | hjk
      · exact Or.inr hij
      exact Or.inr (trans i j k hij hjk)
    le_antisymm := by
      intro i j hij hji
      rcases hij with h | h
      · exact h
      rcases hji with h' | h'
      · exact h'.symm
      exact (lt_asymm (lt i j h) (lt j i h')).elim }
  decLe := fun i j => (inferInstance : Decidable (i = j ∨ r i j = true))
  natural := by
    intro i j h
    rcases h with rfl | h
    · exact le_rfl
    exact (lt i j h).le

/-- Elements 0 through 4 form a chain, and elements 5 and 6 are isolated. -/
def witness : Poset 7 :=
  fromStrict (fun i j => decide (i < j ∧ j.val < 5))
    (by
      intro i j k h h'
      simp only [decide_eq_true_eq] at *
      exact ⟨lt_trans h.1 h'.1, h'.2⟩)
    (by intro i j h; exact (of_decide_eq_true h).1)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def chainThree : Poset 3 := fromStrict (fun i j => decide (i < j))
  (by intro i j k h h'; simpa using lt_trans (of_decide_eq_true h) (of_decide_eq_true h'))
  (by intro i j h; exact of_decide_eq_true h)

def antichainTwo : Poset 2 := fromStrict (fun _ _ => false) (by decide) (by decide)

def twoPairs : Poset 4 :=
  fromStrict (fun i j => decide (i.val < 2 ∧ 2 ≤ j.val)) (by decide) (by decide)

/-- Three specializations of the basic-sequence examples in the table of Theorem 1.3. -/
theorem table_chain : List.insertionSort (· ≤ ·) (descentData chainThree) = [0] := by decide
theorem table_antichain : List.insertionSort (· ≤ ·) (descentData antichainTwo) = [0,1] := by
  decide
theorem table_ordinal_sum : List.insertionSort (· ≤ ·) (descentData twoPairs) = [0,1,1,2] := by
  decide

/-- The two square configurations illustrated in Section 6 also test partial bars. -/
theorem square_at_nineteen : BarcodeValue 1 [0,1] 19 17 := by
  exact ⟨4,0,3,by decide,Or.inr ⟨0,rfl,by decide⟩,by decide,by decide⟩

theorem square_at_twenty_two : BarcodeValue 1 [0,1] 22 21 := by
  exact ⟨4,1,2,by decide,Or.inr ⟨1,rfl,by decide⟩,by decide,by decide⟩

def histogram : List ℕ := [0] ++ List.replicate 16 1 ++ List.replicate 25 2

theorem witness_histogram : List.insertionSort (· ≤ ·) (descentData witness) = histogram := by
  decide

theorem endpoint (a : List ℕ) (ha : IsBarcode witness a) : BarcodeValue 6 a 25 0 := by
  have hp : a.Perm histogram := by
    rw [← witness_histogram]
    exact ha.trans (List.perm_insertionSort _ _).symm
  have weights (k t) : periodWeight k t a = periodWeight k t histogram :=
    (hp.map _).sum_eq
  have lengths : prefixWeight 6 histogram 5 0 = 25 := by decide
  have values : prefixWeight 7 histogram 5 0 = 0 := by decide
  have hend (k) : prefixWeight k a 5 0 = prefixWeight k histogram 5 0 := by
    simp only [prefixWeight, weights, List.take_zero]
  refine ⟨5,0,0,Nat.zero_le _,Or.inl rfl,?_,?_⟩
  · simpa only [Nat.add_zero, hend] using lengths.symm
  · simpa [hend, upperShift] using values.symm

/-- If any coordinate is strictly between zero and one, the two monotone
coordinate changes below exhibit the point as a nontrivial midpoint. -/
theorem extreme_binary (P : Poset d) {x : Point d}
    (hx : x ∈ (orderPolytope P).extremePoints ℝ) (i : Fin d) : x i = 0 ∨ x i = 1 := by
  obtain ⟨hxP,hxext⟩ := mem_extremePoints_iff_left.mp hx
  let y : Point d := fun j => x j ^ 2
  let z : Point d := fun j => 1 - (1-x j)^2
  have hy : y ∈ orderPolytope P := by
    constructor
    · intro j
      exact ⟨sq_nonneg _, by
        dsimp [y]
        nlinarith [(hxP.1 j).1, (hxP.1 j).2,
          mul_nonneg (hxP.1 j).1 (sub_nonneg.mpr (hxP.1 j).2)]⟩
    · intro a b hab
      exact pow_le_pow_left₀ (hxP.1 a).1 (hxP.2 a b hab) 2
  have hz : z ∈ orderPolytope P := by
    constructor
    · intro j
      dsimp [z]
      constructor
      · nlinarith [(hxP.1 j).1, mul_nonneg (hxP.1 j).1 (sub_nonneg.mpr (hxP.1 j).2)]
      · nlinarith [sq_nonneg (1-x j)]
    · intro a b hab
      dsimp [z]
      have := pow_le_pow_left₀ (sub_nonneg.mpr (hxP.1 b).2)
        (sub_le_sub_left (hxP.2 a b hab) 1) 2
      linarith
  have hxseg : x ∈ openSegment ℝ y z := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    ext j
    change (1/2:ℝ)*x j^2+(1/2:ℝ)*(1-(1-x j)^2)=x j
    ring
  have eq := congrFun (hxext y hy z hz hxseg) i
  change x i^2 = x i at eq
  have prod : x i*(x i-1)=0 := by nlinarith
  rcases mul_eq_zero.mp prod with h|h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

def upperBits (P : Poset d) : Finset (Fin d → Bool) :=
  letI : DecidableRel P.order.le := P.decLe
  Finset.univ.filter (fun b => ∀ i j, P.order.le i j → b i = true → b j = true)

def bitPoint (b : Fin d → Bool) : Point d := fun i => if b i then 1 else 0

noncomputable def upperPoints (P : Poset d) : Finset (Point d) := by
  classical
  exact (upperBits P).image bitPoint

theorem vertices_subset (P : Poset d) :
    (orderPolytope P).extremePoints ℝ ⊆ ↑(upperPoints P) := by
  classical
  let inst : DecidableRel P.order.le := P.decLe
  intro x hx
  have hpoly := (mem_extremePoints_iff_left.mp hx).1
  let b : Fin d → Bool := fun i => decide (x i = 1)
  refine Finset.mem_image.mpr ⟨b, ?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i j hij hi
    have hi' : x i=1 := of_decide_eq_true hi
    apply decide_eq_true
    exact le_antisymm (hpoly.1 j).2 (hi' ▸ hpoly.2 i j hij)
  · funext i
    rcases extreme_binary P hx i with hi | hi <;> simp [bitPoint,b,hi]

theorem witness_upper_bits : (upperBits witness).card=24 := by decide

/-- Each feasible binary point is extreme, coordinate by coordinate in the unit interval. -/
theorem bitPoint_extreme (P : Poset d) (b : Fin d → Bool) (hb : b ∈ upperBits P) :
    bitPoint b ∈ (orderPolytope P).extremePoints ℝ := by
  let inst : DecidableRel P.order.le := P.decLe
  simp only [upperBits, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply mem_extremePoints_iff_left.mpr
  constructor
  · constructor
    · intro i
      cases hi : b i <;> simp [bitPoint,hi]
    · intro i j hij
      cases hi : b i with
      | false => cases hj : b j <;> simp [bitPoint,hi,hj]
      | true => simp [bitPoint,hi,hb i j hij hi]
  · rintro y hy z hz ⟨a,c,ha,hc,hac,he⟩
    funext i
    have hext : bitPoint b i ∈ (Set.Icc (0:ℝ) 1).extremePoints ℝ := by
      rw [Set.extremePoints_Icc (by norm_num)]
      cases hi : b i <;> simp [bitPoint,hi]
    exact (mem_extremePoints_iff_left.mp hext).2 (y i) (hy.1 i) (z i) (hz.1 i)
      ⟨a,c,ha,hc,hac,congrFun he i⟩

theorem vertices_eq (P : Poset d) :
    (orderPolytope P).extremePoints ℝ = ↑(upperPoints P) := by
  classical
  apply Set.Subset.antisymm (vertices_subset P)
  intro x hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  exact bitPoint_extreme P b hb

theorem bitPoint_injective : Function.Injective (@bitPoint d) := by
  intro b c h
  funext i
  have eq := congrFun h i
  cases hi : b i <;> cases hj : c i <;> simp_all [bitPoint]

theorem witness_vertex_count : (upperPoints witness).card = 24 := by
  classical
  unfold upperPoints
  rw [Finset.card_image_of_injective _ bitPoint_injective, witness_upper_bits]

noncomputable def witnessPoints : Finset (Point 7) := by
  classical
  exact insert (fun _ => (2:ℝ)) (upperPoints witness)

theorem witness_points_count : witnessPoints.card = 25 := by
  classical
  have hout : (fun _ : Fin 7 => (2:ℝ)) ∉ upperPoints witness := by
    intro h
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp h
    have hzero := congrFun hb (0:Fin 7)
    cases hh : b 0 <;> norm_num [bitPoint,hh] at hzero
  rw [witnessPoints,Finset.card_insert_of_notMem hout,witness_vertex_count]

theorem at_least_one_copy : 1 ≤ extremal witness 25 := by
  classical
  have hid : ((0:Point 7),(1:ℝ)) ∈ copies witness witnessPoints := by
    refine ⟨one_pos,?_⟩
    intro x hx
    change (0:Point 7) + (1:ℝ) • x ∈ insert (fun _ => (2:ℝ)) (upperPoints witness)
    rw [one_smul,zero_add]
    exact Finset.mem_insert_of_mem (vertices_subset witness hx)
  have hone : 1 ≤ (copies witness witnessPoints).encard := by
    simpa using Set.encard_le_encard (Set.singleton_subset_iff.mpr hid)
  exact le_iSup_of_le witnessPoints (le_iSup_of_le witness_points_count hone)

theorem mou_conjecture_false : ¬ MouConjecture := by
  intro h
  obtain ⟨a,ha,heff⟩ := h 7 (by decide) witness
  have hzero := heff 25 0 (endpoint a ha)
  have : (1 : ℕ∞) ≤ 0 := at_least_one_copy.trans hzero
  simp at this

#print axioms table_chain
#print axioms table_antichain
#print axioms table_ordinal_sum
#print axioms square_at_nineteen
#print axioms square_at_twenty_two
#print axioms vertices_eq
#print axioms witness_vertex_count
#print axioms endpoint
#print axioms mou_conjecture_false

end MouBarcode
