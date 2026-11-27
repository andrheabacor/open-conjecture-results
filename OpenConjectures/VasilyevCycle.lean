import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Rotate
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
A counterexample to the universal cycle inequality in Oleg Vasilyev,
*Up or down at every integer*, arXiv:2611.20344v2, Question 7.1.

The ordered, distinct, positive vertices in a cycle describe one complete turn.
The final vertex maps back to the first. The witness set selects the upward
branch on exactly the vertices where the printed orbit increases.
-/

namespace VasilyevCycle

/-- Ceiling of x/2 in the paper. -/
def down (x : ℕ) : ℕ := (x + 1) / 2

/-- Ceiling of 3x/2 in the paper. -/
def up (x : ℕ) : ℕ := (3*x + 1) / 2

/-- For the characteristic function of S, this is the paper's map T_S. -/
def step (inS : ℕ → Bool) (x : ℕ) : ℕ := if inS x then up x else down x

/-- A positive simple cycle in the paper's least-vertex-first convention. -/
def IsCycle (inS : ℕ → Bool) (c : List ℕ) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ (∀ x ∈ c, 0 < x) ∧ c.head? = c.min? ∧
    c.map (step inS) = c.rotate 1

instance (inS : ℕ → Bool) (c : List ℕ) : Decidable (IsCycle inS c) := by
  unfold IsCycle
  infer_instance

/-- All subsets are allowed. A possible choice at zero does not affect positive orbits. -/
noncomputable def characteristic (S : Set ℕ) (x : ℕ) : Bool := by
  classical
  exact decide (x ∈ S)

theorem characteristic_setOf (f : ℕ → Bool) :
    characteristic {x | f x = true} = f := by
  classical
  funext x
  cases hx : f x <;> simp [characteristic, hx]

/-- The first, universally quantified assertion in Question 7.1. -/
def CycleBound : Prop :=
  ∀ (S : Set ℕ) (c : List ℕ), IsCycle (characteristic S) c →
    2 ^ c.length < 3 ^ (c.countP (characteristic S) + 1)

/-- The witness, in orbit order, without repeating its starting vertex at the end. -/
def vertices : List ℕ :=
  [3, 5, 8, 12, 18, 27, 41, 62, 31, 47, 71, 107, 161,
   242, 121, 182, 91, 137, 69, 104, 156, 234, 351, 527, 264, 132,
   198, 297, 149, 75, 113, 170, 85, 43, 65, 98, 49, 74, 37,
   19, 10, 15, 23, 35, 53, 80, 40, 60, 90, 135, 203, 305,
   458, 229, 115, 173, 260, 390, 195, 293, 147, 221, 332, 166, 249,
   125, 188, 94, 141, 212, 106, 159, 239, 120, 180, 270, 405, 608,
   304, 456, 684, 342, 513, 257, 386, 579, 290, 145, 218, 327, 164,
   82, 123, 185, 278, 417, 626, 313, 470, 235, 353, 530, 265, 133,
   67, 34, 51, 26, 39, 59, 30, 45, 68, 102, 153, 230, 345,
   518, 259, 389, 584, 292, 438, 219, 110, 165, 248, 372, 186, 93,
   140, 210, 105, 158, 237, 356, 178, 267, 401, 602, 301, 151, 227,
   114, 171, 86, 129, 194, 291, 437, 656, 328, 492, 246, 369, 554,
   277, 139, 209, 314, 157, 236, 354, 177, 89, 134, 201, 101, 152,
   76, 38, 57, 29, 44, 22, 33, 17, 9, 14, 21, 32, 16,
   24, 36, 54, 81, 122, 183, 275, 413, 620, 310, 465, 698, 349,
   524, 262, 393, 197, 296, 148, 222, 333, 167, 84, 126, 189, 95,
   143, 215, 108, 162, 243, 365, 548, 274, 411, 206, 309, 464, 232,
   348, 174, 87, 131, 66, 99, 50, 25, 13, 7, 11, 6]

/-- A concrete decision function for the upward-step set. -/
def witnessUp (x : ℕ) : Bool :=
  ([3, 5, 7, 8, 9, 10, 12, 14, 15, 16, 18, 21, 22,
   23, 24, 26, 27, 29, 30, 31, 34, 35, 36, 38, 39, 40,
   41, 43, 45, 47, 49, 53, 54, 60, 65, 66, 68, 69, 71,
   75, 81, 82, 84, 86, 87, 89, 90, 91, 93, 94, 95, 101,
   102, 104, 105, 106, 107, 108, 110, 113, 114, 115, 120, 121, 122,
   123, 125, 126, 129, 132, 134, 135, 139, 140, 141, 143, 145, 147,
   148, 151, 153, 156, 157, 158, 159, 161, 162, 165, 166, 173, 178,
   180, 183, 185, 194, 195, 197, 198, 203, 206, 209, 218, 221, 222,
   230, 232, 234, 235, 236, 237, 243, 246, 248, 257, 259, 260, 262,
   267, 270, 274, 275, 278, 291, 292, 304, 305, 309, 310, 313, 328,
   342, 345, 349, 351, 353, 365, 369, 386, 389, 401, 405, 413, 417,
   437, 456, 465] : List ℕ).contains x

/-- Four cycles explicitly listed in the paper below its cycle table and in its examples. -/
theorem paper_cycles :
    IsCycle (fun x => x == 1) [1, 2] ∧
    IsCycle (fun x => x == 2) [2, 3] ∧
    IsCycle (fun x => x == 3) [3, 5] ∧
    IsCycle (fun x => ([4, 6, 9] : List ℕ).contains x) [4, 6, 9, 14, 7] := by
  decide

/-- With t internal vertices still to choose, count simple returns to start.
Intermediate vertices must exceed start, so each rotation is counted once. -/
def completions (start bound : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | 0, x, _ => (if down x = start then 1 else 0) + (if up x = start then 1 else 0)
  | t + 1, x, used =>
    let extend (y : ℕ) :=
      if start < y ∧ y ≤ bound ∧ y ∉ used then completions start bound t y (y :: used) else 0
    extend (down x) + extend (up x)

/-- Count cycles of length t+1 in the positive interval [1,bound]. -/
def boundedCount (t bound : ℕ) : ℕ :=
  ((List.range bound).map fun i => completions (i+1) bound t (i+1) [i+1]).sum

/-- Census rows (length, count, largest vertex) = (1,1,1), (2,3,5), (5,12,26).
The two counts per row also check the displayed maximum inside the table's bound. -/
theorem paper_census :
    (boundedCount 0 1 = 1 ∧ boundedCount 0 0 < 1) ∧
    (boundedCount 1 5 = 3 ∧ boundedCount 1 4 < 3) ∧
    (boundedCount 4 26 = 12 ∧ boundedCount 4 25 < 12) := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- The fourth nonempty row of Table 4.1 records 140 cycles of length 8, with
largest vertex 242. The finite checks use the table's reported ceiling. -/
theorem paper_census_eight :
    boundedCount 7 242 = 140 ∧ boundedCount 7 241 < 140 := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem witness_isCycle : IsCycle witnessUp vertices := by
  decide +kernel

set_option maxRecDepth 16384 in
theorem witness_counts : vertices.length = 233 ∧ vertices.countP witnessUp = 146 := by
  decide +kernel

theorem witness_extrema :
    vertices.head? = some 3 ∧ vertices.min? = some 3 ∧ vertices.max? = some 698 := by
  decide +kernel

set_option maxRecDepth 16384 in
/-- Independently compute the least period through the usual Mathlib iterate. -/
theorem witness_minimal_period : Function.minimalPeriod (step witnessUp) 3 = 233 := by
  let _ : Fact (Nat.Prime 233) := ⟨by decide +kernel⟩
  apply Function.minimalPeriod_eq_prime
  · change (step witnessUp)^[233] 3 = 3
    decide +kernel
  · change ¬ step witnessUp 3 = 3
    decide

theorem exact_gap : (3 : ℕ)^147 < 2^233 := by
  decide +kernel

/-- Negation of the proposed bound for all simple cycles of all maps T_S. -/
theorem cycleBound_false : ¬ CycleBound := by
  intro h
  have bound := h {x | witnessUp x = true} vertices
  rw [characteristic_setOf] at bound
  have claimed := bound witness_isCycle
  rw [witness_counts.1, witness_counts.2] at claimed
  exact (Nat.not_lt_of_ge (Nat.le_of_lt exact_gap)) claimed

#print axioms paper_cycles
#print axioms paper_census
#print axioms paper_census_eight
#print axioms witness_isCycle
#print axioms witness_counts
#print axioms witness_extrema
#print axioms witness_minimal_period
#print axioms exact_gap
#print axioms cycleBound_false

end VasilyevCycle

