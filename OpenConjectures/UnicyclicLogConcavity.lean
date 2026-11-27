import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# A unicyclic connected zero forcing polynomial that fails log-concavity

Mukherjee and Ray, arXiv:2611.10985v2, Problem 6.2, second sentence.
The graph is the path on 0,...,6 with the additional edge 0--4.
-/

namespace MukherjeeRay.UnicyclicLogConcavity

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A colored vertex `u` can color `w` precisely when `w` is its unique white neighbor. -/
def LegalForce (G : SimpleGraph V) (s : Finset V) (u w : V) : Prop :=
  u ∈ s ∧ w ∉ s ∧ G.Adj u w ∧ ∀ v, G.Adj u v → v ∉ s → v = w

/-- A chronological sequence of exactly `k` legal single-vertex forces colors the graph. -/
def Finishes (G : SimpleGraph V) : ℕ → Finset V → Prop
  | 0, s => s = univ
  | k + 1, s => ∃ w, (∃ u, LegalForce G s u w) ∧ Finishes G k (insert w s)

def ZeroForces (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ k, Finishes G k s

theorem finishes_card (G : SimpleGraph V) {k : ℕ} {s : Finset V}
    (h : Finishes G k s) : s.card + k = Fintype.card V := by
  induction k generalizing s with
  | zero =>
    change s = univ at h
    simp [h]
  | succ k ih =>
    obtain ⟨w, ⟨u, legal⟩, tail⟩ := h
    have hc := ih tail
    rw [Finset.card_insert_of_notMem legal.2.1] at hc
    omega

theorem zeroForces_iff (G : SimpleGraph V) (s : Finset V) :
    ZeroForces G s ↔ Finishes G (Fintype.card V - s.card) s := by
  constructor
  · rintro ⟨k, h⟩
    have hc := finishes_card G h
    have : Fintype.card V - s.card = k := by omega
    rwa [this]
  · exact fun h => ⟨_, h⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (u w : V) :
    Decidable (LegalForce G s u w) := by
  unfold LegalForce
  infer_instance

def finishesDec (G : SimpleGraph V) [DecidableRel G.Adj] :
    (k : ℕ) → (s : Finset V) → Decidable (Finishes G k s)
  | 0, s => inferInstanceAs (Decidable (s = univ))
  | k + 1, s => by
    letI (t : Finset V) : Decidable (Finishes G k t) := finishesDec G k t
    unfold Finishes
    infer_instance

instance (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) :
    Decidable (ZeroForces G s) := by
  letI := finishesDec G (Fintype.card V - s.card) s
  exact decidable_of_iff' _ (zeroForces_iff G s)

/-- Count initial subsets of size `k` whose induced graph is connected and which force all vertices. -/
def coefficient (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (((univ : Finset V).powersetCard k).filter
    (fun s : Finset V => (G.induce (s : Set V)).Connected ∧ ZeroForces G s)).card

/-- The paper's coefficient as the cardinality of the subtype of qualifying initial subsets. -/
noncomputable def paperCoefficient (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ (G.induce (s : Set V)).Connected ∧ ZeroForces G s}

theorem paperCoefficient_eq (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    paperCoefficient G k = coefficient G k := by
  let family := ((univ : Finset V).powersetCard k).filter
    (fun s : Finset V => (G.induce (s : Set V)).Connected ∧ ZeroForces G s)
  have mem_family (s : Finset V) : s ∈ family ↔
      s.card = k ∧ (G.induce (s : Set V)).Connected ∧ ZeroForces G s := by
    simp [family, Finset.mem_powersetCard]
  calc
    paperCoefficient G k = Nat.card ↥family :=
      Nat.card_congr (Equiv.subtypeEquivRight fun s => (mem_family s).symm)
    _ = family.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe family)
    _ = coefficient G k := rfl

/-- The polynomial in the paper, with its natural-number coefficients. -/
noncomputable def connectedForcingPolynomial (G : SimpleGraph V) : Polynomial ℕ :=
  ∑ k ∈ range (Fintype.card V + 1), Polynomial.monomial k (paperCoefficient G k)

theorem polynomial_coeff (G : SimpleGraph V) (k : ℕ) :
    (connectedForcingPolynomial G).coeff k = paperCoefficient G k := by
  classical
  simp only [connectedForcingPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · have hsize : Fintype.card V < k := by omega
    have empty : (univ : Finset V).powersetCard k = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using hsize)
    simp [paperCoefficient_eq G k, coefficient, empty]

/-- For finite connected graphs, deleting one edge to obtain a tree characterizes
having exactly one undirected cycle. The unique tree path between its ends closes that cycle. -/
def Unicyclic (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∃ e ∈ G.edgeSet, (G.deleteEdges {e}).IsTree

/-- The coefficient inequality at every positive interior index, indexed as `k + 1`.
Coefficients beyond the order vanish, so this same formula can be required for every `k`. -/
def LogConcave (a : ℕ → ℕ) : Prop :=
  ∀ k, a k * a (k + 2) ≤ a (k + 1) ^ 2

def UniversalClaim : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W),
    Unicyclic G → LogConcave (fun k => (connectedForcingPolynomial G).coeff k)

abbrev tadpole : SimpleGraph (Fin 7) :=
  pathGraph 7 ⊔ edge 0 4

instance pathAdj (n : ℕ) : DecidableRel (pathGraph n).Adj := fun _ _ =>
  decidable_of_iff' _ pathGraph_adj

instance singleEdgeAdj (s t : V) : DecidableRel (edge s t).Adj := fun u v =>
  decidable_of_iff' _ (edge_adj s t u v)

theorem tadpole_unicyclic : Unicyclic tadpole := by
  refine ⟨(connected_pathGraph_add_one 6).mono le_sup_left, s(0, 4), ?_, ?_⟩
  · change tadpole.Adj 0 4
    decide
  · have hd : tadpole.deleteEdges {s(0, 4)} = pathGraph 7 := by
      ext u v
      simp only [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff, tadpole, sup_adj,
        edge_adj, pathGraph_adj]
      revert u v
      decide
    rw [hd]
    exact isTree_pathGraph_add_one 6

abbrev star4 : SimpleGraph (Fin 4) :=
  edge 0 1 ⊔ edge 0 2 ⊔ edge 0 3

/-- The nine-vertex uniform starlike tree, with arm lengths 2,2,2,1,1. -/
private def uniformStarEdges : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (2, 7), (3, 8)]

abbrev uniformStar9 : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ uniformStarEdges)

instance : DecidableRel uniformStar9.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ uniformStarEdges ∨ (v, u) ∈ uniformStarEdges)))

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The polynomial for the four-vertex path printed at the start of Section 5. -/
theorem paper_path4 :
    (List.range 5).map (coefficient (pathGraph 4)) = [0, 2, 3, 2, 1] := by
  decide +kernel

/-- The polynomial for the three-leaf star printed in the same source example. -/
theorem paper_star4 :
    (List.range 5).map (coefficient star4) = [0, 0, 0, 3, 1] := by
  decide +kernel

/-- Three coefficients printed for T′ in Example 5.17, Case I. -/
theorem paper_example_5_17 :
    [5, 6, 7].map (coefficient uniformStar9) = [5, 13, 12] := by
  decide +kernel

theorem tadpole_coefficients :
    (List.range 8).map (coefficient tadpole) = [0, 0, 5, 7, 10, 8, 5, 1] := by
  decide +kernel

theorem not_unicyclic_log_concavity : ¬ UniversalClaim := by
  intro h
  have bound := h (Fin 7) tadpole tadpole_unicyclic 2
  simp only [polynomial_coeff, paperCoefficient_eq] at bound
  have atDegree (i : Fin 8) := congrArg (fun l : List ℕ => l[i.val]?) tadpole_coefficients
  have h2 : coefficient tadpole 2 = 5 := Option.some.inj (atDegree 2)
  have h3 : coefficient tadpole 3 = 7 := Option.some.inj (atDegree 3)
  have h4 : coefficient tadpole 4 = 10 := Option.some.inj (atDegree 4)
  change coefficient tadpole 2 * coefficient tadpole 4 ≤ coefficient tadpole 3 ^ 2 at bound
  rw [h2, h3, h4] at bound
  omega

#print axioms paper_path4
#print axioms paper_star4
#print axioms paper_example_5_17
#print axioms tadpole_unicyclic
#print axioms tadpole_coefficients
#print axioms not_unicyclic_log_concavity

end MukherjeeRay.UnicyclicLogConcavity
