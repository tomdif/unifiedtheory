/-
  Coarse-geometry counting and finite readout/preparation resources.
  Operator suppliers and asymptotic graph counts are analytic; the
  finite combinatorial inequalities below make no continuum assertion.
-/
import UnifiedTheory.Audit.KFCausalGeometryEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCoarseGeometry
noncomputable section
open scoped BigOperators

/-- A positive generating function bounds a family of allowed edge sets. -/
theorem weighted_graph_family_bound {E : Type*} [DecidableEq E]
    (edges : Finset E) (family : Finset (Finset E)) (w : E → ℝ) (lo : ℝ)
    (hw : ∀ e, 0 ≤ w e) (hsub : ∀ g ∈ family, g ⊆ edges)
    (hweight : ∀ g ∈ family, lo ≤ ∏ e ∈ g, w e) :
    (family.card : ℝ) * lo ≤ ∏ e ∈ edges, (1 + w e) := by
  calc
    (family.card : ℝ) * lo = ∑ g ∈ family, lo := by simp
    _ ≤ ∑ g ∈ family, ∏ e ∈ g, w e := Finset.sum_le_sum hweight
    _ ≤ ∑ g ∈ edges.powerset, ∏ e ∈ g, w e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro g hg
        exact Finset.mem_powerset.mpr (hsub g hg)
      · intro g _ _
        exact Finset.prod_nonneg (fun e _ => hw e)
    _ = ∏ e ∈ edges, (1 + w e) := (Finset.prod_one_add edges).symm

/-- The remaining exponent counts coarse cells, after all assignments and
unrestricted internal choices have been included. -/
theorem coarse_entropy_exponent (n d eta logm logb : ℝ) :
    n * logm + (d * n / 2) * logb + (eta * d * n / 2) * logm
      - (d * n / 2) * (logm + logb) =
    -((1 - eta) * d / 2 - 1) * n * logm := by ring

theorem positive_coarse_deficit (d eta : ℝ) (hd : 0 < d)
    (heta : eta < 1 - 2 / d) : 0 < (1 - eta) * d / 2 - 1 := by
  have h := (div_lt_iff₀ hd).mp (show 2 / d < 1 - eta by linarith)
  nlinarith

/-- Trace normalization of a POVM bounds the summed decoding success.
The quantum inequality success(g) <= trace(effect(g)) is supplied separately. -/
theorem readout_dimension_bound {G I : Type*} [Fintype G] [Fintype I]
    (success : G → ℝ) (effects : G → I → ℝ)
    (hs : ∀ g, success g ≤ ∑ i, effects g i)
    (hnorm : ∀ i, ∑ g, effects g i = 1) :
    (∑ g, success g) ≤ (Fintype.card I : ℝ) := by
  calc
    (∑ g, success g) ≤ ∑ g, ∑ i, effects g i := Finset.sum_le_sum (fun g _ => hs g)
    _ = ∑ i, ∑ g, effects g i := Finset.sum_comm
    _ = (Fintype.card I : ℝ) := by simp [hnorm]

theorem uniform_readout_capacity {G I : Type*} [Fintype G] [Fintype I]
    (success : G → ℝ) (effects : G → I → ℝ) (p : ℝ)
    (hs : ∀ g, success g ≤ ∑ i, effects g i)
    (hnorm : ∀ i, ∑ g, effects g i = 1)
    (hp : ∀ g, p ≤ success g) :
    (Fintype.card G : ℝ) * p ≤ (Fintype.card I : ℝ) := by
  calc
    (Fintype.card G : ℝ) * p = ∑ _ : G, p := by simp
    _ ≤ ∑ g, success g := Finset.sum_le_sum (fun g _ => hp g)
    _ ≤ _ := readout_dimension_bound success effects hs hnorm

/-- The finite register capacity needed by unitary preparation from a
maximally mixed input; the operator trace supplies the probability bound. -/
theorem preparation_register_capacity (p m r D : ℝ) (hD : 0 < D)
    (hbound : p ≤ m * r / D) : p * D ≤ m * r :=
  (le_div_iff₀ hD).mp hbound

/-- A resource bound with a logarithmically growing deficit cannot be offset
by a fixed exponential number of ancillary states. -/
theorem preparation_entropy_exponent (a n logm c memory : ℝ) :
    (-a * n * logm + c * n) + memory * n =
    -a * n * logm + (c + memory) * n := by ring

#print axioms weighted_graph_family_bound
#print axioms coarse_entropy_exponent
#print axioms positive_coarse_deficit
#print axioms readout_dimension_bound
#print axioms uniform_readout_capacity
#print axioms preparation_register_capacity
#print axioms preparation_entropy_exponent

end
end UnifiedTheory.Audit.KFCausalCoarseGeometry
