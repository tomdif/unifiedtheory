/- Analytic totality of the repository's Hermite Gaussian family in scalar
L2. The polynomial basis theorem and Gaussian Fourier uniqueness prove
density; no oscillator spectral theorem or graph-core hypothesis is used. -/
import UnifiedTheory.Audit.KFCausalGaussianPolynomialTotality
import UnifiedTheory.Audit.KFCausalNeutralHermiteBasis

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalHermiteL2Completeness
noncomputable section
open MeasureTheory
open KFCausalGaussianPolynomialTotality
open KFCausalNeutralHermiteDomain (multiplier physicistsHermite)
open KFCausalGaussianSliceDomain (gaussian)

/-- The existing normalized Hermite polynomial times an actual L2 Gaussian.
The additional common factor normalizing its L2 norm is not included. -/
def state (a : ℝ) (ha : 0 < a) (w B : ℝ) (n : ℕ) : ScalarHilbert :=
  polynomialState a ha (multiplier w B n)

theorem state_coe (a : ℝ) (ha : 0 < a) (w B : ℝ) (n : ℕ) :
    state a ha w B n =ᵐ[volume] fun x : ℝ =>
      ((physicistsHermite n).eval ((Real.sqrt (2*w):ℂ)*((x:ℂ)-(B:ℂ)))/
        (Real.sqrt ((2:ℝ)^n*n.factorial):ℂ))*gaussian a x := by
  filter_upwards [polynomialState_coe a ha (multiplier w B n)] with x hx
  exact hx.trans (congrArg (fun z => z*gaussian a x)
    (KFCausalNeutralHermiteDomain.multiplier_eval w B n (x:ℂ)))

theorem polynomialState_mem_span (a : ℝ) (ha : 0 < a) (w B : ℝ) (hw : 0 < w)
    (P : Polynomial ℂ) :
    polynomialState a ha P ∈ Submodule.span ℂ (Set.range (state a ha w B)) := by
  obtain ⟨S,c,hP⟩ := KFCausalNeutralHermiteBasis.exists_expansion w B hw P
  rw [hP]
  unfold KFCausalNeutralHermiteBasis.expansion
  rw [map_sum]
  apply Submodule.sum_mem
  intro n _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n,rfl⟩)

/-- Hilbert-space completeness, beyond finite-polynomial spanning. -/
theorem dense_span (a : ℝ) (ha : 0 < a) (w B : ℝ) (hw : 0 < w) :
    (Submodule.span ℂ (Set.range (state a ha w B))).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← dense_monomial_span a ha]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨n,rfl⟩
  rw [← polynomialState_monomial a ha n]
  exact polynomialState_mem_span a ha w B hw _

/-- The matched, centered oscillator Hermite functions are complete in L2. -/
theorem oscillator_dense_span (a : ℝ) (ha : 0 < a) :
    (Submodule.span ℂ (Set.range (state a ha a 0))).topologicalClosure = ⊤ :=
  dense_span a ha a 0 ha

#print axioms state_coe
#print axioms polynomialState_mem_span
#print axioms dense_span
#print axioms oscillator_dense_span
end
end UnifiedTheory.Audit.KFCausalHermiteL2Completeness
