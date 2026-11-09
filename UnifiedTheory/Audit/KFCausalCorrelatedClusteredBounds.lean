/- Bounds for full finite sums. Diagonal quantities appear only as
majorants; the energy and response keep their exact interference. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredBounds
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredDensity
open KFCausalClusteredClockEnvelope (componentBound)

theorem norm_sum_sq_le (m : ℕ) (A : Fin m → ℂ) :
    ‖∑ i, A i‖^2 ≤ (m:ℝ)*∑ i, ‖A i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1:ℝ)) (fun i => ‖A i‖)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ A) 2
  exact hn.trans (by simpa using h)

theorem sum_pair_bound (m : ℕ) (c A D : Fin m → ℂ) (B : Fin m → ℝ)
    (h : ∀ i, ‖A i‖^2+‖D i‖^2 ≤ B i) :
    ‖∑ i, c i*A i‖^2+‖∑ i, c i*D i‖^2 ≤ (m:ℝ)*∑ i, ‖c i‖^2*B i := by
  apply (add_le_add (norm_sum_sq_le m _) (norm_sum_sq_le m _)).trans
  rw [← mul_add,← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul,mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left (h i) (sq_nonneg ‖c i‖)]

theorem cross_bound (A D : ℂ) : ‖2*(conj A*D).re‖ ≤ ‖A‖^2+‖D‖^2 := by
  have h := Complex.abs_re_le_norm (conj A*D)
  rw [norm_mul,Complex.norm_conj] at h
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [sq_nonneg (‖A‖-‖D‖)]

theorem single_pair_bound (n k : ℕ) (α β δ : ℝ) (hδ : 0 < δ)
    (r v b : ℂ) (P : Polynomial ℂ) (p : Joint) (hz : 0 ≤ (KFCausalClusteredClockFactors.Z α r p).re) :
    ‖KFCausalClusteredClockFactors.factor n k α β δ r b P p‖^2+
      ‖KFCausalClusteredClockFactors.slope n k α β δ r v b P p‖^2 ≤ componentBound n k α β r v b P p := by
  let t := ‖Complex.exp (KFCausalClusteredClockFactors.E α β r b p)‖
  let B := ‖MvPolynomial.eval (KFCausalJointPolynomialIntegrability.coordinates p)
    (KFCausalClusteredClockEnvelope.slopePolynomial0 n k α β r v b P)‖
  let C := ‖MvPolynomial.eval (KFCausalJointPolynomialIntegrability.coordinates p)
    (KFCausalClusteredClockEnvelope.slopePolynomial1 n k α r v P)‖
  have ha := pow_le_pow_left₀ (norm_nonneg _)
    (KFCausalClusteredClockEnvelope.factor_norm_le n k α β δ hδ r b P p hz) 2
  have hd := pow_le_pow_left₀ (norm_nonneg _)
    (KFCausalClusteredClockEnvelope.slope_norm_le n k α β δ hδ r v b P p hz) 2
  have hb : (B+C)^2 ≤ 2*B^2+2*C^2 := by nlinarith [sq_nonneg (B-C)]
  have hd' : ‖KFCausalClusteredClockFactors.slope n k α β δ r v b P p‖^2 ≤ t^2*(2*B^2+2*C^2) :=
    hd.trans (by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hb (sq_nonneg t))
  apply (add_le_add ha hd').trans_eq
  dsimp only [t,B,C]
  rw [KFCausalClusteredClockDensity.limitFactor_norm,KFCausalClusteredClockDensity.base_norm]
  unfold componentBound
  ring

variable {m : ℕ} (f : Family m)

def blockBound (k : ℕ) (α β : ℝ) (r v : ℂ) (p : Joint) : ℝ :=
  (m:ℝ)*∑ i, ‖f.amplitude i‖^2*componentBound (f.degree i) k α β r v (f.source i) (f.polynomial i) p

def fullBound (α β : ℝ) (r v : ℂ) (p : Joint) : ℝ :=
  blockBound f 0 α β r v p+blockBound f 1 α β r v p/2+blockBound f 2 α β r v p/4

theorem factor_pair_bound (k : ℕ) (α β δ : ℝ) (hδ : 0 < δ) (r v : ℂ)
    (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖factor f k α β δ r p‖^2+‖slope f k α β δ r v p‖^2 ≤ blockBound f k α β r v p := by
  have hz : 0 ≤ (KFCausalClusteredClockFactors.Z α r p).re := by
    rw [KFCausalClusteredClockFactors.Z,KFCausalReciprocalWedgeGeometry.chart_re]
    positivity
  exact sum_pair_bound m f.amplitude _ _ _ (fun i => single_pair_bound (f.degree i) k α β δ hδ r v
    (f.source i) (f.polynomial i) p hz)

theorem density_norm_le (α β δ : ℝ) (hδ : 0 < δ) (r v : ℂ)
    (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖density f α β δ r p‖ ≤ fullBound f α β r v p := by
  have hk (k : ℕ) := (le_add_of_nonneg_right (sq_nonneg ‖slope f k α β δ r v p‖)).trans
    (factor_pair_bound f k α β δ hδ r v hA p hp)
  have hpos : 0 ≤ density f α β δ r p :=
    KFCausalReciprocalNeutralPositiveForm.positiveDensity_nonneg _ _ _ _ _ _ _ _
  rw [Real.norm_eq_abs,abs_of_nonneg hpos,density_factors f α β δ hδ]
  unfold energyOf fullBound
  exact add_le_add (add_le_add (hk 0) (div_le_div_of_nonneg_right (hk 1) (by norm_num)))
    (div_le_div_of_nonneg_right (hk 2) (by norm_num))

theorem response_norm_le (α β δ : ℝ) (hδ : 0 < δ) (r v : ℂ)
    (hA : 0 ≤ α*KFCausalReciprocalGaussianCoordinates.area r) (p : Joint) (hp : 0 ≤ p.2) :
    ‖response f α β δ r v p‖ ≤ fullBound f α β r v p := by
  have hk (k : ℕ) := (cross_bound (factor f k α β δ r p) (slope f k α β δ r v p)).trans
    (factor_pair_bound f k α β δ hδ r v hA p hp)
  unfold response responseOf fullBound
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    exact add_le_add (hk 0) (by simpa only [norm_div,Real.norm_ofNat] using
      div_le_div_of_nonneg_right (hk 1) (by norm_num : (0:ℝ)≤2))
  · simpa only [norm_div,Real.norm_ofNat] using
      div_le_div_of_nonneg_right (hk 2) (by norm_num : (0:ℝ)≤4)

#print axioms norm_sum_sq_le
#print axioms sum_pair_bound
#print axioms cross_bound
#print axioms single_pair_bound
#print axioms factor_pair_bound
#print axioms density_norm_le
#print axioms response_norm_le
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredBounds
