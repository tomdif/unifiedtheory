import UnifiedTheory.Audit.KFCausalLorentzianContractedBianchi
import UnifiedTheory.Audit.KFCausalConformal4DCurvatureExpansion
import UnifiedTheory.Audit.KFCausalBDG4DActualTemporalVariation

/-! Synthesis of the 4D conformal curvature expansion, Lorentzian contracted
Bianchi identity, Einstein tensor trace `Tr_g(G) = R - (4/2) R = -R = -12c`,
and its temporal derivative `(1/2) d/dc Tr_g(G)|₀ = -6` recovered by the
causal-diamond BDG temporal variation limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DLorentzianBianchiTraceSynthesis
noncomputable section

open Filter Topology
open scoped Real BigOperators
open UnifiedTheory.LayerA.Bianchi (RiemannData)
open UnifiedTheory.LayerA.MetricConstruction (MetricDerivs)
open KFCausalConformal4DDiamondBenchmark (sign eta omega derivativeData)
open KFCausalConformal4DConnection (inverseMetric)
open KFCausalLorentzianContractedBianchi (ricci scalar einstein dRic divRic
  dScalar dEinstein contracted_bianchi signed_einstein_divergence
  lorentzian_metric_divergence conformal_ricci conformal_scalar
  conformal_einstein_time conformal_einstein_spatial)
open KFCausalCSpecRSSConformal (Vg taug)
open KFCausalConformal4DCurvatureExpansion (geometric_remainder_bound
  temporal_curvature_benchmark)
open KFCausalBDG4DTemporalCurvatureLimit (scalar_curvature_derivative)
open KFCausalBDG4DActualTemporalVariation (operator actual_derivative_tendsto
  actual_derivative_matches_curvature)

/-- Weighted trace `∑ b, w b * G_{bb}` of the algebraic Einstein tensor for
metric second-derivative jet data `md`. -/
def einsteinTrace {n : ℕ} (md : MetricDerivs n) (w : Fin n → ℝ) : ℝ :=
  ∑ b, w b * einstein md w b b

/-- Weighted trace `∑ b, w b * ∂_e G_{bb}` of the differentiated Einstein tensor
for Riemann Bianchi data `rd`. -/
def dEinsteinTrace {n : ℕ} (rd : RiemannData n) (w : Fin n → ℝ) (e : Fin n) : ℝ :=
  ∑ b, w b * dEinstein rd w e b b

/-- Components `G_{bd}(0)` of the Einstein tensor of the 4D conformal metric
`Ω² diag(-1,1,1,1)` at the origin. -/
def conformalEinstein (att spatial : ℝ) (b d : Fin 4) : ℝ :=
  einstein (derivativeData att spatial) sign b d

/-- Lorentzian trace `Tr_g(G)(0) = ∑ b, sign b * G_{bb}(0)` of the 4D conformal
Einstein tensor at the origin. -/
def conformalEinsteinTrace (att spatial : ℝ) : ℝ :=
  einsteinTrace (derivativeData att spatial) sign

/-- Temporal conformal specialization `Tr_g(G)(0)` at `(att, spatial) = (2c, 0)`. -/
def temporalEinsteinTrace (c : ℝ) : ℝ :=
  conformalEinsteinTrace (2 * c) 0

/-- Full two-index inverse-metric contraction `g^{ab}(0) G_{ab}(0)` at the
origin of the 4D conformal spacetime. -/
def inverseMetricEinsteinTrace (att spatial : ℝ) : ℝ :=
  ∑ a : Fin 4, ∑ b : Fin 4,
    inverseMetric att spatial 0 a b * conformalEinstein att spatial a b

theorem einsteinTrace_formula {n : ℕ} (md : MetricDerivs n) (w : Fin n → ℝ)
    (hw : ∀ b, w b * w b = 1) :
    einsteinTrace md w = scalar md w - ((n : ℝ) / 2) * scalar md w := by
  have hterm (b : Fin n) :
      w b * einstein md w b b = w b * ricci md w b b - scalar md w / 2 := by
    simp only [einstein, if_true]
    calc w b * (ricci md w b b - scalar md w / 2 * w b)
        = w b * ricci md w b b - (w b * w b) * (scalar md w / 2) := by ring
      _ = w b * ricci md w b b - scalar md w / 2 := by rw [hw b, one_mul]
  unfold einsteinTrace
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold scalar
  simp only [nsmul_eq_mul]
  ring

theorem dEinsteinTrace_formula {n : ℕ} (rd : RiemannData n) (w : Fin n → ℝ)
    (hw : ∀ b, w b * w b = 1) (e : Fin n) :
    dEinsteinTrace rd w e = dScalar rd w e - ((n : ℝ) / 2) * dScalar rd w e := by
  have hterm (b : Fin n) :
      w b * dEinstein rd w e b b = w b * dRic rd w e b b - dScalar rd w e / 2 := by
    simp only [dEinstein, if_true]
    calc w b * (dRic rd w e b b - dScalar rd w e / 2 * w b)
        = w b * dRic rd w e b b - (w b * w b) * (dScalar rd w e / 2) := by ring
      _ = w b * dRic rd w e b b - dScalar rd w e / 2 := by rw [hw b, one_mul]
  unfold dEinsteinTrace
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold dScalar
  simp only [nsmul_eq_mul]
  ring

private theorem sign_sq_one (b : Fin 4) : sign b * sign b = 1 := by
  simp only [sign]
  split_ifs <;> norm_num

theorem lorentzian_einsteinTrace_eq_neg_scalar (md : MetricDerivs 4) :
    einsteinTrace md sign = scalar md sign - (4 / 2) * scalar md sign ∧
    einsteinTrace md sign = -scalar md sign := by
  have h1 := einsteinTrace_formula md sign sign_sq_one
  norm_num at h1
  exact ⟨by linarith, by linarith⟩

/-- In 4D Lorentzian signature, the trace of the differentiated Einstein tensor
equals `-dScalar = -2 * divRic` by the contracted Bianchi identity, while its
divergence vanishes identically. -/
theorem lorentzian_dEinsteinTrace_bianchi (rd : RiemannData 4) (e : Fin 4) :
    dEinsteinTrace rd sign e = -dScalar rd sign e ∧
    dEinsteinTrace rd sign e = -2 * divRic rd sign e ∧
    (∑ a, sign a * dEinstein rd sign a e a) = 0 := by
  have htr := dEinsteinTrace_formula rd sign sign_sq_one e
  norm_num at htr
  have h1 : dEinsteinTrace rd sign e = -dScalar rd sign e := by linarith
  have hcb := contracted_bianchi rd sign e
  have h2 : dEinsteinTrace rd sign e = -2 * divRic rd sign e := by linarith
  have hdiv := signed_einstein_divergence rd sign sign_sq_one e
  exact ⟨h1, h2, hdiv⟩

theorem conformalEinsteinTrace_eq (att spatial : ℝ) :
    conformalEinsteinTrace att spatial =
      KFCausalConformal4DDiamondBenchmark.scalar att spatial -
        (4 / 2) * KFCausalConformal4DDiamondBenchmark.scalar att spatial ∧
    conformalEinsteinTrace att spatial =
      -KFCausalConformal4DDiamondBenchmark.scalar att spatial ∧
    conformalEinsteinTrace att spatial = -6 * att + 18 * spatial := by
  have h := lorentzian_einsteinTrace_eq_neg_scalar (derivativeData att spatial)
  unfold conformalEinsteinTrace
  rw [conformal_scalar] at h
  have h3 : conformalEinsteinTrace att spatial = -6 * att + 18 * spatial := by
    unfold conformalEinsteinTrace
    rw [h.2, KFCausalConformal4DDiamondBenchmark.scalar_curvature]
    ring
  exact ⟨h.1, h.2, h3⟩

theorem inverseMetricEinsteinTrace_eq (att spatial : ℝ) :
    inverseMetricEinsteinTrace att spatial = conformalEinsteinTrace att spatial := by
  unfold inverseMetricEinsteinTrace conformalEinsteinTrace einsteinTrace conformalEinstein
  simp only [inverseMetric, omega, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, zero_div, add_zero, one_pow, inv_one, one_mul, eta, ite_mul, zero_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]

theorem temporal_conformal_einstein_components (c : ℝ) :
    conformalEinstein (2 * c) 0 0 0 = 0 ∧
    ∀ i : Fin 4, i ≠ 0 → conformalEinstein (2 * c) 0 i i = -4 * c := by
  refine ⟨?_, ?_⟩
  · unfold conformalEinstein
    rw [conformal_einstein_time]
    ring
  · intro i hi
    unfold conformalEinstein
    rw [conformal_einstein_spatial (2 * c) 0 i hi]
    ring

theorem temporalEinsteinTrace_eq (c : ℝ) :
    temporalEinsteinTrace c =
      KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 -
        (4 / 2) * KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 ∧
    temporalEinsteinTrace c =
      -KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 ∧
    temporalEinsteinTrace c = -12 * c := by
  have h := conformalEinsteinTrace_eq (2 * c) 0
  unfold temporalEinsteinTrace
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2]
  ring

/-- The 4D conformal curvature benchmark quantities (`R₀₀ = -6c`, `R = 12c`,
and the diamond volume defect coefficient `-R/180 + R₀₀/30 = -4c/15`) expressed
in terms of the Lorentzian Einstein trace `Tr_g(G) = -12c`. -/
theorem temporal_curvature_expansion_from_einsteinTrace (c : ℝ) :
    KFCausalConformal4DDiamondBenchmark.ricci (2 * c) 0 0 0 =
      (1 / 2) * temporalEinsteinTrace c ∧
    KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 =
      -temporalEinsteinTrace c ∧
    (-KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 / 180 +
        KFCausalConformal4DDiamondBenchmark.ricci (2 * c) 0 0 0 / 30) =
      (1 / 45) * temporalEinsteinTrace c := by
  have hb := temporal_curvature_benchmark c
  have htr := (temporalEinsteinTrace_eq c).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [hb.1, htr]; ring
  · rw [hb.2.1, htr]; ring
  · rw [hb.2.2, htr]; ring

/-- Proper-time causal-diamond volume remainder bound expressed directly in
terms of the Lorentzian Einstein tensor trace `temporalEinsteinTrace c`. -/
theorem geometric_remainder_bound_in_einsteinTrace (c T lam : ℝ)
    (hT : 0 < T) (hlam : 0 < lam)
    (hc : |2 * c| ≤ 1 / lam ^ 2) (hTlam : T ≤ lam / 2) :
    |Vg (2 * c) 0 T / ((π / 24) * taug (2 * c) T ^ 4) - 1 -
      ((1 / 45) * temporalEinsteinTrace c) * taug (2 * c) T ^ 2| ≤
        1557 * taug (2 * c) T ^ 4 / lam ^ 4 := by
  have h0 : |(0 : ℝ)| ≤ 1 / lam ^ 2 := by
    rw [abs_zero]
    positivity
  have hrem := geometric_remainder_bound (2 * c) 0 T lam hT hlam hc h0 hTlam
  rwa [(temporal_curvature_expansion_from_einsteinTrace c).2.2] at hrem

theorem temporalEinsteinTrace_hasDerivAt :
    HasDerivAt temporalEinsteinTrace (-12) 0 := by
  have heq : temporalEinsteinTrace =
      fun c => -KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0 :=
    funext (fun c => (temporalEinsteinTrace_eq c).2.1)
  rw [heq]
  exact scalar_curvature_derivative.neg

theorem temporalEinsteinTrace_deriv_zero :
    deriv temporalEinsteinTrace 0 =
      -deriv (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0) 0 ∧
    deriv temporalEinsteinTrace 0 = -12 ∧
    deriv temporalEinsteinTrace 0 = 2 * (-6) := by
  have hd := temporalEinsteinTrace_hasDerivAt.deriv
  have hs := scalar_curvature_derivative.deriv
  refine ⟨?_, hd, ?_⟩
  · linarith
  · linarith

theorem half_temporalEinsteinTrace_deriv_zero :
    (1 / 2) * deriv temporalEinsteinTrace 0 =
      -(1 / 2) * deriv (fun c => KFCausalConformal4DDiamondBenchmark.scalar (2 * c) 0) 0 ∧
    (1 / 2) * deriv temporalEinsteinTrace 0 = -6 := by
  have h := temporalEinsteinTrace_deriv_zero
  refine ⟨?_, ?_⟩
  · linarith [h.1]
  · linarith [h.2.1]

/-- The causal-diamond BDG temporal variation limit `-6` as `rho → ∞` equals
`(1/2) d/dc Tr_g(G)|_{c=0}`. -/
theorem bdg_temporal_variation_tendsto_half_einsteinTrace_deriv :
    Tendsto (fun rho => deriv (operator rho) 0) atTop
      (𝓝 ((1 / 2) * deriv temporalEinsteinTrace 0)) := by
  rw [half_temporalEinsteinTrace_deriv_zero.1]
  exact actual_derivative_matches_curvature

/-- Small-scale `ε → 0⁺` continuum limit of the causal-diamond BDG temporal
variation to `(1/2) d/dc Tr_g(G)|_{c=0} = -6`. -/
theorem bdg_temporal_variation_scale_tendsto_half_einsteinTrace_deriv :
    Tendsto (fun ε : ℝ => deriv (operator ε⁻¹) 0) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 / 2) * deriv temporalEinsteinTrace 0)) ∧
    Tendsto (fun ε : ℝ => deriv (operator ε⁻¹) 0) (𝓝[>] (0 : ℝ))
      (𝓝 (-6)) := by
  refine ⟨bdg_temporal_variation_tendsto_half_einsteinTrace_deriv.comp
    tendsto_inv_nhdsGT_zero,
    actual_derivative_tendsto.comp tendsto_inv_nhdsGT_zero⟩

#print axioms einsteinTrace_formula
#print axioms dEinsteinTrace_formula
#print axioms lorentzian_einsteinTrace_eq_neg_scalar
#print axioms lorentzian_dEinsteinTrace_bianchi
#print axioms conformalEinsteinTrace_eq
#print axioms inverseMetricEinsteinTrace_eq
#print axioms temporal_conformal_einstein_components
#print axioms temporalEinsteinTrace_eq
#print axioms temporal_curvature_expansion_from_einsteinTrace
#print axioms geometric_remainder_bound_in_einsteinTrace
#print axioms temporalEinsteinTrace_hasDerivAt
#print axioms temporalEinsteinTrace_deriv_zero
#print axioms half_temporalEinsteinTrace_deriv_zero
#print axioms bdg_temporal_variation_tendsto_half_einsteinTrace_deriv
#print axioms bdg_temporal_variation_scale_tendsto_half_einsteinTrace_deriv

end
end UnifiedTheory.Audit.KFCausalConformal4DLorentzianBianchiTraceSynthesis
