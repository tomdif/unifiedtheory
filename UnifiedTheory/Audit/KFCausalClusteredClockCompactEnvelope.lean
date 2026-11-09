/- Common integrable envelopes for the full density derivative on compact
clock sets, uniform over every positive charged-width spacing. -/
import UnifiedTheory.Audit.KFCausalJointUniformWeightEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalClusteredClockCompactEnvelope
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalJointCompactPolynomialBounds
open KFCausalClusteredClockFactors
open KFCausalClusteredClockDensity
open KFCausalClusteredClockEnvelope
open KFCausalClusteredWidthDensityIntegrability (factorPolynomial)
open KFCausalJointPolynomialIntegrability (coordinates)
open KFCausalReciprocalGaussianCoordinates (area)

variable {X : Type*} [TopologicalSpace X]

theorem polynomials_controlled (K : Set X) (hK : IsCompact K) (n k : ℕ) (α β : ℝ)
    (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v) (b : ℂ) (P : Polynomial ℂ) :
    Controlled K (fun s p => MvPolynomial.eval (coordinates p) (factorPolynomial n k α (r s) P)) ∧
    Controlled K (fun s p => MvPolynomial.eval (coordinates p) (slopePolynomial0 n k α β (r s) (v s) b P)) ∧
    Controlled K (fun s p => MvPolynomial.eval (coordinates p) (slopePolynomial1 n k α (r s) (v s) P)) := by
  have co (f : X → ℂ) (hf : Continuous f) := controlled_coefficient K hK f hf.continuousOn
  have cx (i : Fin 4) := controlled_coordinate K i
  have hz : Controlled K (fun s p => Z α (r s) p) := by
    simpa only [Z,KFCausalReciprocalWedgeGeometry.chart,Complex.ofReal_add,Complex.ofReal_pow,
      coords,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one] using
      ((co (fun s => KFCausalReciprocalWedgeGeometry.gamma α (r s)) (by
        unfold KFCausalReciprocalWedgeGeometry.gamma; fun_prop)).mul ((cx 0).pow 2 |>.add ((cx 1).pow 2))).add
        ((co (fun s => conj (KFCausalReciprocalWedgeGeometry.gamma α (r s))) (by
          unfold KFCausalReciprocalWedgeGeometry.gamma; fun_prop)).mul (cx 3))
  have hzd : Controlled K (fun s p => Zd α (r s) (v s) p) := by
    simpa [Zd,coords] using
      ((co (fun s => (α:ℂ)*r s*v s) (by fun_prop)).mul ((cx 0).pow 2 |>.add ((cx 1).pow 2))).add
        ((co (fun s => conj ((α:ℂ)*r s*v s)) (by fun_prop)).mul (cx 3))
  have hn : Controlled K (fun s p => N (r s) p) := by
    simpa [N,KFCausalReciprocalNeutralKernel.neutral,coords] using
      (cx 2).add ((co (fun s => 2*((r s).im:ℂ)*Complex.I) (by fun_prop)).mul (cx 1))
  have hnd : Controlled K (fun s p => Nd (v s) p) := by
    simpa [Nd,coords] using (co (fun s => 2*((v s).im:ℂ)*Complex.I) (by fun_prop)).mul (cx 1)
  have hf : Controlled K (fun s p => (F (r s) p:ℂ)) := by
    simpa [F,coords] using (cx 2).add
      ((co (fun s => (KFCausalChargedPairCoordinates.fieldSlope (r s):ℂ)) (by
        unfold KFCausalChargedPairCoordinates.fieldSlope; fun_prop)).mul (cx 1))
  have hfd : Controlled K (fun s p => (Fd (v s) p:ℂ)) := by
    simpa [Fd,coords] using (co (fun s => ((-2*(v s).re:ℝ):ℂ)) (by fun_prop)).mul (cx 1)
  have he : Controlled K (fun s p => Ed α β (r s) (v s) b p) := by
    have hg := (co (fun s => ((8*β*(r s).im*(v s).im:ℝ):ℂ)) (by fun_prop)).mul ((cx 1).pow 2)
    simpa [Ed,Gd,coords] using (hzd.neg.add hg).add ((controlled_const K b).mul hnd)
  have hb0 : Controlled K (fun s p => B0 k α β (r s) (v s) b P p) :=
    ((((controlled_const K (k:ℂ)).mul (hf.pow (k-1))).mul hfd).mul (hn.eval P)).add
      ((hf.pow k).mul (((hn.eval P.derivative).mul hnd).add (he.mul (hn.eval P))))
  have hb1 : Controlled K (fun s p => B1 n k α (r s) (v s) P p) :=
    (((controlled_const K (n:ℂ)).mul (hf.pow k)).mul hzd).mul (hn.eval P)
  constructor
  · simpa only [KFCausalClusteredWidthDensityIntegrability.factorPolynomial_eval] using
      ((hf.pow k).mul (hz.pow n)).mul (hn.eval P)
  · exact ⟨by simpa only [slopePolynomial0_eval] using (hz.pow n).mul hb0,
      by simpa only [slopePolynomial1_eval] using (hz.pow (n-1)).mul hb1⟩

theorem componentBound_envelope (K : Set X) (hK : IsCompact K) (n k : ℕ) (α β q : ℝ)
    (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ s ∈ K, q ≤ α*area (r s))
    (hc : ∀ s ∈ K, q ≤ α*area (r s)-8*β*(r s).im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 → componentBound n k α β (r s) (v s) b P p ≤ D p := by
  have hs := polynomials_controlled K hK n k α β r v hr hv b P
  have envelope (f : X → Joint → ℂ) (hf : Controlled K f) :=
    KFCausalJointUniformWeightEnvelope.controlled_square_envelope K hK f hf
      (fun s => α*area (r s)) (fun s => α*area (r s)-8*β*(r s).im^2)
      (fun s => -4*b.im*(r s).im) (by fun_prop) (2*β) (2*b.re) q (by positivity) hq ha hc
  obtain ⟨A,hAi,hA0,hA⟩ := envelope _ hs.1
  obtain ⟨B,hBi,hB0,hB⟩ := envelope _ hs.2.1
  obtain ⟨C,hCi,hC0,hC⟩ := envelope _ hs.2.2
  refine ⟨fun p => A p+2*B p+2*C p,(hAi.add (hBi.const_mul 2)).add (hCi.const_mul 2),
    fun p => by have := hA0 p; have := hB0 p; have := hC0 p; positivity, ?_⟩
  intro s hs p hp
  have h0 := hA s hs p hp
  have h1 := hB s hs p hp
  have h2 := hC s hs p hp
  unfold componentBound KFCausalClusteredWidthDensityIntegrability.weight
  linarith

theorem responseBound_envelope (K : Set X) (hK : IsCompact K) (n : ℕ) (α β q : ℝ)
    (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ s ∈ K, q ≤ α*area (r s))
    (hc : ∀ s ∈ K, q ≤ α*area (r s)-8*β*(r s).im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 → responseBound n α β (r s) (v s) b P p ≤ D p := by
  obtain ⟨A,hAi,hA0,hA⟩ := componentBound_envelope K hK n 0 α β q r v hr hv b P hβ hq ha hc
  obtain ⟨B,hBi,hB0,hB⟩ := componentBound_envelope K hK n 1 α β q r v hr hv b P hβ hq ha hc
  obtain ⟨C,hCi,hC0,hC⟩ := componentBound_envelope K hK n 2 α β q r v hr hv b P hβ hq ha hc
  refine ⟨fun p => A p+B p/2+C p/4,(hAi.add (hBi.div_const 2)).add (hCi.div_const 4),
    fun p => by have := hA0 p; have := hB0 p; have := hC0 p; positivity, ?_⟩
  intro s hs p hp
  unfold responseBound
  exact add_le_add (add_le_add (hA s hs p hp) (div_le_div_of_nonneg_right (hB s hs p hp) (by norm_num)))
    (div_le_div_of_nonneg_right (hC s hs p hp) (by norm_num))

theorem response_common_envelope (K : Set X) (hK : IsCompact K) (n : ℕ) (α β q : ℝ)
    (r v : X → ℂ) (hr : Continuous r) (hv : Continuous v) (b : ℂ) (P : Polynomial ℂ)
    (hβ : 0 < β) (hq : 0 < q) (ha : ∀ s ∈ K, q ≤ α*area (r s))
    (hc : ∀ s ∈ K, q ≤ α*area (r s)-8*β*(r s).im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ s ∈ K, ∀ p, 0 ≤ p.2 →
        (∀ δ : ℝ, 0 < δ → ‖response n α β δ (r s) (v s) b P p‖ ≤ D p) ∧
        ‖limitResponse n α β (r s) (v s) b P p‖ ≤ D p := by
  obtain ⟨D,hDi,hD0,hD⟩ := responseBound_envelope K hK n α β q r v hr hv b P hβ hq ha hc
  refine ⟨D,hDi,hD0,?_⟩
  intro s hs p hp
  have hh (δ : ℝ) (hδ : 0 < δ) :=
    (response_norm_le n α β δ hδ (r s) (v s) b P (hq.le.trans (ha s hs)) p hp).trans (hD s hs p hp)
  refine ⟨hh,?_⟩
  apply le_of_tendsto (response_tendsto n α β (r s) (v s) b P p).norm
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hh δ hδ

#print axioms polynomials_controlled
#print axioms componentBound_envelope
#print axioms responseBound_envelope
#print axioms response_common_envelope
end
end UnifiedTheory.Audit.KFCausalClusteredClockCompactEnvelope
