/- Actual clock differentiation of each full Joint channel. Compact
Gaussian envelopes are derived from the original physical width floor;
coefficients are fixed for this geometric derivative. -/
import UnifiedTheory.Audit.KFCausalFiniteChannelCoolingSplit
import UnifiedTheory.Audit.KFCausalQuarticResponseClockCoefficients

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalFiniteChannelJointClockDerivative
noncomputable section
open MeasureTheory Filter
open scoped Topology ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalClockFloorRelativeShift (scale scale_smooth)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalFiniteNeutralResponseIntegrability (value slope channelResponse)
open KFCausalClusteredClockFactors (limitFactor limitSlope)

variable (n : ℕ) (α β ε y : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hα : 0<α) (hβ : 0<β) (hwidth : 32*β≤α)
  (hε : 0<ε) (hy : |y|≤Real.pi*ε/3) (hw : ∀i,1≤w i)

include hα hβ hwidth hε hy hw in
private theorem uniform_floors (i : Fin n) (s : ℝ) :
    α/4≤(w i*α)*area (scale ε y s) ∧
    α/4≤(w i*α)*area (scale ε y s)-8*β*(scale ε y s).im^2 := by
  have hA := KFCausalClockFloorExactScaleRegion.square_re_half_le ε y s hε hy
  have hb := KFCausalClockFloorExactScaleRegion.imaginary_square_le_half ε y s hε hy
  have hwa : α≤w i*α := by nlinarith [hw i]
  have hwap : 0≤w i*α := by linarith
  have hbase : α/2≤(w i*α)*area (scale ε y s) := by
    unfold area
    nlinarith [mul_nonneg hwap (sub_nonneg.mpr hA)]
  constructor <;> nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hb)]

private theorem single_bound (j : ℕ) (α β : ℝ) (r rd b : ℂ)
    (P : Polynomial ℂ) (p : Joint) (hz : 0≤(KFCausalClusteredClockFactors.Z α r p).re) :
    ‖limitFactor 0 j α β r b P p‖^2+‖limitSlope 0 j α β r rd b P p‖^2≤
      KFCausalClusteredClockEnvelope.componentBound 0 j α β r rd b P p := by
  have he := KFCausalCorrelatedClusteredBounds.single_pair_bound 0 j α β 1 (by norm_num)
    r rd b P p hz
  simpa only [KFCausalClusteredClockFactors.factor,KFCausalClusteredClockFactors.slope,
    limitFactor,limitSlope,KFCausalClusteredClockFactors.B1,Nat.cast_zero,zero_mul,mul_zero,
    pow_zero,mul_one,add_zero,one_mul] using he

include hα hβ hwidth hε hy hw in
theorem compact_envelope (j : ℕ) (K : Set ℝ) (hK : IsCompact K) :
    ∃ D : Joint→ℝ,Integrable D jointMeasure ∧ (∀p,0≤D p) ∧
      ∀s∈K,∀p,0≤p.2→
      ‖value n α β w b c P j (scale ε y s) p‖^2+
      ‖slope n α β w b c P j (scale ε y s) (deriv (scale ε y) s) p‖^2≤D p := by
  have hr := (scale_smooth ε y hε hy).continuous
  have hd := (scale_smooth ε y hε hy).continuous_deriv_one
  have hone (i : Fin n) := KFCausalClusteredClockCompactEnvelope.componentBound_envelope
    K hK 0 j (w i*α) β (α/4) (scale ε y) (deriv (scale ε y)) hr hd (b i) (P i)
    hβ (by positivity) (fun s _=>(uniform_floors n α β ε y w hα hβ hwidth hε hy hw i s).1)
    (fun s _=>(uniform_floors n α β ε y w hα hβ hwidth hε hy hw i s).2)
  choose D hDi hD0 hD using hone
  refine ⟨fun p=>(n:ℝ)*∑i,‖c i*(w i:ℂ)‖^2*D i p,
    (integrable_finset_sum _ (fun i _=>(hDi i).const_mul _)).const_mul _,?_,?_⟩
  · intro p
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _=>mul_nonneg (sq_nonneg _) (hD0 i p)))
  · intro s hs p hp
    have hbnd (i : Fin n) :
        ‖limitFactor 0 j (w i*α) β (scale ε y s) (b i) (P i) p‖^2+
        ‖limitSlope 0 j (w i*α) β (scale ε y s) (deriv (scale ε y) s) (b i) (P i) p‖^2≤D i p := by
      apply (single_bound j (w i*α) β _ _ _ _ p ?_).trans (hD i s hs p hp)
      rw [KFCausalClusteredClockFactors.Z,KFCausalReciprocalWedgeGeometry.chart_re]
      have ha := (uniform_floors n α β ε y w hα hβ hwidth hε hy hw i s).1
      have hpos : 0≤(w i*α)*area (scale ε y s) := by linarith
      positivity
    exact KFCausalCorrelatedClusteredBounds.sum_pair_bound n (fun i=>c i*(w i:ℂ)) _ _ _ hbnd

include hα hβ hwidth hε hy hw in
theorem channel_integral_derivative (j : ℕ) (s : ℝ) :
    HasDerivAt (fun t=>∫p,‖value n α β w b c P j (scale ε y t) p‖^2 ∂jointMeasure)
      (∫p,channelResponse n α β w b c P j (scale ε y s)
        (deriv (scale ε y) s) p ∂jointMeasure) s := by
  obtain ⟨D,hDi,hD0,hD⟩ := compact_envelope n α β ε y w b c P hα hβ hwidth hε hy hw
    j (Set.Icc (s-1) (s+1)) isCompact_Icc
  have hcont (t : ℝ) := KFCausalFiniteNeutralResponseIntegrability.value_continuous n α β w b c P j (scale ε y t)
  have hresp (t : ℝ) : Continuous (channelResponse n α β w b c P j (scale ε y t) (deriv (scale ε y) t)) :=
    continuous_const.mul (Complex.continuous_re.comp ((Complex.continuous_conj.comp (hcont t)).mul
      (KFCausalFiniteNeutralResponseIntegrability.slope_continuous n α β w b c P j _ _)))
  have hs : s∈Set.Icc (s-1) (s+1) := by constructor <;> linarith
  have hi : Integrable (fun p=>‖value n α β w b c P j (scale ε y s) p‖^2) jointMeasure := by
    apply hDi.mono' ((hcont s).norm.pow 2).aestronglyMeasurable
    filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans (hD s hs p hp)
  have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=fun t p=>‖value n α β w b c P j (scale ε y t) p‖^2)
    (F':=fun t p=>channelResponse n α β w b c P j (scale ε y t) (deriv (scale ε y) t) p)
    (bound:=D) (μ:=jointMeasure)
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Eventually.of_forall (fun t=>((hcont t).norm.pow 2).aestronglyMeasurable)) hi
    (hresp s).aestronglyMeasurable ?_ hDi ?_
  · exact he.2
  · filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
    intro t ht
    exact (KFCausalCorrelatedClusteredBounds.cross_bound _ _).trans (hD t ht p hp)
  · refine Eventually.of_forall (fun p t _=>?_)
    exact KFCausalNeutralQuarticBoundary.norm_square_derivative
      (fun x=>value n α β w b c P j (scale ε y x) p)
      (fun x=>slope n α β w b c P j (scale ε y x) (deriv (scale ε y) x) p) t
      (KFCausalFiniteNeutralResponseIntegrability.value_derivative n α β w b c P j
        (scale ε y) (deriv (scale ε y) t) t p
        (((scale_smooth ε y hε hy).differentiable (by norm_num)).differentiableAt.hasDerivAt))

include hα hβ hwidth hε hy hw in
theorem spatial_integral_derivative (j : ℕ) (s : ℝ) :
    HasDerivAt (fun t=>∫p:Joint,KFCausalJointFourierDilationRepresentation.fieldDensity
      n α β w b c P (scale ε y t) 0 0 j p ∂jointMeasure)
      (∫p:Joint,KFCausalJointNeutralFourierOuterDensity.spatialFieldResponse n α β w b c P
        (scale ε y s) (deriv (scale ε y) s) p.1.1 (p.1.2 0) p.2 j (p.1.2 1) ∂jointMeasure) s := by
  simp_rw [KFCausalFiniteChannelCoolingSplit.density_eq,KFCausalFiniteChannelCoolingSplit.spatial_response_eq]
  exact channel_integral_derivative n α β ε y w b c P hα hβ hwidth hε hy hw j s

#print axioms compact_envelope
#print axioms channel_integral_derivative
#print axioms spatial_integral_derivative
end
end UnifiedTheory.Audit.KFCausalFiniteChannelJointClockDerivative
