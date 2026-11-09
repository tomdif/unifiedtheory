/- The actual paired squeeze becomes uniform transverse dilation after
the physical partial Fourier transform. The Jacobian gives the exact
half-density exp(-5a/2), on every mixed-coordinate L2 state. -/
import UnifiedTheory.Audit.KFCausalChargeSqueezePairedFlow
import UnifiedTheory.Audit.KFCausalPartialFourierDilation
import UnifiedTheory.Audit.KFCausalL2FourierLinearChange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalChargeSqueezePartialFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalChargeSqueezePairedFlow
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block ProductHilbert)
open UnifiedTheory.Audit.KFCausalPartialFourier (leftFourier)
open UnifiedTheory.Audit.KFCausalPartialFourierSlices (leftIntegral)
open UnifiedTheory.Audit.KFCausalPartialFourierIntegral (leftFourier_toLp_coe)
open UnifiedTheory.Audit.KFCausalPartialFourierDilation (fourier_dilation)
open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative (dense_weighted_representative)

local instance pairedHaar : Measure.IsAddHaarMeasure (volume : Measure Paired) :=
  Measure.prod.instIsAddHaarMeasure _ _

def weighted (t : ℝ) (f : Paired → ℂ) (x : Paired) : ℂ :=
  (Real.exp (-t/2):ℂ)*f (pairFlow 1 t x)

theorem integral_squeeze (t : ℝ) (f : Paired → ℂ) (x : Paired) :
    leftIntegral 2 4 (weighted t f) x =
      (Real.exp (-5*t/2):ℂ)*leftIntegral 2 4 f (pairFlow (-1) t x) := by
  have hscale : (Real.exp t)⁻¹ = Real.exp (-1*t) := by
    rw [← Real.exp_neg,neg_one_mul]
  have he : leftIntegral 2 4 (weighted t f) x =
      (Real.exp (-t/2):ℂ)*(𝓕 (fun a : Block 2 => f (Real.exp t • a,
        rightFlow t x.2))) x.1 := by
    simp only [leftIntegral,weighted,pairFlow,one_mul,Real.fourier_eq,Circle.smul_def,smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext a
    ring
  rw [he,fourier_dilation 2 (fun a => f (a,rightFlow t x.2))
    (Real.exp t) (Real.exp_pos _) x.1]
  simp only [Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,fourier_weight,hscale,leftIntegral,pairFlow]

def transportedSchwartz (t : ℝ) (φ : SchwartzMap Paired ℂ) : SchwartzMap Paired ℂ :=
  (Real.exp (-t/2):ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (pairEquiv 1 t) φ

theorem transportedSchwartz_apply (t : ℝ) (φ : SchwartzMap Paired ℂ) (x : Paired) :
    transportedSchwartz t φ x = weighted t φ x := rfl

theorem paired_schwartz (t : ℝ) (φ : SchwartzMap Paired ℂ) :
    pairedTransport t (φ.toLp 2 volume) = (transportedSchwartz t φ).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [pairedTransport_coe t (φ.toLp 2 volume),
    (pairFlow_quasiMeasurePreserving 1 t).ae (φ.coeFn_toLp 2 (volume : Measure Paired)),
    (transportedSchwartz t φ).coeFn_toLp 2 (volume : Measure Paired)] with x hu hf hg
  rw [hu,hf,hg]
  rfl

theorem transformed_schwartz (t : ℝ) (φ : SchwartzMap Paired ℂ) :
    leftFourier 2 4 (pairedTransport t (φ.toLp 2 volume)) =ᵐ[volume]
      fun x => (Real.exp (-5*t/2):ℂ)*(leftFourier 2 4 (φ.toLp 2 volume)) (pairFlow (-1) t x) := by
  rw [paired_schwartz]
  filter_upwards [leftFourier_toLp_coe 2 4 (transportedSchwartz t φ)
    (transportedSchwartz t φ).continuous (transportedSchwartz t φ).integrable
    ((transportedSchwartz t φ).memLp 2 volume),
    (pairFlow_quasiMeasurePreserving (-1) t).ae
      (leftFourier_toLp_coe 2 4 φ φ.continuous φ.integrable (φ.memLp 2 volume))] with x hu hf
  change (leftFourier 2 4 ((transportedSchwartz t φ).toLp 2 volume)) x = _ at hu
  change (leftFourier 2 4 (φ.toLp 2 volume)) (pairFlow (-1) t x) = _ at hf
  rw [hu,hf]
  exact integral_squeeze t φ x

def mixedTransport (t : ℝ) : ProductHilbert 2 4 ≃ₗᵢ[ℂ] ProductHilbert 2 4 :=
  (leftFourier 2 4).symm.trans ((pairedTransport t).trans (leftFourier 2 4))

private theorem conjugate_dense {X D : Type*} [MeasurableSpace X] {μ : Measure X}
    (j : D → Lp ℂ 2 μ) (hj : DenseRange j)
    (F U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ)
    (e : X → X) (he : Measure.QuasiMeasurePreserving e μ μ) (w : ℂ)
    (hr : ∀ d, F (U (j d)) =ᵐ[μ] fun x => w*F (j d) (e x))
    (f : Lp ℂ 2 μ) :
    (F.symm.trans (U.trans F)) f =ᵐ[μ] fun x => w*f (e x) := by
  let V := F.symm.trans (U.trans F)
  have hd : DenseRange (F ∘ j) := F.surjective.denseRange.comp hj F.continuous
  have hs (d : D) : V ((F ∘ j) d) =ᵐ[μ] fun x => w*((F ∘ j) d) (e x) := by
    simpa only [V,Function.comp_apply,LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply] using hr d
  exact dense_weighted_representative (F ∘ j) hd V V.continuous e he
    (fun _ => w) hs f

theorem mixedTransport_coe (t : ℝ) (f : ProductHilbert 2 4) :
    mixedTransport t f =ᵐ[volume] fun x => (Real.exp (-5*t/2):ℂ)*f (pairFlow (-1) t x) := by
  exact conjugate_dense (fun φ : SchwartzMap Paired ℂ => φ.toLp 2 volume)
    (SchwartzMap.denseRange_toLpCLM (E := Paired) (F := ℂ) (p := 2) (μ := volume) (by norm_num))
    (leftFourier 2 4) (pairedTransport t) (pairFlow (-1) t)
    (pairFlow_quasiMeasurePreserving (-1) t) (Real.exp (-5*t/2):ℂ) (transformed_schwartz t) f

private theorem two_coordinates {H K M : Type*}
    [SeminormedAddCommGroup H] [NormedSpace ℂ H]
    [SeminormedAddCommGroup K] [NormedSpace ℂ K]
    [SeminormedAddCommGroup M] [NormedSpace ℂ M]
    (P : H ≃ₗᵢ[ℂ] K) (F : K ≃ₗᵢ[ℂ] M) (U : H ≃ₗᵢ[ℂ] H) (f : H) :
    (P.trans F) (U f) =
      (F.symm.trans ((P.symm.trans (U.trans P)).trans F)) ((P.trans F) f) := by
  simp only [LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply]

theorem physical_mixed_transport (t : ℝ)
    (f : UnifiedTheory.Audit.KFCausalConfigurationTestSpace.Hilbert) :
    KFCausalPhysicalMixedCoordinates.mixedCoordinates (KFCausalPairedSqueezeTransport.transport t f) =
      mixedTransport t (KFCausalPhysicalMixedCoordinates.mixedCoordinates f) := by
  exact two_coordinates KFCausalPhysicalMixedCoordinates.pairedCoordinates
    (leftFourier 2 4) (KFCausalPairedSqueezeTransport.transport t) f

#print axioms integral_squeeze
#print axioms transportedSchwartz_apply
#print axioms paired_schwartz
#print axioms transformed_schwartz
#print axioms mixedTransport_coe
#print axioms physical_mixed_transport
end
end UnifiedTheory.Audit.KFCausalChargeSqueezePartialFourier
