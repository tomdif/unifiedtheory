/- Classical derivatives of actual mixed representatives attach to the
original maximal symmetric momenta. L2 membership comes from the already
constructed Hilbert outputs, with exact inverse chart and clock weight. -/
import UnifiedTheory.Audit.KFCausalMixedInverseRepresentative
import UnifiedTheory.Audit.KFCausalSymmetricMixedTranslation
import UnifiedTheory.Audit.KFCausalL2DirectionalDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalSymmetricMixedDerivativeGraph
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection symmetricVector)
open KFCausalSymmetricMixedTranslation (velocity)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalMixedInverseRepresentative
open KFCausalDirectionalTranslationMomentum (spectralMomentum multiplier multiplier_measurable)
open KFCausalUnitaryRealMultiplier (realPullback_graph)

variable (ε : ℝ) (hε : 0 < ε) (i : Fin 2)

theorem mixedForward_translate (z : Joint 2 4) (t : ℝ) :
    let x := (split 2 4).symm (mixedForward ε (split 2 4 z))
    mixedForward ε (split 2 4 (z+t • symmetricVector i))=
      split 2 4 (x+t • velocity ε hε i (x (.inr 0))) := by
  dsimp only
  let x := (split 2 4).symm (mixedForward ε (split 2 4 z))
  have hx : split 2 4 x=mixedForward ε (split 2 4 z) :=
    (split 2 4).apply_symm_apply _
  have hm : (split 2 4).symm (mixedMap ε hε (split 2 4 x))=z := by
    rw [hx,mixedMap_mixedForward ε hε,MeasurableEquiv.symm_apply_apply]
  have ht := KFCausalSymmetricMixedTranslation.mixedMap_translate ε hε i t x
  rw [hm] at ht
  have he := congrArg (fun y => mixedForward ε (split 2 4 y)) ht
  simpa only [MeasurableEquiv.apply_symm_apply,mixedForward_mixedMap ε hε] using he.symm

theorem chargeProfile_lineDeriv (ρ σ : Block 2 × Block 4 → ℂ)
    (hder : ∀ x : Joint 2 4,
      HasDerivAt (fun t : ℝ => ρ (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))))
        (σ (split 2 4 x)) 0) (z : Joint 2 4) :
    HasLineDerivAt ℝ (chargeProfile ε ρ) (chargeProfile ε σ z) z (symmetricVector i) := by
  let x := (split 2 4).symm (mixedForward ε (split 2 4 z))
  have hc (t : ℝ) : (split 2 4 (z+t • symmetricVector i)).2 0=(split 2 4 z).2 0 := by
    change (z+t • symmetricVector i) (.inr 0)=z (.inr 0)
    have hz : symmetricVector i (.inr 0)=0 := by fin_cases i <;> rfl
    simp only [PiLp.add_apply,PiLp.smul_apply,hz,smul_zero,add_zero]
  have he (t : ℝ) : chargeProfile ε ρ (z+t • symmetricVector i)=
      (Real.sqrt (Real.exp ((split 2 4 z).2 0)+ε):ℂ)*
        ρ (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))) := by
    unfold chargeProfile inverseProfile
    rw [hc,mixedForward_translate ε hε i z t]
  change HasDerivAt (fun t : ℝ => chargeProfile ε ρ (z+t • symmetricVector i))
    (chargeProfile ε σ z) 0
  convert (hder x).const_mul (Real.sqrt (Real.exp ((split 2 4 z).2 0)+ε):ℂ) using 1
  · funext t
    exact he t

theorem derivative_graph (h : ℝ) (hh : h ≠ 0) (f d : Hilbert)
    (ρ σ : Block 2 × Block 4 → ℂ)
    (hf : clockMixed ε hε f =ᵐ[volume] ρ)
    (hd : clockMixed ε hε d =ᵐ[volume] σ)
    (hder : ∀ x : Joint 2 4,
      HasDerivAt (fun t : ℝ => ρ (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))))
        (σ (split 2 4 x)) 0) :
    (f,(-Complex.I*(h:ℂ)) • d) ∈ (transverseMomentum h (symmetricDirection i)).graph := by
  have hF := chargeProfile_memLp ε hε f ρ hf
  have hD := chargeProfile_memLp ε hε d σ hd
  have hfe : hF.toLp (chargeProfile ε ρ)=chargeCoordinates f :=
    Lp.ext (hF.coeFn_toLp.trans (charge_representative ε hε f ρ hf).symm)
  have hde : hD.toLp (chargeProfile ε σ)=chargeCoordinates d :=
    Lp.ext (hD.coeFn_toLp.trans (charge_representative ε hε d σ hd).symm)
  apply (KFCausalSymmetricMomentumGraphEquivalence.symmetric_graph_iff h hh i _ _).mpr
  rw [map_smul,← hfe,← hde]
  apply (realPullback_graph _ _ _ _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (-Complex.I*(h:ℂ))
    ((Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (hD.toLp (chargeProfile ε σ))),
    KFCausalL2DirectionalDerivative.derivative_fourier _ _ _ hF hD
      (chargeProfile_lineDeriv ε hε i ρ σ hder)] with y hy hdy
  rw [hy]
  simp only [Pi.smul_apply,smul_eq_mul,hdy,multiplier,
    Complex.ofReal_mul,Complex.ofReal_ofNat]
  calc
    _ = -(Complex.I*Complex.I)*(2*(Real.pi:ℂ)*(h:ℂ)*
      (inner ℝ y (symmetricVector i):ℂ)*
        ((Lp.fourierTransformₗᵢ (Joint 2 4) ℂ) (hF.toLp (chargeProfile ε ρ))) y) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem second_derivative_graph (h : ℝ) (hh : h ≠ 0) (f d d₂ : Hilbert)
    (ρ σ τ : Block 2 × Block 4 → ℂ)
    (hf : clockMixed ε hε f =ᵐ[volume] ρ)
    (hd : clockMixed ε hε d =ᵐ[volume] σ)
    (hd₂ : clockMixed ε hε d₂ =ᵐ[volume] τ)
    (hder : ∀ x : Joint 2 4,
      HasDerivAt (fun t : ℝ => ρ (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))))
        (σ (split 2 4 x)) 0)
    (hder₂ : ∀ x : Joint 2 4,
      HasDerivAt (fun t : ℝ => σ (split 2 4 (x+t • velocity ε hε i (x (.inr 0)))))
        (τ (split 2 4 x)) 0) :
    (f,(-Complex.I*(h:ℂ)) • d) ∈ (transverseMomentum h (symmetricDirection i)).graph ∧
    ((-Complex.I*(h:ℂ)) • d,(-(h:ℂ)^2) • d₂) ∈
      (transverseMomentum h (symmetricDirection i)).graph := by
  refine ⟨derivative_graph ε hε i h hh f d ρ σ hf hd hder,?_⟩
  have hg := (transverseMomentum h (symmetricDirection i)).graph.smul_mem (-Complex.I*(h:ℂ))
    (derivative_graph ε hε i h hh d d₂ σ τ hd hd₂ hder₂)
  have he : (-Complex.I*(h:ℂ))*(-Complex.I*(h:ℂ))=-(h:ℂ)^2 := by
    calc
      _ = (Complex.I*Complex.I)*(h:ℂ)^2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  simpa only [Prod.smul_mk,smul_smul,he] using hg

#print axioms mixedForward_translate
#print axioms chargeProfile_lineDeriv
#print axioms derivative_graph
#print axioms second_derivative_graph
end
end UnifiedTheory.Audit.KFCausalSymmetricMixedDerivativeGraph
