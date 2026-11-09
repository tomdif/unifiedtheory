/- The completed original integral gives a Hilbert pairing estimate for
the actual projected second outputs and actual static output. This retains
the original finite coherent family; no operator-core extension is assumed. -/
import UnifiedTheory.Audit.KFCausalOrderedStaticIntegratedLower

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalOrderedStaticPotentialHilbertBound
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalFourierGeneralCoordinates (Product)
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalOrderedStaticPotentialPairing (halfOutput sourceProfile field index power)
open KFCausalFiniteSecondHamiltonianColumns (second)
open KFCausalFiniteOrderedStaticOutput (staticOutput)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalOrderedStaticIntegratedLower (originalEnergy)
open KFCausalOrderedStaticTransverseIntegral (originalDensity)
open KFCausalCommonRealGaussianWeightedEnergy (potential)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n→ℝ) (C b : Fin n→ℂ)
  (P : Fin n→Polynomial ℂ) (hε : 0<ε) (ha : ∀i,0<a i)
  (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤ε/10)

def weightedOutput (m g k : ℝ) : Hilbert :=
  (k:ℂ) • zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb (index 0))+
  ((m/2:ℝ):ℂ) • zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb (index 1))+
  ((g/4:ℝ):ℂ) • zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb (index 2))

def weightedEnergy (m g k : ℝ) : ℝ :=
  k*‖halfOutput n ε h a w p C b P hε ha hh hw hb 0‖^2+
  (m/2)*‖halfOutput n ε h a w p C b P hε ha hh hw hb 1‖^2+
  (g/4)*‖halfOutput n ε h a w p C b P hε ha hh hw hb 2‖^2

private theorem power_norm (t : ℝ) (z : ℂ) (j : ℕ) :
    ‖(t:ℂ)^j*z‖^2=t^(2*j)*‖z‖^2 := by
  rw [norm_mul,mul_pow,norm_pow,←pow_mul,mul_comm j 2,pow_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs,←pow_mul]

theorem channel_energy (j : ℕ) :
    Integrable (fun x:Product=>field ε hε x^(2*j)*‖sourceProfile n ε h a w p C b P x‖^2) ∧
    ‖halfOutput n ε h a w p C b P hε ha hh hw hb j‖^2=
      ∫x:Product,field ε hε x^(2*j)*‖sourceProfile n ε h a w p C b P x‖^2 := by
  let u := halfOutput n ε h a w p C b P hε ha hh hw hb j
  have hu := KFCausalOrderedStaticPotentialPairing.halfOutput_coe n ε h a w p C b P
    hε ha hh hw hb j
  have hm := (Lp.memLp (clockMixed ε hε u)).ae_eq hu
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  refine ⟨by simpa only [power_norm] using hi,?_⟩
  calc
    ‖u‖^2=(inner ℂ (clockMixed ε hε u) (clockMixed ε hε u)).re := by
      have hs : (inner ℂ (clockMixed ε hε u) (clockMixed ε hε u)).re=
          ‖clockMixed ε hε u‖^2 := inner_self_eq_norm_sq (𝕜:=ℂ) _
      rw [hs,LinearIsometryEquiv.norm_map]
    _=∫x:Product,field ε hε x^(2*j)*‖sourceProfile n ε h a w p C b P x‖^2 := by
      rw [L2.inner_def]
      have hr : (∫x:Product,inner ℂ ((clockMixed ε hε u) x) ((clockMixed ε hε u) x)).re=
          ∫x:Product,(inner ℂ ((clockMixed ε hε u) x) ((clockMixed ε hε u) x)).re :=
        (integral_re (L2.integrable_inner (𝕜:=ℂ) _ _)).symm
      rw [hr]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
      have hs : (inner ℂ ((field ε hε x:ℂ)^j*sourceProfile n ε h a w p C b P x)
          ((field ε hε x:ℂ)^j*sourceProfile n ε h a w p C b P x)).re=
          ‖(field ε hε x:ℂ)^j*sourceProfile n ε h a w p C b P x‖^2 :=
        inner_self_eq_norm_sq (𝕜:=ℂ) ((field ε hε x:ℂ)^j*sourceProfile n ε h a w p C b P x)
      rw [hs,power_norm]

theorem energy_integral (m g k : ℝ) :
    weightedEnergy n ε h a w p C b P hε ha hh hw hb m g k=
      ∫x:Product,originalEnergy n ε h a w p C b P hε m g k x := by
  have h0 := channel_energy n ε h a w p C b P hε ha hh hw hb 0
  have h1 := channel_energy n ε h a w p C b P hε ha hh hw hb 1
  have h2 := channel_energy n ε h a w p C b P hε ha hh hw hb 2
  unfold weightedEnergy
  rw [h0.2,h1.2,h2.2,←integral_const_mul,←integral_const_mul,←integral_const_mul,
    ←integral_add (h0.1.const_mul k) (h1.1.const_mul (m/2)),
    ←integral_add ((h0.1.const_mul k).add'' (h1.1.const_mul (m/2))) (h2.1.const_mul (g/4))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [originalEnergy,potential]
  ring

theorem pairing_integral (m g k : ℝ) :
    inner ℂ (weightedOutput n ε h a w p C b P hε ha hh hw hb m g k)
      (staticOutput n ε h a w p C b P hε ha hh hw hb)=
      ∫x:Product,originalDensity n ε h a w p C b P hε m g k x := by
  have h0 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 0
  have h2 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 2
  have h4 := KFCausalOrderedStaticPotentialPairing.pairing_integrable n ε h a w p C b P
    hε ha hh hw hb 4
  unfold weightedOutput
  simp only [inner_add_left,inner_smul_left,Complex.conj_ofReal]
  rw [KFCausalOrderedStaticPotentialPairing.projected_pairing_integral,
    KFCausalOrderedStaticPotentialPairing.projected_pairing_integral,
    KFCausalOrderedStaticPotentialPairing.projected_pairing_integral]
  change (k:ℂ)*(∫x:Product,conj ((field ε hε x:ℂ)^0*sourceProfile n ε h a w p C b P x)*
      KFCausalOrderedStaticPotentialPairing.staticProfile n ε h a w p C b P x)+
    ((m/2:ℝ):ℂ)*(∫x:Product,conj ((field ε hε x:ℂ)^2*sourceProfile n ε h a w p C b P x)*
      KFCausalOrderedStaticPotentialPairing.staticProfile n ε h a w p C b P x)+
    ((g/4:ℝ):ℂ)*(∫x:Product,conj ((field ε hε x:ℂ)^4*sourceProfile n ε h a w p C b P x)*
      KFCausalOrderedStaticPotentialPairing.staticProfile n ε h a w p C b P x)=_
  rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,
    ←integral_add (h0.const_mul (k:ℂ)) (h2.const_mul ((m/2:ℝ):ℂ)),
    ←integral_add ((h0.const_mul (k:ℂ)).add'' (h2.const_mul ((m/2:ℝ):ℂ)))
      (h4.const_mul ((g/4:ℝ):ℂ))]
  apply integral_congr_ae
  filter_upwards with x
  simp only [originalDensity,potential,map_mul,map_pow,Complex.conj_ofReal,
    pow_zero,one_mul,Complex.ofReal_add]
  push_cast
  ring

theorem mixed_lower (m g k : ℝ) (hm : 0≤m) (hg : 0≤g) (hk : 0<k) :
    -((2*h^2/ε)*(12+(m+3*g)/k))*weightedEnergy n ε h a w p C b P hε ha hh hw hb m g k≤
      (inner ℂ (weightedOutput n ε h a w p C b P hε ha hh hw hb m g k)
        (staticOutput n ε h a w p C b P hε ha hh hw hb)).re := by
  rw [energy_integral,pairing_integral]
  exact KFCausalOrderedStaticIntegratedLower.integrated_lower n ε h a w p C b P
    hε ha hh hw hb m g k hm hg hk

#print axioms channel_energy
#print axioms energy_integral
#print axioms pairing_integral
#print axioms mixed_lower
end
end UnifiedTheory.Audit.KFCausalOrderedStaticPotentialHilbertBound
