/- Exact physical representatives of ordered polynomial Gaussians at
arbitrary admissible charged and neutral widths. Source coefficient extraction occurs at the complex shifted
coordinate, including the neutral shear. Field factors then multiply
the actual ordered output at the physical coordinate. -/
import UnifiedTheory.Audit.KFCausalShiftedPolynomialMoments
import UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalVariableWidthOrderedProfile
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (position profile profile_smooth)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale scale_smooth)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile
  (clockAmplitude clockAmplitude_smooth gaussianState_profile)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalSourceCircleCoefficients
open UnifiedTheory.Audit.KFCausalPolynomialGaussianStates
  (circleSource sourceBound circleSource_continuous circleSource_bound)
open UnifiedTheory.Audit.KFCausalShiftedPolynomialMoments
open UnifiedTheory.Audit.KFCausalVariableWidthPolynomialDomain
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)
open UnifiedTheory.Audit.KFCausalPhysicalField (physicalField_graph)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare_graph)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "hy" => shift_bound ε h hb
local notation "r" => scale ε (-h/2)

def gaussianProfile (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (x : Configuration) : ℂ :=
  C*profile (clockAmplitude ε a p (-h/2)) r α β b x

theorem sourced_output_coe (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) :
    shiftedOutput ε a α β hε ha hα hβ hw C p b h hb =ᵐ[volume] gaussianProfile ε a α β h C p b := by
  filter_upwards [Lp.coeFn_smul C
    (KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2) hε ha hα hβ hw hy),
    gaussianState_profile ε a α β p (-h/2) b hε ha hα hβ hw hy] with x hs hg
  change (C • KFCausalClockFloorCoherentSpectral.gaussianState ε a α β p b (-h/2)
    hε ha hα hβ hw hy : Hilbert) x = _
  rw [hs,Pi.smul_apply,smul_eq_mul,hg]
  rfl

variable (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (i : Fin 5)
local notation "A" => clockAmplitude ε a p (-h/2)

def orderedProfile (P : Polynomial ℂ) (x : Configuration) : ℂ :=
  P.eval (position (r x.1) x.2 i)*gaussianProfile ε a α β h C p b x

theorem powerOutput_vacuum_coe (n : ℕ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7 =ᵐ[volume]
      fun x : Configuration => (position (r x.1) x.2 i)^n*gaussianProfile ε a α β h C p b x := by
  let Y : ℝ → Hilbert := fun θ =>
    shiftedOutput ε a α β hε ha hα hβ hw (weight n θ) p (circleSource b i θ) h hb
  let U : ℝ → Hilbert := fun θ => (C*normalization n) • Y θ
  let F : ℝ → Configuration → ℂ := fun θ x =>
    (C*normalization n)*(weight n θ*Complex.exp (position (r x.1) x.2 i*circle θ))*
      profile A r α β b x
  have hY : Continuous Y :=
    (KFCausalVariableWidthFieldContinuity.outputs_curve_continuous ε a α β h hε ha hα hβ hw hb
      |p| (sourceBound b) (weight n) (fun _ => p) (circleSource b i)
      (weight_continuous n) continuous_const (circleSource_continuous b i)
      (fun θ => (weight_norm n θ).le) (fun _ => le_rfl) (circleSource_bound b i)).1
  have hu : Continuous U := continuous_const.smul hY
  have hpos := position_continuous r (scale_smooth ε (-h/2) hε hy).continuous i
  have hbase := (profile_smooth A r (clockAmplitude_smooth ε a p (-h/2) hε hy)
    (scale_smooth ε (-h/2) hε hy) α β b).continuous
  have hf : Continuous (fun z : ℝ × Configuration => F z.1 z.2) := by
    exact (continuous_const.mul (((weight_continuous n).comp continuous_fst).mul
      (((hpos.comp continuous_snd).mul (circle_continuous.comp continuous_fst)).cexp))).mul
        (hbase.comp continuous_snd)
  have hr (θ : ℝ) : U θ =ᵐ[volume] F θ := by
    filter_upwards [Lp.coeFn_smul (C*normalization n) (Y θ),
      sourced_output_coe ε a α β hε ha hα hβ hw h hb (weight n θ) p (circleSource b i θ)] with x hx hy'
    change ((C*normalization n) • Y θ) x = _
    rw [hx,Pi.smul_apply,smul_eq_mul]
    change (C*normalization n)*_ = _
    rw [hy']
    unfold gaussianProfile
    rw [circle_profile]
    dsimp only [F]
    ring
  have hg : MemLp (fun x : Configuration =>
      (position (r x.1) x.2 i)^n*gaussianProfile ε a α β h C p b x) 2 volume := by
    convert (shifted_position_power_memLp ε a α β p h b hε ha hα hβ hw hb i n).const_mul C using 1
    funext x
    unfold gaussianProfile
    ring
  have hm (x : Configuration) : (∫ θ, F θ x ∂angleMeasure) =
      (position (r x.1) x.2 i)^n*gaussianProfile ε a α β h C p b x := by
    dsimp only [F]
    rw [integral_mul_const,integral_const_mul]
    have he := exponential_coefficient n (position (r x.1) x.2 i)
    calc
      _ = C*(normalization n*(∫ θ, weight n θ*Complex.exp (position (r x.1) x.2 i*circle θ)
          ∂angleMeasure))*profile A r α β b x := by ring
      _ = _ := by rw [he]; unfold gaussianProfile; ring
  have he := KFCausalL2IntegralRepresentative.integral_coe U F _ hu hf hr hg hm
  have hi : (∫ θ, U θ ∂angleMeasure) = powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7 :=
    integral_smul _ _
  exact hi ▸ he

theorem output_vacuum_coe (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    output ε a α β hε ha hα hβ hw h C p b i hb P v l 7 =ᵐ[volume] orderedProfile ε a α β h C p b i P := by
  have hs (s : Finset ℕ) :
      (∑ n ∈ s, P.coeff n • powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7 : Hilbert) =ᵐ[volume]
        fun x : Configuration => (∑ n ∈ s, P.coeff n*(position (r x.1) x.2 i)^n)*
          gaussianProfile ε a α β h C p b x := by
    induction s using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 volume : (0:Hilbert) =ᵐ[volume] 0)
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      filter_upwards [Lp.coeFn_add (P.coeff n • powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7)
        (∑ k ∈ s, P.coeff k • powerOutput ε a α β hε ha hα hβ hw h C p b i hb k v l 7),
        Lp.coeFn_smul (P.coeff n) (powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7),
        powerOutput_vacuum_coe ε a α β hε ha hα hβ hw h hb C p b i n v l,ih] with x hx hy' hz ht
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx hy'
      rw [hx,hy',hz,ht]
      ring
  filter_upwards [hs P.support] with x hx
  change (∑ n ∈ P.support, P.coeff n • powerOutput ε a α β hε ha hα hβ hw h C p b i hb n v l 7 : Hilbert) x = _
  rw [hx]
  simp only [orderedProfile,Polynomial.eval_eq_sum,Polynomial.sum]

theorem output_linear_coe (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    output ε a α β hε ha hα hβ hw h C p b i hb P v l 5 =ᵐ[volume] fun x : Configuration =>
      (l x.2:ℂ)*orderedProfile ε a α β h C p b i P x := by
  obtain ⟨Y,hY,hL⟩ := (composition_graph _ _ _ _).mp
    (output_graph ε a α β hε ha hα hβ hw h C p b i hb P v l 5)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY
    (output_graph ε a α β hε ha hα hβ hw h C p b i hb P v l 7) rfl
  dsimp only at he
  rw [he] at hL
  filter_upwards [(physicalField_graph l _ _).mp hL,
    output_vacuum_coe ε a α β hε ha hα hβ hw h hb C p b i P v l] with x hx hy'
  rw [hx,hy']

theorem output_quadratic_coe (P : Polynomial ℂ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    output ε a α β hε ha hα hβ hw h C p b i hb P v l 6 =ᵐ[volume] fun x : Configuration =>
      (l x.2:ℂ)^2*orderedProfile ε a α β h C p b i P x := by
  obtain ⟨Y,hY,hQ⟩ := (composition_graph _ _ _ _).mp
    (output_graph ε a α β hε ha hα hβ hw h C p b i hb P v l 6)
  have he := (orderedExponential ε hε h).mem_graph_snd_inj' hY
    (output_graph ε a α β hε ha hα hβ hw h C p b i hb P v l 7) rfl
  dsimp only at he
  rw [he] at hQ
  filter_upwards [(fieldSquare_graph l _ _).mp hQ,
    output_vacuum_coe ε a α β hε ha hα hβ hw h hb C p b i P v l] with x hx hy'
  rw [hx,hy']

#print axioms sourced_output_coe
#print axioms powerOutput_vacuum_coe
#print axioms output_vacuum_coe
#print axioms output_linear_coe
#print axioms output_quadratic_coe
end
end UnifiedTheory.Audit.KFCausalVariableWidthOrderedProfile
