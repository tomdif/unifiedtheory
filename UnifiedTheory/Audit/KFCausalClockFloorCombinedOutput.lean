/- Full angle-L2 energy covariance under the simultaneous chart phase
and paired squeeze. All eight output weights are retained. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaugePairing
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorCombinedOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (gaugeOutput gaugeOutputLp gaugeOutput_apply kinetic rate)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree factorScale outputAction outputAction_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace coordinate coordinateLp outputLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def combinedOutput (ε h r t : ℝ) : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  (gaugeOutput ε h t).comp (outputAction r)
def combinedOutputLp (ε h r t : ℝ) : OutputSpace →L[ℂ] OutputSpace :=
  (combinedOutput ε h r t).compLpL 2 angleMeasure
def weight (r t : ℝ) (i : Fin 8) : ℝ := Real.exp (2*degree i*r + if kinetic i then 2*t else 0)
def weightedPairing (r t : ℝ) (x y : OutputSpace) : ℂ :=
  ∑ i : Fin 8, (weight r t i:ℂ)*inner ℂ (coordinateLp i x) (coordinateLp i y)

theorem combinedOutputLp_comp (ε h r t : ℝ) (x : OutputSpace) :
    combinedOutputLp ε h r t x = gaugeOutputLp ε h t (outputLp r x) := by
  apply Lp.ext
  filter_upwards [(combinedOutput ε h r t).coeFn_compLp x,
    (gaugeOutput ε h t).coeFn_compLp (outputLp r x),(outputAction r).coeFn_compLp x] with θ h1 h2 h3
  change (combinedOutput ε h r t).compLp x θ = (gaugeOutput ε h t).compLp (outputLp r x) θ
  rw [h1,h2]
  change gaugeOutput ε h t (outputAction r (x θ)) = gaugeOutput ε h t ((outputAction r).compLp x θ)
  rw [h3]

theorem point_pairing (ε h : ℝ) (hne : h ≠ 0) (r t : ℝ) (x y : Output (Fin 8) Hilbert) :
    inner ℂ (combinedOutput ε h r t x) (combinedOutput ε h r t y) =
      ∑ i : Fin 8, (weight r t i:ℂ)*inner ℂ (x i) (y i) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ (gaugeOutput ε h t (outputAction r x) i)
    (gaugeOutput ε h t (outputAction r y) i) = _
  have hs : (factorScale r i:ℂ)*(factorScale r i:ℂ) = (Real.exp (2*degree i*r):ℂ) := by
    unfold factorScale
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  by_cases hi : kinetic i
  · simp only [gaugeOutput_apply ε h t hne,hi,if_true,outputAction_apply,map_smul,
      inner_smul_left,inner_smul_right,LinearIsometryEquiv.inner_map_map]
    have he : (Real.exp t:ℂ)*(Real.exp t:ℂ)*(factorScale r i*factorScale r i) = (weight r t i:ℂ) := by
      rw [hs,← Complex.ofReal_mul,← Real.exp_add,← Complex.ofReal_mul,← Real.exp_add]
      simp only [weight,hi,if_true]
      congr 2
      ring
    simp only [factorScale,Complex.conj_ofReal] at he ⊢
    calc
      _ = ((Real.exp t:ℂ)*(Real.exp t:ℂ)*
        ((Real.exp (degree i*r):ℂ)*(Real.exp (degree i*r):ℂ)))*inner ℂ (x i) (y i) := by ring
      _ = _ := by rw [he]
  · simp only [gaugeOutput_apply ε h t hne,hi,if_false,outputAction_apply,map_smul,
      inner_smul_left,inner_smul_right,LinearIsometryEquiv.inner_map_map]
    simp only [factorScale,Complex.conj_ofReal] at hs ⊢
    rw [← mul_assoc,hs]
    simp only [weight,hi,if_false,add_zero]

theorem outputLp_pairing (ε h : ℝ) (hne : h ≠ 0) (r t : ℝ) (x y : OutputSpace) :
    inner ℂ (combinedOutputLp ε h r t x) (combinedOutputLp ε h r t y) = weightedPairing r t x y := by
  have he : (fun θ => inner ℂ (combinedOutputLp ε h r t x θ) (combinedOutputLp ε h r t y θ)) =ᵐ[angleMeasure]
      fun θ => ∑ i : Fin 8, (weight r t i:ℂ)*inner ℂ (coordinateLp i x θ) (coordinateLp i y θ) := by
    filter_upwards [(combinedOutput ε h r t).coeFn_compLp x,(combinedOutput ε h r t).coeFn_compLp y,
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp x),
      ae_all_iff.mpr (fun i : Fin 8 => (coordinate i).coeFn_compLp y)] with θ hx hy hcx hcy
    change inner ℂ ((combinedOutput ε h r t).compLp x θ) ((combinedOutput ε h r t).compLp y θ) = _
    rw [hx,hy,point_pairing ε h hne]
    apply Finset.sum_congr rfl
    intro i _
    have h1 : coordinateLp i x θ = x θ i := hcx i
    have h2 : coordinateLp i y θ = y θ i := hcy i
    rw [h1,h2]
  rw [L2.inner_def,integral_congr_ae he,integral_finset_sum Finset.univ]
  · unfold weightedPairing
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,← L2.inner_def]
  · intro i _
    exact (L2.integrable_inner (𝕜 := ℂ) (coordinateLp i x) (coordinateLp i y)).const_mul _

def balancedDegree (i : Fin 8) : ℝ := (if kinetic i then 2 else 0)-degree i
def balancedPairing (t : ℝ) (x y : OutputSpace) : ℂ :=
  ∑ i : Fin 8, (Real.exp (balancedDegree i*t):ℂ)*inner ℂ (coordinateLp i x) (coordinateLp i y)

theorem balanced_degrees : balancedDegree = ![0,1,1,1,1,-1,-2,0] := by
  funext i
  fin_cases i <;> norm_num [balancedDegree,kinetic,degree]

theorem balanced_output_pairing (t : ℝ) (x y : OutputSpace) :
    weightedPairing ((-1/2:ℝ)*t) t x y = balancedPairing t x y := by
  unfold weightedPairing balancedPairing
  apply Finset.sum_congr rfl
  intro i _
  have he : weight ((-1/2:ℝ)*t) t i = Real.exp (balancedDegree i*t) := by
    unfold weight balancedDegree
    congr 1
    split_ifs <;> ring
  rw [he]

theorem balancedPairing_explicit (t : ℝ) (x y : OutputSpace) :
    balancedPairing t x y = inner ℂ (coordinateLp 0 x) (coordinateLp 0 y)+
      (Real.exp t:ℂ)*(inner ℂ (coordinateLp 1 x) (coordinateLp 1 y)+
        inner ℂ (coordinateLp 2 x) (coordinateLp 2 y)+inner ℂ (coordinateLp 3 x) (coordinateLp 3 y)+
        inner ℂ (coordinateLp 4 x) (coordinateLp 4 y))+
      (Real.exp (-t):ℂ)*inner ℂ (coordinateLp 5 x) (coordinateLp 5 y)+
      (Real.exp (-2*t):ℂ)*inner ℂ (coordinateLp 6 x) (coordinateLp 6 y)+
      inner ℂ (coordinateLp 7 x) (coordinateLp 7 y) := by
  simp [balancedPairing,balanced_degrees,Fin.sum_univ_succ]
  ring

#print axioms combinedOutputLp_comp
#print axioms point_pairing
#print axioms outputLp_pairing
#print axioms balanced_degrees
#print axioms balanced_output_pairing
#print axioms balancedPairing_explicit
end
end UnifiedTheory.Audit.KFCausalClockFloorCombinedOutput
