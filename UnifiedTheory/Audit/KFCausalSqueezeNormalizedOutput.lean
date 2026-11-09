/- The squeeze commutator divided by its parameter has a continuous
strong extension on all angle-L2 outputs. Its zero pairing is the exact
signed energy variation, including both kinetic signs and matter terms. -/
import UnifiedTheory.Audit.KFCausalSqueezeOutputContinuity
import UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (diagonal diagonal_apply selected selected_apply)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace coordinate coordinateLp variation)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (differenceOutput differenceOutputLp differenceOutput_apply)
open UnifiedTheory.Audit.KFCausalSqueezeNormalizedCoefficients
open UnifiedTheory.Audit.KFCausalSqueezeOutputContinuity
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
abbrev O := Output (Fin 8) Hilbert

def liftLinear : (O →L[ℂ] O) →ₗ[ℂ] (OutputSpace →L[ℂ] OutputSpace) where
  toFun L := L.compLpL 2 angleMeasure
  map_add' := ContinuousLinearMap.add_compLpL
  map_smul' := ContinuousLinearMap.smul_compLpL

theorem lift_comp (L M : O →L[ℂ] O) : liftLinear (L.comp M) = (liftLinear L).comp (liftLinear M) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [(L.comp M).coeFn_compLp x,L.coeFn_compLp (M.compLp x),M.coeFn_compLp x]
    with θ h1 h2 h3
  exact h1.trans ((congrArg L h3.symm).trans h2.symm)

def projection (i : Fin 8) : O →L[ℂ] O := selected (fun j => j=i)
def projectionLp (i : Fin 8) : OutputSpace →L[ℂ] OutputSpace := liftLinear (projection i)

theorem diagonal_decomposition (d : Fin 8 → ℂ) : diagonal d = ∑ i : Fin 8, d i • projection i := by
  ext x j
  simp [diagonal_apply,projection,selected_apply,ContinuousLinearMap.sum_apply,eq_comm]

def normalizedOutput (a : ℝ) : O →L[ℂ] O :=
  (diagonal (normalized a)).comp (pureOutput a : O →L[ℂ] O)
def normalizedLp (a : ℝ) : OutputSpace →L[ℂ] OutputSpace := liftLinear (normalizedOutput a)

theorem normalizedOutput_apply (a : ℝ) (x : O) (i : Fin 8) :
    normalizedOutput a x i = normalized a i • KFCausalPairedSqueezeTransport.transport a (x i) := rfl

theorem normalizedLp_split (a : ℝ) (x : OutputSpace) :
    normalizedLp a x = ∑ i : Fin 8, normalized a i • projectionLp i (pureLp a x) := by
  change liftLinear ((diagonal (normalized a)).comp (pureOutput a : O →L[ℂ] O)) x = _
  rw [lift_comp,diagonal_decomposition]
  simp only [map_sum,map_smul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply,projectionLp,pureLp,liftLinear,LinearMap.coe_mk,AddHom.coe_mk]

theorem normalizedLp_joint_continuous : Continuous (fun p : ℝ × OutputSpace => normalizedLp p.1 p.2) := by
  simp only [normalizedLp_split]
  apply continuous_finset_sum
  intro i _
  exact ((normalized_continuous i).comp continuous_fst).smul
    ((projectionLp i).continuous.comp pureLp_joint_continuous)

theorem difference_normalized (a : ℝ) : differenceOutputLp a = (a:ℂ) • normalizedLp a := by
  have he : differenceOutput a = (a:ℂ) • normalizedOutput a := by
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simp only [differenceOutput_apply,ContinuousLinearMap.smul_apply,PiLp.smul_apply,
      normalizedOutput_apply,smul_smul,normalized_scale]
  change liftLinear (differenceOutput a) = (a:ℂ) • liftLinear (normalizedOutput a)
  rw [he,map_smul]

theorem normalizedLp_zero (x : OutputSpace) :
    normalizedLp 0 x = (diagonal (fun i => (2*degree i:ℝ))).compLp x := by
  apply Lp.ext
  filter_upwards [(normalizedOutput 0).coeFn_compLp x,
    (diagonal (fun i => (2*degree i:ℝ))).coeFn_compLp x] with θ hn hd
  have he : normalizedOutput 0 (x θ) = diagonal (fun i => (2*degree i:ℝ)) (x θ) := by
    apply PiLp.ext
    intro i
    simp only [normalizedOutput_apply,normalized_zero,KFCausalPairedSqueezeTransport.transport_initial,
      diagonal_apply]
  exact hn.trans (he.trans hd.symm)

theorem projectionLp_pairing (i : Fin 8) (x : OutputSpace) :
    inner ℂ x (projectionLp i x) = (‖coordinateLp i x‖^2 : ℝ) := by
  have he : inner ℂ x (projectionLp i x) = inner ℂ (coordinateLp i x) (coordinateLp i x) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(projection i).coeFn_compLp x,(coordinate i).coeFn_compLp x] with θ hp hc
    change inner ℂ (x θ) ((projection i).compLp x θ) =
      inner ℂ ((coordinate i).compLp x θ) ((coordinate i).compLp x θ)
    rw [hp,hc,PiLp.inner_apply]
    simp [projection,selected_apply,coordinate,apply_ite]
  exact he.trans (by simpa only [Complex.ofReal_pow] using
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (coordinateLp i x))

theorem normalized_pairing_zero (x : OutputSpace) :
    inner ℂ x (normalizedLp 0 x) = (variation x : ℂ) := by
  rw [normalizedLp_split,pureLp_zero,inner_sum]
  simp only [inner_smul_right,normalized_zero,projectionLp_pairing]
  simp [variation,degree,Fin.sum_univ_succ]
  ring

theorem normalized_strong_limit (x : OutputSpace) :
    Tendsto (fun a => normalizedLp a x) (𝓝 0)
      (𝓝 ((diagonal (fun i => (2*degree i:ℝ))).compLp x)) := by
  simpa only [Function.comp_apply,id_eq,normalizedLp_zero] using
    (normalizedLp_joint_continuous.comp (continuous_id.prodMk (continuous_const (y := x)))).tendsto (0:ℝ)

#print axioms lift_comp
#print axioms diagonal_decomposition
#print axioms normalizedOutput_apply
#print axioms normalizedLp_split
#print axioms normalizedLp_joint_continuous
#print axioms difference_normalized
#print axioms normalizedLp_zero
#print axioms projectionLp_pairing
#print axioms normalized_pairing_zero
#print axioms normalized_strong_limit
end
end UnifiedTheory.Audit.KFCausalSqueezeNormalizedOutput
