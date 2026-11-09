/- An actual nonzero charge-zero Hilbert state that is odd under charged-
plane interchange. The bounded radial imbalance gives an explicit witness;
no Hamiltonian-domain regularity is inferred for this witness. -/
import UnifiedTheory.Audit.KFCausalChargedPlaneSwap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalChargedPlaneSwap
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalPairedRotation (rotate pair_inner)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates action action_coordinates)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator (zeroSector)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentStates (weight weight_memLp weight_ne_zero weight_flow)

def imbalanceRaw (x : Space) : ℝ :=
  (x (.inl 0))^2+(x (.inr 1))^2-((x (.inl 1))^2+(x (.inr 2))^2)
def imbalance (c : ℝ) (x : Space) : ℝ := imbalanceRaw (dilate c x)

theorem imbalance_rotate (θ : ℝ) (x : Space) : imbalanceRaw (rotate θ x) = imbalanceRaw x := by
  have h1 := pair_inner θ (x (.inl 0)) (x (.inr 1)) (x (.inl 0)) (x (.inr 1))
  have h2 := pair_inner θ (x (.inl 1)) (x (.inr 2)) (x (.inl 1)) (x (.inr 2))
  simp only [imbalanceRaw,rotate]
  dsimp
  nlinarith only [h1,h2]

theorem imbalance_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    imbalance c (flowEquiv c hc θ x) = imbalance c x := by
  rw [imbalance,KFCausalChargeGaussianGeometry.dilate_flow,imbalance_rotate]
  rfl

theorem imbalance_swap (c : ℝ) (x : Space) : imbalance c (swap x) = -imbalance c x := by
  simp only [imbalance,imbalanceRaw,dilate,swap]
  dsimp
  ring

def boundedImbalance (c : ℝ) (x : Space) : ℂ := (imbalance c x/(1+|imbalance c x|):ℝ)

theorem boundedImbalance_continuous (c : ℝ) : Continuous (boundedImbalance c) := by
  have hd : Continuous (imbalance c) := by unfold imbalance imbalanceRaw dilate; fun_prop
  exact Complex.continuous_ofReal.comp (hd.div (continuous_const.add hd.abs) (fun x => by positivity))

theorem boundedImbalance_bound (c : ℝ) (x : Space) : ‖boundedImbalance c x‖ ≤ 1 := by
  rw [boundedImbalance,Complex.norm_real,Real.norm_eq_abs,abs_div,
    abs_of_pos (by positivity : 0 < 1+|imbalance c x|)]
  exact (div_le_one (by positivity)).mpr (by linarith [abs_nonneg (imbalance c x)])

theorem boundedImbalance_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    boundedImbalance c (flowEquiv c hc θ x) = boundedImbalance c x := by
  simp only [boundedImbalance,imbalance_flow]

theorem boundedImbalance_swap (c : ℝ) (x : Space) :
    boundedImbalance c (swap x) = -boundedImbalance c x := by
  simp only [boundedImbalance,imbalance_swap,abs_neg,neg_div,Complex.ofReal_neg]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

def witnessProfile (x : Space) : ℂ := boundedImbalance (momentumScale h) x*weight ε a h x

theorem witnessProfile_continuous : Continuous (witnessProfile ε a h) := by
  have hw : Continuous (weight ε a h) := by
    unfold weight KFCausalChargeGaussianGeometry.profile
    simp only [KFCausalChargeGaussianGeometry.radius_coordinates]
    have hc := KFCausalClockFloorInvariantTrial.clockFunction_continuous ε a
    fun_prop
  exact (boundedImbalance_continuous _).mul hw

include hε ha hh in
theorem witnessProfile_memLp : MemLp (witnessProfile ε a h) 2 volume := by
  apply (weight_memLp ε a h hε ha hh).of_le (witnessProfile_continuous ε a h).aestronglyMeasurable
  filter_upwards [] with x
  exact (norm_mul _ _).trans_le (mul_le_of_le_one_left (norm_nonneg _) (boundedImbalance_bound _ _))

def mixedWitness : JointHilbert 2 4 :=
  (witnessProfile_memLp ε a h hε ha hh).toLp (witnessProfile ε a h)
def witness : Hilbert := chargeCoordinates.symm (mixedWitness ε a h hε ha hh)

theorem witness_coordinates : chargeCoordinates (witness ε a h hε ha hh) = mixedWitness ε a h hε ha hh :=
  chargeCoordinates.apply_symm_apply _

theorem mixedWitness_coe : mixedWitness ε a h hε ha hh =ᵐ[volume] witnessProfile ε a h :=
  (witnessProfile_memLp ε a h hε ha hh).coeFn_toLp

theorem witness_zeroSector : witness ε a h hε ha hh ∈ zeroSector h hh := by
  intro θ
  change action h hh θ (witness ε a h hε ha hh) = witness ε a h hε ha hh
  apply chargeCoordinates.injective
  rw [action_coordinates,witness_coordinates]
  apply Lp.ext
  filter_upwards [KFCausalMixedCircleAction.action_coe _ (momentumScale_ne_zero h hh) θ
    (mixedWitness ε a h hε ha hh),
    (flow_preserves_volume _ (momentumScale_ne_zero h hh) θ).quasiMeasurePreserving.ae
      (mixedWitness_coe ε a h hε ha hh),mixedWitness_coe ε a h hε ha hh] with x hx hy hz
  simp only [Function.comp_apply] at hx
  rw [hx,hy,hz]
  simp only [witnessProfile,boundedImbalance_flow,weight_flow ε a h hh]

theorem witness_odd : operator (witness ε a h hε ha hh) = -witness ε a h hε ha hh := by
  apply chargeCoordinates.injective
  rw [coordinates_operator,map_neg,witness_coordinates]
  apply Lp.ext
  filter_upwards [mixed_coe (mixedWitness ε a h hε ha hh),
    swapIsometry.measurePreserving.quasiMeasurePreserving.ae (mixedWitness_coe ε a h hε ha hh),
    mixedWitness_coe ε a h hε ha hh,Lp.coeFn_neg (mixedWitness ε a h hε ha hh)] with x hx hy hz hn
  change mixedWitness ε a h hε ha hh (swap x) = witnessProfile ε a h (swap x) at hy
  rw [hx,hy,hn,Pi.neg_apply,hz]
  simp only [witnessProfile,boundedImbalance_swap,weight_swap,neg_mul]

theorem witness_ne_zero : witness ε a h hε ha hh ≠ 0 := by
  intro hz
  have hm : mixedWitness ε a h hε ha hh = 0 := by
    rw [← witness_coordinates,hz,map_zero]
  have he : witnessProfile ε a h =ᵐ[volume] (fun _ => (0:ℂ)) := by
    filter_upwards [mixedWitness_coe ε a h hε ha hh,Lp.coeFn_zero ℂ 2 (volume : Measure Space)] with x hx h0
    rw [hm] at hx
    exact hx.symm.trans h0
  have heq := Measure.eq_of_ae_eq he (witnessProfile_continuous ε a h) continuous_const
  let x : Space := WithLp.toLp 2 (fun i => if i = Sum.inl (0 : Fin 2) then 1 else 0)
  have hd : imbalance (momentumScale h) x = (momentumScale h)^2 := by
    simp [imbalance,imbalanceRaw,dilate,x]
  have hb : boundedImbalance (momentumScale h) x ≠ 0 := by
    rw [boundedImbalance,hd]
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero (pow_ne_zero 2 (momentumScale_ne_zero h hh)) (by positivity)
  have hn : witnessProfile ε a h x ≠ 0 := mul_ne_zero hb (weight_ne_zero ε a h hε hh x)
  exact hn (congrFun heq x)

theorem witness_not_fixed : witness ε a h hε ha hh ∉ fixedSpace := by
  intro hf
  have he := witness_odd ε a h hε ha hh
  rw [show operator (witness ε a h hε ha hh) = witness ε a h hε ha hh from hf] at he
  have hz : witness ε a h hε ha hh = 0 := by
    have hs : (2 : ℂ) • witness ε a h hε ha hh = 0 := by
      rw [two_smul]
      calc
        _ = -witness ε a h hε ha hh + witness ε a h hε ha hh :=
          congrArg (fun x => x+witness ε a h hε ha hh) he
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  exact witness_ne_zero ε a h hε ha hh hz

#print axioms imbalance_rotate
#print axioms imbalance_flow
#print axioms imbalance_swap
#print axioms boundedImbalance_continuous
#print axioms boundedImbalance_bound
#print axioms boundedImbalance_flow
#print axioms boundedImbalance_swap
#print axioms witnessProfile_continuous
#print axioms witnessProfile_memLp
#print axioms witness_coordinates
#print axioms mixedWitness_coe
#print axioms witness_zeroSector
#print axioms witness_odd
#print axioms witness_ne_zero
#print axioms witness_not_fixed
end
end UnifiedTheory.Audit.KFCausalChargeZeroSwapWitness
