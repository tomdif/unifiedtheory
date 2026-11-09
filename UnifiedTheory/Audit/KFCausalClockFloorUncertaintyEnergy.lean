/- A time-growing lower bound for the full completed averaged energy.
The proof uses a genuine canonical transverse pair and the clock factor.
No vacuum positivity or charge-sector restriction is required. -/
import UnifiedTheory.Audit.KFCausalClockFloorWeightedUncertainty
import UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorUncertaintyEnergy
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl

theorem half_inverse_norm (ε : ℝ) (hε : 0 < ε) (f y : Hilbert)
    (hy : (f,y) ∈ (clockHalf ε).graph) :
    ‖f‖^2 ≤ ‖y‖*‖inverseL ε hε f‖ := by
  have he := congrArg norm (KFCausalClockFloorDefectEnergy.half_inverse_pairing ε hε f y hy)
  rw [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_coe_norm] at he
  exact he.symm.trans_le (norm_inner_le_norm _ _)

theorem scalar_energy_bound (t H N B Y X P E : ℝ)
    (hH : 0 ≤ H) (hX : 0 ≤ X) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hu : H*B^2 ≤ 2*X*P) (hx : X^2 ≤ 2*Real.exp (-2*t)*E)
    (hp : P^2 ≤ 2*E) (hy : Y^2 ≤ 2*E) (hn : N^2 ≤ Y*B) :
    H*B^2 ≤ 4*Real.exp (-t)*E ∧ H*Real.exp t*N^4 ≤ 8*E^2 := by
  have hxp := mul_le_mul hx hp (sq_nonneg P) (by positivity : 0 ≤ 2*Real.exp (-2*t)*E)
  have hex : Real.exp (-t)^2 = Real.exp (-2*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hc : 2*X*P ≤ 4*Real.exp (-t)*E := by
    have hs : (2*X*P)^2 ≤ (4*Real.exp (-t)*E)^2 := by
      simp only [mul_pow,hex]
      nlinarith only [hxp]
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  have hlow := hu.trans hc
  refine ⟨hlow,?_⟩
  have hn2 := pow_le_pow_left₀ (sq_nonneg N) hn 2
  have hyn := mul_le_mul_of_nonneg_right hy (sq_nonneg B)
  have hb := mul_le_mul_of_nonneg_left hlow (show 0 ≤ 2*E by positivity)
  have hh := mul_le_mul_of_nonneg_left (show N^4 ≤ 2*E*B^2 by nlinarith only [hn2,hyn]) hH
  have he : Real.exp t*Real.exp (-t) = 1 := by rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hg := mul_le_mul_of_nonneg_left (show H*N^4 ≤ 8*Real.exp (-t)*E^2 by nlinarith only [hb,hh]) (Real.exp_pos t).le
  calc
    H*Real.exp t*N^4 = Real.exp t*(H*N^4) := by ring
    _ ≤ Real.exp t*(8*Real.exp (-t)*E^2) := hg
    _ = 8*E^2 := by calc
      _ = 8*(Real.exp t*Real.exp (-t))*E^2 := by ring
      _ = _ := by rw [he, mul_one]

def energyControl (ε : ℝ) (hε : 0 < ε) (h t : ℝ) (f : Hilbert) (E : ℝ) : Prop :=
  |h| * ‖inverseL ε hε f‖^2 ≤ 4*Real.exp (-t)*E ∧
    |h| * Real.exp t*‖f‖^4 ≤ 8*E^2

theorem state_uncertainty_energy (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (t E : ℝ) (hE : 0 ≤ E) (f : Hilbert)
    (hq : MeasureTheory.Integrable (fun x => KFCausalClockFloorRotatedAntiSymbol.chargedWeight ε h 0 x*
      ‖(KFCausalPhysicalCircleAction.chargeCoordinates f) x‖^2))
    (hqb : KFCausalClockFloorAveragedChargedMoment.chargedMoment ε h 0 f ≤ 2*Real.exp (-2*t)*E)
    (hp : MeasureTheory.Integrable (fun x => KFCausalComplementaryChargeSymbol.complementaryWeight ε h 0 x*
      ‖(KFCausalChargeTransverseSplit.dualPhysical f) x‖^2))
    (hpb : KFCausalClockFloorAveragedComplementaryMoment.complementaryMoment ε h 0 f ≤ 2*E)
    (hc : ∃ y : Hilbert, (f,y) ∈ (clockHalf ε).graph ∧ ‖y‖^2 ≤ 2*E) :
    energyControl ε hε h t f E := by
  obtain ⟨q,p,hu,hq',hp'⟩ := KFCausalClockFloorWeightedUncertainty.weighted_uncertainty
    ε hε h hne f hq hp
  obtain ⟨y,hyg,hyb⟩ := hc
  exact scalar_energy_bound t |h| ‖f‖ ‖inverseL ε hε f‖ ‖y‖ ‖q‖ ‖p‖ E
    (abs_nonneg h) (norm_nonneg _) (norm_nonneg _) hE
    hu (hq'.trans hqb) (hp'.trans hpb) hyb (half_inverse_norm ε hε f y hyg)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k
local notation "J" => embedding ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k

theorem form_uncertainty_energy (w : V t) :
    energyControl ε hε h t (J t w) (‖A t w‖^2) := by
  have hq := KFCausalClockFloorAveragedChargedMoment.form_chargedMoment_bound
    ε hε h hne m g k t hh 0 w
  have hp := KFCausalClockFloorAveragedComplementaryMoment.form_complementaryMoment_bound
    ε hε h hne m g k t hh 0 w
  have hc := KFCausalClockFloorAveragedClockBound.form_clock_graph_bound
    ε hε h hne m g k t hh w
  exact state_uncertainty_energy ε hε h hne t (‖A t w‖^2) (sq_nonneg _) (J t w)
    hq.1 hq.2 hp.1 hp.2 hc

theorem reference_uncertainty_energy (w : V 0) :
    energyControl ε hε h t (J 0 w) (timeEnergy ε hε h hne hh m g k t w) := by
  let v := formTransfer ε hε h hne hh m g k 0 t w
  have he := form_uncertainty_energy ε hε h hne hh m g k t v
  have hj : J t v = J 0 w := transfer_embedding ε hε h hne hh m g k 0 t w
  have ha : ‖A t v‖^2 = timeEnergy ε hε h hne hh m g k t w :=
    timeEnergy_actual ε hε h hne hh m g k t w
  exact (congrArg₂ (energyControl ε hε h t) hj ha).mp he

#print axioms half_inverse_norm
#print axioms scalar_energy_bound
#print axioms state_uncertainty_energy
#print axioms form_uncertainty_energy
#print axioms reference_uncertainty_energy
end
end UnifiedTheory.Audit.KFCausalClockFloorUncertaintyEnergy
