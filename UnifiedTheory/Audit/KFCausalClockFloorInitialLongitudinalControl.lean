/- Derived two-sided longitudinal control of the actual inverse-clock-weighted
boosted initial states. Both tails and a momentum-domain norm bound are uniform
in admissible small nonzero hbar. No positive-time Hamiltonian propagation is
asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorInitialNegativeExponential
import UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorInitialLongitudinalControl
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorInitialNegativeExponential
open UnifiedTheory.Audit.KFCausalClockFloorTwoSidedSpectralControl
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalTails (positiveTail negativeTail positive_tail_bound)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral (boostedExponentialOutput)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedExponentialBound (exponentialMass boostedExponential_bound)
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier (symbol momentum_fourier_coe)
open UnifiedTheory.Audit.KFCausalClockFloorExponential (symbol_measurable)
open UnifiedTheory.Audit.KFCausalClockFloorSpectralTransport (scaled_transport_fourier)
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryTransport (transport)

def budget (ε a : ℝ) (p : Configuration) : ℝ :=
  (exponentialMass ε a p+exponentialMass ε a (-p))/clockMass ε a

theorem initial_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    input ε a h hε ha hh p ∈ (longitudinalMomentum ε hε h).domain :=
  two_exponential_domain ε hε h hh _ _ _
    (positive_graph ε a h hε ha hh hb p) (negative_graph ε a h hε ha hh hb p)

def momentumOutput (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : Hilbert :=
  longitudinalMomentum ε hε h ⟨input ε a h hε ha hh p,initial_domain ε a h hε ha hh hb p⟩

theorem initial_momentum_bound (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) :
    ‖momentumOutput ε a h hε ha hh hb p‖^2 ≤ 2*budget ε a p := by
  have he := two_exponential_momentum_bound ε hε h hh _ _ _
    (positive_graph ε a h hε ha hh hb p) (negative_graph ε a h hε ha hh hb p)
  have hp := boostedExponential_bound ε a h hε ha hh hb h1 p
  have hn := negative_output_bound ε a h hε ha hh hb h1 p
  unfold budget
  rw [add_div]
  exact he.trans (by linarith)

theorem initial_positive_tail (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (R : ℝ) :
    positiveTail ε hε h R (input ε a h hε ha hh p) ≤
      Real.exp (-R)*(exponentialMass ε a p/clockMass ε a) :=
  (positive_tail_bound ε hε h R _ _ (positive_graph ε a h hε ha hh hb p)).trans
    (mul_le_mul_of_nonneg_left (boostedExponential_bound ε a h hε ha hh hb h1 p) (Real.exp_pos _).le)

theorem initial_negative_tail (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (R : ℝ) :
    negativeTail ε hε h R (input ε a h hε ha hh p) ≤
      Real.exp (-R)*(exponentialMass ε a (-p)/clockMass ε a) :=
  (negative_tail_bound ε hε h R _ _ (negative_graph ε a h hε ha hh hb p)).trans
    (mul_le_mul_of_nonneg_left (negative_output_bound ε a h hε ha hh hb h1 p) (Real.exp_pos _).le)

theorem initial_two_tails (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (R : ℝ) :
    positiveTail ε hε h R (input ε a h hε ha hh p)+
      negativeTail ε hε h R (input ε a h hε ha hh p) ≤ Real.exp (-R)*budget ε a p := by
  have he := add_le_add (initial_positive_tail ε a h hε ha hh hb h1 p R)
    (initial_negative_tail ε a h hε ha hh hb h1 p R)
  exact he.trans_eq (by unfold budget; ring)

theorem uniform_initial_tails (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ h : ℝ, ∀ hh : h ≠ 0, ∀ _hb : |h| ≤ 2*Real.pi*ε/3, |h| ≤ 1 →
      positiveTail ε hε h R (input ε a h hε ha hh p)+
        negativeTail ε hε h R (input ε a h hε ha hh p) < η := by
  have ht : Tendsto (fun R : ℝ => Real.exp (-R)*budget ε a p) atTop (𝓝 0) := by
    simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const (budget ε a p)
  obtain ⟨R,hR,he⟩ := ((eventually_ge_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds hη))).exists
  exact ⟨R,hR,fun h hh hb h1 => (initial_two_tails ε a h hε ha hh hb h1 p R).trans_lt he⟩

theorem initial_transport_difference (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (h1 : |h| ≤ 1) (p : Configuration) (v : ℝ) :
    ‖transport ε hε (h*v) (input ε a h hε ha hh p)-input ε a h hε ha hh p‖^2 ≤
      v^2*(2*budget ε a p) := by
  let f := input ε a h hε ha hh p
  let q := momentumOutput ε a h hε ha hh hb p
  have hq : (v:ℂ) • coupledFourier ε hε q =ᵐ[volume]
      fun k => ((v*symbol h k:ℝ):ℂ)*(coupledFourier ε hε f) k := by
    filter_upwards [Lp.coeFn_smul (v:ℂ) (coupledFourier ε hε q),
      momentum_fourier_coe ε hε h hh ⟨f,initial_domain ε a h hε ha hh hb p⟩] with k hv hk
    change (coupledFourier ε hε q) k = (symbol h k:ℂ)*(coupledFourier ε hε f) k at hk
    rw [hv,Pi.smul_apply,smul_eq_mul,hk,Complex.ofReal_mul,mul_assoc]
  have he := KFCausalLpPhaseTranslation.modulation_difference volume
    (fun k => v*symbol h k) (measurable_const.mul (symbol_measurable h))
    (coupledFourier ε hε f) ((v:ℂ) • coupledFourier ε hε q) hq
  rw [← scaled_transport_fourier,← map_sub,LinearIsometryEquiv.norm_map,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,LinearIsometryEquiv.norm_map] at he
  have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
  rw [mul_pow,sq_abs] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (initial_momentum_bound ε a h hε ha hh hb h1 p) (sq_nonneg v))

#print axioms initial_domain
#print axioms initial_momentum_bound
#print axioms initial_positive_tail
#print axioms initial_negative_tail
#print axioms initial_two_tails
#print axioms uniform_initial_tails
#print axioms initial_transport_difference

end
end UnifiedTheory.Audit.KFCausalClockFloorInitialLongitudinalControl
