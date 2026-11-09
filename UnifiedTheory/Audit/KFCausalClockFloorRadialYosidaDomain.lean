/- Uniform bounds on the actual bounded radial cutoffs force the full
maximal radial operator domain. Fatou supplies the missing square moment;
no radial domain or limiting output is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
import UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol
open KFCausalClockFloorRotatedAntiSymbol (chargedWeight_continuous)
open KFCausalUnitaryRealMultiplier (realPullback realPullback_domain)
open KFCausalRealMultiplierSelfAdjoint (realPullback_selfAdjoint realPullback_norm_square)
open KFCausalAveragedEnergyGraph (l2_norm_square)

private theorem radial_measurable (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    Measurable (radial ε h) :=
  (((chargedWeight_continuous ε hε h 0).add
    (chargedWeight_continuous ε hε h 1)).div_const 2).measurable

def operator (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback chargeCoordinates (radial ε h) (radial_measurable ε hε h)

theorem operator_selfAdjoint (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    IsSelfAdjoint (operator ε hε h) :=
  realPullback_selfAdjoint chargeCoordinates (radial ε h) (radial_measurable ε hε h)

theorem symbol_tendsto (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (x : KFCausalEuclideanProductCoordinates.Joint 2 4) :
    Tendsto (fun n : ℕ => symbol ε h ((n:ℝ)+1) x) atTop (𝓝 (radial ε h x)) := by
  have hz : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht := KFCausalPureMomentumCutoff.value_tendsto _ hz (radial ε h x)
  apply ht.congr'
  filter_upwards [] with n
  unfold KFCausalPureMomentumCutoff.value symbol
  rw [abs_of_nonneg (radial_nonnegative ε hε h x)]
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ)

private def density (N : ℝ) (f : Hilbert) (x : KFCausalEuclideanProductCoordinates.Joint 2 4) : ℝ :=
  symbol ε h N x^2 * ‖(chargeCoordinates f) x‖^2

private theorem density_eq (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    (fun x => ‖(chargeCoordinates (action ε hε h N hN f)) x‖^2) =ᵐ[volume]
      density ε h N f := by
  filter_upwards [action_coe ε hε h N hN f] with x hx
  rw [hx,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

include hε in
private theorem density_integrable (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    Integrable (density ε h N f) volume :=
  ((memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (chargeCoordinates (action ε hε h N hN f)))).mp (Lp.memLp _)).congr
    (density_eq ε hε h N hN f)

private theorem density_integral (N : ℝ) (hN : 0 < N) (f : Hilbert) :
    (∫ x, density ε h N f x) = ‖action ε hε h N hN f‖^2 := by
  rw [← chargeCoordinates.norm_map (action ε hε h N hN f),l2_norm_square]
  exact integral_congr_ae (density_eq ε hε h N hN f).symm

theorem domain_of_uniform_bound (f : Hilbert) (B : ℝ)
    (hB : ∀ n : ℕ, ‖action ε hε h ((n:ℝ)+1) (by positivity) f‖ ≤ B) :
    f ∈ (operator ε hε h).domain := by
  have hi : Integrable (fun x => radial ε h x^2*‖(chargeCoordinates f) x‖^2) volume := by
    apply KFCausalPureMomentumCutoffDomain.integrable_of_uniform_nonnegative_integrals
      (fun n => density ε h ((n:ℝ)+1) f) _
      (fun n => density_integrable ε hε h _ (by positivity) f)
      (fun n x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (((radial_measurable ε hε h).pow_const 2).aestronglyMeasurable.mul
        ((Lp.aestronglyMeasurable (chargeCoordinates f)).norm.pow 2))
      (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (fun x => ((symbol_tendsto ε hε h x).pow 2).mul_const _) (B^2)
    intro n
    rw [density_integral ε hε h _ (by positivity) f]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
  apply (realPullback_domain chargeCoordinates (radial ε h) (radial_measurable ε hε h) f).mpr
  apply (memLp_two_iff_integrable_sq_norm
    ((Complex.continuous_ofReal.measurable.comp (radial_measurable ε hε h)).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (chargeCoordinates f)))).mpr
  exact hi.congr (Eventually.of_forall (fun x => by
    change radial ε h x^2*‖(chargeCoordinates f) x‖^2 =
      ‖(radial ε h x:ℂ)*(chargeCoordinates f) x‖^2
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]))

theorem norm_of_uniform_bound (f : Hilbert) (B : ℝ)
    (hB : ∀ n : ℕ, ‖action ε hε h ((n:ℝ)+1) (by positivity) f‖ ≤ B) :
    ‖operator ε hε h ⟨f,domain_of_uniform_bound ε hε h f B hB⟩‖ ≤ B := by
  have hBn : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hi := (realPullback_domain chargeCoordinates (radial ε h) (radial_measurable ε hε h) f).mp
    (domain_of_uniform_bound ε hε h f B hB)
  have hi' := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have hd : Integrable (fun x => radial ε h x^2*‖(chargeCoordinates f) x‖^2) volume :=
    hi'.congr (Eventually.of_forall (fun x => by
      change ‖(radial ε h x:ℂ)*(chargeCoordinates f) x‖^2 =
        radial ε h x^2*‖(chargeCoordinates f) x‖^2
      rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]))
  have ht : Tendsto (fun n : ℕ => ∫ x, density ε h ((n:ℝ)+1) f x) atTop
      (𝓝 (∫ x, radial ε h x^2*‖(chargeCoordinates f) x‖^2)) := by
    apply tendsto_integral_of_dominated_convergence _
      (fun n => (density_integrable ε hε h _ (by positivity) f).aestronglyMeasurable) hd
    · intro n
      filter_upwards [] with x
      change ‖symbol ε h ((n:ℝ)+1) x^2*‖(chargeCoordinates f) x‖^2‖ ≤ _
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (symbol_nonnegative ε hε h _ (by positivity) x)
          (symbol_le_radial ε hε h _ (by positivity) x) 2) (sq_nonneg _)
    · exact Eventually.of_forall (fun x => ((symbol_tendsto ε hε h x).pow 2).mul_const _)
  have hb : (∫ x, radial ε h x^2*‖(chargeCoordinates f) x‖^2) ≤ B^2 := by
    apply le_of_tendsto ht
    filter_upwards [] with n
    rw [density_integral ε hε h _ (by positivity) f]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
  apply (sq_le_sq₀ (norm_nonneg _) hBn).mp
  exact (realPullback_norm_square chargeCoordinates (radial ε h) (radial_measurable ε hε h)
    ⟨f,domain_of_uniform_bound ε hε h f B hB⟩).le.trans hb

#print axioms operator_selfAdjoint
#print axioms symbol_tendsto
#print axioms domain_of_uniform_bound
#print axioms norm_of_uniform_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDomain
