/- Actual fixed-Schwartz centered reflected bounds from the proved
finite-matrix grid and Wilson concentration. The proposed a^-4 normalization
is not identified with continuum curvature or the physical running coupling. -/
import UnifiedTheory.Clay.YangMills.ReflectedDefectBound
import UnifiedTheory.Clay.YangMills.WilsonGridCouplingRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.ReflectedGridRate
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open UnitaryCharacterObservables CellReflectionCovariance WilsonReflectedTensor
open UnitaryHaarNeighborhood WilsonGridCouplingRate ReflectedWilsonRenormalization

variable (d : Type*) [Fintype d]

def energyConstant : ℝ := 4*(Fintype.card d : ℝ)^4*(1+3*(Fintype.card d : ℝ))^2 +
  2*(Fintype.card d : ℝ)

def rateConstant : ℝ := 24*(Fintype.card d : ℝ)*energyConstant d

theorem rateConstant_nonneg : 0 ≤ rateConstant d := by
  unfold rateConstant energyConstant
  positivity

theorem tolerance_bound (K : ℕ) (hK : 0 < K) :
    2*squaredTolerance d K + 2*(Fintype.card d : ℝ)/((2*K+1 : ℕ) : ℝ)^2 ≤
      energyConstant d / (K : ℝ)^2 := by
  have hk : 0 < (K : ℝ) := Nat.cast_pos.mpr hK
  have hbase : (K : ℝ) ≤ ((2*K+1 : ℕ) : ℝ) := by exact_mod_cast (show K ≤ 2*K+1 by omega)
  have he : 2*(Fintype.card d : ℝ)/((2*K+1 : ℕ) : ℝ)^2 ≤
      2*(Fintype.card d : ℝ)/(K : ℝ)^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hk)
    nlinarith
  apply (add_le_add (le_refl (2*squaredTolerance d K)) he).trans_eq
  rw [squaredTolerance_formula]
  unfold energyConstant
  ring

variable [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

theorem reflectedForm_grid_bound (a : ℝ) (ha : a ≠ 0) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : betaThreshold d K ≤ beta)
    (f g : CorrelationTest 1) :
    ‖reflectedForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) f g‖ ≤
      rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g / (K : ℝ)^2 := by
  have h := ReflectedDefectBound.reflectedForm_bound G N a ha plane ρ hρ beta f g
  have he := (average_inverse_square_bound d G N ρ hρ K hK beta hbeta).trans
    (tolerance_bound d K hK)
  have hf : 0 ≤ BoundedKernelDistribution.l1Seminorm volume f := apply_nonneg _ _
  have hg : 0 ≤ BoundedKernelDistribution.l1Seminorm volume g := apply_nonneg _ _
  apply h.trans
  calc
    _ ≤ 24*(Fintype.card d : ℝ)*(energyConstant d/(K : ℝ)^2) *
        BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by gcongr
    _ = _ := by unfold rateConstant; ring

/-- A sufficient bound for an actual rescaled fixed-test form. All lattice,
action-law and observable dependence is retained; no renormalized limit is assumed. -/
theorem proposedCurvatureForm_grid_bound (a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : betaThreshold d K ≤ beta)
    (center : ℂ) (f g : CorrelationTest 1) :
    ‖proposedCurvatureForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) center f g‖ ≤
      rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g / (a^8*(K : ℝ)^2) := by
  have h := reflectedForm_grid_bound d G N a ha.ne' plane ρ hρ K hK beta hbeta f g
  have he := bare_eq_eighth_power_rescaled G N a ha.ne' plane
    (realPartCharacter G (unitaryCharacter ρ))
    (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ))
    (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d) center f g
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos ha 8)] at h
  have hk : 0 < (K : ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hK)
  have hh := (le_div_iff₀ hk).mp h
  apply (le_div_iff₀ (mul_pos (pow_pos ha 8) hk)).mpr
  convert hh using 1 <;> ring

theorem proposed_uniform_bound (a : ℝ) (ha : 0 < a) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (K : ℕ) (hK : 0 < K) (beta : ℝ) (hbeta : betaThreshold d K ≤ beta)
    (hbalance : 1 ≤ a^8*(K : ℝ)^2) (center : ℂ) (f g : CorrelationTest 1) :
    ‖proposedCurvatureForm G N a plane (realPartCharacter G (unitaryCharacter ρ))
      (unitaryCharacter ρ) beta (Fintype.card d) center f g‖ ≤
      rateConstant d * BoundedKernelDistribution.l1Seminorm volume f *
        BoundedKernelDistribution.l1Seminorm volume g := by
  apply (proposedCurvatureForm_grid_bound d G N a ha plane ρ hρ K hK beta hbeta
    center f g).trans
  apply div_le_self _ hbalance
  exact mul_nonneg (mul_nonneg (rateConstant_nonneg d) (apply_nonneg _ _)) (apply_nonneg _ _)

end
end UnifiedTheory.Clay.YangMills.ReflectedGridRate
