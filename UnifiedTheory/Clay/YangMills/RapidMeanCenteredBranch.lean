/- A genuine uniformly bounded all-order mean-centered a^-4 Wilson family.
The coefficient is chosen sufficiently large that all positive-order centered
correlations vanish. This verifies the strong bound hypothesis on an actual
branch while showing that this branch cannot supply a positive tuned endpoint. -/
import UnifiedTheory.Clay.YangMills.MeanCenteredWilsonMoments
import UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit
import UnifiedTheory.Clay.YangMills.ExplicitLatticeScales
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RapidMeanCenteredBranch
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 WilsonCrossingKernel
open UnitaryCharacterObservables ExplicitLatticeScales MeanCenteredWilsonMoments
open scoped Topology NNReal

def grid (k : ℕ) : ℕ := (k+1)^(2*(k+1))

theorem grid_pos (k : ℕ) : 0 < grid k := by unfold grid; positivity

def factor (k m : ℕ) : ℝ := ((k : ℝ)+1)^(4*m) / ((k : ℝ)+1)^(4*(k+1))

theorem factor_nonneg (k m : ℕ) : 0 ≤ factor k m := by unfold factor; positivity

theorem scale_eq (k : ℕ) : ((spacing k)^4)⁻¹ = ((k : ℝ)+1)^4 := by
  simp only [spacing, one_div, inv_pow, inv_inv]

theorem factor_eq (k m : ℕ) :
    |((spacing k)^4)⁻¹|^m / (grid k : ℝ)^2 = factor k m := by
  rw [scale_eq, abs_of_nonneg (by positivity)]
  simp only [grid, factor, Nat.cast_pow, Nat.cast_add, Nat.cast_one, ← pow_mul]
  congr 2
  omega

theorem factor_small (k m : ℕ) (hkm : m ≤ k) : factor k m ≤ spacing k ^ 4 := by
  have hb : 1 ≤ (k : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hp : 0 < (k : ℝ)+1 := by positivity
  have hd : ((k : ℝ)+1)^(4*m+4) ≤ ((k : ℝ)+1)^(4*(k+1)) :=
    pow_le_pow_right₀ hb (by omega)
  calc
    factor k m ≤ ((k : ℝ)+1)^(4*m) / ((k : ℝ)+1)^(4*m+4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = spacing k ^ 4 := by
      rw [pow_add]
      unfold spacing
      field_simp

theorem factor_tendsto (m : ℕ) : Tendsto (fun k => factor k m) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun k => factor_nonneg k m))
    ((eventually_ge_atTop m).mono (fun k hk => factor_small k m hk))
  simpa using spacing_to_zero.pow 4

theorem factor_bounded (m : ℕ) : ∃ C : ℝ≥0, ∀ k, factor k m ≤ C := by
  obtain ⟨C,hC⟩ := (factor_tendsto m).bddAbove_range
  exact ⟨⟨max C 0, le_max_right _ _⟩, fun k => (hC (Set.mem_range_self k)).trans (le_max_left _ _)⟩

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def start (k : ℕ) : ℝ := WilsonGridCouplingRate.betaThreshold d (grid k)

def counterterm (period : ℕ → ℕ) [∀ k, NeZero (period k)] (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (k : ℕ) (beta : ℝ) : ℝ :=
  (MeanCenteredWilsonMoments.center d G (2*period k) plane ρ beta).re

/-- Exact dictionary to the actual proposed sequence: the counterterm is the
same-law mean, not a variance chosen normalization. -/
theorem proposed_eq_centered (period : ℕ → ℕ) [∀ k, NeZero (period k)] (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (beta : ℕ → ℝ) (k m : ℕ)
    (f : CorrelationTest m) :
    ((TunedRenormalizedLimit.proposedSequence d G period spacing plane ρ hρ
      (counterterm d G period plane ρ) beta k).correlation m f) =
    ((MeanCenteredWilsonMoments.hierarchy d G (2*period k) (spacing k) plane ρ hρ
      (beta k) (((spacing k)^4)⁻¹)).correlation m f) := by
  have hc := WilsonMeanSubtraction.mean_realPart G (2*period k) plane
    (unitaryCharacter ρ) (unitaryCharacter ρ) (beta k) (Fintype.card d)
  change center d G (2*period k) plane ρ (beta k) =
    ((center d G (2*period k) plane ρ (beta k)).re : ℂ) at hc
  simp only [TunedRenormalizedLimit.proposedSequence, RenormalizedWilsonUltrafilter.affineSequence,
    RenormalizedOSWitness.sequence, RenormalizedWilsonHierarchy.realHierarchy,
    MeanCenteredWilsonMoments.hierarchy, RenormalizedWilsonHierarchy.hierarchy_apply, counterterm]
  rw [RenormalizedWilsonHierarchy.realPart_affine, ← hc]
  rfl

def momentConstant (m : ℕ) : ℝ :=
  12 * (2*(Fintype.card d : ℝ))^m * ReflectedGridRate.energyConstant d

theorem momentConstant_nonneg (m : ℕ) : 0 ≤ momentConstant d m := by
  unfold momentConstant ReflectedGridRate.energyConstant
  positivity

theorem actual_bound (period : ℕ → ℕ) [∀ k, NeZero (period k)] (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (k : ℕ) (beta : ℝ) (hbeta : start d k ≤ beta) (m : ℕ) (f : CorrelationTest (m+1)) :
    ‖((TunedRenormalizedLimit.proposedSequence d G period spacing plane ρ hρ
      (counterterm d G period plane ρ) (fun _ => beta) k).correlation (m+1) f)‖ ≤
      momentConstant d m * factor k (m+1) * BoundedKernelDistribution.l1Seminorm volume f := by
  rw [proposed_eq_centered]
  have h := hierarchy_grid_bound d G (2*period k) (spacing k) plane ρ hρ (grid k) (grid_pos k)
    beta hbeta (((spacing k)^4)⁻¹) m f
  rw [factor_eq k (m+1)] at h
  exact h

/-- A derived uniform continuous seminorm at every order, for every beta at
or above the explicit threshold. No uniform-bound assumption is supplied. -/
theorem actual_uniform_seminorms (period : ℕ → ℕ) [∀ k, NeZero (period k)] (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) :
    ∃ p : ∀ m, Seminorm ℂ (CorrelationTest m), (∀ m, Continuous (p m)) ∧
      ∀ (k : ℕ) (beta : ℝ), start d k ≤ beta → ∀ m (f : CorrelationTest m),
        ‖((TunedRenormalizedLimit.proposedSequence d G period spacing plane ρ hρ
          (counterterm d G period plane ρ) (fun _ => beta) k).correlation m f)‖ ≤ p m f := by
  choose C hC using factor_bounded
  let A : ℕ → ℝ≥0 := fun m => match m with
    | 0 => 1
    | n+1 => ⟨momentConstant d n * C (n+1), mul_nonneg (momentConstant_nonneg d n) (C _).coe_nonneg⟩
  let p : ∀ m, Seminorm ℂ (CorrelationTest m) := fun m =>
    BoundedKernelDistribution.boundSeminorm volume (A m)
  refine ⟨p, fun m => BoundedKernelDistribution.boundSeminorm_continuous volume (A m), ?_⟩
  intro k beta hbeta m f
  cases m with
  | zero =>
      rw [proposed_eq_centered, MeanCenteredWilsonMoments.hierarchy,
        RenormalizedWilsonHierarchy.hierarchy_order_zero]
      change ‖∫ x, f x‖ ≤ (1 : ℝ) * BoundedKernelDistribution.l1Seminorm volume f
      rw [one_mul, BoundedKernelDistribution.l1Seminorm_apply]
      exact norm_integral_le_integral_norm _
  | succ m =>
      have h := actual_bound d G period plane ρ hρ k beta hbeta m f
      apply h.trans
      change momentConstant d m * factor k (m+1) * _ ≤
        (momentConstant d m * C (m+1)) * _
      gcongr
      · exact momentConstant_nonneg d m
      · exact hC (m+1) k

/-- Every positive-order correlation actually vanishes on this branch,
including any choice beta(k) above the thresholds. -/
theorem positive_order_tendsto_zero (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℕ → ℝ) (hbeta : ∀ k, start d k ≤ beta k) (m : ℕ)
    (f : CorrelationTest (m+1)) :
    Tendsto (fun k => (TunedRenormalizedLimit.proposedSequence d G period spacing plane ρ hρ
      (counterterm d G period plane ρ) beta k).correlation (m+1) f) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun k => momentConstant d m * factor k (m+1) *
    BoundedKernelDistribution.l1Seminorm volume f)
  · intro k
    have h := actual_bound d G period plane ρ hρ k (beta k) (hbeta k) m f
    simpa only [TunedRenormalizedLimit.proposedSequence, RenormalizedWilsonUltrafilter.affineSequence,
      RenormalizedOSWitness.sequence] using h
  · simpa only [mul_zero, zero_mul] using
      ((factor_tendsto (m+1)).const_mul (momentConstant d m)).mul_const
        (BoundedKernelDistribution.l1Seminorm volume f)

/-- The actual proposed reflected signal vanishes for every sequence above
the thresholds. This is a proved obstruction to using this bounded branch
as the missing positive endpoint. -/
theorem signal_tendsto_zero (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (beta : ℕ → ℝ) (hbeta : ∀ k, start d k ≤ beta k) (f : CorrelationTest 1) :
    Tendsto (fun k => ProposedCouplingTail.signal d G (2*period k) 1 (spacing k)
      plane ρ 1 f (beta k)) atTop (𝓝 0) := by
  let C := ProposedCouplingTail.boundConstant d 1 1 f
  apply squeeze_zero_norm (a := fun k => C * factor k 2)
  · intro k
    have h := ProposedCouplingTail.signal_grid_bound d G (2*period k) 1 (spacing k)
      (spacing_pos k) plane ρ hρ 1 f (grid k) (grid_pos k) (beta k) (hbeta k)
    rw [Real.norm_eq_abs]
    apply h.trans_eq
    rw [← factor_eq k 2, abs_of_nonneg (by positivity)]
    dsimp [C]
    simp only [inv_pow, ← pow_mul]
    norm_num
    ring
  · simpa only [mul_zero] using (factor_tendsto 2).const_mul C

theorem no_positive_endpoint (period : ℕ → ℕ) [∀ k, NeZero (period k)]
    (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (f : CorrelationTest 1) (target : ℝ) (htarget : 0 < target) :
    ¬ (∀ k, target < ProposedCouplingTail.signal d G (2*period k) 1 (spacing k)
      plane ρ 1 f (start d k)) := by
  intro hpos
  have hsmall := (signal_tendsto_zero d G period plane ρ hρ (start d)
    (fun _ => le_rfl) f).eventually (gt_mem_nhds htarget)
  obtain ⟨k,hk⟩ := hsmall.exists
  exact (hpos k).not_gt hk

end
end UnifiedTheory.Clay.YangMills.RapidMeanCenteredBranch
