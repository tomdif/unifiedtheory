/- Actual all-order mean-centered Wilson moments are controlled by one
plaquette defect mean. Repeated and colliding insertions are included. The
bound is strong enough for rapidly concentrating, possibly trivial branches;
it is not a positive ultraviolet fluctuation estimate. -/
import UnifiedTheory.Clay.YangMills.WilsonMeanSubtraction
import UnifiedTheory.Clay.YangMills.ReflectedGridRate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.MeanCenteredWilsonMoments
noncomputable section
open MeasureTheory Filter ContinuumControl RegulatedGauge PeriodicLattice4
open WilsonMomentBounds WilsonCrossingKernel UnitaryCharacterObservables
open CellReflectionCovariance WilsonReflectedTensor AffineWilsonSmearing
open scoped Topology NNReal

variable (d : Type*) [Fintype d] [Nonempty d] [DecidableEq d]
  (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (N : ℕ) [NeZero N]

def center (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ) (beta : ℝ) : ℂ :=
  WilsonMeanSubtraction.mean G N plane (realPartCharacter G (unitaryCharacter ρ))
    (unitaryCharacter ρ) beta (Fintype.card d)

def meanDefect (ρ : G →* Matrix.unitaryGroup d ℂ) (beta : ℝ) : ℝ :=
  ∫ U, WilsonAverageDefect.averageDefect N G ρ U
    ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)

theorem meanDefect_nonneg (ρ : G →* Matrix.unitaryGroup d ℂ) (beta : ℝ) :
    0 ≤ meanDefect d G N ρ beta :=
  integral_nonneg (WilsonAverageDefect.average_nonneg N G ρ)

theorem center_norm (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta : ℝ) : ‖center d G N plane ρ beta‖ ≤ Fintype.card d := by
  letI := wilsonLaw_probability N G _ (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d)
  apply (norm_integral_le_of_norm_le (integrable_const (Fintype.card d : ℝ))
    (Eventually.of_forall (fun U => BareDefectHierarchy.real_character_bound ρ _))).trans
  simp

theorem center_defect (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta : ℝ) :
    ‖center d G N plane ρ beta - (Fintype.card d : ℂ)‖ ≤ 6 * meanDefect d G N ρ beta := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)
  letI : IsProbabilityMeasure μ := wilsonLaw_probability N G _
    (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d)
  let F := loopObservable (Vertex N) G (realPartCharacter G (unitaryCharacter ρ))
    (loops N (0,plane))
  have hf : Integrable F μ :=
    (loopObservable_continuous (Vertex N) G _ (realPart_continuous G _
      (unitaryCharacter_continuous ρ hρ)) _).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (WilsonAverageDefect.plaquetteDefect N G ρ (0,plane)) μ :=
    (WilsonAverageDefect.plaquette_continuous N G ρ hρ (0,plane)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : center d G N plane ρ beta - (Fintype.card d : ℂ) =
      ∫ U, F U - (Fintype.card d : ℂ) ∂μ := by
    rw [integral_sub hf (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
    rfl
  rw [he]
  exact (norm_integral_le_of_norm_le hd (Eventually.of_forall (fun U => by
    exact (BareDefectHierarchy.real_character_difference ρ _).le))).trans
      (WilsonAverageDefect.mean_plaquette_le_six_average N G ρ hρ beta _ (0,plane))

def insertion (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (beta scale : ℝ) : G → ℂ :=
  affineCharacter (realPartCharacter G (unitaryCharacter ρ)) (center d G N plane ρ beta) scale

theorem insertion_bound (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta scale : ℝ) (g : G) :
    ‖insertion d G N plane ρ beta scale g‖ ≤ |scale| * (2 * Fintype.card d) := by
  rw [insertion, affineCharacter, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := (norm_sub_le _ _).trans
    (add_le_add (BareDefectHierarchy.real_character_bound ρ g) (center_norm d G N plane ρ hρ beta))
  linarith

theorem centered_l1 (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta : ℝ) (p : PlaquetteIndex N) :
    (∫ U, ‖loopObservable (Vertex N) G (realPartCharacter G (unitaryCharacter ρ))
      (loops N p) U - center d G N plane ρ beta‖
      ∂wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)) ≤
        12 * meanDefect d G N ρ beta := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)
  letI : IsProbabilityMeasure μ := wilsonLaw_probability N G _
    (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d)
  let F := loopObservable (Vertex N) G (realPartCharacter G (unitaryCharacter ρ)) (loops N p)
  have hc : Continuous F := loopObservable_continuous (Vertex N) G _
    (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)) _
  have hi : Integrable (fun U => ‖F U-center d G N plane ρ beta‖) μ :=
    (hc.sub continuous_const).norm.integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hd : Integrable (WilsonAverageDefect.plaquetteDefect N G ρ p) μ :=
    (WilsonAverageDefect.plaquette_continuous N G ρ hρ p).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (U : RegulatedGauge.Configuration (Vertex N) G) :
      ‖F U - center d G N plane ρ beta‖ ≤
        WilsonAverageDefect.plaquetteDefect N G ρ p U +
          ‖center d G N plane ρ beta - (Fintype.card d : ℂ)‖ := by
    calc
      _ = ‖(F U - (Fintype.card d : ℂ)) -
          (center d G N plane ρ beta - (Fintype.card d : ℂ))‖ := by congr 1; ring
      _ ≤ ‖F U-(Fintype.card d : ℂ)‖ +
          ‖center d G N plane ρ beta-(Fintype.card d : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [show ‖F U-(Fintype.card d : ℂ)‖ =
          WilsonAverageDefect.plaquetteDefect N G ρ p U from
            BareDefectHierarchy.real_character_difference ρ _]
  have hh := integral_mono hi (hd.add (integrable_const _)) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add hd (integrable_const _), integral_const, probReal_univ, one_smul] at hh
  have hm := WilsonAverageDefect.mean_plaquette_le_six_average N G ρ hρ beta
    (Fintype.card d) p
  have hcdef := center_defect d G N plane ρ hρ beta
  change _ ≤ 12 * meanDefect d G N ρ beta
  change (∫ U, ‖F U-center d G N plane ρ beta‖ ∂μ) ≤ _
  change (∫ U, WilsonAverageDefect.plaquetteDefect N G ρ p U ∂μ) ≤
    6 * meanDefect d G N ρ beta at hm
  linarith

theorem word_bound_succ (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta scale : ℝ) (m : ℕ)
    (q : Fin (m+1) → PlaquetteIndex N) (U : RegulatedGauge.Configuration (Vertex N) G) :
    ‖WilsonSmearedObservable.word G N (insertion d G N plane ρ beta scale) (m+1) q U‖ ≤
      |scale|^(m+1) * (2 * (Fintype.card d : ℝ))^m *
        ‖loopObservable (Vertex N) G (realPartCharacter G (unitaryCharacter ρ))
          (loops N (q 0)) U - center d G N plane ρ beta‖ := by
  rw [WilsonSmearedObservable.word, Fin.prod_univ_succ, norm_mul]
  have ht : ‖∏ j : Fin m, loopObservable (Vertex N) G (insertion d G N plane ρ beta scale)
      (loops N (q j.succ)) U‖ ≤ (|scale| * (2 * (Fintype.card d : ℝ)))^m := by
    rw [norm_prod]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ)
        (f := fun j : Fin m => ‖loopObservable (Vertex N) G (insertion d G N plane ρ beta scale)
          (loops N (q j.succ)) U‖)
        (g := fun _ => |scale| * (2 * (Fintype.card d : ℝ)))
        (fun _ _ => norm_nonneg _) (fun j _ =>
          insertion_bound d G N plane ρ hρ beta scale _))
  apply (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq
  simp only [loopObservable, wilson, insertion, affineCharacter, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, pow_succ]
  ring

/-- Repeated and overlapping plaquettes are allowed; one factor supplies the
small mean defect while the remaining factors use the exact dimension bound. -/
theorem coefficient_bound_succ (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta scale : ℝ) (m : ℕ)
    (q : Fin (m+1) → PlaquetteIndex N) :
    ‖RenormalizedWilsonHierarchy.coefficient G N (insertion d G N plane ρ beta scale)
      (unitaryCharacter ρ) beta (Fintype.card d) (m+1) q‖ ≤
      |scale|^(m+1) * (2 * (Fintype.card d : ℝ))^m * (12 * meanDefect d G N ρ beta) := by
  let μ := wilsonLaw N G (unitaryCharacter ρ) beta (Fintype.card d)
  letI : IsProbabilityMeasure μ := wilsonLaw_probability N G _
    (unitaryCharacter_continuous ρ hρ) beta (Fintype.card d)
  have hi : Integrable (fun U => ‖loopObservable (Vertex N) G
      (realPartCharacter G (unitaryCharacter ρ)) (loops N (q 0)) U -
        center d G N plane ρ beta‖) μ := ((loopObservable_continuous (Vertex N) G _
    (realPart_continuous G _ (unitaryCharacter_continuous ρ hρ)) (loops N (q 0))).sub
      continuous_const).norm.integrable_of_hasCompactSupport
        (μ := μ) (HasCompactSupport.of_compactSpace _)
  have h := norm_integral_le_of_norm_le
    (hi.const_mul (|scale|^(m+1) * (2*(Fintype.card d : ℝ))^m))
    (Eventually.of_forall (word_bound_succ d G N plane ρ hρ beta scale m q))
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left (centered_l1 d G N plane ρ hρ beta (q 0))
    (by positivity))

def hierarchy (a : ℝ) (plane : Plane) (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) (beta scale : ℝ) : Hierarchy :=
  RenormalizedWilsonHierarchy.hierarchy G N a plane (insertion d G N plane ρ beta scale)
    (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ)
    (‖scale‖₊ * (2 * (Fintype.card d : ℝ≥0)))
    (fun g => by simpa only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_natCast,
      coe_nnnorm, Real.norm_eq_abs] using insertion_bound d G N plane ρ hρ beta scale g)
    beta (Fintype.card d)

theorem hierarchy_bound_succ (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (beta scale : ℝ)
    (m : ℕ) (f : CorrelationTest (m+1)) :
    ‖(hierarchy d G N a plane ρ hρ beta scale).correlation (m+1) f‖ ≤
      |scale|^(m+1) * (2*(Fintype.card d : ℝ))^m * (12*meanDefect d G N ρ beta) *
        BoundedKernelDistribution.l1Seminorm volume f := by
  rw [hierarchy, RenormalizedWilsonHierarchy.hierarchy_apply,
    BoundedKernelDistribution.l1Seminorm_apply, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (f.integrable.norm.const_mul _)
  exact Eventually.of_forall (fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (coefficient_bound_succ d G N plane ρ hρ beta scale m
      (PeriodicCellSampling.sampleConfiguration (m+1) N a plane x)) (norm_nonneg _))

theorem hierarchy_grid_bound (a : ℝ) (plane : Plane)
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (K : ℕ) (hK : 0 < K)
    (beta : ℝ) (hbeta : WilsonGridCouplingRate.betaThreshold d K ≤ beta)
    (scale : ℝ) (m : ℕ) (f : CorrelationTest (m+1)) :
    ‖(hierarchy d G N a plane ρ hρ beta scale).correlation (m+1) f‖ ≤
      (12 * (2*(Fintype.card d : ℝ))^m * ReflectedGridRate.energyConstant d) *
        (|scale|^(m+1) / (K : ℝ)^2) * BoundedKernelDistribution.l1Seminorm volume f := by
  have he := (WilsonGridCouplingRate.average_inverse_square_bound d G N ρ hρ K hK beta hbeta).trans
    (ReflectedGridRate.tolerance_bound d K hK)
  have h := hierarchy_bound_succ d G N a plane ρ hρ beta scale m f
  apply h.trans
  calc
    _ ≤ |scale|^(m+1) * (2*(Fintype.card d : ℝ))^m *
        (12*(ReflectedGridRate.energyConstant d/(K : ℝ)^2)) *
          BoundedKernelDistribution.l1Seminorm volume f := by
      gcongr
      exact he
    _ = _ := by ring

end
end UnifiedTheory.Clay.YangMills.MeanCenteredWilsonMoments
