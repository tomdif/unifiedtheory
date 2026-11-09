/- Exact connected-derivative effect of a quadratic source counterterm.
Every derivative order is genuine at compact cutoff. Orders above two are
unchanged, so quadratic subtraction cannot repair divergent higher cumulants.
No divergence of physical higher cumulants is asserted here. -/
import UnifiedTheory.Clay.YangMills.WilsonQuadraticJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.QuadraticCumulantInvariance
noncomputable section
open MeasureTheory CompactQuadraticJets
open scoped Topology

section Compact
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem sourcePartition_positive (F : X → ℝ) (hF : Continuous F) (t : ℝ) :
    0 < sourcePartition μ F t := by
  simpa only [CompactGibbsSource.partition, CompactGibbsSource.weight,
    CompactGibbsSource.action, zero_sub, neg_neg, sourcePartition] using
    CompactGibbsSource.partition_positive μ (fun _ => 0) F continuous_const hF t

/-- Smoothness is obtained from the previously constructed dominated integral jets. -/
theorem renormalized_contDiff (F : X → ℝ) (hF : Continuous F) (q : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (renormalized μ F q) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_eq_jet μ F hF q m]
  exact fun t => (jet_hasDerivAt μ F hF q m t).differentiableAt

theorem sourcePartition_contDiff (F : X → ℝ) (hF : Continuous F) :
    ContDiff ℝ (⊤ : ℕ∞) (sourcePartition μ F) := by
  have he : renormalized μ F 0 = sourcePartition μ F := by
    funext t
    simp [renormalized]
  rw [← he]
  exact renormalized_contDiff μ F hF 0

/-- The real logarithm is globally legitimate, including signed counterterms. -/
theorem log_renormalized (F : X → ℝ) (hF : Continuous F) (q t : ℝ) :
    Real.log (renormalized μ F q t) = Real.log (sourcePartition μ F t) - q*t^2 := by
  rw [renormalized, Real.log_mul (Real.exp_ne_zero _)
    (sourcePartition_positive μ F hF t).ne', Real.log_exp]
  ring

theorem log_sourcePartition_contDiff (F : X → ℝ) (hF : Continuous F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => Real.log (sourcePartition μ F t)) :=
  (sourcePartition_contDiff μ F hF).log (fun t => (sourcePartition_positive μ F hF t).ne')

/-- All connected derivatives, defined from the logarithm of the actual generating function. -/
def connectedJet (F : X → ℝ) (q : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  iteratedDeriv m (fun s => Real.log (renormalized μ F q s)) t

/-- The complete zero-source cumulant transformation: exactly the second order changes. -/
theorem connectedJet_zero (F : X → ℝ) (hF : Continuous F) (q : ℝ) (m : ℕ) :
    connectedJet μ F q m 0 =
      connectedJet μ F 0 m 0 - if m = 2 then 2*q else 0 := by
  have he : (fun s => Real.log (renormalized μ F q s)) =
      fun s => Real.log (sourcePartition μ F s) - q*s^2 :=
    funext (fun s => log_renormalized μ F hF q s)
  have h0 : (fun s => Real.log (renormalized μ F 0 s)) =
      fun s => Real.log (sourcePartition μ F s) := by
    funext s
    simp only [log_renormalized μ F hF, zero_mul, sub_zero]
  unfold connectedJet
  rw [he, h0, iteratedDeriv_fun_sub
    ((log_sourcePartition_contDiff μ F hF).of_le
      (show (m : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (by fun_prop : ContDiffAt ℝ m (fun s : ℝ => q*s^2) 0)]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
  split_ifs <;> norm_num [Nat.factorial]
  ring

/-- The statement holds at every source value, not only at zero. -/
theorem higher_connectedJet (F : X → ℝ) (hF : Continuous F) (q : ℝ)
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ) : connectedJet μ F q m t = connectedJet μ F 0 m t := by
  have he : (fun s => Real.log (renormalized μ F q s)) =
      fun s => Real.log (sourcePartition μ F s) - q*s^2 :=
    funext (fun s => log_renormalized μ F hF q s)
  have h0 : (fun s => Real.log (renormalized μ F 0 s)) =
      fun s => Real.log (sourcePartition μ F s) := by
    funext s
    simp only [log_renormalized μ F hF, zero_mul, sub_zero]
  unfold connectedJet
  rw [he, h0, iteratedDeriv_fun_sub
    ((log_sourcePartition_contDiff μ F hF).of_le
      (show (m : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (by fun_prop : ContDiffAt ℝ m (fun s : ℝ => q*s^2) t)]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_pow,
    Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 < m)]
  simp

/-- The familiar fourth connected combination is exactly unchanged. For a
centered source this is its fourth cumulant. -/
theorem fourth_connected_combination (F : X → ℝ) (hF : Continuous F) (q : ℝ) :
    iteratedDeriv 4 (renormalized μ F q) 0 -
        3 * (iteratedDeriv 2 (renormalized μ F q) 0)^2 =
      (∫ x, (F x)^4 ∂μ) - 3 * (∫ x, (F x)^2 ∂μ)^2 := by
  rw [fourth_derivative μ F hF q, second_derivative μ F hF q]
  ring

end Compact

section Wilson
open ContinuumControl PeriodicLattice4 LocalCountertermReflection
variable (n : ℕ) [NeZero n] (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The all-order identity is bound to the actual centered interacting Wilson source. -/
theorem wilson_connected_zero (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) (m : ℕ) :
    iteratedDeriv m (fun t => Real.log (WilsonQuadraticJets.generating n G a plane χ
      β c κ f t)) 0 =
      iteratedDeriv m (fun t => Real.log (WilsonQuadraticJets.generating n G a plane χ
        β c 0 f t)) 0 - if m = 2 then 2 * κ * (localSquare f).re else 0 := by
  letI := wilsonLaw_probability n G χ hχ β c
  have h := connectedJet_zero (wilsonLaw n G χ β c)
    (WilsonQuadraticJets.centeredSource n G a plane χ β c f)
    (WilsonQuadraticJets.centeredSource_continuous n G a plane χ hχ β c f)
    (κ * (localSquare f).re) m
  simpa only [connectedJet, WilsonQuadraticJets.generating, zero_mul, mul_assoc] using h

/-- Higher connected Wilson derivatives cannot be altered by a quadratic source factor. -/
theorem wilson_higher_connected (a : ℝ) (plane : Plane) (χ : G → ℂ) (hχ : Continuous χ)
    (β c κ : ℝ) (f : CorrelationTest 1) (m : ℕ) (hm : 3 ≤ m) (t : ℝ) :
    iteratedDeriv m (fun s => Real.log (WilsonQuadraticJets.generating n G a plane χ
      β c κ f s)) t =
      iteratedDeriv m (fun s => Real.log (WilsonQuadraticJets.generating n G a plane χ
        β c 0 f s)) t := by
  letI := wilsonLaw_probability n G χ hχ β c
  simpa only [connectedJet, WilsonQuadraticJets.generating, zero_mul] using
    higher_connectedJet (wilsonLaw n G χ β c)
      (WilsonQuadraticJets.centeredSource n G a plane χ β c f)
      (WilsonQuadraticJets.centeredSource_continuous n G a plane χ hχ β c f)
      (κ * (localSquare f).re) m hm t

end Wilson

end
end UnifiedTheory.Clay.YangMills.QuadraticCumulantInvariance
