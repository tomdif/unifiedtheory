/- A convergent actual probability sequence supplies a global force with
physical time bounds, full weak dynamics, and all-resolvent net convergence. -/
import UnifiedTheory.Audit.KFCausalNeutralJointForceLimit
import UnifiedTheory.Audit.KFCausalNeutralNetForceDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce
noncomputable section
open MeasureTheory Filter Set SchwartzMap BoundedContinuousFunction
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralTemporalCompactness (curve)
open UnifiedTheory.Audit.KFCausalNeutralInitialProbability (initialProbability)
open UnifiedTheory.Audit.KFCausalNeutralSpacetimeForce (forceWindow)
open UnifiedTheory.Audit.KFCausalNeutralIntegratedForce (forceInterval)
open UnifiedTheory.Audit.KFCausalNeutralForceConsistency (forceBudget)
open UnifiedTheory.Audit.KFCausalGlobalSpacetimeForce (Force)
open UnifiedTheory.Audit.KFCausalNeutralTensorTestEquation (IntervalBalance TensorWeakEquation)
open UnifiedTheory.Audit.KFCausalTensorTestClosure (UniformWeakEquation)
open UnifiedTheory.Audit.KFCausalSmoothWeakEquation (SmoothWeakEquation)
open UnifiedTheory.Audit.KFCausalGlobalNetForceUniqueness
open UnifiedTheory.Audit.KFCausalNeutralForceClusterIdentification
open UnifiedTheory.Audit.KFCausalNeutralFullSequenceForceConvergence
open UnifiedTheory.Audit.KFCausalNeutralJointForceLimit

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)

/-- All fields are derived in `exists_force_of_probability_limit` below. -/
structure Description (ν : ℝ → ProbabilityMeasure ℝ) (J : Force) : Prop where
  positive_time : J.positive.map Prod.fst ≪ volume
  negative_time : J.negative.map Prod.fst ≪ volume
  no_time_atoms : ∀ t : ℝ, J.positive ({t} ×ˢ univ)+J.negative ({t} ×ˢ univ) = 0
  physical_time_bound : ∀ T b c : ℝ, b ≤ c → |b-s| ≤ T → |c-s| ≤ T →
    ∀ A : Set ℝ, MeasurableSet A →
      (J.window b c).positive (A ×ˢ univ)+(J.window b c).negative (A ×ˢ univ) ≤
        ENNReal.ofReal (forceBudget ε a m g k s T p)*volume (A ∩ Icc b c)
  interval_balance : IntervalBalance ν J
  tensor_equation : TensorWeakEquation ν J
  uniform_equation : UniformWeakEquation ν J
  smooth_equation : SmoothWeakEquation ν J
  fourier_balance : ∀ b c : ℝ, b ≤ c → ∀ v : ℝ,
    Complex.I*(v : ℂ)*(J.interval b c).fourier v =
      charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v
  fourier_reconstruction : ∀ b c : ℝ, b ≤ c → ∀ v : ℝ, v ≠ 0 →
    (J.interval b c).fourier v =
      (charFun (ν c : Measure ℝ) v-charFun (ν b : Measure ℝ) v)/(Complex.I*(v : ℂ))
  net_unique : ∀ K : Force, IntervalBalance ν K → NetEquivalent J K ∧
    ∀ b c : ℝ, ∀ q : (ℝ × ℝ) →ᵇ ℂ, (J.window b c).evaluate q = (K.window b c).evaluate q
  spacetime_convergence : ∀ r : ℕ → ℝ, ∀ hr : ∀ n, 0 < r n, Tendsto r atTop atTop →
    ∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ × ℝ,ℂ),
      Tendsto (fun n =>
        (forceWindow ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF)
          atTop (𝓝 ((J.window b c).evaluate q.toBCF))
  momentum_convergence : ∀ r : ℕ → ℝ, ∀ hr : ∀ n, 0 < r n, Tendsto r atTop atTop →
    ∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ,ℂ),
      Tendsto (fun n =>
        (forceInterval ε a (h n) hε ha (hne n) (hh n) m g k s p (r n) (hr n) b c).evaluate q.toBCF)
          atTop (𝓝 ((J.interval b c).evaluate q.toBCF))

  spacetime_joint : ∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ × ℝ,ℂ),
    Tendsto (fun z : ℕ × Ioi (0 : ℝ) =>
      (forceWindow ε a (h z.1) hε ha (hne z.1) (hh z.1) m g k s p z.2.1 z.2.2 b c).evaluate q.toBCF)
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter (Ioi (0 : ℝ))))
        (𝓝 ((J.window b c).evaluate q.toBCF))
  momentum_joint : ∀ b c : ℝ, b ≤ c → ∀ q : C₀(ℝ,ℂ),
    Tendsto (fun z : ℕ × Ioi (0 : ℝ) =>
      (forceInterval ε a (h z.1) hε ha (hne z.1) (hh z.1) m g k s p z.2.1 z.2.2 b c).evaluate q.toBCF)
        ((atTop : Filter ℕ) ×ˢ (atTop : Filter (Ioi (0 : ℝ))))
        (𝓝 ((J.interval b c).evaluate q.toBCF))

theorem exists_force_of_probability_limit (hz : Tendsto h atTop (𝓝 0))
    (ν : ℝ → ProbabilityMeasure ℝ)
    (hchar : ∀ z : ℝ × ℝ, Tendsto (fun n => curve ε a (h n) hε ha (hne n) (hh n)
      m g k s p z) atTop (𝓝 (charFun (ν z.1 : Measure ℝ) z.2)))
    (hm : 0 < m) (hg : 0 < g) (hk : 0 < k) :
    Continuous ν ∧ ν s = initialProbability p ∧
      ∃ J : Force, Description ε a hε ha m g k s p h hne hh ν J := by
  let r : ℕ → ℝ := fun n => (n : ℝ)+1
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r]; positivity
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨ρ,hρ,κ,hκcont,hκinitial,hκ,_,_,_,_,J,_,_,hpa,hna,
    hslice,_,_,hbound,hbalance,htensor,huniform,hsmooth,hfourier,hreconstruct,hunique⟩ :=
    KFCausalNeutralNetForceDynamics.exists_net_force_dynamics
      ε a hε ha m g k s p h hne hh hz r hr hm hg hk hrtop
  have he : κ = ν := probability_curve_eq_of_characteristic_limits _ κ ν hκ
    (fun z => (hchar z).comp hρ.tendsto_atTop)
  subst κ
  refine ⟨hκcont,hκinitial,J,⟨hpa,hna,hslice,hbound,hbalance,htensor,huniform,hsmooth,
    hfourier,hreconstruct,hunique,?_,?_,?_,?_⟩⟩
  · exact spacetime_converges ε a hε ha m g k s p h hne hh hz ν hchar J hbalance hm hg hk
  · exact momentum_converges ε a hε ha m g k s p h hne hh hz ν hchar J hbalance hm hg hk
  · exact spacetime_joint_limit ε a hε ha m g k s p h hne hh hz ν hchar J hbalance hm hg hk
  · exact momentum_joint_limit ε a hε ha m g k s p h hne hh hz ν hchar J hbalance hm hg hk

#print axioms exists_force_of_probability_limit
end
end UnifiedTheory.Audit.KFCausalNeutralProbabilityDeterminesForce
