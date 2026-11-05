/-
An actual vacuum form gap gives bounded two-sided resolvents throughout the
positive gap interval for the constructed maximal OS Hamiltonian. The proof
sharpens the centered Laplace-resolvent bound to 1/(1+m), constructs a genuine
Neumann inverse for every 0 < lambda < m, and adds the explicit vacuum inverse.
Both inverse laws are proved on the actual maximal graph. The resulting bounded
resolvents transfer through the established full Schwartz unitary equivalence.

Combined with OSClusteringGap this closes the conditional implication from its
explicit connected-kernel quadratic decay estimate to SpectralGap.IntervalGap.
The physical decay estimate, a nonzero continuum excitation, and the separate
FiniteExcitation requirement remain unproved here.
-/

import UnifiedTheory.Clay.YangMills.OSClusteringGap
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSFormGapResolvent
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSLaplaceResolvent OSLaplaceHamiltonian

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane}
  (D : Evolution W plane hp)

def vacuumProjection : State (hp := hp) →L[ℂ] State (hp := hp) :=
  (innerSL ℂ (OSVacuumSector.vacuum W plane hp)).smulRight
    (OSVacuumSector.vacuum W plane hp)

def center : State (hp := hp) →L[ℂ] State (hp := hp) := 1 - vacuumProjection (hp := hp)

@[simp] theorem vacuumProjection_apply (x : State (hp := hp)) :
    vacuumProjection x = (inner ℂ (OSVacuumSector.vacuum W plane hp) x) •
      OSVacuumSector.vacuum W plane hp := rfl

@[simp] theorem center_apply (x : State (hp := hp)) :
    center x = OSVacuumSector.centered W plane hp x := rfl

theorem vacuumProjection_idempotent
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (x : State (hp := hp)) : vacuumProjection (vacuumProjection x) = vacuumProjection x := by
  simp only [vacuumProjection_apply]
  rw [inner_smul_right (𝕜 := ℂ) (OSVacuumSector.vacuum W plane hp)
    (OSVacuumSector.vacuum W plane hp)
    (inner ℂ (OSVacuumSector.vacuum W plane hp) x),
    OSVacuumSector.vacuum_inner W plane hp hn, mul_one]

theorem vacuumProjection_resolvent (x : State (hp := hp)) :
    vacuumProjection (resolvent D x) = vacuumProjection x := by
  simp only [vacuumProjection_apply, ← resolvent_symmetric, OSHamiltonianVacuum.resolvent_vacuum]

theorem resolvent_vacuumProjection (x : State (hp := hp)) :
    resolvent D (vacuumProjection x) = vacuumProjection x := by
  simp only [vacuumProjection_apply, map_smul, OSHamiltonianVacuum.resolvent_vacuum]

def centeredResolvent : State (hp := hp) →L[ℂ] State (hp := hp) :=
  (resolvent D).comp center

@[simp] theorem centeredResolvent_apply (x : State (hp := hp)) :
    centeredResolvent D x = resolvent D x - vacuumProjection x := by
  simp only [centeredResolvent, ContinuousLinearMap.comp_apply, center,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub,
    resolvent_vacuumProjection]

theorem vacuumProjection_centeredResolvent
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (x : State (hp := hp)) : vacuumProjection (centeredResolvent D x) = 0 := by
  rw [centeredResolvent_apply, map_sub, vacuumProjection_resolvent,
    vacuumProjection_idempotent hn, sub_self]

theorem centeredResolvent_vacuumProjection
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (x : State (hp := hp)) : centeredResolvent D (vacuumProjection x) = 0 := by
  rw [centeredResolvent_apply, resolvent_vacuumProjection,
    vacuumProjection_idempotent hn, sub_self]

theorem centered_norm_le
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (x : State (hp := hp)) : ‖center x‖ ≤ ‖x‖ := by
  have h := OSFixedSector.centered_norm_sq hn x
  change ‖center x‖ ^ 2 = ‖x‖ ^ 2 -
    ‖inner ℂ (OSVacuumSector.vacuum W plane hp) x‖ ^ 2 at h
  nlinarith [sq_nonneg ‖inner ℂ (OSVacuumSector.vacuum W plane hp) x‖,
    norm_nonneg (center x), norm_nonneg x]

/-- The form gap sharpens the actual centered Laplace resolvent norm. -/
theorem centeredResolvent_bound
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (x : State (hp := hp)) :
    ‖centeredResolvent D x‖ ≤ (1 + m)⁻¹ * ‖x‖ := by
  let u := center (hp := hp) x
  have ho : inner ℂ (OSVacuumSector.vacuum W plane hp) (resolvent D u) = 0 := by
    rw [← resolvent_symmetric, OSHamiltonianVacuum.resolvent_vacuum]
    exact OSVacuumSector.centered_orthogonal W plane hp hn x
  have h := hgap (rangePoint D u) ho
  rw [apply_range, rangePoint_value, inner_sub_left, Complex.sub_re] at h
  rw [show (inner ℂ (resolvent D u) (resolvent D u)).re = ‖resolvent D u‖ ^ 2 from
    inner_self_eq_norm_sq (𝕜 := ℂ) (resolvent D u)] at h
  have hpair := re_inner_le_norm (𝕜 := ℂ) u (resolvent D u)
  change (inner ℂ u (resolvent D u)).re ≤ ‖u‖ * ‖resolvent D u‖ at hpair
  have hbound : (1 + m) * ‖resolvent D u‖ ≤ ‖u‖ := by
    by_cases hz : resolvent D u = 0
    · simp only [hz, norm_zero, mul_zero, norm_nonneg]
    · have hpos := norm_pos_iff.mpr hz
      nlinarith
  have hu := centered_norm_le hn x
  change ‖u‖ ≤ ‖x‖ at hu
  change ‖resolvent D u‖ ≤ (1 + m)⁻¹ * ‖x‖
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (by linarith : 0 < 1 + m)).mpr (by nlinarith)

theorem centeredResolvent_norm
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m) :
    ‖centeredResolvent D‖ ≤ (1 + m)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (centeredResolvent_bound D hn m hm hgap)

def neumannOperator (lam : ℝ) : State (hp := hp) →L[ℂ] State (hp := hp) :=
  1 - ((1 + lam : ℝ) : ℂ) • centeredResolvent D

def neumannInverse (lam : ℝ) : State (hp := hp) →L[ℂ] State (hp := hp) :=
  Ring.inverse (neumannOperator D lam)

@[simp] theorem neumannOperator_apply (lam : ℝ) (x : State (hp := hp)) :
    neumannOperator D lam x = x - ((1 + lam : ℝ) : ℂ) • centeredResolvent D x := rfl

/-- A genuine Banach-algebra inverse follows from the derived centered norm bound. -/
theorem neumannOperator_isUnit
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (lam : ℝ) (hlam : 0 < lam) (hlam_m : lam < m) : IsUnit (neumannOperator D lam) := by
  unfold neumannOperator
  apply isUnit_one_sub_of_norm_lt_one (R := State (hp := hp) →L[ℂ] State (hp := hp))
  have hnlam : ‖((1 + lam : ℝ) : ℂ)‖ = 1 + lam := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hb : ‖((1 + lam : ℝ) : ℂ) • centeredResolvent D‖ ≤
      (1 + lam) * (1 + m)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖((1 + lam : ℝ) : ℂ) • centeredResolvent D x‖ ≤
      ((1 + lam) * (1 + m)⁻¹) * ‖x‖
    rw [norm_smul, hnlam, mul_assoc]
    exact mul_le_mul_of_nonneg_left (centeredResolvent_bound D hn m hm hgap x)
      (by linarith)
  apply lt_of_le_of_lt hb
  rw [← div_eq_mul_inv]
  exact (div_lt_one (by linarith : 0 < 1 + m)).mpr (by linarith)

theorem neumann_right (lam : ℝ) (hunit : IsUnit (neumannOperator D lam))
    (x : State (hp := hp)) : neumannOperator D lam (neumannInverse D lam x) = x := by
  have h := congrArg (fun f : State (hp := hp) →L[ℂ] State (hp := hp) => f x)
    (Ring.mul_inverse_cancel (neumannOperator D lam) hunit)
  exact h

theorem neumann_left (lam : ℝ) (hunit : IsUnit (neumannOperator D lam))
    (x : State (hp := hp)) : neumannInverse D lam (neumannOperator D lam x) = x := by
  have h := congrArg (fun f : State (hp := hp) →L[ℂ] State (hp := hp) => f x)
    (Ring.inverse_mul_cancel (neumannOperator D lam) hunit)
  exact h

theorem vacuumProjection_neumann
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (lam : ℝ) (x : State (hp := hp)) :
    vacuumProjection (neumannOperator D lam x) = vacuumProjection x := by
  rw [neumannOperator_apply, map_sub, map_smul, vacuumProjection_centeredResolvent D hn,
    smul_zero, sub_zero]

theorem vacuumProjection_neumannInverse
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (lam : ℝ) (hunit : IsUnit (neumannOperator D lam)) (x : State (hp := hp)) :
    vacuumProjection (neumannInverse D lam x) = vacuumProjection x := by
  have h := congrArg (vacuumProjection (hp := hp)) (neumann_right D lam hunit x)
  rw [vacuumProjection_neumann D hn] at h
  exact h

def shiftedFactor (lam : ℝ) : State (hp := hp) →L[ℂ] State (hp := hp) :=
  1 - ((1 + lam : ℝ) : ℂ) • resolvent D

@[simp] theorem shiftedFactor_apply (lam : ℝ) (x : State (hp := hp)) :
    shiftedFactor D lam x = x - ((1 + lam : ℝ) : ℂ) • resolvent D x := rfl

theorem shiftedFactor_neumann (lam : ℝ) (x : State (hp := hp)) :
    shiftedFactor D lam x = neumannOperator D lam x -
      ((1 + lam : ℝ) : ℂ) • vacuumProjection x := by
  rw [shiftedFactor_apply, neumannOperator_apply, centeredResolvent_apply, smul_sub]
  module

theorem vacuumProjection_shiftedFactor (lam : ℝ) (x : State (hp := hp)) :
    vacuumProjection (shiftedFactor D lam x) = -(lam : ℂ) • vacuumProjection x := by
  rw [shiftedFactor_apply, map_sub, map_smul, vacuumProjection_resolvent,
    Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
  module

theorem shiftedFactor_vacuumProjection (lam : ℝ) (x : State (hp := hp)) :
    shiftedFactor D lam (vacuumProjection x) = -(lam : ℂ) • vacuumProjection x := by
  rw [shiftedFactor_apply, resolvent_vacuumProjection,
    Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
  module

theorem shiftedFactor_injective
    (lam : ℝ) (hlam : lam ≠ 0) (hunit : IsUnit (neumannOperator D lam)) :
    Function.Injective (shiftedFactor D lam) := by
  apply (shiftedFactor D lam).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  change shiftedFactor D lam x = 0 at hx
  have hpz := congrArg (vacuumProjection (hp := hp)) hx
  rw [vacuumProjection_shiftedFactor, map_zero] at hpz
  have hP : vacuumProjection x = 0 := (smul_eq_zero.mp hpz).resolve_left (by
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlam))
  have hK : neumannOperator D lam x = 0 := by
    rw [shiftedFactor_neumann, hP, smul_zero, sub_zero] at hx
    exact hx
  have h := neumann_left D lam hunit x
  rw [hK, map_zero] at h
  exact h.symm

def shiftedInverse (lam : ℝ) : State (hp := hp) →L[ℂ] State (hp := hp) :=
  (neumannInverse D lam).comp (centeredResolvent D) -
    (lam : ℂ)⁻¹ • vacuumProjection

@[simp] theorem shiftedInverse_apply (lam : ℝ) (x : State (hp := hp)) :
    shiftedInverse D lam x = neumannInverse D lam (centeredResolvent D x) -
      (lam : ℂ)⁻¹ • vacuumProjection x := rfl

theorem shiftedInverse_factor
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (lam : ℝ) (hlam : lam ≠ 0) (hunit : IsUnit (neumannOperator D lam))
    (x : State (hp := hp)) :
    shiftedFactor D lam (shiftedInverse D lam x) = resolvent D x := by
  rw [shiftedInverse_apply, map_sub, map_smul, shiftedFactor_vacuumProjection,
    shiftedFactor_neumann, neumann_right D lam hunit,
    vacuumProjection_neumannInverse D hn lam hunit,
    vacuumProjection_centeredResolvent D hn, smul_zero, sub_zero,
    smul_smul, mul_neg, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam),
    neg_one_smul, sub_neg_eq_add, centeredResolvent_apply, sub_add_cancel]

/-- The constructed bounded map is a two-sided resolvent witness on the exact
maximal Hamiltonian graph; the inverse is not supplied as a hypothesis. -/
def resolventWitness
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (lam : ℝ) (hlam : lam ≠ 0) (hunit : IsUnit (neumannOperator D lam)) :
    SpectralGap.ResolventWitness (hamiltonian D) lam where
  inverse := shiftedInverse D lam
  right_inverse y := by
    apply (graph_iff D _ _).mpr
    have h := shiftedInverse_factor D hn lam hlam hunit y
    rw [shiftedFactor_apply] at h
    rw [map_add, map_add, map_smul]
    rw [← h]
    simp only [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
    module
  left_inverse x := by
    apply shiftedFactor_injective D lam hlam hunit
    rw [shiftedInverse_factor D hn lam hlam hunit, map_sub, map_smul,
      shiftedFactor_apply]
    have h := resolvent_left D x
    rw [map_add] at h
    rw [eq_sub_of_add_eq h]
    rw [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
    module

theorem intervalGap_of_formGap
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m) :
    SpectralGap.IntervalGap (hamiltonian D) m := by
  refine ⟨hm, ?_⟩
  intro lam hlam hlam_m
  exact ⟨resolventWitness D hn lam (ne_of_gt hlam)
    (neumannOperator_isUnit D hn m hm hgap lam hlam hlam_m)⟩

theorem intervalGap_of_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m) :
    SpectralGap.IntervalGap (hamiltonian D) m :=
  intervalGap_of_formGap D hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay)

/-- Transport an actually constructed bounded two-sided inverse through the
existing unitary equivalence and exact Hamiltonian graph identity. -/
def fullResolventWitness
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (lam : ℝ) (R : SpectralGap.ResolventWitness (hamiltonian D) lam) :
    SpectralGap.ResolventWitness
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) lam where
  inverse :=
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    e.toLinearIsometry.toContinuousLinearMap.comp
      (R.inverse.comp e.symm.toLinearIsometry.toContinuousLinearMap)
  right_inverse y := by
    rw [FullSchwartzHamiltonian.graph_transport]
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    change (e.symm (e (R.inverse (e.symm y))),
      e.symm (y + (lam : ℂ) • e (R.inverse (e.symm y)))) ∈ (hamiltonian D).graph
    simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply]
    exact R.right_inverse (e.symm y)
  left_inverse x := by
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    have hg := (FullSchwartzHamiltonian.graph_transport W plane hp hfull D
      (x : FullSchwartzHamiltonian.State W plane hfull)
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)).mp
        ((FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).mem_graph_iff.mpr
          ⟨x, rfl, rfl⟩)
    obtain ⟨u, hu, hAu⟩ := (hamiltonian D).mem_graph_iff.mp hg
    have h := congrArg e (R.left_inverse u)
    rw [hu, hAu, LinearIsometryEquiv.apply_symm_apply] at h
    change e (R.inverse (e.symm
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x -
        (lam : ℂ) • (x : FullSchwartzHamiltonian.State W plane hfull)))) = x
    rw [map_sub, map_smul]
    exact h

theorem full_intervalGap_of_formGap
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m) :
    SpectralGap.IntervalGap (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) m := by
  refine ⟨hm, ?_⟩
  intro lam hlam hlam_m
  obtain ⟨R⟩ := (intervalGap_of_formGap D hn m hm hgap).2 lam hlam hlam_m
  exact ⟨fullResolventWitness D hfull lam R⟩

theorem full_intervalGap_of_quadraticDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m) :
    SpectralGap.IntervalGap (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) m :=
  full_intervalGap_of_formGap D hfull hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay)

end
end UnifiedTheory.Clay.YangMills.OSFormGapResolvent
