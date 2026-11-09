/-
Finite positive spectral excitation for the actual OS Hamiltonian follows from
a nonzero vacuum-orthogonal state and a positive vacuum form gap. The actual
centered Laplace resolvent is positive and nonzero, its norm rho lies in (0,1),
and the bounded C*-algebra spectrum contains rho. A hypothetical graph inverse
at rho^(-1)-1 would construct a bounded inverse at rho, contradicting that
spectral membership. No compactness, eigenvector, or finite-excitation hypothesis
is used. Exact graph transport supplies the same result on full Schwartz states.

The module also derives vacuum uniqueness from centered coercivity and combines
the proved results into the repository SpectralRequirements structure. The
physical hierarchy, quantitative connected-kernel decay, and nonzero continuum
orthogonal state remain explicit inputs; this is conditional spectral
reconstruction, not a construction of continuum Yang--Mills theory.
-/

import UnifiedTheory.Clay.YangMills.OSFormGapResolvent
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSFiniteExcitation
noncomputable section
open MeasureTheory ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSLaplaceResolvent OSLaplaceHamiltonian
open OSFormGapResolvent

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane}
  (D : Evolution W plane hp)

theorem vacuumProjection_symmetric (x y : State (hp := hp)) :
    inner ℂ (vacuumProjection x) y = inner ℂ x (vacuumProjection y) := by
  rw [vacuumProjection_apply, vacuumProjection_apply,
    inner_smul_left (𝕜 := ℂ) (OSVacuumSector.vacuum W plane hp) y
      (inner ℂ (OSVacuumSector.vacuum W plane hp) x),
    inner_smul_right (𝕜 := ℂ) x (OSVacuumSector.vacuum W plane hp)
      (inner ℂ (OSVacuumSector.vacuum W plane hp) y)]
  rw [← inner_conj_symm (𝕜 := ℂ) x (OSVacuumSector.vacuum W plane hp)]
  ring

theorem centeredResolvent_symmetric (x y : State (hp := hp)) :
    inner ℂ (centeredResolvent D x) y = inner ℂ x (centeredResolvent D y) := by
  rw [centeredResolvent_apply, centeredResolvent_apply, inner_sub_left, inner_sub_right,
    resolvent_symmetric, vacuumProjection_symmetric]

/-- Positivity is inherited from the actual Laplace integral after orthogonal
vacuum subtraction, not inferred from a hypothetical spectral description. -/
theorem centeredResolvent_positive
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) :
    (centeredResolvent D).IsPositive := by
  refine ⟨centeredResolvent_symmetric D, ?_⟩
  intro x
  let q := center (hp := hp) x
  have ho : inner ℂ (OSVacuumSector.vacuum W plane hp) (resolvent D q) = 0 := by
    rw [← resolvent_symmetric, OSHamiltonianVacuum.resolvent_vacuum]
    exact OSVacuumSector.centered_orthogonal W plane hp hn x
  have hc : inner ℂ (resolvent D q) (vacuumProjection x) = 0 := by
    rw [vacuumProjection_apply, inner_smul_right (𝕜 := ℂ) (resolvent D q)
      (OSVacuumSector.vacuum W plane hp) (inner ℂ (OSVacuumSector.vacuum W plane hp) x),
      ← inner_conj_symm (𝕜 := ℂ) (resolvent D q) (OSVacuumSector.vacuum W plane hp), ho]
    simp only [map_zero, mul_zero]
  have he : inner ℂ (resolvent D q) q = inner ℂ (resolvent D q) x := by
    change inner ℂ (resolvent D q) (x - vacuumProjection x) = _
    rw [inner_sub_right, hc, sub_zero]
  change 0 ≤ (inner ℂ (resolvent D q) x).re
  rw [← he]
  have h := resolvent_positive D q
  rw [resolvent_symmetric] at ⊢
  exact h

theorem centeredResolvent_ne_zero (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    centeredResolvent D ≠ 0 := by
  intro hz
  have h := congrArg (fun f : State (hp := hp) →L[ℂ] State (hp := hp) => f w) hz
  change centeredResolvent D w = 0 at h
  rw [centeredResolvent_apply, vacuumProjection_apply, ho, zero_smul, sub_zero] at h
  exact hw (resolvent_injective D (by simpa only [map_zero] using h))

/-- A nonzero positive centered resolvent has its positive norm in its spectrum.
This is the bounded C*-algebra spectrum, with no compactness or eigenvector premise. -/
theorem centeredResolvent_norm_mem_spectrum
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    (‖centeredResolvent D‖ : ℂ) ∈ spectrum ℂ (centeredResolvent D) := by
  letI endomorphismNontrivial : Nontrivial (State (hp := hp) →L[ℂ] State (hp := hp)) :=
    ⟨⟨centeredResolvent D, 0, centeredResolvent_ne_zero D w hw ho⟩⟩
  have hnonneg : 0 ≤ centeredResolvent D :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (centeredResolvent_positive D hn)
  have hs := CStarAlgebra.norm_mem_spectrum_of_nonneg (a := centeredResolvent D) hnonneg
  exact spectrum.algebraMap_mem ℂ (R := ℝ)
    (A := State (hp := hp) →L[ℂ] State (hp := hp)) hs

/-- The left graph inverse law evaluated on the existing Laplace range. -/
theorem inverse_shiftedFactor (lam : ℝ)
    (B : SpectralGap.ResolventWitness (hamiltonian D) lam) (x : State (hp := hp)) :
    B.inverse (shiftedFactor D lam x) = resolvent D x := by
  have h := B.left_inverse (rangePoint D x)
  rw [apply_range, rangePoint_value] at h
  have he : x - resolvent D x - (lam : ℂ) • resolvent D x = shiftedFactor D lam x := by
    rw [shiftedFactor_apply, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
    module
  rw [he] at h
  exact h

/-- The right graph inverse law gives the other resolvent-factor identity. -/
theorem resolvent_inverse_identity (lam : ℝ)
    (B : SpectralGap.ResolventWitness (hamiltonian D) lam) (x : State (hp := hp)) :
    resolvent D x + ((1 + lam : ℝ) : ℂ) • resolvent D (B.inverse x) = B.inverse x := by
  have h := (graph_iff D _ _).mp (B.right_inverse x)
  rw [map_add, map_add, map_smul] at h
  rw [Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
  convert h using 1
  module

/-- A hypothetical unbounded graph resolvent constructs an actual unit in the
bounded operator algebra; no bounded inverse is assumed separately. -/
theorem shiftedFactor_isUnit_of_graph_inverse (lam : ℝ)
    (B : SpectralGap.ResolventWitness (hamiltonian D) lam) : IsUnit (shiftedFactor D lam) := by
  let V : State (hp := hp) →L[ℂ] State (hp := hp) :=
    1 + ((1 + lam : ℝ) : ℂ) • B.inverse
  refine ⟨⟨shiftedFactor D lam, V, ?_, ?_⟩, rfl⟩
  · ext x
    change shiftedFactor D lam (x + ((1 + lam : ℝ) : ℂ) • B.inverse x) = x
    rw [shiftedFactor_apply, map_add, map_smul, resolvent_inverse_identity D lam B]
    module
  · ext x
    change shiftedFactor D lam x +
      ((1 + lam : ℝ) : ℂ) • B.inverse (shiftedFactor D lam x) = x
    rw [inverse_shiftedFactor D lam B, shiftedFactor_apply, sub_add_cancel]

def vacuumFactor (lam : ℝ) : State (hp := hp) →L[ℂ] State (hp := hp) :=
  1 - ((1 + lam : ℝ) : ℂ) • vacuumProjection

theorem neumann_mul_vacuumFactor
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) (lam : ℝ) :
    neumannOperator D lam * vacuumFactor (hp := hp) lam = shiftedFactor D lam := by
  ext x
  change neumannOperator D lam (x - ((1 + lam : ℝ) : ℂ) • vacuumProjection x) = _
  rw [neumannOperator_apply, map_sub, map_smul, centeredResolvent_vacuumProjection D hn,
    smul_zero, sub_zero, centeredResolvent_apply, shiftedFactor_apply, smul_sub]
  module

theorem vacuumFactor_mul_neumann
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x) (lam : ℝ) :
    vacuumFactor (hp := hp) lam * neumannOperator D lam = shiftedFactor D lam := by
  ext x
  change neumannOperator D lam x -
    ((1 + lam : ℝ) : ℂ) • vacuumProjection (neumannOperator D lam x) = _
  rw [vacuumProjection_neumann D hn, neumannOperator_apply, centeredResolvent_apply,
    shiftedFactor_apply, smul_sub]
  module

theorem neumann_isUnit_of_graph_inverse
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (lam : ℝ) (B : SpectralGap.ResolventWitness (hamiltonian D) lam) :
    IsUnit (neumannOperator D lam) := by
  letI operatorMonoid : Monoid (State (hp := hp) →L[ℂ] State (hp := hp)) :=
    (ContinuousLinearMap.monoidWithZero (R₁ := ℂ) (M₁ := State (hp := hp))).toMonoid
  have hc : Commute (neumannOperator D lam) (vacuumFactor (hp := hp) lam) :=
    (neumann_mul_vacuumFactor D hn lam).trans (vacuumFactor_mul_neumann D hn lam).symm
  have hprod : IsUnit (neumannOperator D lam * vacuumFactor (hp := hp) lam) := by
    rw [neumann_mul_vacuumFactor D hn lam]
    exact shiftedFactor_isUnit_of_graph_inverse D lam B
  exact ((Commute.isUnit_mul_iff
    (M := State (hp := hp) →L[ℂ] State (hp := hp)) hc).mp hprod).1

/-- A nonzero bounded spectral value transforms to a failure of the actual
unbounded graph-resolvent requirement, including continuous spectrum. -/
theorem not_inRealResolvent_of_centered_spectrum
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (rho : ℝ) (hrho : rho ≠ 0)
    (hs : (rho : ℂ) ∈ spectrum ℂ (centeredResolvent D)) :
    ¬ SpectralGap.InRealResolvent (hamiltonian D) (rho⁻¹ - 1) := by
  rintro ⟨B⟩
  have hN := neumann_isUnit_of_graph_inverse D hn (rho⁻¹ - 1) B
  have hscalar : IsUnit (algebraMap ℂ (State (hp := hp) →L[ℂ] State (hp := hp)) (rho : ℂ)) :=
    (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hrho)).map _
  have hunit := hscalar.mul hN
  have he : algebraMap ℂ (State (hp := hp) →L[ℂ] State (hp := hp)) (rho : ℂ) *
      neumannOperator D (rho⁻¹ - 1) =
      algebraMap ℂ (State (hp := hp) →L[ℂ] State (hp := hp)) (rho : ℂ) -
        centeredResolvent D := by
    ext x
    change (rho : ℂ) •
      (x - ((1 + (rho⁻¹ - 1) : ℝ) : ℂ) • centeredResolvent D x) =
        (rho : ℂ) • x - centeredResolvent D x
    rw [smul_sub, smul_smul]
    have hc : (rho : ℂ) * ((1 + (rho⁻¹ - 1) : ℝ) : ℂ) = 1 := by
      rw [show (1 + (rho⁻¹ - 1) : ℝ) = rho⁻¹ by ring, Complex.ofReal_inv,
        mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hrho)]
    rw [hc, one_smul]
  rw [he] at hunit
  exact (spectrum.mem_iff.mp hs) hunit

/-- The nonzero centered state and positive form gap force a finite positive
spectral excitation. No compactness, eigenvector, or finite-excitation premise is used. -/
theorem finiteExcitation_of_formGap
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    SpectralGap.FiniteExcitation (hamiltonian D) := by
  have hrho : 0 < ‖centeredResolvent D‖ := (norm_pos_iff (a := centeredResolvent D)).mpr
    (centeredResolvent_ne_zero D w hw ho)
  have hlt : ‖centeredResolvent D‖ < 1 :=
    lt_of_le_of_lt (centeredResolvent_norm D hn m hm hgap)
      ((inv_lt_one₀ (by linarith : 0 < 1 + m)).mpr (by linarith))
  refine ⟨‖centeredResolvent D‖⁻¹ - 1,
    sub_pos.mpr ((one_lt_inv₀ hrho).mpr hlt), ?_⟩
  exact not_inRealResolvent_of_centered_spectrum D hn _ (ne_of_gt hrho)
    (centeredResolvent_norm_mem_spectrum D hn w hw ho)

theorem finiteExcitation_of_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m)
    (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    SpectralGap.FiniteExcitation (hamiltonian D) :=
  finiteExcitation_of_formGap D hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay) w hw ho

/-- A full Schwartz graph inverse would pull back to a graph inverse on the
original kernel Hilbert space by the proved unitary graph equivalence. -/
def pullbackResolventWitness
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (lam : ℝ) (B : SpectralGap.ResolventWitness
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) lam) :
    SpectralGap.ResolventWitness (hamiltonian D) lam where
  inverse :=
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    e.symm.toLinearIsometry.toContinuousLinearMap.comp
      (B.inverse.comp e.toLinearIsometry.toContinuousLinearMap)
  right_inverse y := by
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    have h := (FullSchwartzHamiltonian.graph_transport W plane hp hfull D _ _).mp
      (B.right_inverse (e y))
    change (e.symm (B.inverse (e y)),
      e.symm (e y + (lam : ℂ) • B.inverse (e y))) ∈ (hamiltonian D).graph at h
    simp only [map_add, map_smul, LinearIsometryEquiv.symm_apply_apply] at h
    exact h
  left_inverse x := by
    let e := FullSchwartzHilbert.equivalence W plane hp hfull
    have hg : (e (x : State (hp := hp)), e (hamiltonian D x)) ∈
        (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph := by
      rw [FullSchwartzHamiltonian.graph_transport]
      simp only [e, LinearIsometryEquiv.symm_apply_apply]
      exact (hamiltonian D).mem_graph_iff.mpr ⟨x, rfl, rfl⟩
    obtain ⟨u, hu, hAu⟩ :=
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).mem_graph_iff.mp hg
    have h := congrArg e.symm (B.left_inverse u)
    rw [hu, hAu, LinearIsometryEquiv.symm_apply_apply] at h
    change e.symm (B.inverse (e (hamiltonian D x -
      (lam : ℂ) • (x : State (hp := hp))))) = x
    rw [map_sub, map_smul]
    exact h

theorem full_finiteExcitation_of_formGap
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    SpectralGap.FiniteExcitation (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  have hnonzero : e.symm w ≠ 0 := by
    intro hz
    exact hw (e.symm.injective (by simpa only [map_zero] using hz))
  have horth : inner ℂ (OSVacuumSector.vacuum W plane hp) (e.symm w) = 0 := by
    have h := e.symm.inner_map_map (RenormalizedFullOSLimit.fullVacuum W plane hfull) w
    rw [FullSchwartzVacuum.inverse_vacuum] at h
    exact h.trans ho
  obtain ⟨lam, hlam, hnot⟩ := finiteExcitation_of_formGap D hn m hm hgap
    (e.symm w) hnonzero horth
  refine ⟨lam, hlam, ?_⟩
  rintro ⟨B⟩
  exact hnot ⟨pullbackResolventWitness D hfull lam B⟩

theorem full_finiteExcitation_of_quadraticDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    SpectralGap.FiniteExcitation (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D) :=
  full_finiteExcitation_of_formGap D hfull hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay) w hw ho

/-- Positive centered coercivity also excludes every additional zero-energy
vector of the actual maximal Hamiltonian. -/
theorem unique_zero_of_formGap
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (x : State (hp := hp)) (hg : (x, 0) ∈ (hamiltonian D).graph) :
    ∃ c : ℂ, x = c • OSVacuumSector.vacuum W plane hp := by
  have hR : resolvent D x = x := by
    simpa only [zero_add] using (graph_iff D x 0).mp hg
  let u := center (hp := hp) x
  have hP : vacuumProjection u = 0 := by
    change vacuumProjection (x - vacuumProjection x) = 0
    rw [map_sub, vacuumProjection_idempotent hn, sub_self]
  have hRu : resolvent D u = u := by
    change resolvent D (x - vacuumProjection x) = x - vacuumProjection x
    rw [map_sub, hR, resolvent_vacuumProjection]
  have hJ : centeredResolvent D u = u := by
    rw [centeredResolvent_apply, hRu, hP, sub_zero]
  have hb := centeredResolvent_bound D hn m hm hgap u
  rw [hJ] at hb
  have hc : (1 + m)⁻¹ < 1 :=
    (inv_lt_one₀ (by linarith : 0 < 1 + m)).mpr (by linarith)
  have hz : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
  have hu := norm_eq_zero.mp hz
  refine ⟨inner ℂ (OSVacuumSector.vacuum W plane hp) x, ?_⟩
  exact sub_eq_zero.mp hu

theorem full_unique_zero_of_formGap
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (x : FullSchwartzHamiltonian.State W plane hfull)
    (hg : (x, 0) ∈ (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).graph) :
    ∃ c : ℂ, x = c • RenormalizedFullOSLimit.fullVacuum W plane hfull := by
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  have h := (FullSchwartzHamiltonian.graph_transport W plane hp hfull D x 0).mp hg
  simp only [map_zero] at h
  obtain ⟨c, hc⟩ := unique_zero_of_formGap D hn m hm hgap (e.symm x) h
  refine ⟨c, ?_⟩
  have he := congrArg e hc
  simpa only [e, LinearIsometryEquiv.apply_symm_apply, map_smul,
    FullSchwartzVacuum.equivalence_vacuum] using he

/-- The full repository spectral package follows from the physical form bound
and an actual nonzero orthogonal state. These two inputs are not constructed here. -/
theorem spectralRequirements_of_formGap
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    SpectralGap.SpectralRequirements (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m := by
  refine {
    self_adjoint := selfAdjoint D
    vacuum_norm := OSVacuumSector.vacuum_norm W plane hp hn
    vacuum_stationary := OSHamiltonianVacuum.vacuum_graph D
    positive_energy := ?_
    unique_zero_energy := unique_zero_of_formGap D hn m hm hgap
    spectral_gap := intervalGap_of_formGap D hn m hm hgap
    finite_excitation := finiteExcitation_of_formGap D hn m hm hgap w hw ho }
  intro x
  have he : (inner ℂ (hamiltonian D x) (x : State (hp := hp))).re =
      (inner ℂ (x : State (hp := hp)) (hamiltonian D x)).re := by
    simpa only [RCLike.re_to_complex] using
      (inner_re_symm (𝕜 := ℂ) (hamiltonian D x) (x : State (hp := hp)))
  rw [he]
  exact nonnegative D x

theorem spectralRequirements_of_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m)
    (w : State (hp := hp)) (hw : w ≠ 0)
    (ho : inner ℂ (OSVacuumSector.vacuum W plane hp) w = 0) :
    SpectralGap.SpectralRequirements (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m :=
  spectralRequirements_of_formGap D hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay) w hw ho

theorem full_spectralRequirements_of_formGap
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hgap : SpectralGap.VacuumFormGap (hamiltonian D) (OSVacuumSector.vacuum W plane hp) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    SpectralGap.SpectralRequirements
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D)
      (RenormalizedFullOSLimit.fullVacuum W plane hfull) m := by
  refine {
    self_adjoint := FullSchwartzHamiltonian.selfAdjoint W plane hp hfull D
    vacuum_norm := RenormalizedFullOSLimit.fullVacuum_norm W plane hp hfull hn
    vacuum_stationary := FullSchwartzVacuum.vacuum_graph W plane hp hfull D
    positive_energy := ?_
    unique_zero_energy := full_unique_zero_of_formGap D hfull hn m hm hgap
    spectral_gap := full_intervalGap_of_formGap D hfull hn m hm hgap
    finite_excitation := full_finiteExcitation_of_formGap D hfull hn m hm hgap w hw ho }
  intro x
  have he :
      (inner ℂ (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)
        (x : FullSchwartzHamiltonian.State W plane hfull)).re =
      (inner ℂ (x : FullSchwartzHamiltonian.State W plane hfull)
        (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)).re := by
    simpa only [RCLike.re_to_complex] using (inner_re_symm (𝕜 := ℂ)
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)
      (x : FullSchwartzHamiltonian.State W plane hfull))
  rw [he]
  exact FullSchwartzHamiltonian.nonnegative W plane hp hfull D x

/-- Conditional spectral reconstruction for the actual full Schwartz candidate.
The physical correlation estimate and nonzero orthogonal state remain explicit. -/
theorem full_spectralRequirements_of_quadraticDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m)
    (hdecay : OSClusteringGap.QuadraticDecay (W := W) (plane := plane) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    SpectralGap.SpectralRequirements
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D)
      (RenormalizedFullOSLimit.fullVacuum W plane hfull) m :=
  full_spectralRequirements_of_formGap D hfull hn m hm
    (OSClusteringGap.vacuumFormGap_of_quadraticDecay D hn m hdecay) w hw ho

end
end UnifiedTheory.Clay.YangMills.OSFiniteExcitation
