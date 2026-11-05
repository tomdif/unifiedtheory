/-
Quantitative connected-kernel decay gives a positive energy-form bound for the
actual maximal OS Hamiltonian. The explicit input controls every finite complex
linear combination, including cross terms, at every nonnegative time with
prefactor one: C_t(c) <= exp(-2 m t) C_0(c). An exact finite-form identity and
the actual dense kernel embedding give decay on the full centered Hilbert sector;
the proved right generator derivative at zero then gives the energy bound.

The same bound transfers to the full Schwartz Hamiltonian and makes an existing
nonzero orthogonal reflected witness have strictly positive energy after actual
resolvent regularization. The physical kernel-decay inequality and the nonzero
witness remain inputs. Neither bounded resolvents throughout a spectral interval
nor the separate finite-excitation requirement is established in this module.
-/

import UnifiedTheory.Clay.YangMills.OSFixedSector
import UnifiedTheory.Clay.YangMills.OSResolventWitnessState
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.OSClusteringGap
noncomputable section
open MeasureTheory Filter ContinuumControl PeriodicLattice4 OSPositiveTimeKernel
open KernelHilbertCompletion OSScalarDynamics OSLaplaceResolvent
open scoped NNReal Topology BigOperators

variable {W : Hierarchy} {plane : Plane} {hp : Positive W plane}
  (D : Evolution W plane hp)

def translatedForm (c : Label →₀ ℂ) (t : ℝ≥0) : ℂ :=
  c.sum (fun i a => c.sum (fun j b => star a * b * kernel W plane (i, shift (t+t) j)))

def vacuumCoefficient (c : Label →₀ ℂ) : ℂ :=
  c.sum (fun i a => a * kernel W plane (OSFactorizedCollapse.vacuumLabel, i))

def connectedQuadratic (c : Label →₀ ℂ) (t : ℝ≥0) : ℝ :=
  (translatedForm (W := W) (plane := plane) c t).re -
    ‖vacuumCoefficient (W := W) (plane := plane) c‖ ^ 2

theorem embed_sum (c : Label →₀ ℂ) :
    embed (positiveKernel W plane hp) c =
      c.sum (fun i a => a • canonical (positiveKernel W plane hp) i) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single c]
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro i hi
  rw [show (Finsupp.single i (c i) : Formal (positiveKernel W plane hp)) =
    c i • basisState (positiveKernel W plane hp) i by
      change Finsupp.single i (c i) = c i • (Finsupp.single i 1 : Label →₀ ℂ)
      simp]
  rw [map_smul]
  rfl

theorem vacuumCoefficient_eq_inner (c : Label →₀ ℂ) :
    vacuumCoefficient (W := W) (plane := plane) c =
      inner ℂ (OSVacuumSector.vacuum W plane hp) (embed (positiveKernel W plane hp) c) := by
  classical
  rw [embed_sum]
  simp only [vacuumCoefficient, Finsupp.sum, inner_sum, OSVacuumSector.vacuum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_smul_right (𝕜 := ℂ)
    (canonical (positiveKernel W plane hp) OSFactorizedCollapse.vacuumLabel)
    (canonical (positiveKernel W plane hp) i) (c i), canonical_inner]
  rfl

theorem translatedForm_eq_inner (c : Label →₀ ℂ) (t : ℝ≥0) :
    translatedForm (W := W) (plane := plane) c t =
      inner ℂ (embed (positiveKernel W plane hp) c)
        (D.operator (t+t) (embed (positiveKernel W plane hp) c)) := by
  classical
  rw [embed_sum]
  simp only [Finsupp.sum, map_sum, map_smul, D.canonical_action]
  rw [sum_inner]
  simp_rw [inner_sum]
  unfold translatedForm Finsupp.sum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [inner_smul_left (𝕜 := ℂ) (canonical (positiveKernel W plane hp) i)
    (c j • canonical (positiveKernel W plane hp) (shift (t+t) j)) (c i),
    inner_smul_right (𝕜 := ℂ) (canonical (positiveKernel W plane hp) i)
      (canonical (positiveKernel W plane hp) (shift (t+t) j)) (c j), canonical_inner]
  simp only [positiveKernel, RCLike.star_def]
  ring

theorem connectedQuadratic_eq_norm_sq
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (c : Label →₀ ℂ) (t : ℝ≥0) :
    connectedQuadratic (W := W) (plane := plane) c t =
      ‖D.operator t (OSVacuumSector.centered W plane hp
        (embed (positiveKernel W plane hp) c))‖ ^ 2 := by
  rw [OSVacuumSector.evolution_centered, OSFixedSector.centered_norm_sq hn,
    OSVacuumSector.inner_vacuum_evolution, norm_sq_eq_re_inner (𝕜 := ℂ), D.symmetric,
    D.add, ← translatedForm_eq_inner, ← vacuumCoefficient_eq_inner]
  rfl

/-- Exponential domination of every finite connected reflected-kernel quadratic
form. This is an explicit physical correlation estimate, not an operator premise. -/
def QuadraticDecay (m : ℝ) : Prop :=
  ∀ (c : Label →₀ ℂ) (t : ℝ≥0),
    connectedQuadratic (W := W) (plane := plane) c t ≤
      Real.exp (-2 * m * (t : ℝ)) * connectedQuadratic (W := W) (plane := plane) c 0

theorem continuous_centered : Continuous (OSVacuumSector.centered W plane hp) := by
  exact continuous_id.sub (((innerSL ℂ (OSVacuumSector.vacuum W plane hp)).continuous).smul
    continuous_const)

/-- The actual dense kernel embedding extends the finite-form estimate to every
centered Hilbert vector without a new decay or domain assumption. -/
theorem centered_norm_sq_decay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : QuadraticDecay (W := W) (plane := plane) m)
    (t : ℝ≥0) (x : State (hp := hp)) :
    ‖D.operator t (OSVacuumSector.centered W plane hp x)‖ ^ 2 ≤
      Real.exp (-2 * m * (t : ℝ)) * ‖OSVacuumSector.centered W plane hp x‖ ^ 2 := by
  have hc : IsClosed {v : State (hp := hp) |
      ‖D.operator t (OSVacuumSector.centered W plane hp v)‖ ^ 2 ≤
        Real.exp (-2 * m * (t : ℝ)) * ‖OSVacuumSector.centered W plane hp v‖ ^ 2} :=
    isClosed_le (((D.operator t).continuous.comp continuous_centered).norm.pow 2)
      (continuous_const.mul (continuous_centered.norm.pow 2))
  apply hc.closure_subset_iff.mpr ?_ (denseRange_embed (positiveKernel W plane hp) x)
  rintro _ ⟨c, rfl⟩
  have h := hdecay c t
  rw [connectedQuadratic_eq_norm_sq D hn, connectedQuadratic_eq_norm_sq D hn, D.zero] at h
  exact h

theorem orthogonal_norm_sq_decay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : QuadraticDecay (W := W) (plane := plane) m)
    (t : ℝ≥0) (x : State (hp := hp))
    (hx : inner ℂ (OSVacuumSector.vacuum W plane hp) x = 0) :
    ‖D.operator t x‖ ^ 2 ≤ Real.exp (-2 * m * (t : ℝ)) * ‖x‖ ^ 2 := by
  simpa only [OSVacuumSector.centered, hx, zero_smul, sub_zero] using
    centered_norm_sq_decay D hn m hdecay t x

/-- Exact right derivative of the squared norm on the full constructed
Hamiltonian domain. -/
theorem right_norm_sq_derivative (x : (OSLaplaceHamiltonian.hamiltonian D).domain) :
    HasDerivWithinAt (fun t : ℝ => ‖D.operator t.toNNReal (x : State (hp := hp))‖ ^ 2)
      (-2 * (inner ℂ (OSLaplaceHamiltonian.hamiltonian D x) (x : State (hp := hp))).re)
      (Set.Ici 0) 0 := by
  letI realInnerSpace : InnerProductSpace ℝ (State (hp := hp)) :=
    InnerProductSpace.complexToReal
  have h := (OSLaplaceGenerator.right_derivative D x).norm_sq
  simp only [Real.toNNReal_zero, D.zero, real_inner_eq_re_inner ℂ, inner_neg_right,
    RCLike.re_to_complex, Complex.neg_re] at h
  rw [show (inner ℂ (x : State (hp := hp)) (OSLaplaceHamiltonian.hamiltonian D x)).re =
    (inner ℂ (OSLaplaceHamiltonian.hamiltonian D x) (x : State (hp := hp))).re from
      by simpa only [RCLike.re_to_complex] using
        (inner_re_symm (𝕜 := ℂ) (x : State (hp := hp))
          (OSLaplaceHamiltonian.hamiltonian D x))] at h
  convert h using 1
  ring

/-- Differentiating the actual finite-kernel bound gives coercivity on the
vacuum-orthogonal part of the maximal Hamiltonian domain. -/
theorem vacuumFormGap_of_quadraticDecay
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : QuadraticDecay (W := W) (plane := plane) m) :
    SpectralGap.VacuumFormGap (OSLaplaceHamiltonian.hamiltonian D)
      (OSVacuumSector.vacuum W plane hp) m := by
  intro x hx
  let g : ℝ → ℝ := fun t => ‖D.operator t.toNNReal (x : State (hp := hp))‖ ^ 2 -
    Real.exp (-2 * m * t) * ‖(x : State (hp := hp))‖ ^ 2
  have he : HasDerivAt (fun t : ℝ => Real.exp (-2 * m * t) *
      ‖(x : State (hp := hp))‖ ^ 2) (-2 * m * ‖(x : State (hp := hp))‖ ^ 2) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (-2 * m)).exp.mul_const
      (‖(x : State (hp := hp))‖ ^ 2)) using 1
    simp only [id_eq, mul_zero, Real.exp_zero, mul_one, one_mul]
  have hd : HasDerivWithinAt g
      (-2 * (inner ℂ (OSLaplaceHamiltonian.hamiltonian D x) (x : State (hp := hp))).re -
        (-2 * m * ‖(x : State (hp := hp))‖ ^ 2)) (Set.Ici 0) 0 :=
    (right_norm_sq_derivative D x).sub he.hasDerivWithinAt
  have hg0 : g 0 = 0 := by simp only [g, Real.toNNReal_zero, D.zero, mul_zero,
    Real.exp_zero, one_mul, sub_self]
  have hgl (t : ℝ) (ht : 0 ≤ t) : g t ≤ 0 := by
    apply sub_nonpos.mpr
    simpa only [Real.coe_toNNReal t ht] using orthogonal_norm_sq_decay D hn m hdecay
      t.toNNReal (x : State (hp := hp)) hx
  have hlim := (hasDerivWithinAt_iff_tendsto_slope'
    (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).mp (hd.mono Set.Ioi_subset_Ici_self)
  have hdle : -2 * (inner ℂ (OSLaplaceHamiltonian.hamiltonian D x)
      (x : State (hp := hp))).re - (-2 * m * ‖(x : State (hp := hp))‖ ^ 2) ≤ 0 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (slope_nonpos_iff_of_le ht.le).mpr (by rw [hg0]; exact hgl t ht.le)
  linarith

/-- Coercivity transfers to the actual full Schwartz Hamiltonian through its
proved unitary graph transport. -/
theorem full_vacuumFormGap_of_quadraticDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hdecay : QuadraticDecay (W := W) (plane := plane) m) :
    SpectralGap.VacuumFormGap (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D)
      (RenormalizedFullOSLimit.fullVacuum W plane hfull) m := by
  intro x hx
  let e := FullSchwartzHilbert.equivalence W plane hp hfull
  have hg := (FullSchwartzHamiltonian.graph_transport W plane hp hfull D
    (x : FullSchwartzHamiltonian.State W plane hfull)
    (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D x)).mp
      ((FullSchwartzHamiltonian.hamiltonian W plane hp hfull D).mem_graph_iff.mpr
        ⟨x, rfl, rfl⟩)
  obtain ⟨y, hy, hAy⟩ := (OSLaplaceHamiltonian.hamiltonian D).mem_graph_iff.mp hg
  have horth : inner ℂ (OSVacuumSector.vacuum W plane hp)
      (y : State (hp := hp)) = 0 := by
    rw [hy]
    have hi := e.symm.inner_map_map (RenormalizedFullOSLimit.fullVacuum W plane hfull)
      (x : FullSchwartzHamiltonian.State W plane hfull)
    rw [FullSchwartzVacuum.inverse_vacuum] at hi
    exact hi.trans hx
  have h := vacuumFormGap_of_quadraticDecay D hn m hdecay y horth
  rw [hy, hAy, e.symm.norm_map, e.symm.inner_map_map] at h
  exact h

/-- A nonzero orthogonal reflected witness, after the existing actual Laplace
regularization, has strictly positive finite energy under positive kernel decay.
This is not an assertion that a positive real spectral value exists. -/
theorem regularized_energy_pos_of_quadraticDecay
    (hfull : FullPositiveTimeReflection.Positive W plane)
    (hn : ∀ f : CorrelationTest 0, W.correlation 0 f = ∫ x, f x)
    (m : ℝ) (hm : 0 < m) (hdecay : QuadraticDecay (W := W) (plane := plane) m)
    (w : FullSchwartzHamiltonian.State W plane hfull) (hw : w ≠ 0)
    (ho : inner ℂ (RenormalizedFullOSLimit.fullVacuum W plane hfull) w = 0) :
    0 < (inner ℂ
      (FullSchwartzHamiltonian.hamiltonian W plane hp hfull D
        (FullSchwartzHamiltonian.rangePoint W plane hp hfull D w))
      (FullSchwartzHamiltonian.rangePoint W plane hp hfull D w :
        FullSchwartzHamiltonian.State W plane hfull)).re := by
  have h := full_vacuumFormGap_of_quadraticDecay D hfull hn m hdecay
    (FullSchwartzHamiltonian.rangePoint W plane hp hfull D w)
    (OSResolventWitnessState.resolvent_orthogonal W plane hp hfull D w ho)
  have hnorm : 0 < ‖(FullSchwartzHamiltonian.rangePoint W plane hp hfull D w :
      FullSchwartzHamiltonian.State W plane hfull)‖ :=
    norm_pos_iff.mpr (OSResolventWitnessState.resolvent_nonzero W plane hp hfull D w hw)
  exact lt_of_lt_of_le (mul_pos hm (sq_pos_of_pos hnorm)) h

end
end UnifiedTheory.Clay.YangMills.OSClusteringGap
