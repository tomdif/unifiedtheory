/- A nontrivial finite-dimensional unitary representation supplies an actual
nonconstant class observable and hence strictly positive finite-lattice
plaquette variance. Existence of the physical representation and uniform
continuum nontriviality are not asserted. -/
import UnifiedTheory.Clay.YangMills.WilsonCrossingKernel
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteNontriviality
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables
noncomputable section
open scoped ComplexOrder
open Matrix RegulatedGauge WilsonCrossingKernel PeriodicLattice4 WilsonMomentBounds

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A unitary matrix has trace equal to the dimension only when it is identity. -/
theorem unitary_trace_eq_card_iff (A : Matrix.unitaryGroup d ℂ) :
    Matrix.trace (A : Matrix d d ℂ) = (Fintype.card d : ℂ) ↔ A = 1 := by
  constructor
  · intro ht
    have hA : (A : Matrix d d ℂ)ᴴ * (A : Matrix d d ℂ) = 1 := A.2.1
    have hz : Matrix.trace (((A : Matrix d d ℂ) - 1)ᴴ * ((A : Matrix d d ℂ) - 1)) = 0 := by
      simp only [conjTranspose_sub, conjTranspose_one, sub_mul, mul_sub,
        hA, mul_one, one_mul, trace_sub, trace_conjTranspose, trace_one, ht]
      simp
    have he : (A : Matrix d d ℂ) - 1 = 0 := trace_conjTranspose_mul_self_eq_zero_iff.mp hz
    exact Subtype.ext (sub_eq_zero.mp he)
  · rintro rfl
    simp

theorem unitary_column_square_sum (A : Matrix.unitaryGroup d ℂ) (j : d) :
    ∑ i, ‖A i j‖ ^ 2 = 1 := by
  have hA : (A : Matrix d d ℂ)ᴴ * (A : Matrix d d ℂ) = 1 := A.2.1
  have he := congrArg (fun M : Matrix d d ℂ => (M j j).re) hA
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq,
    Matrix.one_apply_eq, Complex.one_re] using he

theorem unitary_entry_bound (A : Matrix.unitaryGroup d ℂ) (i j : d) : ‖A i j‖ ≤ 1 := by
  have he := Finset.single_le_sum (s := Finset.univ) (f := fun k => ‖A k j‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  rw [unitary_column_square_sum] at he
  nlinarith [norm_nonneg (A i j)]

theorem unitary_trace_bound (A : Matrix.unitaryGroup d ℂ) :
    ‖Matrix.trace (A : Matrix d d ℂ)‖ ≤ (Fintype.card d : ℝ) := by
  calc
    ‖Matrix.trace (A : Matrix d d ℂ)‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : d, (1 : ℝ) := Finset.sum_le_sum (fun i _ => unitary_entry_bound A i i)
    _ = Fintype.card d := by simp

variable {G : Type*} [Group G]

theorem unitaryCharacter_one (ρ : G →* Matrix.unitaryGroup d ℂ) :
    unitaryCharacter ρ 1 = (Fintype.card d : ℂ) := by
  simp [unitaryCharacter]

theorem unitaryCharacter_class (ρ : G →* Matrix.unitaryGroup d ℂ) :
    ClassFunction G (unitaryCharacter ρ) :=
  matrixCharacter_class G (Unitary.toUnits.comp ρ)

theorem unitaryCharacter_ne_at_one (ρ : G →* Matrix.unitaryGroup d ℂ)
    (g : G) (hg : ρ g ≠ 1) : unitaryCharacter ρ g ≠ unitaryCharacter ρ 1 := by
  rw [unitaryCharacter_one]
  exact fun h => hg ((unitary_trace_eq_card_iff (ρ g)).mp h)

variable [TopologicalSpace G]

theorem unitaryCharacter_continuous (ρ : G →* Matrix.unitaryGroup d ℂ)
    (hρ : Continuous ρ) : Continuous (unitaryCharacter ρ) := by
  unfold unitaryCharacter Matrix.trace
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp ((continuous_apply i).comp
    (continuous_subtype_val.comp hρ)))

variable [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- Unconditional finite-regulator positivity once the nontrivial continuous
unitary representation is supplied; no variance hypothesis is inserted. -/
theorem unitary_plaquette_variance_pos (n : ℕ) [NeZero n] [Fact (1 < n)]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (g : G) (hg : ρ g ≠ 1) (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) :
    0 < ∫ U, ‖loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) U -
      ∫ W, loopObservable (Vertex n) G (unitaryCharacter ρ) (plaquette n x μ ν) W
        ∂wilsonLaw n G (unitaryCharacter ρ) β c‖ ^ 2
      ∂wilsonLaw n G (unitaryCharacter ρ) β c :=
  PeriodicPlaquetteNontriviality.plaquette_variance_pos n G _
    (unitaryCharacter_continuous ρ hρ) g 1 (unitaryCharacter_ne_at_one ρ g hg)
    β c x μ ν hμν

/-- The explicit bare-moment bound is the representation dimension to the
moment order, independent of period, coupling, and the chosen loops. -/
theorem unitary_periodic_moment_bound (n : ℕ) [NeZero n]
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (β c : ℝ)
    (m : ℕ) (obsBase : Fin m → Quiver.Symmetrify (Vertex n))
    (obsLoops : ∀ i, Quiver.Path (obsBase i) (obsBase i)) :
    ‖moment (wilsonLaw n G (unitaryCharacter ρ) β c) Finset.univ
      (fun i => loopObservable (Vertex n) G (unitaryCharacter ρ) (obsLoops i))‖ ≤
        (Fintype.card d : ℝ) ^ m := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    wilson_moment_bound (Vertex n) G (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ)
      (Fintype.card d : ℝ) (Nat.cast_nonneg _) (fun g => unitary_trace_bound (ρ g))
      (base n) (loops n) β c Finset.univ obsBase obsLoops

end
end UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables
