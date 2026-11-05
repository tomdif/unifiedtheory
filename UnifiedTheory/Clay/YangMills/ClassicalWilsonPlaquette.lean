/- The actual periodic lattice Wilson plaquette evaluated on constant matrix
connections. Its classical a^4 trace-defect limit is proved from exponential
links. These deterministic configurations supply no Wilson-law covariance bound. -/
import UnifiedTheory.Clay.YangMills.UnitaryExponentialPlaquette
import UnifiedTheory.Clay.YangMills.WilsonAverageDefect
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Clay.YangMills.ClassicalWilsonPlaquette
noncomputable section
open Matrix Filter RegulatedGauge PeriodicLattice4 PeriodicTimeReflection
open PeriodicPlaquetteReflection UnitaryExponentialPlaquette
open scoped Topology Matrix.Norms.Operator

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The same skew-Hermitian generator is used on every link in each direction. -/
def constantConnection (N : ℕ) (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (a : ℝ) :
    Configuration (Vertex N) (Matrix.unitaryGroup d ℂ) :=
  fun e => UnitaryExponentialPlaquette.link (A ((edgeCoordinates N e).2))
    (hA ((edgeCoordinates N e).2)) a

@[simp] theorem linkValue_constant (N : ℕ) (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (a : ℝ) (x : Vertex N) (μ : Fin 4) :
    linkValue N (Matrix.unitaryGroup d ℂ) (constantConnection N A hA a) x μ =
      UnitaryExponentialPlaquette.link (A μ) (hA μ) a := rfl

/-- Identifies the repository's actual oriented lattice holonomy, with its
existing multiplication order, with the constructed commutator plaquette. -/
theorem holonomy_eq (N : ℕ) (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (a : ℝ) (x : Vertex N) (μ ν : Fin 4) :
    holonomy (Quiver.Symmetrify (Vertex N)) (Matrix.unitaryGroup d ℂ)
      (orientedExtension (Vertex N) (Matrix.unitaryGroup d ℂ) (constantConnection N A hA a))
      (PeriodicLattice4.plaquette N x μ ν) =
      UnitaryExponentialPlaquette.plaquette (A μ) (hA μ) (A ν) (hA ν) a := by
  rw [plaquette_holonomy_eq_product]
  simp only [plaquetteProduct, linkValue_constant, UnitaryExponentialPlaquette.plaquette]

theorem plaquetteDefect_eq (N : ℕ) (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (a : ℝ) (p : PlaquetteIndex N) :
    WilsonAverageDefect.plaquetteDefect N (Matrix.unitaryGroup d ℂ)
      (MonoidHom.id _) p (constantConnection N A hA a) =
      (Fintype.card d : ℝ) - (Matrix.trace
        (UnitaryExponentialPlaquette.plaquette (A p.2.1.1) (hA p.2.1.1)
          (A p.2.1.2) (hA p.2.1.2) a : Matrix d d ℂ)).re := by
  unfold WilsonAverageDefect.plaquetteDefect loops
  rw [holonomy_eq N A hA a p.1 p.2.1.1 p.2.1.2]
  rfl

/-- The exact lattice observable has a classical curvature-bracket limit. -/
theorem plaquetteDefect_tendsto (N : ℕ) (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (p : PlaquetteIndex N) :
    Tendsto (fun a : ℝ => WilsonAverageDefect.plaquetteDefect N (Matrix.unitaryGroup d ℂ)
      (MonoidHom.id _) p (constantConnection N A hA a) / a ^ 4)
      (𝓝[≠] 0) (𝓝 (energy (A p.2.1.1 * A p.2.1.2 - A p.2.1.2 * A p.2.1.1))) := by
  simpa only [plaquetteDefect_eq] using
    plaquette_defect_tendsto (A p.2.1.1) (hA p.2.1.1) (A p.2.1.2) (hA p.2.1.2)

/-- A concrete pair of noncommuting skew-Hermitian two-by-two generators. -/
def referenceX : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; Complex.I, 0]
def referenceY : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

theorem referenceX_skew : star referenceX = -referenceX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceX, Matrix.star_apply]

theorem referenceY_skew : star referenceY = -referenceY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [referenceY, Matrix.star_apply]

theorem reference_energy : energy (referenceX * referenceY - referenceY * referenceX) = 4 := by
  norm_num [energy, referenceX, referenceY, Matrix.mul_apply, Fin.sum_univ_two]

/-- A concrete positive leading coefficient, without a supplied nonzero hypothesis. -/
theorem reference_defect_tendsto :
    Tendsto (fun a : ℝ => ((2 : ℝ) - (Matrix.trace
      (UnitaryExponentialPlaquette.plaquette referenceX referenceX_skew
        referenceY referenceY_skew a : Matrix (Fin 2) (Fin 2) ℂ)).re) / a ^ 4)
      (𝓝[≠] 0) (𝓝 (4 : ℝ)) := by
  simpa only [Fintype.card_fin, Nat.cast_ofNat, reference_energy] using
    plaquette_defect_tendsto referenceX referenceX_skew referenceY referenceY_skew

/-- A fixed four-dimensional constant connection with two active directions. -/
def referenceGenerators (μ : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  if μ = 0 then referenceX else if μ = 1 then referenceY else 0

theorem referenceGenerators_skew (μ : Fin 4) :
    star (referenceGenerators μ) = -referenceGenerators μ := by
  by_cases h0 : μ = 0
  · simp [referenceGenerators, h0, referenceX_skew]
  · by_cases h1 : μ = 1
    · simp [referenceGenerators, h0, h1, referenceY_skew]
    · simp [referenceGenerators, h0, h1]

def referencePlane : Plane := ⟨(0, 1), by decide⟩

theorem reference_lattice_defect_eq (N : ℕ) (x : Vertex N) (a : ℝ) :
    WilsonAverageDefect.plaquetteDefect N (Matrix.unitaryGroup (Fin 2) ℂ)
      (MonoidHom.id _) (x, referencePlane)
      (constantConnection N referenceGenerators referenceGenerators_skew a) =
      2 - (Matrix.trace (UnitaryExponentialPlaquette.plaquette referenceX referenceX_skew
        referenceY referenceY_skew a : Matrix (Fin 2) (Fin 2) ℂ)).re := by
  rw [plaquetteDefect_eq]
  simp [referencePlane, referenceGenerators]

/-- The positive coefficient belongs to the actual lattice Wilson observable. -/
theorem reference_lattice_defect_tendsto (N : ℕ) (x : Vertex N) :
    Tendsto (fun a : ℝ => WilsonAverageDefect.plaquetteDefect N
      (Matrix.unitaryGroup (Fin 2) ℂ) (MonoidHom.id _) (x, referencePlane)
      (constantConnection N referenceGenerators referenceGenerators_skew a) / a ^ 4)
      (𝓝[≠] 0) (𝓝 (4 : ℝ)) := by
  simpa only [reference_lattice_defect_eq] using reference_defect_tendsto

/-- One deterministic lower bound works at every site and every period.
It concerns these explicitly constructed configurations, not their probability. -/
theorem reference_lattice_defect_lower :
    ∀ᶠ a : ℝ in 𝓝[≠] 0, ∀ (N : ℕ) (x : Vertex N),
      2 * a ^ 4 ≤ WilsonAverageDefect.plaquetteDefect N
        (Matrix.unitaryGroup (Fin 2) ℂ) (MonoidHom.id _) (x, referencePlane)
        (constantConnection N referenceGenerators referenceGenerators_skew a) := by
  have he := reference_defect_tendsto.eventually
    (eventually_gt_nhds (show (2 : ℝ) < 4 by norm_num))
  filter_upwards [he, self_mem_nhdsWithin] with a ha ha0
  have ha0 : a ≠ 0 := by simpa using ha0
  have ha4 : 0 < a ^ 4 := by positivity
  intro N x
  rw [reference_lattice_defect_eq]
  exact ((lt_div_iff₀ ha4).mp ha).le

/-- The action per physical lattice volume is an exact finite sum of the
normalized trace defects on a constant connection. -/
theorem action_density_eq (N : ℕ) [NeZero N] (A : Fin 4 → Matrix d d ℂ)
    (hA : ∀ μ, star (A μ) = -A μ) (β a : ℝ) :
    orientedWilsonAction (Vertex N) (Matrix.unitaryGroup d ℂ)
      (WilsonCrossingKernel.unitaryCharacter (MonoidHom.id _)) (base N) (loops N)
      β (Fintype.card d) (constantConnection N A hA a) /
        ((Fintype.card (Vertex N) : ℝ) * a ^ 4) =
      β * ∑ p : Plane, ((Fintype.card d : ℝ) - (Matrix.trace
        (UnitaryExponentialPlaquette.plaquette (A p.1.1) (hA p.1.1)
          (A p.1.2) (hA p.1.2) a : Matrix d d ℂ)).re) / a ^ 4 := by
  change (β * ∑ p : PlaquetteIndex N, WilsonAverageDefect.plaquetteDefect N
    (Matrix.unitaryGroup d ℂ) (MonoidHom.id _) p (constantConnection N A hA a)) /
      ((Fintype.card (Vertex N) : ℝ) * a ^ 4) = _
  simp_rw [plaquetteDefect_eq]
  rw [Fintype.sum_prod_type]
  let b : Plane → ℝ := fun p => (Fintype.card d : ℝ) - (Matrix.trace
    (UnitaryExponentialPlaquette.plaquette (A p.1.1) (hA p.1.1)
      (A p.1.2) (hA p.1.2) a : Matrix d d ℂ)).re
  change (β * ∑ _ : Vertex N, ∑ p : Plane, b p) /
      ((Fintype.card (Vertex N) : ℝ) * a ^ 4) = β * ∑ p : Plane, b p / a ^ 4
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.sum_div, mul_left_comm β (Fintype.card (Vertex N) : ℝ),
    mul_div_mul_left _ _ (ne_of_gt (WilsonAverageDefect.volume_pos N)), mul_div_assoc]

/-- The actual Wilson action density converges to the constant-connection
curvature energy. The period may vary arbitrarily; the coupling here is fixed,
so this does not identify a quantum running-coupling trajectory. -/
theorem action_density_tendsto (N : ℝ → ℕ) [∀ a, NeZero (N a)]
    (A : Fin 4 → Matrix d d ℂ) (hA : ∀ μ, star (A μ) = -A μ) (β : ℝ) :
    Tendsto (fun a : ℝ => orientedWilsonAction (Vertex (N a)) (Matrix.unitaryGroup d ℂ)
      (WilsonCrossingKernel.unitaryCharacter (MonoidHom.id _)) (base (N a)) (loops (N a))
      β (Fintype.card d) (constantConnection (N a) A hA a) /
        ((Fintype.card (Vertex (N a)) : ℝ) * a ^ 4))
      (𝓝[≠] 0) (𝓝 (β * ∑ p : Plane, energy (A p.1.1 * A p.1.2 - A p.1.2 * A p.1.1))) := by
  have hs := tendsto_finset_sum Finset.univ (fun (p : Plane) _ =>
    plaquette_defect_tendsto (A p.1.1) (hA p.1.1) (A p.1.2) (hA p.1.2))
  simpa only [action_density_eq] using hs.const_mul β

end
end UnifiedTheory.Clay.YangMills.ClassicalWilsonPlaquette
