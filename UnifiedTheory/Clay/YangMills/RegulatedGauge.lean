/- Gauge configurations, path holonomy and Wilson observables on a quiver.
The gauge group is arbitrary and may be noncommutative. This algebraic layer
applies to compact Lie groups without reducing them to a finite gauge group.
No continuum limit or Yang--Mills mass gap is asserted. -/
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.RegulatedGauge
noncomputable section

variable (V : Type*) [Quiver V] (G : Type*) [Group G]

abbrev Edge := Σ a : V, Σ b : V, (a ⟶ b)
abbrev Configuration := Edge V → G
abbrev GaugeTransformation := V → G

def link (U : Configuration V G) {a b : V} (e : a ⟶ b) : G := U ⟨a, b, e⟩

def gauge (g : GaugeTransformation V G) (U : Configuration V G) : Configuration V G :=
  fun e => g e.1 * U e * (g e.2.1)⁻¹

theorem gauge_one (U : Configuration V G) : gauge V G 1 U = U := by
  funext e
  simp [gauge]

theorem gauge_mul (g h : GaugeTransformation V G) (U : Configuration V G) :
    gauge V G g (gauge V G h U) = gauge V G (g * h) U := by
  funext e
  simp [gauge, mul_assoc]

def gaugeEquiv (g : GaugeTransformation V G) : Configuration V G ≃ Configuration V G where
  toFun := gauge V G g
  invFun := gauge V G g⁻¹
  left_inv U := by rw [gauge_mul, inv_mul_cancel, gauge_one]
  right_inv U := by rw [gauge_mul, mul_inv_cancel, gauge_one]

def holonomy (U : Configuration V G) {a : V} : {b : V} → Quiver.Path a b → G
  | _, .nil => 1
  | _, .cons p e => holonomy U p * link V G U e

theorem holonomy_nil (U : Configuration V G) (a : V) :
    holonomy V G U (Quiver.Path.nil : Quiver.Path a a) = 1 := rfl

theorem holonomy_cons (U : Configuration V G) {a b c : V}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    holonomy V G U (p.cons e) = holonomy V G U p * link V G U e := rfl

theorem holonomy_comp (U : Configuration V G) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    holonomy V G U (p.comp q) = holonomy V G U p * holonomy V G U q := by
  induction q with
  | nil => simp [holonomy]
  | cons q e hq => simp only [Quiver.Path.comp_cons, holonomy_cons, hq, mul_assoc]

theorem holonomy_gauge (g : GaugeTransformation V G) (U : Configuration V G)
    {a b : V} (p : Quiver.Path a b) :
    holonomy V G (gauge V G g U) p = g a * holonomy V G U p * (g b)⁻¹ := by
  induction p with
  | nil => simp [holonomy]
  | @cons b c p e hp =>
    rw [holonomy_cons, holonomy_cons, hp]
    simp [link, gauge, mul_assoc]

def ClassFunction (χ : G → ℂ) : Prop := ∀ g x, χ (g * x * g⁻¹) = χ x

def wilson (χ : G → ℂ) (U : Configuration V G) {a : V} (p : Quiver.Path a a) : ℂ :=
  χ (holonomy V G U p)

theorem wilson_gauge (χ : G → ℂ) (hχ : ClassFunction G χ)
    (g : GaugeTransformation V G) (U : Configuration V G) {a : V} (p : Quiver.Path a a) :
    wilson V G χ (gauge V G g U) p = wilson V G χ U p := by
  unfold wilson
  rw [holonomy_gauge, hχ]

variable {d : Type*} [Fintype d] [DecidableEq d]

def matrixCharacter (ρ : G →* (Matrix d d ℂ)ˣ) (g : G) : ℂ := Matrix.trace (ρ g : Matrix d d ℂ)

theorem matrixCharacter_class (ρ : G →* (Matrix d d ℂ)ˣ) :
    ClassFunction G (matrixCharacter G ρ) := by
  intro g x
  simp only [matrixCharacter, map_mul, map_inv, Units.val_mul]
  exact Matrix.trace_units_conj (ρ g) (ρ x : Matrix d d ℂ)

theorem matrix_wilson_gauge (ρ : G →* (Matrix d d ℂ)ˣ)
    (g : GaugeTransformation V G) (U : Configuration V G) {a : V} (p : Quiver.Path a a) :
    wilson V G (matrixCharacter G ρ) (gauge V G g U) p =
      wilson V G (matrixCharacter G ρ) U p :=
  wilson_gauge V G _ (matrixCharacter_class G ρ) g U p

variable {P : Type*} [Fintype P]

def wilsonAction (χ : G → ℂ) (base : P → V) (loops : ∀ p, Quiver.Path (base p) (base p))
    (β c : ℝ) (U : Configuration V G) : ℝ :=
  β * ∑ p, (c - (wilson V G χ U (loops p)).re)

theorem wilsonAction_gauge (χ : G → ℂ) (hχ : ClassFunction G χ)
    (base : P → V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ)
    (g : GaugeTransformation V G) (U : Configuration V G) :
    wilsonAction V G χ base loops β c (gauge V G g U) = wilsonAction V G χ base loops β c U := by
  simp only [wilsonAction, wilson_gauge V G χ hχ]

def boltzmannWeight (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) (U : Configuration V G) : ℝ :=
  Real.exp (-wilsonAction V G χ base loops β c U)

theorem boltzmannWeight_pos (χ : G → ℂ) (base : P → V)
    (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) (U : Configuration V G) :
    0 < boltzmannWeight V G χ base loops β c U := Real.exp_pos _

theorem boltzmannWeight_gauge (χ : G → ℂ) (hχ : ClassFunction G χ)
    (base : P → V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ)
    (g : GaugeTransformation V G) (U : Configuration V G) :
    boltzmannWeight V G χ base loops β c (gauge V G g U) =
      boltzmannWeight V G χ base loops β c U := by
  rw [boltzmannWeight, boltzmannWeight, wilsonAction_gauge V G χ hχ]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_gauge (g : GaugeTransformation V G) : Continuous (gauge V G g) := by
  apply continuous_pi
  intro e
  exact (continuous_const.mul (continuous_apply e)).mul continuous_const

theorem continuous_holonomy {a b : V} (p : Quiver.Path a b) :
    Continuous (fun U : Configuration V G => holonomy V G U p) := by
  induction p with
  | nil => exact continuous_const
  | cons p e hp => exact hp.mul (continuous_apply _)

theorem continuous_wilson (χ : G → ℂ) (hχ : Continuous χ) {a : V} (p : Quiver.Path a a) :
    Continuous (fun U : Configuration V G => wilson V G χ U p) :=
  hχ.comp (continuous_holonomy V G p)

theorem continuous_wilsonAction (χ : G → ℂ) (hχ : Continuous χ)
    (base : P → V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    Continuous (wilsonAction V G χ base loops β c) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro p _
  exact continuous_const.sub (Complex.continuous_re.comp (continuous_wilson V G χ hχ (loops p)))

theorem continuous_boltzmannWeight (χ : G → ℂ) (hχ : Continuous χ)
    (base : P → V) (loops : ∀ p, Quiver.Path (base p) (base p)) (β c : ℝ) :
    Continuous (boltzmannWeight V G χ base loops β c) :=
  Real.continuous_exp.comp (continuous_wilsonAction V G χ hχ base loops β c).neg

end
end UnifiedTheory.Clay.YangMills.RegulatedGauge
