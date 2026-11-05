/- A genuine four-dimensional periodic finite lattice and its Wilson probability
law for arbitrary compact gauge groups. A backward edge is the inverse of its
forward link. Varying the period supplies regulators, but this file proves no
uniform estimate, continuum convergence, reflection positivity, or mass gap. -/
import UnifiedTheory.Clay.YangMills.RegulatedGaugeOrientation
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicLattice4
noncomputable section
open RegulatedGauge MeasureTheory

abbrev Vertex (n : ℕ) := Fin 4 → ZMod n

def step (n : ℕ) (x : Vertex n) (μ : Fin 4) : Vertex n := x + Pi.single μ 1

theorem step_comm (n : ℕ) (x : Vertex n) (μ ν : Fin 4) :
    step n (step n x μ) ν = step n (step n x ν) μ := by
  simp only [step, add_assoc]
  rw [add_comm (Pi.single μ 1) (Pi.single ν 1)]

instance latticeQuiver (n : ℕ) : Quiver (Vertex n) where
  Hom x y := {μ : Fin 4 // step n x μ = y}

instance homFintype (n : ℕ) (x y : Vertex n) : Fintype (x ⟶ y) := by
  classical
  exact inferInstanceAs (Fintype {μ : Fin 4 // step n x μ = y})

instance edgeFintype (n : ℕ) [NeZero n] : Fintype (Edge (Vertex n)) := by
  unfold Edge
  infer_instance

def forward (n : ℕ) (x : Vertex n) (μ : Fin 4) : x ⟶ step n x μ := ⟨μ, rfl⟩

/-- The oriented elementary μν square with two forward and two backward steps. -/
def plaquette (n : ℕ) (x : Vertex n) (μ ν : Fin 4) :
    @Quiver.Path (Quiver.Symmetrify (Vertex n)) _ x x :=
  (((Quiver.Path.nil.cons (Sum.inl (forward n x μ))).cons
    (Sum.inl (forward n (step n x μ) ν))).cons
    (Sum.inr ⟨μ, step_comm n x ν μ⟩)).cons (Sum.inr (forward n x ν))

theorem plaquette_length (n : ℕ) (x : Vertex n) (μ ν : Fin 4) :
    (plaquette n x μ ν).length = 4 := rfl

abbrev Plane := {d : Fin 4 × Fin 4 // d.1 < d.2}
abbrev PlaquetteIndex (n : ℕ) := Vertex n × Plane

def base (n : ℕ) (p : PlaquetteIndex n) : Quiver.Symmetrify (Vertex n) := p.1

def loops (n : ℕ) (p : PlaquetteIndex n) : Quiver.Path (base n p) (base n p) :=
  plaquette n p.1 p.2.1.1 p.2.1.2

variable (n : ℕ) [NeZero n] (G : Type*) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- The periodic four-dimensional Wilson law on the independent positive links. -/
def wilsonLaw (χ : G → ℂ) (β c : ℝ) : Measure (Configuration (Vertex n) G) :=
  orientedWilsonMeasure (Vertex n) G χ (base n) (loops n) β c

theorem wilsonLaw_probability (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    IsProbabilityMeasure (wilsonLaw n G χ β c) :=
  orientedWilsonMeasure_probability (Vertex n) G χ hχ (base n) (loops n) β c

theorem gauge_preserves_wilsonLaw (χ : G → ℂ) (hcχ : Continuous χ)
    (hiχ : ClassFunction G χ) (β c : ℝ) (g : GaugeTransformation (Vertex n) G) :
    MeasurePreserving (gauge (Vertex n) G g) (wilsonLaw n G χ β c) (wilsonLaw n G χ β c) :=
  gauge_preserves_orientedWilsonMeasure (Vertex n) G χ hcχ hiχ (base n) (loops n) β c g

end
end UnifiedTheory.Clay.YangMills.PeriodicLattice4
