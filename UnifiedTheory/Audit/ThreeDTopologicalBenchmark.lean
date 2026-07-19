/-
  Audit/ThreeDTopologicalBenchmark.lean

  FINITE 2+1D TOPOLOGICAL BENCHMARK — LOCAL ZERO, GLOBAL NONZERO

  Bianca Dittrich's 2+1-dimensional example highlights a distinction
  that the dimension-squeeze argument alone does not record:

    * vacuum 2+1D gravity has no local propagating graviton modes;
    * nontrivial topology can still carry global holonomy/moduli data.

  This file connects three existing parts of the repository:

    1. GravitationalPlaneWaves: `ttModeCount 3 = 0`.
    2. DiscreteBundles / DiscreteAmbroseSinger: loop holonomy and its
       gauge transformation law.
    3. ToricCode: the finite 2-torus has two global logical cycles.

  We use the standard one-vertex CW presentation of the torus,

      pi_1(T^2) = <a, b | a b a^-1 b^-1 = 1>,

  as a directed graph with two generator edges and their reverses.
  A flat connection valued in Multiplicative (Z x Z) has distinct,
  nontrivial holonomies around a and b, while its fundamental
  plaquette holonomy is the identity.  Because the gauge group is
  abelian, both cycle holonomies are gauge invariant.

  HONEST SCOPE:

  This is a finite kinematic witness, not a quantization of 2+1D
  gravity.  It proves that the repository's own discrete-connection
  machinery can represent the local/global distinction.  It does not
  yet construct a physical Hilbert space, quantum dynamics, or a
  refinement-invariant continuum theory.
-/

import UnifiedTheory.LayerA.DiscreteAmbroseSinger
import UnifiedTheory.LayerA.GravitationalPlaneWaves
import UnifiedTheory.LayerB.ToricCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.ThreeDTopologicalBenchmark

open UnifiedTheory.LayerA.DiscreteBundles
open UnifiedTheory.LayerA.DiscreteAmbroseSinger
open UnifiedTheory.LayerA.GravitationalPlaneWaves
open UnifiedTheory.LayerB.ToricCode

/-! ## 1. One-vertex torus presentation -/

/-- The two torus generators and their reverse-oriented edges. -/
inductive TorusEdge where
  | a
  | b
  | aInv
  | bInv
  deriving DecidableEq, Repr

/-- One vertex with two directed generator loops and their reverses. -/
def torusGraph : DirectedGraph where
  Vertex := Unit
  Edge := TorusEdge
  src := fun _ => ()
  tgt := fun _ => ()

/-- Every nonempty edge word is a loop because the presentation has one
vertex. -/
def torusLoop (edges : List TorusEdge) (hne : 0 < edges.length) :
    GraphLoop torusGraph where
  edges := edges
  composable := by
    intro _
    rfl
  nonempty := hne
  closed := rfl

/-- The first noncontractible generator cycle. -/
def cycleA : GraphLoop torusGraph :=
  torusLoop [.a] (by decide)

/-- The second noncontractible generator cycle. -/
def cycleB : GraphLoop torusGraph :=
  torusLoop [.b] (by decide)

/-- The fundamental torus plaquette relation `a b a^-1 b^-1`. -/
def fundamentalPlaquette : Plaquette torusGraph :=
  torusLoop [.a, .b, .aInv, .bInv] (by decide)

/-! ## 2. A flat connection with global holonomy -/

/-- An abelian group with two independent integer holonomy labels. -/
abbrev TorusHolonomyGroup := Multiplicative (ℤ × ℤ)

/-- Independent holonomy along the `a` cycle. -/
def holA : TorusHolonomyGroup := Multiplicative.ofAdd (1, 0)

/-- Independent holonomy along the `b` cycle. -/
def holB : TorusHolonomyGroup := Multiplicative.ofAdd (0, 1)

/-- The inverse-oriented generator transports are assigned group inverses. -/
def torusConnection : DiscreteConnection torusGraph TorusHolonomyGroup where
  transport
    | .a => holA
    | .b => holB
    | .aInv => holA⁻¹
    | .bInv => holB⁻¹

/-- The `a`-cycle detects the first global holonomy label. -/
theorem cycleA_holonomy :
    holonomy torusConnection cycleA.toGraphPath = holA := by
  rfl

/-- The `b`-cycle detects the second global holonomy label. -/
theorem cycleB_holonomy :
    holonomy torusConnection cycleB.toGraphPath = holB := by
  rfl

/-- The first global holonomy is nontrivial. -/
theorem cycleA_holonomy_nontrivial :
    holonomy torusConnection cycleA.toGraphPath ≠ 1 := by
  rw [cycleA_holonomy]
  decide

/-- The second global holonomy is nontrivial. -/
theorem cycleB_holonomy_nontrivial :
    holonomy torusConnection cycleB.toGraphPath ≠ 1 := by
  rw [cycleB_holonomy]
  decide

/-- The two noncontractible cycles carry independent labels. -/
theorem cycle_holonomies_distinct :
    holonomy torusConnection cycleA.toGraphPath ≠
      holonomy torusConnection cycleB.toGraphPath := by
  rw [cycleA_holonomy, cycleB_holonomy]
  decide

/-- Local curvature vanishes on the fundamental plaquette: the commutator
`a b a^-1 b^-1` is the identity in the abelian holonomy group. -/
theorem fundamental_plaquette_is_flat :
    discreteCurvature torusConnection fundamentalPlaquette = 1 := by
  change holA * holB * holA⁻¹ * holB⁻¹ = 1
  simp

/-- The connection is flat on the one-plaquette torus presentation. -/
theorem torus_connection_is_flat :
    IsFlat torusConnection [fundamentalPlaquette] := by
  intro plaquette hmem
  rw [List.mem_singleton.mp hmem]
  exact fundamental_plaquette_is_flat

/-! ## 3. The global data survives gauge transformation -/

/-- On the abelian torus model, the first cycle holonomy is invariant under
every vertex gauge transformation. -/
theorem cycleA_holonomy_gauge_invariant
    (gauge : GaugeTransformation torusGraph TorusHolonomyGroup) :
    holonomy (gaugeTransform torusConnection gauge) cycleA.toGraphPath =
      holonomy torusConnection cycleA.toGraphPath := by
  rw [gauge_conjugates_loop_holonomy torusConnection gauge cycleA]
  simp [mul_comm]

/-- The second cycle holonomy is also gauge invariant. -/
theorem cycleB_holonomy_gauge_invariant
    (gauge : GaugeTransformation torusGraph TorusHolonomyGroup) :
    holonomy (gaugeTransform torusConnection gauge) cycleB.toGraphPath =
      holonomy torusConnection cycleB.toGraphPath := by
  rw [gauge_conjugates_loop_holonomy torusConnection gauge cycleB]
  simp [mul_comm]

/-! ## 4. Local-zero/global-nonzero synthesis -/

/-- **Finite 2+1D topological benchmark.**

The existing local polarization theorem and the new flat-torus witness coexist:

* the local propagating TT-mode count in three spacetime dimensions is zero;
* the discrete connection is locally flat;
* two distinct nontrivial global cycle holonomies survive gauge transformations;
* the repository's toric-code combinatorics independently records two global
  logical cycles on a finite 2-torus.

This is the precise finite connection suggested by the 2+1D quantum-gravity
lesson.  Quantum dynamics and refinement invariance remain open.
-/
theorem local_zero_global_nonzero_benchmark :
    ttModeCount 3 = 0
    ∧ IsFlat torusConnection [fundamentalPlaquette]
    ∧ holonomy torusConnection cycleA.toGraphPath ≠ 1
    ∧ holonomy torusConnection cycleB.toGraphPath ≠ 1
    ∧ holonomy torusConnection cycleA.toGraphPath ≠
        holonomy torusConnection cycleB.toGraphPath
    ∧ (∀ gauge : GaugeTransformation torusGraph TorusHolonomyGroup,
        holonomy (gaugeTransform torusConnection gauge) cycleA.toGraphPath =
          holonomy torusConnection cycleA.toGraphPath)
    ∧ (∀ gauge : GaugeTransformation torusGraph TorusHolonomyGroup,
        holonomy (gaugeTransform torusConnection gauge) cycleB.toGraphPath =
          holonomy torusConnection cycleB.toGraphPath)
    ∧ toricNumLogicalQubits_L2 = 2
    ∧ toricDistance_L2 = 2 := by
  exact ⟨dimension_3_polarization_count,
    torus_connection_is_flat,
    cycleA_holonomy_nontrivial,
    cycleB_holonomy_nontrivial,
    cycle_holonomies_distinct,
    cycleA_holonomy_gauge_invariant,
    cycleB_holonomy_gauge_invariant,
    toricNumLogicalQubits_L2_eq,
    toricDistance_L2_eq⟩

/-! ## Trust regression output -/

#print axioms fundamental_plaquette_is_flat
#print axioms cycleA_holonomy_gauge_invariant
#print axioms cycleB_holonomy_gauge_invariant
#print axioms local_zero_global_nonzero_benchmark

end UnifiedTheory.Audit.ThreeDTopologicalBenchmark
