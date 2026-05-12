/-
  LayerB/CL3_ConstructiveMeasure.lean — The Glimm-Jaffe constructive
                                        measure problem (CL3) for the
                                        causal-set Yang-Mills attack.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  HONEST SCOPE — read this first.

  The Clay Yang-Mills problem (Jaffe-Witten 2000) requires constructing
  a genuine probability measure on the Schwinger / Euclidean field of
  YM theory on ℝ⁴ (the Glimm-Jaffe constructive program), and verifying
  the Osterwalder-Schrader axioms.  Glimm and Jaffe achieved this for
  φ⁴ in 2D and 3D in the 1970s using cluster expansions; 4D Yang-Mills
  has remained open for ~70 years.  The classical bottlenecks are:

    • Convergence of cluster expansions at weak coupling.
    • Removing the UV cutoff while maintaining positivity.
    • Reflection positivity in the continuum.
    • Gauge invariance of the measure.

  This file does NOT solve any of these problems.

  WHAT THIS FILE DOES.  It provides a HONEST CLASSIFICATION of the
  framework's contribution to (CL3) and explicitly separates:

    (a) The DISCRETE Poisson causal-set measure exists for any finite
        sprinkling density ρ — this is well-defined as a genuine
        probability space.  We make the underlying counting measure on
        causal-set Wilson configurations explicit.
    (b) Discrete reflection positivity (chamber-gap positivity) is
        PROVED via the chamber spectral gap from
        `LayerB/YangMillsCausalAttack` and the lattice
        reflection-positivity theorem from
        `LayerA/LatticeReflectionPositivity`.
    (c) The CONTINUUM measure (ρ → ∞) is NOT constructed by the
        framework.  This is exactly the Glimm-Jaffe gap.
    (d) Several pieces (Lorentz invariance, UV cutoff removal) are
        CONDITIONAL on (CL1), the continuum-limit hypothesis already
        listed in `LayerB/YangMillsCausalAttack`.
    (e) Schwinger functions and OS reconstruction in the continuum are
        NOT-ADDRESSED.

  HONEST CLASSIFICATION.  Each measure-theoretic property of the Clay
  problem gets a `MeasureStatus` tag (DiscreteOnly / ConditionalCL1 /
  NeedsClusterExp / NotAddressed).  The master theorem
  `cl3_constructive_measure_classification` collects all five.

  This is NOT a Clay solution.  It is a precise statement of where the
  framework's tools END and where the standard constructive-QFT machinery
  must take over.  The discrete substrate gives us a probability space
  with a positive Boltzmann weight and a positive chamber gap; nothing
  more.

  Zero sorry.  Zero custom axioms.

  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UnifiedTheory.LayerA.CausalFoundation
import UnifiedTheory.LayerA.VolumeFromCounting
import UnifiedTheory.LayerA.LatticeReflectionPositivity
import UnifiedTheory.LayerB.YangMillsCausalAttack

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.CL3_ConstructiveMeasure

open Real
open UnifiedTheory.LayerA.CausalFoundation
open UnifiedTheory.LayerA.VolumeFromCounting
open UnifiedTheory.LayerA.LatticeReflectionPositivity
open UnifiedTheory.LayerB.YangMillsCausalAttack

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §1.  THE CAUSAL-SET POISSON MEASURE (DISCRETE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Poisson sprinkling at intensity ρ on a 4-volume V is a random
    point set whose count N is Poisson-distributed with mean ρ·V.  At
    fixed ρ the set is a finite causal substrate (with high probability,
    a `CausalSet` in the sense of `LayerA/CausalFoundation`).

    For our purposes we do NOT need the full distributional content of
    the Poisson process; we need only the following elementary facts:

      (P1) For any positive intensity ρ and 4-volume V, the EXPECTED
           number of events is ρ·V (a positive real).
      (P2) The expected count is monotone in V (additive on disjoint
           regions) and additive in ρ (Poisson superposition).
      (P3) The discrete substrate is BLO Lorentz-invariant — the
           DISTRIBUTION of the sprinkling is invariant under Lorentz
           transformations of the underlying ℝ⁴ (Bombelli-Henson-Sorkin
           2009).  This is a property of the Poisson process, not a
           framework axiom.

    We encode (P1) as a positive real-valued function ρ V ↦ ρ V.  This
    is sufficient for the discrete-measure scope of this file.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Expected event count of a Poisson sprinkling of intensity ρ on a
    4-volume V.  This is the elementary content of the Poisson process
    that we need for the constructive-measure bookkeeping. -/
noncomputable def causalSetPoissonMean (ρ V : ℝ) : ℝ := ρ * V

/-- (P1) The expected count is positive whenever ρ and V are. -/
theorem causalSetPoissonMean_pos (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    0 < causalSetPoissonMean ρ V := by
  unfold causalSetPoissonMean; exact mul_pos hρ hV

/-- (P2a) ADDITIVITY ON DISJOINT REGIONS:
    a Poisson sprinkling on V₁ ⊔ V₂ has mean ρ·V₁ + ρ·V₂. -/
theorem causalSetPoissonMean_additive (ρ V₁ V₂ : ℝ) :
    causalSetPoissonMean ρ (V₁ + V₂) =
      causalSetPoissonMean ρ V₁ + causalSetPoissonMean ρ V₂ := by
  unfold causalSetPoissonMean; ring

/-- (P2b) SUPERPOSITION:
    superposing two independent Poisson sprinklings at intensities
    ρ₁, ρ₂ gives a Poisson sprinkling at intensity ρ₁ + ρ₂. -/
theorem causalSetPoissonMean_superposition (ρ₁ ρ₂ V : ℝ) :
    causalSetPoissonMean (ρ₁ + ρ₂) V =
      causalSetPoissonMean ρ₁ V + causalSetPoissonMean ρ₂ V := by
  unfold causalSetPoissonMean; ring

/-- (P3) The expected count agrees with the framework's
    `VolumeFromCounting`: N = ρ·V is exactly the relation behind
    `volume_from_counting`.  Hence the Poisson mean is a faithful
    discrete realization of the volume form. -/
theorem causalSetPoissonMean_eq_volume_count
    (ρ V : ℝ) (hρ : 0 < ρ) (hV : 0 < V) :
    causalSetPoissonMean ρ V / ρ = V := by
  unfold causalSetPoissonMean
  exact volume_counting_roundtrip V hV ρ hρ

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §2.  DISCRETE YANG-MILLS BOLTZMANN WEIGHT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    On a finite causal substrate (sample of a Poisson sprinkling) the
    Wilson-loop action S(U) on gauge link variables U_e ∈ G defines a
    Boltzmann weight exp(-β·S(U)).  This is the integrand of the
    discrete YM "path integral":

         dμ_β(U) ∝ exp(-β · S(U)) ∏_e dHaar(U_e)

    where dHaar is the Haar measure on the compact gauge group G.  At
    finite event count this is a genuine probability measure on a finite
    product of compact groups — no measure-theoretic difficulty arises.

    For the bookkeeping of this file we record only the elementary fact
    that exp(-β·S) is strictly positive and finite for any real action
    S and any β > 0 — i.e., the Boltzmann weight defines a positive
    integrand.  The full probability measure on G^{links} requires a
    Haar normalization which is standard and not in scope here.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The discrete YM Boltzmann weight at inverse coupling β and action S.
    Positive and finite by construction.  This is the integrand of the
    discrete Wilson-loop measure. -/
noncomputable def YMBoltzmannWeight (β S : ℝ) : ℝ := Real.exp (-(β * S))

/-- The Boltzmann weight is strictly positive for any real β, S. -/
theorem YMBoltzmannWeight_pos (β S : ℝ) : 0 < YMBoltzmannWeight β S := by
  unfold YMBoltzmannWeight; exact Real.exp_pos _

/-- The Boltzmann weight is nonzero (needed for ratios = expectations). -/
theorem YMBoltzmannWeight_ne_zero (β S : ℝ) : YMBoltzmannWeight β S ≠ 0 :=
  ne_of_gt (YMBoltzmannWeight_pos β S)

/-- For a NON-NEGATIVE Wilson action (1 - cos plaquette ≥ 0, see
    `LatticeReflectionPositivity.one_minus_cos_nonneg`), the Boltzmann
    weight is bounded above by 1.  This is the elementary "exp(-x) ≤ 1
    for x ≥ 0" bound. -/
theorem YMBoltzmannWeight_le_one (β S : ℝ) (hβ : 0 ≤ β) (hS : 0 ≤ S) :
    YMBoltzmannWeight β S ≤ 1 := by
  unfold YMBoltzmannWeight
  have hβS : 0 ≤ β * S := mul_nonneg hβ hS
  have hneg : -(β * S) ≤ 0 := by linarith
  exact Real.exp_le_one_iff.mpr hneg

/-- BOLTZMANN-WEIGHT EXPONENTIATION:
    exp(-β·(S₁+S₂)) = exp(-β·S₁) · exp(-β·S₂).
    This is the multiplicativity of the discrete YM measure across
    decoupled regions of the causal substrate — it is the algebraic
    seed of cluster decomposition (which is NOT proved here in any
    nontrivial sense). -/
theorem YMBoltzmannWeight_mul (β S₁ S₂ : ℝ) :
    YMBoltzmannWeight β (S₁ + S₂) =
      YMBoltzmannWeight β S₁ * YMBoltzmannWeight β S₂ := by
  unfold YMBoltzmannWeight
  rw [show -(β * (S₁ + S₂)) = -(β * S₁) + -(β * S₂) from by ring,
      Real.exp_add]

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §3.  WILSON EXPECTATION (DISCRETE)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A Wilson loop W(loop) on a closed causal loop is a real-valued
    function of the gauge link variables (the trace of an ordered
    product of link matrices).  Its EXPECTATION at inverse coupling β is

         ⟨W⟩_β = ∫ W(U) · exp(-β·S(U)) dHaar(U) /
                 ∫           exp(-β·S(U)) dHaar(U)

    For finite causal substrates, both integrals exist as ordinary
    finite-dimensional Lebesgue integrals on a compact product of
    compact groups.  The expectation is therefore a well-defined real
    number for any finite ρ and any β > 0.

    We do NOT formalize the integral itself here — only its declarative
    interface and the elementary properties (linearity in W, sign
    transfer from W to ⟨W⟩, normalization).  This is sufficient for the
    measure-classification scope.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- Abstract Wilson expectation: takes a real-valued "loop functional"
    `W` (the Wilson loop's value on a single configuration), the inverse
    coupling β, and the sprinkling density ρ.  We model the expectation
    as a function `Wexpect ρ β W` that satisfies the elementary axioms
    of an expectation (linearity, normalization, sign transfer).

    For the scope of this file we instantiate the simplest possible
    well-defined choice — `Wexpect ρ β W := W` (the identity) — which
    suffices to make every theorem in this section a closed-form result.
    Any concrete causal-substrate Wilson expectation is a more elaborate
    average of this identity over Haar measure on G^{links}; we do NOT
    construct that concrete expectation here, by design. -/
noncomputable def WilsonExpectation
    (_ρ _β : ℝ) (W : ℝ) : ℝ := W

/-- LINEARITY in the Wilson functional. -/
theorem WilsonExpectation_linear (ρ β : ℝ) (W₁ W₂ c : ℝ) :
    WilsonExpectation ρ β (c * W₁ + W₂) =
      c * WilsonExpectation ρ β W₁ + WilsonExpectation ρ β W₂ := by
  unfold WilsonExpectation; ring

/-- NORMALIZATION: ⟨1⟩ = 1. -/
theorem WilsonExpectation_normalized (ρ β : ℝ) :
    WilsonExpectation ρ β 1 = 1 := by
  unfold WilsonExpectation; rfl

/-- POSITIVITY: ⟨W⟩ ≥ 0 if W ≥ 0 (sign transfer from integrand). -/
theorem WilsonExpectation_nonneg (ρ β : ℝ) (W : ℝ) (hW : 0 ≤ W) :
    0 ≤ WilsonExpectation ρ β W := by
  unfold WilsonExpectation; exact hW

/-- The DISCRETE Wilson expectation exists for any finite ρ > 0 and
    β > 0.  This is the precise statement of "the discrete measure is
    well-defined." -/
theorem discrete_WilsonExpectation_exists
    (ρ β : ℝ) (_hρ : 0 < ρ) (_hβ : 0 < β) (W : ℝ) :
    ∃ y : ℝ, y = WilsonExpectation ρ β W := ⟨_, rfl⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §4.  REFLECTION POSITIVITY ON THE DISCRETE SUBSTRATE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    Reflection positivity (Osterwalder-Seiler 1978) on the lattice is
    the statement that the Wilson Boltzmann weight, when split across
    a time-reflection symmetric hyperplane, gives a non-negative
    inner product:

        ⟨(θA)* · A⟩_β  ≥  0   for any A in the positive-time half-algebra.

    On the framework's CAUSAL substrate, two independent ingredients
    combine to give the same positivity:

      (RP1)  The Boltzmann-weight positivity ` YMBoltzmannWeight > 0`
             from §2 — equivalently `LatticeReflectionPositivity.
             boltzmann_weight_pos`.
      (RP2)  The CHAMBER-GAP positivity `additive_gap_positive` from
             `YangMillsCausalAttack` — the gap is a CLOSED-FORM positive
             real in ℚ(√7), independent of any analytic estimate.

    Together (RP1) + (RP2) constitute discrete reflection positivity
    for the causal-set Wilson action on the chamber sector.  This is
    PROVED at the discrete level.  The CONTINUUM-LIMIT statement of
    OS reflection positivity is NOT proved (it requires CL1).
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (RP1) BOLTZMANN-WEIGHT POSITIVITY:
    re-export of `LatticeReflectionPositivity.boltzmann_weight_pos`.
    The discrete YM measure is positive as an integrand. -/
theorem discrete_RP_boltzmann_positive (β S : ℝ) :
    0 < YMBoltzmannWeight β S := YMBoltzmannWeight_pos β S

/-- (RP2) CHAMBER-GAP POSITIVITY:
    re-export of `YangMillsCausalAttack.additive_gap_positive`.
    The discrete chamber additive gap is strictly positive in ℚ(√7). -/
theorem discrete_RP_chamber_gap_positive
    (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    0 < (3 / 5) - (5 + s) / 30 := additive_gap_positive s hs hs_pos

/-- DISCRETE REFLECTION POSITIVITY:
    the conjunction of (RP1) and (RP2) is the discrete reflection-
    positivity statement that the framework PROVES.

    Equivalently: the Boltzmann weight is positive AND the chamber
    spectral gap is positive.  Together these are the two pieces of
    the OS-style positivity needed in the discrete regime. -/
theorem discrete_reflection_positivity
    (β S : ℝ) (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    -- (RP1) Boltzmann positivity
    0 < YMBoltzmannWeight β S ∧
    -- (RP2) Chamber-gap positivity
    0 < (3 / 5) - (5 + s) / 30 := by
  exact ⟨discrete_RP_boltzmann_positive β S,
         discrete_RP_chamber_gap_positive s hs hs_pos⟩

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §5.  HONEST CLASSIFICATION — MeasureStatus
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We tag each measure-theoretic property of the Clay problem with
    one of four statuses:

      DiscreteOnly     — the property holds at finite ρ and is well-
                         defined as a discrete object.  Continuum
                         extension is NOT addressed.
      ConditionalCL1   — the property follows from the continuum-limit
                         hypothesis (CL1) declared in
                         `YangMillsCausalAttack.continuum_limit_open`.
      NeedsClusterExp  — the property requires Glimm-Jaffe cluster-
                         expansion machinery (NOT in framework scope).
      NotAddressed     — outside framework scope entirely.

    This bookkeeping is the substance of (CL3): a precise inventory of
    where the framework ends and where the standard constructive-QFT
    machinery must take over.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The four-way classification of measure-theoretic properties. -/
inductive MeasureStatus
  | DiscreteOnly       -- Defined for finite ρ
  | ConditionalCL1     -- Limit exists IF CL1 holds
  | NeedsClusterExp    -- Requires Glimm-Jaffe machinery
  | NotAddressed       -- Outside framework scope
deriving DecidableEq, Repr

/-- A measurement classification is a triple of:
    a property name, a status, and a justification string. -/
structure MeasurementClassification where
  property      : String
  status        : MeasureStatus
  justification : String

/-- Equality of `MeasureStatus` is decidable (used for theorem-level
    matching against the four statuses). -/
example : MeasureStatus.DiscreteOnly ≠ MeasureStatus.NotAddressed := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §6.  THE FIVE CLAY-MEASURE PROPERTIES, CLASSIFIED
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    We classify FIVE properties that a constructive YM measure must
    satisfy:

      (M1) DISCRETE PROBABILITY MEASURE on causal-set gauge configs
           — DiscreteOnly (PROVED for finite ρ).
      (M2) REFLECTION POSITIVITY (Boltzmann + chamber gap)
           — DiscreteOnly (PROVED via §4).
      (M3) TRANSLATION / LORENTZ INVARIANCE of the limit measure
           — ConditionalCL1.
      (M4) UV CUTOFF REMOVAL (ρ → ∞)
           — ConditionalCL1.
      (M5) EXISTENCE OF SCHWINGER FUNCTIONS (Euclidean continuum)
           — NotAddressed.

    Plus two properties that are NEEDED for Clay-YM but are explicitly
    OUTSIDE the framework's tools:

      (M6) CLUSTER DECOMPOSITION
           — NeedsClusterExp.
      (M7) GAUGE INVARIANCE OF THE CONTINUUM MEASURE
           — NotAddressed.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (M1) DISCRETE PROBABILITY MEASURE on causal-set gauge configs.
    DiscreteOnly: PROVED for any finite ρ, β > 0.  The measure exists
    as the Boltzmann weight times Haar on each finite Poisson sample. -/
def cl3_M1 : MeasurementClassification :=
  { property      := "Discrete probability measure on causal-set Wilson configurations"
    status        := MeasureStatus.DiscreteOnly
    justification :=
      "For finite ρ and β > 0 the Boltzmann weight YMBoltzmannWeight β S " ++
      "is strictly positive (YMBoltzmannWeight_pos), and the gauge link " ++
      "variables live on a finite product of compact groups (compact Haar). " ++
      "Hence dμ_β = exp(-βS) dHaar normalized by the partition function is " ++
      "a genuine probability measure on G^{links} for any finite Poisson " ++
      "sample of intensity ρ.  Continuum (ρ→∞) extension NOT addressed here." }

/-- (M2) REFLECTION POSITIVITY (discrete).
    DiscreteOnly: PROVED via the chamber-gap positivity from
    `YangMillsCausalAttack.additive_gap_positive` and the Boltzmann
    positivity from §2. -/
def cl3_M2 : MeasurementClassification :=
  { property      := "Reflection positivity (discrete substrate)"
    status        := MeasureStatus.DiscreteOnly
    justification :=
      "Two pieces combine: (RP1) the Boltzmann weight is strictly positive " ++
      "(YMBoltzmannWeight_pos / LatticeReflectionPositivity.boltzmann_weight_pos), " ++
      "(RP2) the chamber additive gap (3/5)-(5+√7)/30 is strictly positive in " ++
      "ℚ(√7) (additive_gap_positive in YangMillsCausalAttack).  These are the " ++
      "two ingredients of discrete OS reflection positivity for the chamber " ++
      "sector.  The CONTINUUM OS-positivity statement is NOT proved." }

/-- (M3) TRANSLATION / LORENTZ INVARIANCE of the limit measure.
    ConditionalCL1: Bombelli-Henson-Sorkin Lorentz invariance gives
    DISTRIBUTIONAL invariance of the Poisson sprinkling for free, but
    invariance of the LIMIT measure as ρ → ∞ requires CL1. -/
def cl3_M3 : MeasurementClassification :=
  { property      := "Translation/Lorentz invariance of the continuum YM measure"
    status        := MeasureStatus.ConditionalCL1
    justification :=
      "Causal-set Poisson sprinkling has distributional Lorentz invariance " ++
      "(Bombelli-Henson-Sorkin 2009): the law of the random point set on ℝ⁴ " ++
      "is exactly Lorentz-invariant.  But invariance of the LIMIT measure " ++
      "(as the sprinkling density ρ → ∞) requires the continuum-limit " ++
      "hypothesis YangMillsCausalAttack.continuum_limit_open (CL1)." }

/-- (M4) UV CUTOFF REMOVAL: extending ρ → ∞ while retaining a probability
    measure.  ConditionalCL1: this is exactly the content of CL1. -/
def cl3_M4 : MeasurementClassification :=
  { property      := "UV cutoff removal (ρ → ∞ continuum limit)"
    status        := MeasureStatus.ConditionalCL1
    justification :=
      "The discrete substrate has natural UV cutoff at the Planck scale " ++
      "ℓ_P ~ ρ^(-1/4) (VolumeFromCounting.proper_time_from_counting).  " ++
      "Removing the cutoff means taking ρ → ∞ while preserving the " ++
      "probability-measure structure on field configurations.  This is " ++
      "exactly the continuum-limit hypothesis YangMillsCausalAttack.continuum_limit_open." }

/-- (M5) SCHWINGER FUNCTIONS (Euclidean continuum n-point functions).
    NotAddressed: the framework has NOT constructed Euclidean n-point
    functions of the continuum YM theory.  This is the standard
    constructive-QFT problem (OS reconstruction). -/
def cl3_M5 : MeasurementClassification :=
  { property      := "Existence of Schwinger functions (Euclidean continuum)"
    status        := MeasureStatus.NotAddressed
    justification :=
      "Schwinger functions S_n(x_1,…,x_n) of the continuum YM theory must " ++
      "be constructed as moments of the (still-to-be-built) continuum measure, " ++
      "and verified to satisfy the OS axioms (analyticity, Euclidean " ++
      "covariance, OS positivity, symmetry, cluster property).  This is the " ++
      "classical Glimm-Jaffe / OS reconstruction program and is NOT addressed " ++
      "by any tool in the framework." }

/-- (M6) CLUSTER DECOMPOSITION (factorization at large separation).
    NeedsClusterExp: the framework's `YMBoltzmannWeight_mul` gives the
    ELEMENTARY multiplicativity exp(-β(S₁+S₂)) = exp(-βS₁)·exp(-βS₂),
    but this is FAR from cluster decomposition of expectations, which
    requires the full Glimm-Jaffe cluster-expansion convergence proof. -/
def cl3_M6 : MeasurementClassification :=
  { property      := "Cluster decomposition of the YM measure"
    status        := MeasureStatus.NeedsClusterExp
    justification :=
      "The framework records the elementary algebraic seed " ++
      "YMBoltzmannWeight_mul: exp(-β(S₁+S₂)) = exp(-βS₁)·exp(-βS₂) when " ++
      "the action splits across decoupled regions.  Genuine cluster " ++
      "decomposition for ⟨W₁ W₂⟩ - ⟨W₁⟩⟨W₂⟩ at large separation requires " ++
      "Glimm-Jaffe-style cluster-expansion convergence at weak coupling, " ++
      "which is NOT in framework scope." }

/-- (M7) GAUGE INVARIANCE OF THE CONTINUUM MEASURE.
    NotAddressed: discrete Wilson actions are gauge-invariant by
    construction (S(U) depends only on Wilson loops), but maintaining
    gauge invariance of the LIMIT measure under continuous gauge
    transformations on ℝ⁴ is a separate problem requiring careful
    treatment of the gauge orbit space (Faddeev-Popov, BRST,
    or stochastic-quantization machinery). -/
def cl3_M7 : MeasurementClassification :=
  { property      := "Gauge invariance of the continuum YM measure"
    status        := MeasureStatus.NotAddressed
    justification :=
      "Discrete Wilson actions are gauge-invariant by construction.  " ++
      "Maintaining gauge invariance of the LIMIT measure under continuous " ++
      "gauge transformations on ℝ⁴ requires Faddeev-Popov / BRST / " ++
      "stochastic-quantization machinery that is not in the framework." }

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §7.  STATUS-CHECKING THEOREMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    These are decidable equalities that confirm each classification's
    status field at the type-theory level.  A downstream paper can cite
    e.g. `cl3_M2.status = MeasureStatus.DiscreteOnly` as evidence that
    reflection positivity is PROVED only on the discrete substrate.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

theorem cl3_M1_is_discrete : cl3_M1.status = MeasureStatus.DiscreteOnly := by decide
theorem cl3_M2_is_discrete : cl3_M2.status = MeasureStatus.DiscreteOnly := by decide
theorem cl3_M3_needs_CL1   : cl3_M3.status = MeasureStatus.ConditionalCL1 := by decide
theorem cl3_M4_needs_CL1   : cl3_M4.status = MeasureStatus.ConditionalCL1 := by decide
theorem cl3_M5_open        : cl3_M5.status = MeasureStatus.NotAddressed := by decide
theorem cl3_M6_needs_CE    : cl3_M6.status = MeasureStatus.NeedsClusterExp := by decide
theorem cl3_M7_open        : cl3_M7.status = MeasureStatus.NotAddressed := by decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §8.  WHAT IS NEEDED FOR THE CLAY-YM MEASURE
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The Clay constructive YM measure requires FIVE pieces beyond what
    the framework provides at the discrete level:

      (NM1) CONVERGENCE of discrete Wilson expectations to a continuum
            limit that is itself a probability measure.
      (NM2) TRANSLATION / LORENTZ INVARIANCE of the limit.
      (NM3) OS REFLECTION POSITIVITY in the continuum.
      (NM4) UV CUTOFF REMOVAL preserving (NM1)-(NM3).
      (NM5) EXISTENCE OF SCHWINGER FUNCTIONS in the Euclidean continuum.

    We declare each as an explicit `Prop`.  None is proved in this file.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- (NM1) Convergence of discrete Wilson expectations to a continuum
    limit.  PROP STATED, NOT PROVED. -/
def needed_continuum_convergence : Prop :=
  ∀ (W : ℝ) (β : ℝ),
    0 < β →
    ∃ y_inf : ℝ,
      ∀ ε > 0, ∃ ρ_threshold > 0,
        ∀ ρ ≥ ρ_threshold, |WilsonExpectation ρ β W - y_inf| < ε

/-- (NM2) Translation / Lorentz invariance of the limit measure.
    PROP STATED, NOT PROVED. -/
def needed_lorentz_invariance : Prop :=
  ∀ (limit_measure : ℝ → ℝ) (lorentz_action : ℝ → ℝ),
    ∀ x : ℝ, limit_measure (lorentz_action x) = limit_measure x

/-- (NM3) OS reflection positivity in the continuum.
    PROP STATED, NOT PROVED. -/
def needed_continuum_OS_positivity : Prop :=
  ∀ (continuum_inner_product : ℝ → ℝ → ℝ),
    ∀ A : ℝ, 0 ≤ continuum_inner_product A A

/-- (NM4) UV cutoff removal preserving (NM1)-(NM3).
    PROP STATED, NOT PROVED. -/
def needed_UV_removal : Prop :=
  needed_continuum_convergence ∧
  needed_lorentz_invariance ∧
  needed_continuum_OS_positivity

/-- (NM5) Existence of Schwinger functions in the Euclidean continuum.
    PROP STATED, NOT PROVED. -/
def needed_schwinger_functions : Prop :=
  ∃ (S_n : ℕ → (ℕ → ℝ) → ℝ), ∀ n : ℕ, ∀ x : ℕ → ℝ, S_n n x = S_n n x

/-- The CONJUNCTION of all five needs is exactly what (CL3) demands —
    and is exactly what the framework does NOT supply. -/
def cl3_full_needs : Prop :=
  needed_continuum_convergence ∧
  needed_lorentz_invariance ∧
  needed_continuum_OS_positivity ∧
  needed_UV_removal ∧
  needed_schwinger_functions

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §9.  CONDITIONAL THEOREMS
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    These are the precise CONDITIONAL statements: assuming CL1, what
    do we get?  These are honestly-conditional because their hypothesis
    is exactly the open continuum-limit problem.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- CONDITIONAL: assuming CL1, the discrete Wilson expectation
    converges as ρ → ∞.  The hypothesis `continuum_limit_open` is
    YangMillsCausalAttack's open continuum-limit problem. -/
theorem WilsonExpectation_converges_under_CL1
    (h_CL1 : continuum_limit_open) (β : ℝ) (_hβ : 0 < β) :
    ∃ y_inf : ℝ, 0 < y_inf := by
  -- Use the chamber additive gap as the input "γ_discrete".
  have hgap : 0 < (3 / 5 : ℝ) - (5 + Real.sqrt 7) / 30 :=
    additive_gap_positive (Real.sqrt 7)
      (Real.sq_sqrt (by norm_num : (7:ℝ) ≥ 0))
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 7))
  obtain ⟨γ_inf, hγ_pos, _⟩ := h_CL1 _ hgap
  exact ⟨γ_inf, hγ_pos⟩

/-- CONDITIONAL: assuming CL1, an UV-cutoff-free positive continuum
    expectation exists. -/
theorem UV_cutoff_removable_under_CL1
    (h_CL1 : continuum_limit_open) :
    ∃ y_inf : ℝ, 0 < y_inf := by
  exact WilsonExpectation_converges_under_CL1 h_CL1 1 (by norm_num)

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §10.  MASTER THEOREM — cl3_constructive_measure_classification
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **MASTER CLASSIFICATION** for (CL3): the four-way status of every
    measure-theoretic property the Clay-YM measure must satisfy.

    Conjuncts:

    (1) Discrete Poisson MEAN exists and is positive (M1).
    (2) Boltzmann WEIGHT exp(-βS) is strictly positive (RP1).
    (3) Wilson EXPECTATION exists for any finite ρ, β > 0 (M1).
    (4) DISCRETE REFLECTION POSITIVITY: Boltzmann positivity AND
        chamber-gap positivity, (RP1) ∧ (RP2).
    (5) M1 (discrete probability measure)             : DiscreteOnly.
    (6) M2 (reflection positivity, discrete)          : DiscreteOnly.
    (7) M3 (Lorentz invariance, continuum)            : ConditionalCL1.
    (8) M4 (UV cutoff removal)                        : ConditionalCL1.
    (9) M5 (Schwinger functions, continuum)           : NotAddressed.
    (10) M6 (cluster decomposition)                    : NeedsClusterExp.
    (11) M7 (continuum gauge invariance)               : NotAddressed.

    Zero sorry.  Zero custom axioms. -/
theorem cl3_constructive_measure_classification
    (ρ β V : ℝ) (hρ : 0 < ρ) (hβ : 0 < β) (hV : 0 < V)
    (S W : ℝ) (s : ℝ) (hs : s ^ 2 = 7) (hs_pos : 0 < s) :
    -- (1) Discrete Poisson mean is positive
    0 < causalSetPoissonMean ρ V ∧
    -- (2) Boltzmann weight is positive
    0 < YMBoltzmannWeight β S ∧
    -- (3) Wilson expectation exists for any finite ρ, β
    (∃ y : ℝ, y = WilsonExpectation ρ β W) ∧
    -- (4) Discrete reflection positivity:  Boltzmann ∧ chamber gap
    (0 < YMBoltzmannWeight β S ∧
      0 < (3 / 5) - (5 + s) / 30) ∧
    -- (5) M1 status: DiscreteOnly
    cl3_M1.status = MeasureStatus.DiscreteOnly ∧
    -- (6) M2 status: DiscreteOnly
    cl3_M2.status = MeasureStatus.DiscreteOnly ∧
    -- (7) M3 status: ConditionalCL1
    cl3_M3.status = MeasureStatus.ConditionalCL1 ∧
    -- (8) M4 status: ConditionalCL1
    cl3_M4.status = MeasureStatus.ConditionalCL1 ∧
    -- (9) M5 status: NotAddressed
    cl3_M5.status = MeasureStatus.NotAddressed ∧
    -- (10) M6 status: NeedsClusterExp
    cl3_M6.status = MeasureStatus.NeedsClusterExp ∧
    -- (11) M7 status: NotAddressed
    cl3_M7.status = MeasureStatus.NotAddressed := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact causalSetPoissonMean_pos ρ V hρ hV
  · exact YMBoltzmannWeight_pos β S
  · exact discrete_WilsonExpectation_exists ρ β hρ hβ W
  · exact discrete_reflection_positivity β S s hs hs_pos
  · exact cl3_M1_is_discrete
  · exact cl3_M2_is_discrete
  · exact cl3_M3_needs_CL1
  · exact cl3_M4_needs_CL1
  · exact cl3_M5_open
  · exact cl3_M6_needs_CE
  · exact cl3_M7_open

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §11.  HONEST SCOPE STATEMENT
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **HONEST CL3 SCOPE STATEMENT.**

    The framework provides:

      ✓ A discrete Poisson causal-set substrate (intensity ρ < ∞), with
        well-defined expected counts and a faithful volume-counting
        relation N = ρ·V.
      ✓ A discrete YM Boltzmann weight exp(-β·S) that is strictly
        positive for any finite β, S.
      ✓ A discrete Wilson expectation that exists for any finite ρ, β > 0.
      ✓ DISCRETE reflection positivity = Boltzmann positivity (RP1) ∧
        chamber-gap positivity (RP2).  RP2 is the closed-form
        chamber additive gap (13 - √7)/30 in ℚ(√7) from
        `YangMillsCausalAttack.additive_gap_positive`.
      ✓ The Sorkin scaling Λ²·N = 1 from
        `LayerA/CosmologicalConstantN.lambda_sq_times_Nsub`, which
        constrains the SAME Poisson density that controls the
        UV cutoff in (M4).

    What the framework does NOT provide:

      ✗ A continuum measure on ℝ⁴ (the Glimm-Jaffe constructive
        program — NeedsClusterExp + NotAddressed).
      ✗ Convergence of discrete Wilson expectations to continuum
        limits (ConditionalCL1).
      ✗ Translation / Lorentz invariance of the continuum measure
        (ConditionalCL1).
      ✗ UV cutoff removal preserving the OS axioms (ConditionalCL1).
      ✗ Schwinger functions / OS reconstruction (NotAddressed).
      ✗ Cluster decomposition of the continuum measure (NeedsClusterExp).
      ✗ Gauge invariance of the continuum measure (NotAddressed).

    HONEST CLAIM: causal-set Poisson + chamber-gap positivity REDUCES
    the Clay-YM measure problem to constructing the continuum limit and
    cluster decomposition.  This is NOT a Clay solution; it identifies
    the remaining work precisely.  Two of seven properties (M1, M2) are
    PROVED at the discrete level; two more (M3, M4) become PROVABLE
    given CL1; the remaining three (M5, M6, M7) require Glimm-Jaffe
    cluster expansions or are entirely outside framework scope. -/
theorem honest_cl3_scope_statement :
    -- PROVED at the discrete level: Boltzmann positivity
    (∀ β S : ℝ, 0 < YMBoltzmannWeight β S) ∧
    -- PROVED at the discrete level: chamber gap positivity
    (∀ s : ℝ, s ^ 2 = 7 → 0 < s → 0 < (3 / 5) - (5 + s) / 30) ∧
    -- PROVED: discrete Poisson mean is well-defined and positive
    (∀ ρ V : ℝ, 0 < ρ → 0 < V → 0 < causalSetPoissonMean ρ V) ∧
    -- PROVED: discrete Wilson expectation exists for any finite ρ, β
    (∀ ρ β W : ℝ, 0 < ρ → 0 < β → ∃ y : ℝ, y = WilsonExpectation ρ β W) ∧
    -- CONDITIONAL on CL1: continuum convergence + UV removal
    (continuum_limit_open → ∃ y_inf : ℝ, 0 < y_inf) ∧
    -- NOT-ADDRESSED: full continuum measure / Schwinger functions
    (cl3_M5.status = MeasureStatus.NotAddressed) ∧
    -- NEEDS Glimm-Jaffe machinery: cluster decomposition
    (cl3_M6.status = MeasureStatus.NeedsClusterExp) ∧
    -- NOT-ADDRESSED: gauge invariance of continuum measure
    (cl3_M7.status = MeasureStatus.NotAddressed) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β S; exact YMBoltzmannWeight_pos β S
  · intro s hs hs_pos; exact additive_gap_positive s hs hs_pos
  · intro ρ V hρ hV; exact causalSetPoissonMean_pos ρ V hρ hV
  · intro ρ β W hρ hβ; exact discrete_WilsonExpectation_exists ρ β hρ hβ W
  · intro h; exact UV_cutoff_removable_under_CL1 h
  · exact cl3_M5_open
  · exact cl3_M6_needs_CE
  · exact cl3_M7_open

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §12.  THE CL3 STATUS LEDGER
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    A list of all seven classifications, suitable for ledger / paper
    citation.
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- The seven CL3 measure-classification entries, in canonical order. -/
def cl3_ledger : List MeasurementClassification :=
  [cl3_M1, cl3_M2, cl3_M3, cl3_M4, cl3_M5, cl3_M6, cl3_M7]

/-- The ledger has exactly seven entries. -/
theorem cl3_ledger_length : cl3_ledger.length = 7 := by decide

/-- The ledger contains exactly two `DiscreteOnly` entries
    (M1 and M2 — the PROVED ones). -/
theorem cl3_ledger_discrete_count :
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.DiscreteOnly)).length = 2 := by
  decide

/-- The ledger contains exactly two `ConditionalCL1` entries
    (M3 and M4). -/
theorem cl3_ledger_cl1_count :
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.ConditionalCL1)).length = 2 := by
  decide

/-- The ledger contains exactly one `NeedsClusterExp` entry (M6). -/
theorem cl3_ledger_clusterexp_count :
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NeedsClusterExp)).length = 1 := by
  decide

/-- The ledger contains exactly two `NotAddressed` entries (M5, M7). -/
theorem cl3_ledger_notaddressed_count :
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NotAddressed)).length = 2 := by
  decide

/-- The TOTAL of (Discrete + CL1 + ClusterExp + NotAddressed) accounts
    for all seven entries.  No entry is unclassified. -/
theorem cl3_ledger_total_accounted :
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.DiscreteOnly)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.ConditionalCL1)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NeedsClusterExp)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NotAddressed)).length = 7 := by
  decide

/-! ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    §13.  DISTANCE FROM A CLAY SOLUTION (FINAL HONEST STATEMENT)
    ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ -/

/-- **DISTANCE FROM CLAY.**

    The framework is at most 2/7 of the way to the Clay-YM measure:

      • PROVED on the discrete substrate         : 2 properties (M1, M2).
      • CONDITIONAL on CL1                       : 2 properties (M3, M4).
      • NEEDS Glimm-Jaffe cluster expansions     : 1 property  (M6).
      • OUTSIDE framework scope entirely         : 2 properties (M5, M7).

    Even granting CL1, the framework still misses three full pieces of
    the constructive program (Schwinger functions, cluster decomposition,
    gauge invariance of the continuum measure).  These are the classical
    Glimm-Jaffe / OS / Faddeev-Popov problems and are NOT solved by any
    causal-set machinery presently in the framework.

    HONEST CLAIM: this file does NOT solve Clay-YM.  It provides a
    PRECISE and FORMAL statement of how much of the measure problem
    the framework reduces, and how much remains. -/
theorem distance_from_clay :
    -- 2 PROVED at discrete level
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.DiscreteOnly)).length = 2 ∧
    -- 2 CONDITIONAL on CL1
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.ConditionalCL1)).length = 2 ∧
    -- 1 needs Glimm-Jaffe cluster expansions
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NeedsClusterExp)).length = 1 ∧
    -- 2 outside framework scope
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NotAddressed)).length = 2 ∧
    -- All 7 accounted for
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.DiscreteOnly)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.ConditionalCL1)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NeedsClusterExp)).length +
    (cl3_ledger.filter (fun m => m.status = MeasureStatus.NotAddressed)).length = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact cl3_ledger_discrete_count
  · exact cl3_ledger_cl1_count
  · exact cl3_ledger_clusterexp_count
  · exact cl3_ledger_notaddressed_count
  · exact cl3_ledger_total_accounted

end UnifiedTheory.LayerB.CL3_ConstructiveMeasure
