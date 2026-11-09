/- A non-vacuum vector in the actual reflected Wilson Hilbert space.
The spatial plaquette based at time zero belongs to the fixed boundary. Its
real character has the proved volume-uniform fluctuation floor at bounded
coupling. This supplies no renormalized continuum limit or time evolution. -/
import UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel
import UnifiedTheory.Clay.YangMills.UnitaryUniformVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.BoundaryPlaquetteOS
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit PeriodicHalfAction
open PeriodicPlaquetteReflection PeriodicTimeReflection PeriodicSiteReflection
open WilsonMomentBounds WilsonCrossingKernel UnitaryCharacterObservables
open UnitaryUniformVariance CountableCorrelationCompactness PositiveKernelForm KernelHilbertCompletion

variable (n : ℕ) [NeZero n] (G : Type*) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def boundaryPlaquette : PlaquetteIndex (2 * n) := (0, ⟨(1, 2), by decide⟩)

theorem boundaryPlaquette_boundary : BoundaryP n (boundaryPlaquette n) := by
  simp [BoundaryP, PeriodicHalfGeometry.Boundary, boundaryPlaquette]

def realCharacter (χ : G → ℂ) (g : G) : ℂ := (χ g).re

def boundaryValue (χ : G → ℂ) (b : BoundaryConfiguration n G) : ℂ :=
  realCharacter G χ (plaquetteProduct (2 * n) G (assemble n G (b, (1, 1))) 0 1 2)

def family (χ : G → ℂ) (i : Bool)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) : ℂ :=
  if i then boundaryValue n G χ z.1 else 1

theorem loop_assemble (χ : G → ℂ) (z : SplitConfiguration n G) :
    loopObservable (Vertex (2 * n)) G (realCharacter G χ)
      (plaquette (2 * n) 0 1 2) (assemble n G z) = boundaryValue n G χ z.1 := by
  rcases z with ⟨b, x, y⟩
  change realCharacter G χ (holonomy (Quiver.Symmetrify (Vertex (2 * n))) G
    (orientedExtension (Vertex (2 * n)) G (assemble n G (b, (x, y))))
    (plaquette (2 * n) 0 1 2)) = _
  rw [plaquette_holonomy_eq_product]
  have he := boundary_plaquette_independent n G (boundaryPlaquette n)
    (boundaryPlaquette_boundary n) b x y 1 1
  change plaquetteProduct (2 * n) G (assemble n G (b, (x, y))) 0 1 2 =
    plaquetteProduct (2 * n) G (assemble n G (b, (1, 1))) 0 1 2 at he
  rw [he]
  rfl

theorem observable_true (χ : G → ℂ) (U : Configuration (Vertex (2 * n)) G) :
    observable n G (family n G χ true) U =
      loopObservable (Vertex (2 * n)) G (realCharacter G χ) (plaquette (2 * n) 0 1 2) U := by
  have h := loop_assemble n G χ (splitConfiguration n G U)
  rw [assemble_split] at h
  exact h.symm

theorem observable_false (χ : G → ℂ) (U : Configuration (Vertex (2 * n)) G) :
    observable n G (family n G χ false) U = 1 := rfl

theorem observable_reflection (χ : G → ℂ) (i : Bool)
    (U : Configuration (Vertex (2 * n)) G) :
    observable n G (family n G χ i) (reflectConfiguration (2 * n) G U) =
      observable n G (family n G χ i) U := by
  change (if i then boundaryValue n G χ
    (splitConfiguration n G (reflectConfiguration (2 * n) G U)).1 else 1) = _
  rw [split_reflection]
  rfl

theorem action_realCharacter (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) :
    orientedWilsonAction (Vertex (2 * n)) G (realCharacter G χ)
      (base (2 * n)) (loops (2 * n)) β c U =
    orientedWilsonAction (Vertex (2 * n)) G χ
      (base (2 * n)) (loops (2 * n)) β c U := rfl

theorem realCharacter_continuous (χ : G → ℂ) (hχ : Continuous χ) :
    Continuous (realCharacter G χ) :=
  Complex.continuous_ofReal.comp (Complex.continuous_re.comp hχ)

theorem law_realCharacter (χ : G → ℂ) (β c : ℝ) :
    wilsonLaw (2 * n) G (realCharacter G χ) β c = wilsonLaw (2 * n) G χ β c := rfl

theorem haarFluctuation_realCharacter (χ : G → ℂ) :
    HaarCenteredFluctuation.haarFluctuation G (realCharacter G χ) =
      HaarCenteredFluctuation.haarFluctuation G χ := rfl

theorem boundaryValue_continuous (χ : G → ℂ) (hχ : Continuous χ) :
    Continuous (boundaryValue n G χ) := by
  have h : Continuous (fun b : BoundaryConfiguration n G =>
      loopObservable (Vertex (2 * n)) G (realCharacter G χ)
        (plaquette (2 * n) 0 1 2) (assemble n G (b, (1, 1)))) :=
    (loopObservable_continuous (Vertex (2 * n)) G (realCharacter G χ)
    (realCharacter_continuous G χ hχ) (plaquette (2 * n) 0 1 2)).comp
      ((continuous_assemble n G).comp (continuous_id.prodMk continuous_const))
  simpa only [loop_assemble] using h

theorem family_continuous (χ : G → ℂ) (hχ : Continuous χ) (i : Bool) :
    Continuous (family n G χ i) := by
  cases i
  · exact continuous_const
  · exact (boundaryValue_continuous n G χ hχ).comp continuous_fst

theorem kernel_eq_ordinary (χ : G → ℂ) (β c : ℝ) :
    ReflectedWilsonKernel.kernel n G χ β c (family n G χ) =
      ProbabilityGramCompactness.kernel (wilsonLaw (2 * n) G χ β c)
        (fun i => observable n G (family n G χ i)) := by
  funext p
  simp only [ReflectedWilsonKernel.kernel, ProbabilityGramCompactness.kernel,
    observable_reflection]

theorem reflected_variance_identity (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    (ReflectedWilsonKernel.kernel n G χ β c (family n G χ) (true, true) -
      ReflectedWilsonKernel.kernel n G χ β c (family n G χ) (true, false) *
      ReflectedWilsonKernel.kernel n G χ β c (family n G χ) (false, true)).re =
    ∫ U, ‖loopObservable (Vertex (2 * n)) G (realCharacter G χ) (plaquette (2 * n) 0 1 2) U -
      ∫ W, loopObservable (Vertex (2 * n)) G (realCharacter G χ) (plaquette (2 * n) 0 1 2) W
        ∂wilsonLaw (2 * n) G χ β c‖ ^ 2 ∂wilsonLaw (2 * n) G χ β c := by
  letI := wilsonLaw_probability (2 * n) G χ hχ β c
  rw [kernel_eq_ordinary]
  have he := ConnectedGramLimit.gram_variance_identity (wilsonLaw (2 * n) G χ β c)
    (fun i => observable n G (family n G χ i))
    (fun i => ReflectedWilsonKernel.continuous_observable n G _ (family_continuous n G χ hχ i))
    false true (observable_false n G χ)
  simpa only [observable_true] using he.symm

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem family_bound (ρ : G →* Matrix.unitaryGroup d ℂ) (i : Bool)
    (z : BoundaryConfiguration n G × HalfConfiguration n G) :
    ‖family n G (unitaryCharacter ρ) i z‖ ≤ max 1 (Fintype.card d : ℝ) := by
  cases i
  · exact (by simpa only [family, Bool.false_eq_true, ↓reduceIte, norm_one] using
      (le_max_left (1 : ℝ) (Fintype.card d : ℝ)))
  · change ‖( (unitaryCharacter ρ _).re : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact ((Complex.abs_re_le_norm _).trans (unitary_trace_bound _)).trans (le_max_right _ _)

theorem real_plaquette_variance_lower (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (betaMax β c : ℝ) (hβ : |β| ≤ betaMax) :
    varianceFloor ρ betaMax ≤
    ∫ U, ‖loopObservable (Vertex (2 * n)) G (realCharacter G (unitaryCharacter ρ))
        (plaquette (2 * n) 0 1 2) U -
      ∫ W, loopObservable (Vertex (2 * n)) G (realCharacter G (unitaryCharacter ρ))
        (plaquette (2 * n) 0 1 2) W ∂wilsonLaw (2 * n) G (unitaryCharacter ρ) β c‖ ^ 2
      ∂wilsonLaw (2 * n) G (unitaryCharacter ρ) β c := by
  letI : Fact (1 < 2 * n) := ⟨by have hn := NeZero.pos n; omega⟩
  have hb (g : G) : ‖realCharacter G (unitaryCharacter ρ) g‖ ≤ (Fintype.card d : ℝ) := by
    change ‖((unitaryCharacter ρ g).re : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (unitary_trace_bound _)
  have h := WilsonUniformVariance.bounded_coupling_variance_lower (2 * n) G
    (realCharacter G (unitaryCharacter ρ))
    (realCharacter_continuous G _ (unitaryCharacter_continuous ρ hρ))
    (Fintype.card d : ℝ) (Nat.cast_nonneg _) hb betaMax β c hβ 0 1 2 (by decide)
  simpa only [law_realCharacter, haarFluctuation_realCharacter, varianceFloor] using h

theorem reflected_variance_lower (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (betaMax β c : ℝ) (hβ : |β| ≤ betaMax) :
    varianceFloor ρ betaMax ≤
      (ReflectedWilsonKernel.kernel n G (unitaryCharacter ρ) β c
        (family n G (unitaryCharacter ρ)) (true, true) -
      ReflectedWilsonKernel.kernel n G (unitaryCharacter ρ) β c
        (family n G (unitaryCharacter ρ)) (true, false) *
      ReflectedWilsonKernel.kernel n G (unitaryCharacter ρ) β c
        (family n G (unitaryCharacter ρ)) (false, true)).re := by
  rw [reflected_variance_identity n G _ (unitaryCharacter_continuous ρ hρ)]
  exact real_plaquette_variance_lower n G ρ hρ betaMax β c hβ

/-- The two labels are the constant vacuum and the real boundary plaquette.
This is the reflected Wilson kernel, not the ordinary probability kernel. -/
def boundaryKernel (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (β c : ℝ) : PositiveKernel Bool :=
  ReflectedWilsonKernel.positiveKernel n G (unitaryCharacter ρ)
    (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
    (unitaryCharacter_inverse_re G ρ) β c (family n G (unitaryCharacter ρ))
    (family_continuous n G _ (unitaryCharacter_continuous ρ hρ))

theorem boundaryKernel_normalized (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (β c : ℝ) : (boundaryKernel n G ρ hρ β c).value (false, false) = 1 :=
  ReflectedWilsonKernel.kernel_normalized n G _ (unitaryCharacter_continuous ρ hρ)
    β c (family n G (unitaryCharacter ρ)) false (fun _ => rfl)

theorem finite_centered_floor (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (betaMax β c : ℝ) (hβ : |β| ≤ betaMax) :
    varianceFloor ρ betaMax ≤ ‖centered (boundaryKernel n G ρ hρ β c) false true‖ ^ 2 := by
  rw [centered_norm_sq _ false true (boundaryKernel_normalized n G ρ hρ β c)]
  exact reflected_variance_lower n G ρ hρ betaMax β c hβ

theorem finite_nonvacuum (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ)
    (g : G) (hg : ρ g ≠ 1) (β c : ℝ) :
    canonical (boundaryKernel n G ρ hρ β c) true ∉
      Submodule.span ℂ ({vacuum (boundaryKernel n G ρ hρ β c) false} :
        Set (Hilbert (boundaryKernel n G ρ hρ β c))) := by
  apply canonical_not_vacuum_span _ false true (boundaryKernel_normalized n G ρ hρ β c)
  exact (varianceFloor_pos ρ hρ g hg |β|).trans_le
    (reflected_variance_lower n G ρ hρ |β| β c le_rfl)

/-- A volume-independent positive boundary fluctuation survives an actual
reflected-kernel subsequence at uniformly bounded coupling. In particular the
completed limit Hilbert space is strictly larger than its vacuum line. -/
theorem exists_bounded_coupling_nonvacuum_limit
    (ρ : G →* Matrix.unitaryGroup d ℂ) (hρ : Continuous ρ) (g : G) (hg : ρ g ≠ 1)
    (period : ℕ → ℕ) [∀ k, NeZero (period k)] (beta offset : ℕ → ℝ)
    (betaMax : ℝ) (hbeta : ∀ k, |beta k| ≤ betaMax) :
    ∃ (K : PositiveKernel Bool) (phi : ℕ → ℕ), StrictMono phi ∧
      CoordinateConvergence
        (fun k => ReflectedWilsonKernel.kernel (period (phi k)) G (unitaryCharacter ρ)
          (beta (phi k)) (offset (phi k)) (family (period (phi k)) G (unitaryCharacter ρ)))
        K.value ∧ K.value (false, false) = 1 ∧
      0 < varianceFloor ρ betaMax ∧ varianceFloor ρ betaMax ≤ connectedVariance K false true ∧
      ‖vacuum K false‖ = 1 ∧
      canonical K true ∉ Submodule.span ℂ ({vacuum K false} : Set (Hilbert K)) := by
  obtain ⟨K, phi, hphi, hc, _, hn⟩ :=
    ReflectedWilsonKernel.exists_normalized_reflected_limit G period beta offset
      (unitaryCharacter ρ) (unitaryCharacter_continuous ρ hρ) (unitaryCharacter_class ρ)
      (unitaryCharacter_inverse_re G ρ) (fun k => family (period k) G (unitaryCharacter ρ))
      (fun k => family_continuous (period k) G _ (unitaryCharacter_continuous ρ hρ))
      (fun _ => max 1 (Fintype.card d : ℝ))
      (fun _ => zero_le_one.trans (le_max_left _ _))
      (fun k => family_bound (period k) G ρ) false (fun _ _ => rfl)
  have hpos := varianceFloor_pos ρ hρ g hg betaMax
  have hv : varianceFloor ρ betaMax ≤ connectedVariance K false true :=
    ConnectedGramLimit.connected_floor_survives _ _ hc false true (varianceFloor ρ betaMax)
      (fun k => reflected_variance_lower (period (phi k)) G ρ hρ
        betaMax (beta (phi k)) (offset (phi k)) (hbeta (phi k)))
  exact ⟨K, phi, hphi, hc, hn, hpos, hv, vacuum_norm K false hn,
    canonical_not_vacuum_span K false true hn (hpos.trans_le hv)⟩

end
end UnifiedTheory.Clay.YangMills.BoundaryPlaquetteOS
