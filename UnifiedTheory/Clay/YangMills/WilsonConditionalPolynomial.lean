/- Polynomial ordinary plaquette fluctuations in the actual one-link
conditional Wilson Gibbs law, uniformly over volume and exterior links.
This does not bound the normalized response after integrating out a half lattice. -/
import UnifiedTheory.Clay.YangMills.SingleLinkWilsonLipschitz
import UnifiedTheory.Clay.YangMills.UnitaryGibbsTraceFluctuation
import UnifiedTheory.Clay.YangMills.GibbsConditionalLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonConditionalPolynomial
noncomputable section
open MeasureTheory Matrix RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open UnitaryCharacterObservables WilsonCrossingKernel SingleCoordinateProduct
open UnitaryHaarCaps UnitaryGibbsTraceFluctuation CompactGibbsContinuity GibbsCoordinateTransport

variable (n : ℕ) [NeZero n] (d : Type*) [Fintype d] [DecidableEq d]

local instance : DecidableEq (Edge (Vertex n)) := Classical.decEq _

def action (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (g : Matrix.unitaryGroup d ℂ) : ℝ :=
  orientedWilsonAction (Vertex n) (Matrix.unitaryGroup d ℂ)
    (unitaryCharacter (MonoidHom.id _)) (base n) (loops n) β c
    (assemble (selectedLink n x μ) (r,g))

theorem action_continuous (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) : Continuous (action n d β c x μ r) :=
  (continuous_orientedWilsonAction _ (Matrix.unitaryGroup d ℂ)
    (unitaryCharacter (MonoidHom.id _)) (unitaryCharacter_continuous _ continuous_id) _ _ β c).comp
    ((assemble_continuous _).comp (continuous_const.prodMk continuous_id))

theorem action_lipschitz (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ)
    (A B : Matrix.unitaryGroup d ℂ) (s : ℝ) (hs : 0 ≤ s)
    (h : ∀ i j, ‖A i j-B i j‖ ≤ s) :
    |action n d β c x μ r A-action n d β c x μ r B| ≤
      (24*(Fintype.card d : ℝ)^3*|β|)*s := by
  refine SingleLinkWilsonLipschitz.action_lipschitz n (Matrix.unitaryGroup d ℂ)
    (MonoidHom.id _) β c x μ _ _ ?_ s hs ?_
  · intro e he
    simp only [assemble_other _ _ he]
  · simpa only [assemble_self, MonoidHom.id_apply] using h

/-- Right-translate the observable by any fixed residual holonomy. The
translated action costs one additional dimension factor in its Lipschitz bound. -/
theorem translated_trace_lower [Nonempty d] (β c : ℝ) (x : Vertex n) (μ : Fin 4)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ) (R : Matrix.unitaryGroup d ℂ)
    (k : ℕ) (hk : 0 < k) (hβ : 24*(Fintype.card d : ℝ)^4*|β| ≤ k) (center : ℂ) :
    polynomialFloor d k ≤ ∫ g, ‖realTrace d (g*R)-center‖^2
      ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r) := by
  let S := action n d β c x μ r
  let S' := fun U : Matrix.unitaryGroup d ℂ => S (U*R⁻¹)
  have hS : Continuous S := action_continuous n d β c x μ r
  have hS' : Continuous S' := hS.comp (continuous_id.mul continuous_const)
  have hLip (A B : Matrix.unitaryGroup d ℂ) (s : ℝ) (hs : 0 ≤ s)
      (h : ∀ i j, ‖A i j-B i j‖ ≤ s) :
      |S' A-S' B| ≤ (24*(Fintype.card d : ℝ)^4*|β|)*s := by
    have he (i j : d) : ‖(A*R⁻¹) i j-(B*R⁻¹) i j‖ ≤ (Fintype.card d : ℝ)*s := by
      have hh := SingleLinkWilsonLipschitz.right_mul_entry R⁻¹
        ((A : Matrix d d ℂ)-(B : Matrix d d ℂ)) s h i j
      simpa only [sub_mul, ← UnitaryGroup.mul_val] using hh
    have hh := action_lipschitz n d β c x μ r (A*R⁻¹) (B*R⁻¹) _ (by positivity) he
    change |S' A-S' B| ≤ _ at hh
    convert hh using 1 <;> ring
  have hh := polynomial_lower d S' hS' (24*(Fintype.card d : ℝ)^4*|β|)
    (by positivity) hLip k hk hβ center
  have he := weighted_integral_transport
    (compactHaar (Matrix.unitaryGroup d ℂ)) (compactHaar (Matrix.unitaryGroup d ℂ))
    (MeasurableEquiv.mulRight R⁻¹) (measurePreserving_mul_right _ R⁻¹)
    (fun g => Real.exp (-S g)) (Real.continuous_exp.comp hS.neg).measurable
    (fun g => (Real.exp_pos _).le) (partition_positive _ S hS)
    (fun g => ‖realTrace d (g*R)-center‖^2)
  have he' : (∫ g, ‖realTrace d g-center‖^2 ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) S') =
      ∫ g, ‖realTrace d (g*R)-center‖^2 ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) S := by
    simpa only [law, Function.comp_apply, MeasurableEquiv.coe_mulRight,
      inv_mul_cancel_right] using he
  rw [he'] at hh
  exact hh

/-- This is the actual selected plaquette under the exact fixed-exterior
Wilson action, for every exterior and every center, including its Gibbs mean. -/
theorem plaquette_conditional_lower [Fact (1 < n)] [Nonempty d]
    (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν)
    (r : Exterior n (Matrix.unitaryGroup d ℂ) x μ)
    (k : ℕ) (hk : 0 < k) (hβ : 24*(Fintype.card d : ℝ)^4*|β| ≤ k) (center : ℂ) :
    polynomialFloor d k ≤ ∫ g,
      ‖realTrace d (holonomy (Quiver.Symmetrify (Vertex n)) (Matrix.unitaryGroup d ℂ)
        (orientedExtension (Vertex n) (Matrix.unitaryGroup d ℂ)
          (assemble (selectedLink n x μ) (r,g))) (plaquette n x μ ν))-center‖^2
      ∂law (compactHaar (Matrix.unitaryGroup d ℂ)) (action n d β c x μ r) := by
  simp_rw [plaquette_split n (Matrix.unitaryGroup d ℂ) x μ ν hμν r]
  exact translated_trace_lower n d β c x μ r _ k hk hβ center

/-- Uniform ordinary plaquette second moment under the FULL interacting
periodic Wilson law. The constant has no volume or exterior dependence. -/
theorem full_plaquette_lower [Fact (1 < n)] [Nonempty d]
    (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν)
    (k : ℕ) (hk : 0 < k) (hβ : 24*(Fintype.card d : ℝ)^4*|β| ≤ k) (center : ℂ) :
    polynomialFloor d k ≤ ∫ U,
      ‖realTrace d (holonomy (Quiver.Symmetrify (Vertex n)) (Matrix.unitaryGroup d ℂ)
        (orientedExtension (Vertex n) (Matrix.unitaryGroup d ℂ) U) (plaquette n x μ ν))-center‖^2
      ∂gibbsMeasure (Vertex n) (Matrix.unitaryGroup d ℂ)
        (orientedWilsonAction (Vertex n) (Matrix.unitaryGroup d ℂ)
          (unitaryCharacter (MonoidHom.id _)) (base n) (loops n) β c) := by
  let S := orientedWilsonAction (Vertex n) (Matrix.unitaryGroup d ℂ)
    (unitaryCharacter (MonoidHom.id _)) (base n) (loops n) β c
  let F := fun U : Configuration (Vertex n) (Matrix.unitaryGroup d ℂ) =>
    realTrace d (holonomy (Quiver.Symmetrify (Vertex n)) (Matrix.unitaryGroup d ℂ)
      (orientedExtension (Vertex n) (Matrix.unitaryGroup d ℂ) U) (plaquette n x μ ν))
  have hS : Continuous S := continuous_orientedWilsonAction _ _ _
    (unitaryCharacter_continuous _ continuous_id) _ _ β c
  have hF : Continuous F := (realTrace_continuous d).comp
    ((continuous_holonomy (Quiver.Symmetrify (Vertex n)) (Matrix.unitaryGroup d ℂ)
      (plaquette n x μ ν)).comp (continuous_orientedExtension (Vertex n) (Matrix.unitaryGroup d ℂ)))
  change polynomialFloor d k ≤ ∫ U, ‖F U-center‖^2 ∂gibbsMeasure _ _ S
  rw [gibbs_integral_split (Vertex n) (Matrix.unitaryGroup d ℂ) S hS (selectedLink n x μ)]
  apply GibbsConditionalLower.expectation_lower
    (compactHaar (Matrix.unitaryGroup d ℂ))
    (Measure.pi (fun _ : {e : Edge (Vertex n) // e ≠ selectedLink n x μ} =>
      compactHaar (Matrix.unitaryGroup d ℂ)))
    (fun z => S (assemble (selectedLink n x μ) z)) (hS.comp (assemble_continuous _))
    (fun z => ‖F (assemble (selectedLink n x μ) z)-center‖^2)
    (((hF.comp (assemble_continuous _)).sub continuous_const).norm.pow 2)
    (polynomialFloor d k)
  intro r
  exact plaquette_conditional_lower n d β c x μ ν hμν r k hk hβ center

/-- A fully specified bound, with no supplied coupling or fluctuation premise.
The grid index grows at most linearly in |beta|. -/
theorem full_plaquette_explicit [Fact (1 < n)] [Nonempty d]
    (β c : ℝ) (x : Vertex n) (μ ν : Fin 4) (hμν : μ ≠ ν) (center : ℂ) :
    polynomialFloor d (⌈24*(Fintype.card d : ℝ)^4*|β|⌉₊+1) ≤ ∫ U,
      ‖realTrace d (holonomy (Quiver.Symmetrify (Vertex n)) (Matrix.unitaryGroup d ℂ)
        (orientedExtension (Vertex n) (Matrix.unitaryGroup d ℂ) U) (plaquette n x μ ν))-center‖^2
      ∂gibbsMeasure (Vertex n) (Matrix.unitaryGroup d ℂ)
        (orientedWilsonAction (Vertex n) (Matrix.unitaryGroup d ℂ)
          (unitaryCharacter (MonoidHom.id _)) (base n) (loops n) β c) := by
  apply full_plaquette_lower n d β c x μ ν hμν _ (by omega) _ center
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_succ _))

end
end UnifiedTheory.Clay.YangMills.WilsonConditionalPolynomial
