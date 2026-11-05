/- Actual cyclic time translations of a periodic lattice, including exact
plaquette covariance and invariance of product Haar and Wilson probability.
No Osterwalder--Schrader shift, Hamiltonian, or mass gap is inferred. -/
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicTimeTranslation
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4
open PeriodicTimeReflection PeriodicPlaquetteReflection

variable (N : ℕ)

def shiftVertex (s : ZMod N) (x : Vertex N) : Vertex N := x + Pi.single 0 s

@[simp] theorem shiftVertex_zero (x : Vertex N) : shiftVertex N 0 x = x := by
  simp [shiftVertex]

theorem shiftVertex_add (s t : ZMod N) (x : Vertex N) :
    shiftVertex N s (shiftVertex N t x) = shiftVertex N (s + t) x := by
  simp only [shiftVertex, Pi.single_add]
  abel

theorem shiftVertex_step (s : ZMod N) (x : Vertex N) (μ : Fin 4) :
    shiftVertex N s (step N x μ) = step N (shiftVertex N s x) μ := by
  unfold shiftVertex step
  abel

def vertexShiftEquiv (s : ZMod N) : Vertex N ≃ Vertex N where
  toFun := shiftVertex N s
  invFun := shiftVertex N (-s)
  left_inv x := by rw [shiftVertex_add, neg_add_cancel, shiftVertex_zero]
  right_inv x := by rw [shiftVertex_add, add_neg_cancel, shiftVertex_zero]

def edgeShiftEquiv (s : ZMod N) : Edge (Vertex N) ≃ Edge (Vertex N) :=
  (edgeCoordinates N).trans
    ((Equiv.prodCongr (vertexShiftEquiv N s) (Equiv.refl (Fin 4))).trans (edgeCoordinates N).symm)

@[simp] theorem edgeShift_zero (e : Edge (Vertex N)) : edgeShiftEquiv N 0 e = e := by
  apply (edgeCoordinates N).injective
  simp only [edgeShiftEquiv, vertexShiftEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, Equiv.coe_fn_mk]
  exact Prod.ext (shiftVertex_zero N e.1) rfl

theorem edgeShift_add (s t : ZMod N) (e : Edge (Vertex N)) :
    edgeShiftEquiv N s (edgeShiftEquiv N t e) = edgeShiftEquiv N (s + t) e := by
  apply (edgeCoordinates N).injective
  simp only [edgeShiftEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.prodCongr_apply, vertexShiftEquiv, Equiv.coe_fn_mk, Equiv.refl_apply]
  exact Prod.ext (shiftVertex_add N s t e.1) rfl

variable (G : Type*) [Group G]

def shiftConfiguration (s : ZMod N) (U : Configuration (Vertex N) G) : Configuration (Vertex N) G :=
  U ∘ edgeShiftEquiv N s

@[simp] theorem shiftConfiguration_zero (U : Configuration (Vertex N) G) :
    shiftConfiguration N G 0 U = U := by
  funext e
  simp [shiftConfiguration]

theorem shiftConfiguration_add (s t : ZMod N) (U : Configuration (Vertex N) G) :
    shiftConfiguration N G s (shiftConfiguration N G t U) = shiftConfiguration N G (s + t) U := by
  funext e
  simp only [shiftConfiguration, Function.comp_apply, edgeShift_add, add_comm t s]

def configurationShiftEquiv (s : ZMod N) : Configuration (Vertex N) G ≃ Configuration (Vertex N) G where
  toFun := shiftConfiguration N G s
  invFun := shiftConfiguration N G (-s)
  left_inv U := by rw [shiftConfiguration_add, neg_add_cancel, shiftConfiguration_zero]
  right_inv U := by rw [shiftConfiguration_add, add_neg_cancel, shiftConfiguration_zero]

@[simp] theorem shift_link (s : ZMod N) (U : Configuration (Vertex N) G)
    (x : Vertex N) (μ : Fin 4) :
    linkValue N G (shiftConfiguration N G s U) x μ = linkValue N G U (shiftVertex N s x) μ := rfl

theorem shifted_plaquette (s : ZMod N) (U : Configuration (Vertex N) G)
    (x : Vertex N) (μ ν : Fin 4) :
    plaquetteProduct N G (shiftConfiguration N G s U) x μ ν =
      plaquetteProduct N G U (shiftVertex N s x) μ ν := by
  simp only [plaquetteProduct, shift_link, shiftVertex_step]

theorem plaquette_holonomy_shift (s : ZMod N) (U : Configuration (Vertex N) G)
    (x : Vertex N) (μ ν : Fin 4) :
    holonomy (Quiver.Symmetrify (Vertex N)) G (orientedExtension (Vertex N) G
      (shiftConfiguration N G s U)) (plaquette N x μ ν) =
    holonomy (Quiver.Symmetrify (Vertex N)) G (orientedExtension (Vertex N) G U)
      (plaquette N (shiftVertex N s x) μ ν) := by
  simp only [plaquette_holonomy_eq_product, shifted_plaquette]

def shiftPlaquette (s : ZMod N) (p : PlaquetteIndex N) : PlaquetteIndex N :=
  (shiftVertex N s p.1, p.2)

def plaquetteShiftEquiv (s : ZMod N) : PlaquetteIndex N ≃ PlaquetteIndex N :=
  Equiv.prodCongr (vertexShiftEquiv N s) (Equiv.refl Plane)

variable [NeZero N]

theorem wilsonAction_shift (χ : G → ℂ) (β c : ℝ) (s : ZMod N)
    (U : Configuration (Vertex N) G) :
    orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c (shiftConfiguration N G s U) =
      orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c U := by
  change β * ∑ p : PlaquetteIndex N, (c - (χ (holonomy (Quiver.Symmetrify (Vertex N)) G
    (orientedExtension (Vertex N) G (shiftConfiguration N G s U))
    (plaquette N p.1 p.2.1.1 p.2.1.2))).re) =
      β * ∑ p : PlaquetteIndex N, (c - (χ (holonomy (Quiver.Symmetrify (Vertex N)) G
        (orientedExtension (Vertex N) G U) (plaquette N p.1 p.2.1.1 p.2.1.2))).re)
  simp only [plaquette_holonomy_shift]
  congr 1
  exact Equiv.sum_comp (plaquetteShiftEquiv N s)
    (fun p => c - (χ (holonomy (Quiver.Symmetrify (Vertex N)) G
      (orientedExtension (Vertex N) G U) (plaquette N p.1 p.2.1.1 p.2.1.2))).re)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem shiftConfiguration_continuous (s : ZMod N) : Continuous (shiftConfiguration N G s) :=
  continuous_pi (fun _ => continuous_apply _)

def configurationShiftMeasurableEquiv (s : ZMod N) :
    Configuration (Vertex N) G ≃ᵐ Configuration (Vertex N) G :=
  { configurationShiftEquiv N G s with
    measurable_toFun := (shiftConfiguration_continuous N G s).measurable
    measurable_invFun := (shiftConfiguration_continuous N G (-s)).measurable }

theorem reference_preserves_shift (s : ZMod N) :
    MeasurePreserving (shiftConfiguration N G s)
      (referenceMeasure G (Vertex N)) (referenceMeasure G (Vertex N)) := by
  have h := measurePreserving_piCongrLeft
    (fun _ : Edge (Vertex N) => compactHaar G) (edgeShiftEquiv N s).symm
  convert h using 1
  funext U e
  simp [shiftConfiguration, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem wilsonLaw_preserves_shift (χ : G → ℂ) (hcχ : Continuous χ)
    (β c : ℝ) (s : ZMod N) :
    MeasurePreserving (shiftConfiguration N G s) (wilsonLaw N G χ β c) (wilsonLaw N G χ β c) := by
  apply MeasurePreserving.smul_measure
  apply preserves_withDensity (reference_preserves_shift N G s) _
    (Real.continuous_exp.comp
      (continuous_orientedWilsonAction (Vertex N) G χ hcχ (base N) (loops N) β c).neg).measurable.ennreal_ofReal
  intro U
  change ENNReal.ofReal (Real.exp (-orientedWilsonAction (Vertex N) G χ (base N) (loops N) β c
    (shiftConfiguration N G s U))) = _
  rw [wilsonAction_shift]
  rfl

end
end UnifiedTheory.Clay.YangMills.PeriodicTimeTranslation
