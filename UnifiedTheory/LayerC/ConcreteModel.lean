/-
  LayerC/ConcreteModel.lean — Concrete realization of MatterParentU

  Constructs U★: an explicit model with real defect sectors.

  Model:
  - V = ℝ² (source/dressing field space)
  - T = ℝ³, Ω = ℝ (tensor/1-form spaces)
  - Defects = ℝ² pairs (κ, δ) with κ = source, δ = dressing
  - Stable = nonzero
  - BF: Kpart = (κ,0), Ppart = (0,δ)
  - Null: bias = κ
  - Source measure = first coordinate

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.DefectEquivalence
import UnifiedTheory.LayerB.UnifiedBranch
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace UnifiedTheory.LayerC

open UnifiedTheory.LayerA
open UnifiedTheory.LayerB

/-! ### Field space ℝ² -/

abbrev FieldSpace := Fin 2 → ℝ
abbrev TensorSpace := Fin 3 → ℝ
abbrev OneFormSpace := ℝ

noncomputable def proj₁ : FieldSpace →ₗ[ℝ] ℝ where
  toFun v := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def πK_map : FieldSpace →ₗ[ℝ] FieldSpace where
  toFun v := fun i => if i = (0 : Fin 2) then v 0 else 0
  map_add' u w := by
    ext i; simp only [Pi.add_apply]
    by_cases hi : i = 0 <;> simp [hi]
  map_smul' r v := by
    ext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    by_cases hi : i = 0 <;> simp [hi]

lemma πK_map_idem : πK_map ∘ₗ πK_map = πK_map := by
  ext v i; simp only [LinearMap.comp_apply, πK_map]
  by_cases hi : i = 0 <;> simp [hi]

lemma proj₁_vanishes_on_ker_πK (v : FieldSpace) (hv : πK_map v = 0) :
    proj₁ v = 0 := by
  have : (πK_map v) 0 = 0 := by rw [hv]; rfl
  simp only [πK_map, ite_true] at this
  exact this

noncomputable def concreteBF : SourceDressingDecomp FieldSpace where
  πK := πK_map
  sourceFunc := proj₁
  πK_idem := πK_map_idem
  source_vanishes_on_P := proj₁_vanishes_on_ker_πK

/-! ### Scale block: α = 2 -/

noncomputable def concreteScale : ScaleBlock where
  c_pot := 1
  α := 2
  hc := one_ne_zero
  h_fixedPoint := by
    intro ℓ hℓ r hr
    rw [renormOp_powerLaw 1 2 ℓ r hℓ hr]
    norm_num

/-! ### Null block: Minkowski form -/

def concreteNull : NullBlock where
  a_S := -1
  b_S := 0
  c_S := 1
  h_null := by
    intro v hv; simp only [genQuad, minkQuad] at *; nlinarith

/-! ### Endpoint block: pure Einstein -/

noncomputable def concreteEndpt : EndptBlock TensorSpace OneFormSpace where
  cd := {
    R_ricci := fun i => if i = 0 then 1 else 0
    g_metric := fun i => if i = 1 then 1 else 0
    R_scalar := 2
  }
  c_L := 1
  d_L := -1/2
  e_L := 0
  h_div := by
    intro gradR
    have h : (1 : ℝ) / 2 + (-1 / 2) = 0 := by ring
    rw [h, zero_smul]
  h_nondeg := ⟨1, one_ne_zero⟩

/-! ### Defect sector -/

structure ConcreteDefect where
  κ : ℝ
  δ : ℝ

def concreteStable (d : ConcreteDefect) : Prop := d.κ ≠ 0 ∨ d.δ ≠ 0

def concreteToBF (d : ConcreteDefect) : BFDefectData FieldSpace where
  Kpart := fun i => if i = (0 : Fin 2) then d.κ else 0
  Ppart := fun i => if i = (0 : Fin 2) then 0 else d.δ

def concreteToNull (d : ConcreteDefect) : NullDefectData where
  bias := d.κ

noncomputable def concreteDefects : DefectBlock FieldSpace where
  Defect := ConcreteDefect
  Stable := concreteStable
  toBF := concreteToBF
  toNull := concreteToNull
  sourceMeas := ⟨proj₁⟩
  biasScale := 1
  sourceMatchesBias := fun d _ => by
    change proj₁ (concreteToBF d).Kpart = 1 * (concreteToNull d).bias
    simp [proj₁, concreteToBF, concreteToNull, one_mul]
  dressingNeutral := by
    intro d _
    simp only [proj₁, concreteToBF]
    rfl

/-! ### Assemble U★ -/

noncomputable def concreteParentU : ParentU FieldSpace TensorSpace OneFormSpace where
  scale := concreteScale
  null := concreteNull
  bf := ⟨concreteBF⟩
  endpt := concreteEndpt

noncomputable def U_star : MatterParentU FieldSpace TensorSpace OneFormSpace where
  toParentU := concreteParentU
  defects := concreteDefects

/-! ### Witness defects -/

def inertDefect : ConcreteDefect := ⟨0, 1⟩
def sourceDefect : ConcreteDefect := ⟨1, 0⟩

theorem inertDefect_stable : concreteStable inertDefect := Or.inr one_ne_zero
theorem sourceDefect_stable : concreteStable sourceDefect := Or.inl one_ne_zero

theorem inertDefect_isInert : IsInert concreteDefects inertDefect := by
  constructor
  · show proj₁ (concreteToBF inertDefect).Kpart = 0
    simp [proj₁, concreteToBF, inertDefect]
  · show (concreteToNull inertDefect).bias = 0
    simp [concreteToNull, inertDefect]

theorem sourceDefect_isSource : IsSourceCarrying concreteDefects sourceDefect := by
  show proj₁ (concreteToBF sourceDefect).Kpart ≠ 0
  simp [proj₁, concreteToBF, sourceDefect]

/-! ### The Realization Theorem -/

/-- **Concrete Realization Theorem.**

    U★ is an explicit MatterParentU such that:
    (1) The unified Einstein branch applies.
    (2) Both inert and source-carrying stable defects exist.

    This proves the framework is non-vacuous and both sides
    of the defect dichotomy are populated in a concrete model. -/
theorem concrete_realization :
    -- (1) Einstein branch applies to U★
    U_star.toParentU.scale.α = 2
    ∧ (∃ c₀ : ℝ, ∀ v w,
        genBilin U_star.toParentU.null.a_S U_star.toParentU.null.b_S
          U_star.toParentU.null.c_S v w = c₀ * minkBilin v w)
    -- (2) Inert defect exists
    ∧ (∃ d, U_star.defects.Stable d ∧ IsInert U_star.defects d)
    -- (3) Source-carrying defect exists
    ∧ (∃ d, U_star.defects.Stable d ∧ IsSourceCarrying U_star.defects d) :=
  ⟨LayerB.bridge_rg U_star.toParentU.scale,
   LayerB.bridge_null U_star.toParentU.null,
   ⟨inertDefect, inertDefect_stable, inertDefect_isInert⟩,
   ⟨sourceDefect, sourceDefect_stable, sourceDefect_isSource⟩⟩

end UnifiedTheory.LayerC
