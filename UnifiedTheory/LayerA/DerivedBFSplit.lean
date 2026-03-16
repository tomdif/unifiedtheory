/-
  LayerA/DerivedBFSplit.lean — Derive source/dressing split from a functional

  The previous BFSourceDressing.lean STIPULATED the K/P decomposition
  and the vanishing of source on P. This file DERIVES both from a
  single primitive: a nonzero linear functional φ : V →ₗ[ℝ] ℝ.

  Construction:
    Given φ and any v₀ with φ(v₀) ≠ 0:
    - πK(v) = (φ(v) / φ(v₀)) • v₀     (project onto source direction)
    - πP(v) = v - πK(v)                 (everything else is dressing)

  Derived (not stipulated):
    - πK is a linear idempotent projection  (proven)
    - v = πK(v) + πP(v)                    (proven)
    - φ(πP(v)) = 0                          (proven — dressing has zero source)
    - φ(πK(v)) = φ(v)                       (proven — source captures all of φ)

  The source/dressing split is a CONSEQUENCE of having a source
  functional, not an independent postulate.
-/
import UnifiedTheory.LayerA.BFSourceDressing

namespace UnifiedTheory.LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### The source functional primitive -/

/-- Primitive data: a nonzero source functional and a reference vector. -/
structure SourceFunctional (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The source variation functional φ -/
  φ : V →ₗ[ℝ] ℝ
  /-- A reference source vector -/
  v₀ : V
  /-- v₀ is detected by φ (nonzero source) -/
  hv₀ : φ v₀ ≠ 0

variable (sf : SourceFunctional V)

/-! ### Derived projections -/

/-- **Source projection (DERIVED)**: πK(v) = (φ(v)/φ(v₀)) • v₀.
    Projects onto the source-capable direction. -/
noncomputable def sourceProj : V →ₗ[ℝ] V where
  toFun v := (sf.φ v / sf.φ sf.v₀) • sf.v₀
  map_add' u w := by
    simp only [map_add, add_div, add_smul]
  map_smul' r v := by
    simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_div_assoc, mul_smul]

/-- **Dressing projection (DERIVED)**: πP = id - πK. -/
noncomputable def dressingProj : V →ₗ[ℝ] V :=
  LinearMap.id - sourceProj sf

/-! ### Prove all properties -/

/-- The source projection is idempotent: πK ∘ πK = πK. -/
theorem sourceProj_idem :
    (sourceProj sf) ∘ₗ (sourceProj sf) = sourceProj sf := by
  ext v
  simp only [LinearMap.comp_apply, sourceProj, LinearMap.coe_mk, AddHom.coe_mk]
  -- Goal: (sf.φ ((sf.φ v / sf.φ sf.v₀) • sf.v₀) / sf.φ sf.v₀) • sf.v₀ = (sf.φ v / sf.φ sf.v₀) • sf.v₀
  congr 1
  rw [LinearMap.map_smul, smul_eq_mul, mul_div_assoc]
  field_simp

/-- Every vector decomposes: v = πK(v) + πP(v). -/
theorem source_dressing_decomp (v : V) :
    v = sourceProj sf v + dressingProj sf v := by
  simp [dressingProj, LinearMap.sub_apply, LinearMap.id_apply, add_sub_cancel]

/-- **Source functional captures everything on K**: φ(πK(v)) = φ(v). -/
theorem source_on_K (v : V) :
    sf.φ (sourceProj sf v) = sf.φ v := by
  simp only [sourceProj, LinearMap.coe_mk, AddHom.coe_mk, map_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ sf.hv₀

/-- **Source functional vanishes on dressing**: φ(πP(v)) = 0.
    THIS IS THE KEY DERIVED RESULT. Previously stipulated, now proven. -/
theorem source_vanishes_on_dressing (v : V) :
    sf.φ (dressingProj sf v) = 0 := by
  simp only [dressingProj, LinearMap.sub_apply, LinearMap.id_apply]
  rw [map_sub, source_on_K, sub_self]

/-! ### Construct SourceDressingDecomp from SourceFunctional -/

/-- **Every source functional induces a SourceDressingDecomp.**
    The K/P split is not stipulated — it is constructed from φ,
    and all properties are derived from linearity. -/
noncomputable def decompFromFunctional : SourceDressingDecomp V where
  πK := sourceProj sf
  sourceFunc := sf.φ
  πK_idem := sourceProj_idem sf
  source_vanishes_on_P := fun v hv => by
    -- Need: φ(v) = 0 when πK(v) = 0
    -- If πK(v) = 0, then v = πP(v), so φ(v) = φ(πP(v)) = 0
    have : v = sourceProj sf v + dressingProj sf v := source_dressing_decomp sf v
    rw [hv, zero_add] at this
    rw [this]
    exact source_vanishes_on_dressing sf v

/-- **The derived decomposition theorem.**
    From a single nonzero linear functional φ:
    (1) A canonical K/P split exists
    (2) The decomposition v = πK(v) + πP(v) holds
    (3) φ vanishes on the P-channel
    (4) φ(πK(v)) = φ(v) — the K-channel captures all source data
    All derived, nothing stipulated. -/
theorem functional_derives_decomposition :
    -- (1) K/P split exists (constructed above)
    (∀ v : V, v = (decompFromFunctional sf).πK v + (decompFromFunctional sf).πP v)
    -- (2) Source vanishes on P
    ∧ (∀ v : V, (decompFromFunctional sf).πK v = 0 →
        sf.φ v = 0)
    -- (3) K captures all source data
    ∧ (∀ v : V, sf.φ (sourceProj sf v) = sf.φ v) :=
  ⟨fun v => (decompFromFunctional sf).decompose v,
   fun v hv => (decompFromFunctional sf).source_vanishes_on_P v hv,
   source_on_K sf⟩

end UnifiedTheory.LayerA
