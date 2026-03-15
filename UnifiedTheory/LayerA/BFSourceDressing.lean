/-
  Layer A.2 — BF source/dressing algebraic split

  In the constrained BF/Plebanski framework, the Yang-Mills sector splits into:
    - K-type channel: source-capable (couples to curvature)
    - P-type channel: dressing-only (does not source gravity)

  This file formalizes the algebraic structure of this split:
  given a Lie algebra decomposition and a constraint structure,
  only the K-type components appear in the gravitational source term.

  The key algebraic fact: the source variation δS/δB picks out exactly
  the K-type components, while P-type components decouple algebraically.
-/
import Mathlib.Analysis.Normed.Field.Basic

namespace UnifiedTheory.LayerA

/-- Abstract source/dressing decomposition.
    Given a vector space V (representing field configurations)
    and a projection π onto a subspace K (source-capable channel),
    the complementary projection (1 - π) gives the dressing channel P. -/
structure SourceDressingDecomp (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- Projection onto the source-capable (K-type) channel -/
  πK : V →ₗ[ℝ] V
  /-- The source functional -/
  sourceFunc : V →ₗ[ℝ] ℝ
  /-- πK is idempotent -/
  πK_idem : πK ∘ₗ πK = πK
  /-- The source functional vanishes on the dressing (P-type) channel -/
  source_vanishes_on_P : ∀ v : V, πK v = 0 → sourceFunc v = 0

/-- The dressing projection is complementary to the source projection. -/
noncomputable def SourceDressingDecomp.πP {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : SourceDressingDecomp V) : V →ₗ[ℝ] V :=
  LinearMap.id - d.πK

/-- Every field decomposes as source + dressing. -/
theorem SourceDressingDecomp.decompose {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : SourceDressingDecomp V) (v : V) :
    v = d.πK v + d.πP v := by
  simp [SourceDressingDecomp.πP, LinearMap.sub_apply, LinearMap.id_apply, add_sub_cancel]

end UnifiedTheory.LayerA
