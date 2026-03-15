/-
  LayerB/UnifiedBranch.lean — The unified branch theorem

  Given a ParentU, project to each Layer A input and assemble
  the full conditional Einstein branch. Every step is proven.

  This is the first genuine unified-theory theorem:
  a single parent structure implies Einstein + Λ.
-/
import UnifiedTheory.LayerB.ParentU
import UnifiedTheory.ConditionalEinstein

namespace UnifiedTheory.LayerB

open LayerA

/-! ### Bridge theorems: ParentU projections → Layer A hypotheses -/

/-- Bridge 1: ParentU.scale projects to the RG fixed-point hypothesis. -/
theorem bridge_rg (sb : ScaleBlock) : sb.α = 2 :=
  (renorm_fixedPoint_iff sb.c_pot sb.hc sb.α).mp sb.h_fixedPoint

/-- Bridge 2: ParentU.null projects to the null-cone proportionality. -/
theorem bridge_null (nb : NullBlock) :
    ∃ c₀ : ℝ, ∀ v w, genBilin nb.a_S nb.b_S nb.c_S v w = c₀ * minkBilin v w :=
  null_determines_up_to_trace_1plus1 nb.a_S nb.b_S nb.c_S nb.h_null

/-- Bridge 3: ParentU.bf projects to the K/P decomposition. -/
theorem bridge_bf {V : Type*} [AddCommGroup V] [Module ℝ V]
    (bb : BFBlock V) : ∀ v : V, v = bb.decomp.πK v + bb.decomp.πP v :=
  bb.decomp.decompose

/-- Bridge 4: ParentU.endpt projects to the Lovelock classification. -/
theorem bridge_einstein {T Ω : Type*}
    [AddCommGroup T] [Module ℝ T]
    [AddCommGroup Ω] [Module ℝ Ω]
    (eb : EndptBlock T Ω) :
    ∃ a b : ℝ, naturalOf eb.cd eb.c_L eb.d_L eb.e_L =
      a • einsteinOf eb.cd + b • eb.cd.g_metric :=
  lovelock_endpoint eb.cd eb.c_L eb.d_L eb.e_L eb.h_div eb.h_nondeg

/-! ### The unified branch theorem -/

/-- **Unified branch theorem.**

    From a single parent structure U, all four Layer A conclusions
    follow simultaneously:

    (a) The potential exponent is exactly α = 2.
    (b) The null-cone form is proportional to Minkowski.
    (c) Field configurations split into source + dressing.
    (d) The gravitational tensor is Einstein + Λ.

    FULLY PROVEN. No axioms beyond Lean core. -/
theorem unified_branch
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {T Ω : Type*} [AddCommGroup T] [Module ℝ T]
    [AddCommGroup Ω] [Module ℝ Ω]
    (U : ParentU V T Ω) :
    -- (a) Inverse-square law
    U.scale.α = 2
    -- (b) Null-cone determination
    ∧ (∃ c₀ : ℝ, ∀ v w,
        genBilin U.null.a_S U.null.b_S U.null.c_S v w = c₀ * minkBilin v w)
    -- (c) Source/dressing decomposition
    ∧ (∀ v : V, v = U.bf.decomp.πK v + U.bf.decomp.πP v)
    -- (d) Einstein + Λ
    ∧ (∃ a b : ℝ, naturalOf U.endpt.cd U.endpt.c_L U.endpt.d_L U.endpt.e_L =
        a • einsteinOf U.endpt.cd + b • U.endpt.cd.g_metric) :=
  ⟨bridge_rg U.scale,
   bridge_null U.null,
   bridge_bf U.bf,
   bridge_einstein U.endpt⟩

end UnifiedTheory.LayerB
