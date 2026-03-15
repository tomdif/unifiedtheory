/-
  LayerB/ParentU.lean — The parent unified object U

  U is the minimal structure whose projections generate all four
  Layer A inputs. Intentionally boring: just enough data to state
  projections, nothing more.

  Four blocks:
    1. ScaleBlock  → feeds RenormRigidity
    2. NullBlock   → feeds NullConeTensor
    3. BFBlock     → feeds BFSourceDressing
    4. EndptBlock  → feeds LovelockEinstein
-/
import UnifiedTheory.LayerA.RenormRigidity
import UnifiedTheory.LayerA.NullConeTensor
import UnifiedTheory.LayerA.BFSourceDressing
import UnifiedTheory.LayerA.LovelockEinstein

namespace UnifiedTheory.LayerB

open LayerA

/-! ### Block 1: Scale / renormalization data -/

/-- RG data: potential coefficient, exponent, and the fixed-point law. -/
structure ScaleBlock where
  c_pot : ℝ
  α : ℝ
  hc : c_pot ≠ 0
  h_fixedPoint : ∀ ℓ > 0, ∀ r > 0,
    renormOp ℓ (powerLawPotential c_pot α) r = powerLawPotential c_pot α r

/-! ### Block 2: Null-geometry data -/

/-- Null-cone data: symmetric form on ℝ^{1+1} vanishing on null vectors. -/
structure NullBlock where
  a_S : ℝ
  b_S : ℝ
  c_S : ℝ
  h_null : ∀ v : Fin 2 → ℝ, minkQuad v = 0 → genQuad a_S b_S c_S v = 0

/-! ### Block 3: BF source/dressing data -/

/-- BF data: field space with K/P decomposition. -/
structure BFBlock (V : Type*) [AddCommGroup V] [Module ℝ V] where
  decomp : SourceDressingDecomp V

/-! ### Block 4: Endpoint / Lovelock data -/

/-- Lovelock data: curvature data + divergence-free natural tensor. -/
structure EndptBlock (T : Type*) (Ω : Type*)
    [AddCommGroup T] [Module ℝ T]
    [AddCommGroup Ω] [Module ℝ Ω] where
  cd : CurvatureData T
  c_L : ℝ
  d_L : ℝ
  e_L : ℝ
  h_div : ∀ gradR : Ω, (c_L / 2 + d_L) • gradR = 0
  h_nondeg : ∃ ω : Ω, ω ≠ 0

/-! ### The parent object -/

/-- **ParentU**: the minimal unified parent structure.
    Packages the four data blocks needed to project onto
    all Layer A theorem inputs. -/
structure ParentU
    (V : Type*) [AddCommGroup V] [Module ℝ V]
    (T : Type*) (Ω : Type*)
    [AddCommGroup T] [Module ℝ T]
    [AddCommGroup Ω] [Module ℝ Ω] where
  scale : ScaleBlock
  null : NullBlock
  bf : BFBlock V
  endpt : EndptBlock T Ω

end UnifiedTheory.LayerB
