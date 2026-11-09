/- Smooth compactly supported spacetime tests, their partial derivatives
and Schwartz momentum slices. Mixed partials commute by second-derivative symmetry. -/
import UnifiedTheory.Audit.KFCausalSpacetimeSliceRegularity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests
noncomputable section
open Set Filter BoundedContinuousFunction SchwartzMap
open scoped Topology CompactlySupported ContDiff
open UnifiedTheory.Audit.KFCausalSpacetimeUniformTests (slice)

structure Test where
  value : ℝ × ℝ → ℂ
  smooth : ContDiff ℝ ∞ value
  compact : HasCompactSupport value

def Test.toBCF (φ : Test) : (ℝ × ℝ) →ᵇ ℂ :=
  (⟨⟨φ.value,φ.smooth.continuous⟩,φ.compact⟩ : C_c(ℝ × ℝ,ℂ)).toBoundedContinuousFunction

theorem Test.uniformContinuous (φ : Test) : UniformContinuous φ.toBCF :=
  φ.compact.uniformContinuous_of_continuous φ.smooth.continuous

def Test.directional (φ : Test) (v : ℝ × ℝ) : Test where
  value := fun z => fderiv ℝ φ.value z v
  smooth := (contDiff_infty_iff_fderiv.mp φ.smooth).2.clm_apply contDiff_const
  compact := φ.compact.fderiv_apply ℝ v

def Test.dt (φ : Test) : Test := φ.directional (1,0)
def Test.dp (φ : Test) : Test := φ.directional (0,1)

theorem Test.time_derivative (φ : Test) (t p : ℝ) :
    HasDerivAt (fun u => φ.value (u,p)) (φ.dt.value (t,p)) t := by
  exact ((φ.smooth.differentiable (by simp)) (t,p)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t p))

theorem Test.momentum_derivative (φ : Test) (t p : ℝ) :
    HasDerivAt (fun x => φ.value (t,x)) (φ.dp.value (t,p)) p := by
  exact ((φ.smooth.differentiable (by simp)) (t,p)).hasFDerivAt.comp_hasDerivAt p
    ((hasDerivAt_const p t).prodMk (hasDerivAt_id p))

theorem Test.directional_twice (φ : Test) (v w z : ℝ × ℝ) :
    ((φ.directional v).directional w).value z =
      fderiv ℝ (fderiv ℝ φ.value) z w v := by
  change fderiv ℝ (fun y => fderiv ℝ φ.value y v) z w = _
  rw [fderiv_clm_apply
    ((contDiff_infty_iff_fderiv.mp φ.smooth).2.differentiable (by simp) z)
    (differentiableAt_const v)]
  simp

theorem Test.mixed_partials (φ : Test) (z : ℝ × ℝ) :
    φ.dp.dt.value z = φ.dt.dp.value z := by
  change ((φ.directional (0,1)).directional (1,0)).value z =
    ((φ.directional (1,0)).directional (0,1)).value z
  rw [φ.directional_twice,φ.directional_twice]
  exact (φ.smooth.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).eq (1,0) (0,1)

theorem Test.slice_compact (φ : Test) (t : ℝ) :
    HasCompactSupport (fun p => φ.value (t,p)) := by
  have hi : Isometry (fun p : ℝ => (t,p)) :=
    Isometry.of_dist_eq (fun p q => by simp [Prod.dist_eq])
  exact φ.compact.comp_isClosedEmbedding hi.isClosedEmbedding

def Test.schwartz (φ : Test) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  (φ.slice_compact t).toSchwartzMap (φ.smooth.comp (contDiff_const.prodMk contDiff_id))

theorem Test.schwartz_apply (φ : Test) (t p : ℝ) : φ.schwartz t p = φ.value (t,p) := rfl

theorem Test.schwartz_deriv (φ : Test) (t p : ℝ) :
    derivCLM ℂ ℂ (φ.schwartz t) p = φ.dp.value (t,p) := by
  rw [derivCLM_apply]
  exact (φ.momentum_derivative t p).deriv

theorem Test.schwartz_toBCF (φ : Test) (t : ℝ) :
    (φ.schwartz t).toBoundedContinuousFunction = slice t φ.toBCF := by
  ext p
  rfl

theorem Test.schwartz_deriv_toBCF (φ : Test) (t : ℝ) :
    (derivCLM ℂ ℂ (φ.schwartz t)).toBoundedContinuousFunction = slice t φ.dp.toBCF := by
  ext p
  exact φ.schwartz_deriv t p

#print axioms Test.uniformContinuous
#print axioms Test.time_derivative
#print axioms Test.momentum_derivative
#print axioms Test.directional_twice
#print axioms Test.mixed_partials
#print axioms Test.slice_compact
#print axioms Test.schwartz_apply
#print axioms Test.schwartz_deriv
#print axioms Test.schwartz_toBCF
#print axioms Test.schwartz_deriv_toBCF
end
end UnifiedTheory.Audit.KFCausalSmoothSpacetimeTests
