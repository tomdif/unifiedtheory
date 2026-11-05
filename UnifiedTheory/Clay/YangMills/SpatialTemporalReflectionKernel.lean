/- Spatial reflection positivity of the actual temporal kinetic interaction
and raw Wilson slab. Spatial plaquette deletion is retained on both slices.
No continuum estimate or ground-state limit is used. -/
import UnifiedTheory.Clay.YangMills.SpatialTemporalLinkKernels
import UnifiedTheory.Clay.YangMills.WilsonTemporalGauge

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.SpatialTemporalReflectionKernel
noncomputable section
open WilsonTimeSlab SpatialHalfEdgeGeometry SpatialHalfEdgeSplit
open SpatialPlaquetteCutGeometry SpatialTemporalLinkKernels WilsonSingleLinkStaples
open PositiveKernelForm PositiveKernelInsertion

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem defect_reflection (e : Link (2 * n)) (u v : SpatialLinks (2 * n) Q) :
    defect n e (reflection n Q u,reflection n Q v) =
      defect n (reflectLink (2 * n) e) (u,v) := by
  unfold defect reflection
  by_cases he : e.2 = 0
  · simp only [if_pos he, inv_inv]
    rw [character_mul_comm]
    have hi := character_inverse_re ((u (reflectLink (2 * n) e))⁻¹ *
      v (reflectLink (2 * n) e))
    simp only [mul_inv_rev, inv_inv] at hi
    rw [hi]
  · simp only [if_neg he]

theorem kineticAction_reflection (u v : SpatialLinks (2 * n) Q) :
    kineticAction character 2 (reflection n Q u) (reflection n Q v) =
      kineticAction character 2 u v := by
  change (∑ e : Link (2 * n), defect n e (reflection n Q u,reflection n Q v)) =
    ∑ e : Link (2 * n), defect n e (u,v)
  simp_rw [defect_reflection]
  exact Equiv.sum_comp ((reflectLink_involutive (2 * n)).toPerm)
    (fun e => defect n e (u,v))

theorem pairAssemble_swap (a b : PairHalf n) :
    pairAssemble n b a =
      (reflection n Q (pairAssemble n a b).1,reflection n Q (pairAssemble n a b).2) := by
  unfold pairAssemble
  rw [assemble_reflection n Q (a.1,b.1), assemble_reflection n Q (a.2,b.2)]

theorem kineticAction_swap (a b : PairHalf n) :
    kineticAction character 2 (pairAssemble n b a).1 (pairAssemble n b a).2 =
      kineticAction character 2 (pairAssemble n a b).1 (pairAssemble n a b).2 := by
  rw [pairAssemble_swap, kineticAction_reflection]

def kineticKernel (s : ℝ) (hs : 0 ≤ s) : PositiveKernel (PairHalf n) :=
  finiteProduct (fun e : Link (2 * n) => linkKernel n e s hs)

theorem kineticKernel_value (s : ℝ) (hs : 0 ≤ s) (a b : PairHalf n) :
    (kineticKernel n s hs).value (a,b) =
      (kineticWeight character s 2 (pairAssemble n a b).1 (pairAssemble n a b).2 : ℂ) := by
  rw [kineticKernel, finiteProduct_value]
  simp_rw [linkKernel_value]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  have he : (∑ e : Link (2 * n), -(s / 2) *
      (defect n e (pairAssemble n a b) + defect n e (pairAssemble n b a))) =
      -(s / 2) * (kineticAction character 2 (pairAssemble n a b).1 (pairAssemble n a b).2 +
        kineticAction character 2 (pairAssemble n b a).1 (pairAssemble n b a).2) := by
    unfold kineticAction defect
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he, kineticAction_swap n a b]
  ring

theorem kineticKernel_continuous (s : ℝ) (hs : 0 ≤ s) :
    Continuous (kineticKernel n s hs).value := by
  have hw : Continuous (fun uv : SpatialLinks (2 * n) Q × SpatialLinks (2 * n) Q =>
      kineticWeight character s 2 uv.1 uv.2) := by
    unfold kineticWeight kineticAction
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    exact continuous_finset_sum Finset.univ (fun e _ => defect_continuous n e)
  have hc := Complex.continuous_ofReal.comp (hw.comp (pairAssemble_continuous n))
  exact hc.congr (fun z => (kineticKernel_value n s hs z.1 z.2).symm)

def slabKernel (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p) (s : ℝ) (hs : 0 ≤ s) :
    PositiveKernel (PairHalf n) :=
  product (product (pullback (SpatialWilsonReflectionKernel.positiveKernel n γ hγ) Prod.fst)
    (kineticKernel n s hs))
    (pullback (SpatialWilsonReflectionKernel.positiveKernel n γ hγ) Prod.snd)

theorem slabKernel_value (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p)
    (hr : ∀ p, γ (reflectPlaquette n p) = γ p) (s : ℝ) (hs : 0 ≤ s) (a b : PairHalf n) :
    (slabKernel n γ hγ s hs).value (a,b) =
      (SpatialWilsonReflectionKernel.weight n γ (pairAssemble n a b).1 *
        kineticWeight character s 2 (pairAssemble n a b).1 (pairAssemble n a b).2 *
        SpatialWilsonReflectionKernel.weight n γ (pairAssemble n a b).2 : ℝ) := by
  simp only [slabKernel, product_value, pullback,
    SpatialWilsonReflectionKernel.positiveKernel_value n γ hγ hr,
    kineticKernel_value, ← Complex.ofReal_mul]
  rfl

/-- The actual raw slab is the spatial reflection kernel on paired halves.
This includes both spatial potentials and every kinetic link. -/
theorem rawKernel_value (β : ℝ) (hβ : 0 ≤ β) (a b : PairHalf n) :
    (slabKernel n (fun _ => β / 2) (fun _ => by positivity) β hβ).value (a,b) =
      (WilsonTemporalGauge.rawKernel character β 2
        (pairAssemble n a b).1 (pairAssemble n a b).2 : ℂ) := by
  rw [slabKernel_value n _ _ (fun _ => rfl)]
  unfold WilsonTemporalGauge.rawKernel
  rw [SpatialWilsonReflectionKernel.constant_weight,
    SpatialWilsonReflectionKernel.constant_weight]
  rw [show 2 * (β / 2) = β by ring]

end
end UnifiedTheory.Clay.YangMills.SpatialTemporalReflectionKernel
