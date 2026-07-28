/-
  Audit/KFCausalMinkowski4DProfileTheorem.lean — THE COMPOSED PROFILE THEOREM

  The end-to-end analytic statement of the 4D operator theorem on the
  (u,v)-profile plane: for a profile `F` with two more derivative layers
  (`Fu, Fuv, Fuvu, Fuvv`), uniform bounds, and box supports,

    √a·( ∬_{(0,∞)²} a(v−u)²·f4D(au²v²)·F  −  (1/6)·F(0,0) )
        ⟶  (√π/24)·(F_uu(0,0) + F_vv(0,0)) − (√π/6)·F_uv(0,0)     (a → ∞).

  Chain (each arrow previously machine-checked):
    corner4_quadrant       — the subtraction equals `∬ 𝒦·F_uv` exactly;
    quadrant_gate_split    — `√a·∬𝒦F_uv` is the corner gate's three integrals;
    bdg_4d_gate_jet_value  — the gate limit collapses to the point jet.

  Combined with `gate_jet_dictionary`, `sphericalMean_quadratic`,
  `dictionary_4d`, and `bdg_4d_normalization` (all proven), the right-hand side
  is `□φ` with coefficient exactly 1 for the null-reduced S²-averaged field.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DGateSplit

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DQuadrant
open UnifiedTheory.Audit.KFCausalMinkowski4DGateSplit
open UnifiedTheory.Audit.KFCausalMinkowski4DDictionary

namespace UnifiedTheory.Audit.KFCausalMinkowski4DProfileTheorem

/-- **THE COMPOSED PROFILE THEOREM**: the complete 4D operator limit on the
profile plane, from the raw cone integrand to the point jet. -/
theorem bdg_4d_profile (A B CF CFu Mv Mu3 Mv3 Ccone : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (F Fu Fuv Fuvu Fuvv : ℝ → ℝ → ℝ) (Fuu Fvv : ℝ → ℝ)
    (hFC : Continuous (Function.uncurry F))
    (hFuc : Continuous (Function.uncurry Fu))
    (hFuvc : Continuous (Function.uncurry Fuv))
    (hFd : ∀ v u, HasDerivAt (fun u' => F u' v) (Fu u v) u)
    (hFud : ∀ u v, HasDerivAt (fun v' => Fu u v') (Fuv u v) v)
    (hFuvdu : ∀ v u, HasDerivAt (fun u' => Fuv u' v) (Fuvu u v) u)
    (hFuvdv : ∀ u v, HasDerivAt (fun v' => Fuv u v') (Fuvv u v) v)
    (hCF : ∀ u v, |F u v| ≤ CF) (hCFu : ∀ u v, |Fu u v| ≤ CFu)
    (hMv : ∀ u v, |Fuv u v| ≤ Mv)
    (hMu3 : ∀ u v, |Fuvu u v| ≤ Mu3) (hMv3 : ∀ u v, |Fuvv u v| ≤ Mv3)
    (hCcone : ∀ (a : ℝ), 0 < a → ∀ u v,
      |a*(v-u)^2 * f4D (a*u^2*v^2) * F u v| ≤ Ccone * a)
    (hsUF : ∀ u v, A ≤ u → F u v = 0) (hsVF : ∀ u v, B ≤ v → F u v = 0)
    (hsUFu : ∀ u v, A ≤ u → Fu u v = 0) (hsVFu : ∀ u v, B ≤ v → Fu u v = 0)
    (hsUFuv : ∀ u v, A ≤ u → Fuv u v = 0) (hsVFuv : ∀ u v, B ≤ v → Fuv u v = 0)
    (hFvvd : ∀ u, HasDerivAt Fvv (Fuvv u 0) u)
    (hFuud : ∀ v, HasDerivAt Fuu (Fuvu 0 v) v)
    (hpdvc : Continuous (fun u => Fuvv u 0))
    (hpduc : Continuous (fun v => Fuvu 0 v))
    (hFvvs : ∀ u, A ≤ u → Fvv u = 0) (hFuus : ∀ v, B ≤ v → Fuu v = 0) :
    Tendsto (fun a : ℝ => Real.sqrt a *
        ((∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
            a*(v-u)^2 * f4D (a*u^2*v^2) * F u v) - (1/6) * F 0 0))
      atTop (𝓝 (Real.sqrt π/24 * (Fuu 0 + Fvv 0) - Real.sqrt π/6 * Fuv 0 0)) := by
  apply Filter.Tendsto.congr' _
    (bdg_4d_gate_jet_value Fuv Fuvu Fuvv Fuu Fvv Mu3 Mv3 Mv A B hA hB
      hFuvc hFuvdu hFuvdv hMu3 hMv3 hMv hsUFuv hsVFuv
      hFvvd hFuud hpdvc hpduc hFvvs hFuus)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  have hquad := corner4_quadrant a A B CF CFu Mv (Ccone * a) ha hA hB F Fu Fuv
    hFC hFuc hFuvc hFd hFud hCF hCFu hMv (hCcone a ha)
    hsUF hsVF hsUFu hsVFu hsUFuv hsVFuv
  have hsplit := quadrant_gate_split a A B Mv ha hA hB Fuv
    hFuvc.measurable hMv hsUFuv hsVFuv
  rw [show (∫ v in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ),
      a*(v-u)^2 * f4D (a*u^2*v^2) * F u v) - (1/6) * F 0 0
      = ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
        ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
          - (1/2) * K4 (a*u^2*v^2)) * Fuv u v from by
    rw [hquad]; ring]
  rw [hsplit]

#print axioms bdg_4d_profile

end UnifiedTheory.Audit.KFCausalMinkowski4DProfileTheorem
