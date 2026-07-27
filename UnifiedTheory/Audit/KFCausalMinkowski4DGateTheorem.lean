/-
  Audit/KFCausalMinkowski4DGateTheorem.lean — THE COMPLETE 4D CORNER GATE

  The assembly of the three closed limits into the gate stated in
  KFCausalMinkowski4DGate.lean:

      √a ∬ 𝒦4_a·g  →  −(√π/24)[∫₀^∞∂_v g(u,0)du + ∫₀^∞∂_u g(0,v)dv] − (√π/6)·g(0,0),

  with `𝒦4_a = (u/v + v/u)·J4(au²v²) − ½·K4(au²v²)`:

   • the `(u/v)`-edge:  `J4_edge_outer`            → −(√π/24)·∫ ∂_v g(u,0) du
   • the `(v/u)`-edge:  `J4_edge_outer` transposed → −(√π/24)·∫ ∂_u g(0,v) dv
   • the K4-corner:     `K4_corner_value`          → (√π/3)·g(0,0), weighted −½ → −(√π/6)·g(0,0)

  Every arrow is machine-checked and axiom-clean; this file only adds linearity
  of limits and the transposition congruence.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DEdgeAssembly
import UnifiedTheory.Audit.KFCausalMinkowski4DLogMoment

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DEdgeAssembly
open UnifiedTheory.Audit.KFCausalMinkowski4DLogMoment

namespace UnifiedTheory.Audit.KFCausalMinkowski4DGateTheorem

/-- **THE COMPLETE 4D CORNER GATE.**  For a profile `g` continuously
differentiable in each argument with uniform bounds and compact support,

    ∫₀^∞ √a ∫₀^∞ (u/v)·J4(au²v²)·g dv du
      + ∫₀^∞ √a ∫₀^∞ (v/u)·J4(au²v²)·g du dv
      − ½·√a·∬ K4(au²v²)·g dv du
    ⟶  −(√π/24)·[∫₀^∞ ∂_v g(u,0) du + ∫₀^∞ ∂_u g(0,v) dv] − (√π/6)·g(0,0). -/
theorem bdg_4d_corner_gate (g pdug pdvg : ℝ → ℝ → ℝ) (Mu Mv Cg A B : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hdv : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hMv : ∀ u v, |pdvg u v| ≤ Mv)
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0) :
    Tendsto (fun a : ℝ =>
        (∫ u in Ioi (0:ℝ), Real.sqrt a * ∫ v in Ioi (0:ℝ),
            (u/v) * J4 (a*u^2*v^2) * g u v)
        + (∫ v in Ioi (0:ℝ), Real.sqrt a * ∫ u in Ioi (0:ℝ),
            (v/u) * J4 (a*u^2*v^2) * g u v)
        - (1/2) * (Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
            K4 (a*u^2*v^2) * g u v))
      atTop (𝓝 (-(Real.sqrt π)/24 *
          ((∫ u in Ioi (0:ℝ), pdvg u 0) + ∫ v in Ioi (0:ℝ), pdug 0 v)
        - (Real.sqrt π)/6 * g 0 0)) := by
  -- the (u/v)-edge
  have h1 := J4_edge_outer g pdvg hgc hdv Mv hMv A hA hsuppU
  -- the (v/u)-edge: `J4_edge_outer` on the transposed profile
  have h2raw := J4_edge_outer (fun u v => g v u) (fun u v => pdug v u)
    (hgc.comp continuous_swap) (fun u v => hdu u v) Mu (fun u v => hMu v u)
    B hB (fun u v hu => hsuppV v u hu)
  have h2 : Tendsto (fun a : ℝ => ∫ v in Ioi (0:ℝ), Real.sqrt a *
      ∫ u in Ioi (0:ℝ), (v/u) * J4 (a*u^2*v^2) * g u v)
      atTop (𝓝 (-(Real.sqrt π)/24 * ∫ v in Ioi (0:ℝ), pdug 0 v)) := by
    apply h2raw.congr
    intro a
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    rw [show a*x^2*y^2 = a*y^2*x^2 from by ring]
  -- the K4-corner, weighted by −½
  have h3 := K4_corner_value g pdug Mu Cg A B hA hB hgc hdu hMu hgb hsuppU hsuppV
  have hsum := (h1.add h2).sub (h3.const_mul (1/2))
  convert hsum using 2
  ring

/-! ## The algebraic capstone: gate × dictionary × normalization = □φ -/

/-- **The 4D operator capstone (algebraic layer).**  Feeding the corner-gate
value through the jet dictionary (`C = 2πT` with `T = φ_tt`, `3D = 2πS` with
`S = Δφ` from the spherical mean `M = φ + r²Δφ/6`) and applying the exact BDG
normalization `(4/√6)·√(24/π)·(3/(2π))·(π√π/12) = 1`:

    normalization × (√π/24)(3D − C) = S − T = □φ    (mostly-plus). -/
theorem bdg_4d_capstone (T S : ℝ) :
    (4 / Real.sqrt 6) * Real.sqrt (24/π) * (3/(2*π)) *
      ((Real.sqrt π/24) * (3*((2*π/3)*S) - 2*π*T)) = S - T := by
  calc (4 / Real.sqrt 6) * Real.sqrt (24/π) * (3/(2*π)) *
        ((Real.sqrt π/24) * (3*((2*π/3)*S) - 2*π*T))
      = (4 / Real.sqrt 6) * Real.sqrt (24/π) * (3/(2*π)) *
        ((π * Real.sqrt π/12) * (S - T)) := by
        rw [UnifiedTheory.Audit.KFCausalMinkowski4DGate.gate_spherical_value]
    _ = ((4 / Real.sqrt 6) * Real.sqrt (24/π) * (3/(2*π)) *
        (π * Real.sqrt π/12)) * (S - T) := by ring
    _ = 1 * (S - T) := by
        rw [UnifiedTheory.Audit.KFCausalMinkowski4DGate.bdg_4d_normalization]
    _ = S - T := one_mul _

#print axioms bdg_4d_corner_gate
#print axioms bdg_4d_capstone

end UnifiedTheory.Audit.KFCausalMinkowski4DGateTheorem
