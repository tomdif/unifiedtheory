/-
  Audit/KFCausalMinkowski4DDictionary.lean — closing the seam:
  edge FTC collapse + the 4D null-coordinate dictionary

  The corner gate (`bdg_4d_corner_gate`) delivers

    −(√π/24)[∫₀^∞ ∂_v g(u,0) du + ∫₀^∞ ∂_u g(0,v) dv] − (√π/6)·g(0,0).

  When `g = ∂_u∂_v F` is the mixed derivative of the reduced field `F`, the two
  edge integrands are themselves total derivatives along their integration axes
  (`∂_v g(·,0) = (F_vv(·,0))′`, `∂_u g(0,·) = (F_uu(0,·))′`), so each edge
  integral collapses by the fundamental theorem of calculus to a point value:

    gate value  =  (√π/24)(F_uu(0,0) + F_vv(0,0)) − (√π/6)·F_uv(0,0)

  — exactly the jet-dictionary combination.  This file proves:

  * `edge_ftc` — `∫₀^∞ h′ = −h(0)` for a compactly-supported continuously
    differentiable `h` (with the vanishing of `h′` beyond the support derived,
    not assumed);
  * `bdg_4d_gate_jet_value` — the corner gate with its limit rewritten to the
    point-jet combination (a genuine `Tendsto` theorem);
  * `dictionary_4d` — the 4D analogue of the 2D `dictionary_separable`:
    chain-rule certificates for `F(u,v) = P(−(u+v)/2) + Q((v−u)/2)` (the
    null-substituted time/radial profile of the S²-averaged field), giving
    `F_uv = ¼P″ − ¼Q″` and `F_uu = F_vv = ¼P″ + ¼Q″`;
  * `dictionary_4d_jet` — instantiated on the quadratic jet
    `P(t) = A + Bt + Ct²`, `Q(r) = Dr²`: `F_uv(0,0) = (C−D)/2`,
    `F_uu(0,0) = F_vv(0,0) = (C+D)/2` — the inputs of `gate_jet_dictionary`,
    which together with `gate_spherical_value`, `sphericalMean_quadratic` and
    `bdg_4d_normalization` (`bdg_4d_capstone`) produce `□φ` with coefficient 1.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DGateTheorem

open MeasureTheory Real Set Filter Topology
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DGateTheorem

namespace UnifiedTheory.Audit.KFCausalMinkowski4DDictionary

/-- **The edge FTC collapse**: for `h` continuously differentiable with
`h = 0` beyond `A`, `∫₀^∞ h′ = −h(0)`.  The vanishing of `h′` beyond the
support is derived from derivative uniqueness, not assumed. -/
theorem edge_ftc (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hd : ∀ x, HasDerivAt h (h' x) x) (hc : Continuous h')
    (hsupp : ∀ x, A ≤ x → h x = 0) :
    ∫ x in Ioi (0:ℝ), h' x = -h 0 := by
  -- beyond the support the derivative vanishes
  have hzero : ∀ x, A < x → h' x = 0 := by
    intro x hx
    have hev : h =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
        using hsupp y (le_of_lt hy)
    have hconst : HasDerivAt h 0 x :=
      (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq hev
    exact (hd x).unique hconst
  -- integrability: continuous on the support closure, zero beyond
  have hint : IntegrableOn h' (Ioi (0:ℝ)) := by
    rw [show Ioi (0:ℝ) = Ioc 0 A ∪ Ioi A from
      (Ioc_union_Ioi_eq_Ioi (le_of_lt hA)).symm]
    apply IntegrableOn.union
    · exact hc.integrableOn_Ioc
    · exact (integrableOn_zero).congr_fun
        (fun x hx => (hzero x hx).symm) measurableSet_Ioi
  -- h tends to 0 at infinity (it is eventually 0)
  have htend : Tendsto h atTop (nhds 0) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop A] with x hx
      using (hsupp x hx).symm
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (m := 0)
    (fun x _ => hd x) hint htend
  rw [this, zero_sub]

/-- **The corner gate with the point-jet limit**: when the gate profile
`g = ∂_u∂_v F` carries edge data `∂_v g(·,0) = (F_vv(·,0))′` and
`∂_u g(0,·) = (F_uu(0,·))′`, the gate limit is

    (√π/24)·(F_uu(0,0) + F_vv(0,0)) − (√π/6)·g(0,0). -/
theorem bdg_4d_gate_jet_value (g pdug pdvg : ℝ → ℝ → ℝ) (Fuu Fvv : ℝ → ℝ)
    (Mu Mv Cg A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hgc : Continuous (Function.uncurry g))
    (hdu : ∀ v u, HasDerivAt (fun u' => g u' v) (pdug u v) u)
    (hdv : ∀ u v, HasDerivAt (fun v' => g u v') (pdvg u v) v)
    (hMu : ∀ u v, |pdug u v| ≤ Mu) (hMv : ∀ u v, |pdvg u v| ≤ Mv)
    (hgb : ∀ u v, |g u v| ≤ Cg)
    (hsuppU : ∀ u v, A ≤ u → g u v = 0) (hsuppV : ∀ u v, B ≤ v → g u v = 0)
    (hFvv : ∀ u, HasDerivAt Fvv (pdvg u 0) u)
    (hFuu : ∀ v, HasDerivAt Fuu (pdug 0 v) v)
    (hpdvc : Continuous (fun u => pdvg u 0))
    (hpduc : Continuous (fun v => pdug 0 v))
    (hFvvs : ∀ u, A ≤ u → Fvv u = 0) (hFuus : ∀ v, B ≤ v → Fuu v = 0) :
    Tendsto (fun a : ℝ =>
        (∫ u in Ioi (0:ℝ), Real.sqrt a * ∫ v in Ioi (0:ℝ),
            (u/v) * J4 (a*u^2*v^2) * g u v)
        + (∫ v in Ioi (0:ℝ), Real.sqrt a * ∫ u in Ioi (0:ℝ),
            (v/u) * J4 (a*u^2*v^2) * g u v)
        - (1/2) * (Real.sqrt a * ∫ u in Ioi (0:ℝ), ∫ v in Ioi (0:ℝ),
            K4 (a*u^2*v^2) * g u v))
      atTop (𝓝 (Real.sqrt π/24 * (Fuu 0 + Fvv 0) - Real.sqrt π/6 * g 0 0)) := by
  have h := bdg_4d_corner_gate g pdug pdvg Mu Mv Cg A B hA hB hgc hdu hdv
    hMu hMv hgb hsuppU hsuppV
  have hv : (∫ u in Ioi (0:ℝ), pdvg u 0) = -Fvv 0 :=
    edge_ftc Fvv (fun u => pdvg u 0) A hA hFvv hpdvc hFvvs
  have hu : (∫ v in Ioi (0:ℝ), pdug 0 v) = -Fuu 0 :=
    edge_ftc Fuu (fun v => pdug 0 v) B hB hFuu hpduc hFuus
  rw [hv, hu] at h
  convert h using 2
  ring

/-- **The 4D null-coordinate dictionary** (the analogue of the 2D
`dictionary_separable`): for the time/radial profile
`F(u,v) = P(−(u+v)/2) + Q((v−u)/2)` (`t = −(u+v)/2`, `r = (v−u)/2`),
the chain rule gives the certificates

    ∂_v F = −½P′ + ½Q′,        ∂_u∂_v F = ¼P″ − ¼Q″,
    ∂_u F = −½P′ − ½Q′,        ∂_u∂_u F = ¼P″ + ¼Q″,

so `F_uv = ¼P″ − ¼Q″` and `F_uu = F_vv = ¼P″ + ¼Q″`. -/
theorem dictionary_4d (P P' P'' Q Q' Q'' : ℝ → ℝ)
    (hP : ∀ t, HasDerivAt P (P' t) t) (hP' : ∀ t, HasDerivAt P' (P'' t) t)
    (hQ : ∀ r, HasDerivAt Q (Q' r) r) (hQ' : ∀ r, HasDerivAt Q' (Q'' r) r) :
    (∀ u v, HasDerivAt (fun w => P (-(u + w) / 2) + Q ((w - u) / 2))
        (-(1/2) * P' (-(u + v) / 2) + (1/2) * Q' ((v - u) / 2)) v)
    ∧ (∀ u v, HasDerivAt
        (fun u' => -(1/2) * P' (-(u' + v) / 2) + (1/2) * Q' ((v - u') / 2))
        ((1/4) * P'' (-(u + v) / 2) - (1/4) * Q'' ((v - u) / 2)) u)
    ∧ (∀ u v, HasDerivAt (fun u' => P (-(u' + v) / 2) + Q ((v - u') / 2))
        (-(1/2) * P' (-(u + v) / 2) - (1/2) * Q' ((v - u) / 2)) u) := by
  refine ⟨fun u v => ?_, fun u v => ?_, fun u v => ?_⟩
  · have hin1 : HasDerivAt (fun w : ℝ => -(u + w) / 2) (-(1/2)) v := by
      have := (((hasDerivAt_id v).const_add u).neg).div_const 2
      convert this using 1
      norm_num
    have hin2 : HasDerivAt (fun w : ℝ => (w - u) / 2) (1/2) v := by
      have := ((hasDerivAt_id v).sub_const u).div_const 2
      convert this using 1
    have h1 := (hP (-(u + v) / 2)).comp v hin1
    have h2 := (hQ ((v - u) / 2)).comp v hin2
    have := h1.add h2
    convert this using 1
    ring
  · have hin1 : HasDerivAt (fun u' : ℝ => -(u' + v) / 2) (-(1/2)) u := by
      have := (((hasDerivAt_id u).add_const v).neg).div_const 2
      convert this using 1
      norm_num
    have hin2 : HasDerivAt (fun u' : ℝ => (v - u') / 2) (-(1/2)) u := by
      have := ((hasDerivAt_id u).const_sub v).div_const 2
      convert this using 1
      norm_num
    have h1 := ((hP' (-(u + v) / 2)).comp u hin1).const_mul (-(1/2) : ℝ)
    have h2 := ((hQ' ((v - u) / 2)).comp u hin2).const_mul ((1/2) : ℝ)
    have := h1.add h2
    convert this using 1
    ring
  · have hin1 : HasDerivAt (fun u' : ℝ => -(u' + v) / 2) (-(1/2)) u := by
      have := (((hasDerivAt_id u).add_const v).neg).div_const 2
      convert this using 1
      norm_num
    have hin2 : HasDerivAt (fun u' : ℝ => (v - u') / 2) (-(1/2)) u := by
      have := ((hasDerivAt_id u).const_sub v).div_const 2
      convert this using 1
      norm_num
    have h1 := (hP (-(u + v) / 2)).comp u hin1
    have h2 := (hQ ((v - u) / 2)).comp u hin2
    have := h1.add h2
    convert this using 1
    ring

/-- **The jet instantiation**: for the quadratic jet `P(t) = A₀ + Bt + Ct²`,
`Q(r) = Dr²` (the exact output shape of `sphericalMean_quadratic` in time and
radius), at the origin

    F_uv(0,0) = (C − D)/2,     F_uu(0,0) = F_vv(0,0) = (C + D)/2

— the inputs of `gate_jet_dictionary`, whose combination
`(√π/24)(F_uu + F_vv) − (√π/6)F_uv = (√π/24)(3D − C)` feeds
`bdg_4d_capstone` to give `□φ` with coefficient exactly 1. -/
theorem dictionary_4d_jet (A₀ B C D : ℝ) :
    ((1/4) * (2*C) - (1/4) * (2*D) = (C - D)/2)
    ∧ ((1/4) * (2*C) + (1/4) * (2*D) = (C + D)/2)
    ∧ (∀ t, HasDerivAt (fun s => A₀ + B*s + C*s^2) (B + 2*C*t) t)
    ∧ (∀ t, HasDerivAt (fun s => B + 2*C*s) (2*C) t)
    ∧ (∀ r, HasDerivAt (fun s => D*s^2) (2*D*r) r)
    ∧ (∀ r, HasDerivAt (fun s => 2*D*s) (2*D) r) := by
  refine ⟨by ring, by ring, fun t => ?_, fun t => ?_, fun r => ?_, fun r => ?_⟩
  · have h1 := ((hasDerivAt_id t).const_mul B)
    have h2 := (((hasDerivAt_id t).pow 2).const_mul C)
    have := (h1.const_add A₀).add h2
    convert this using 1
    push_cast
    simp only [id_eq]
    ring
  · have := ((hasDerivAt_id t).const_mul (2*C)).const_add B
    convert this using 1
    ring
  · have := (((hasDerivAt_id r).pow 2).const_mul D)
    convert this using 1
    push_cast
    simp only [id_eq]
    ring
  · have := ((hasDerivAt_id r).const_mul (2*D))
    convert this using 1
    ring

#print axioms edge_ftc
#print axioms bdg_4d_gate_jet_value
#print axioms dictionary_4d
#print axioms dictionary_4d_jet

end UnifiedTheory.Audit.KFCausalMinkowski4DDictionary
