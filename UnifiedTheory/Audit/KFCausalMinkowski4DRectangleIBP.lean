/-
  Audit/KFCausalMinkowski4DRectangleIBP.lean — the finite-a rectangle double IBP

  The 4D analogue of the 2D `corner_rectangle_ibp`: on interior rectangles
  `[ε,A]×[δ,B]` (where the kernel identities hold), ordinary compact-interval
  integration by parts converts the raw cone integrand `a(v−u)²·f4D(au²v²)·F`
  into the gate kernel acting on derivatives of `F` — no differentiation under
  an improper integral anywhere.

  With `𝒦(u,v) = (v/u + u/v)·J4(z) − ½K4(z)` and its `∂_v`-primitive
  `D1(u,v) = u⁻¹G4(z) + u(v²)⁻¹H4(z) − au²v·K4′(z)`  (`z = au²v²`):

  * `corner4_ibp_u` (inner rung, fixed `v ≠ 0`):  since `∂_u D1 = a(v−u)²f4D`
    (`kernel4_mixed`) and `F(A) = 0`,

      ∫_ε^A a(v−u)²f4D·F du  =  −D1(ε,v)·F(ε) − ∫_ε^A D1·F′ du;

  * `corner4_ibp_v` (outer rung, fixed `u ≠ 0`):  since `∂_v 𝒦 = D1`
    (`kernel4_deriv_v`) and `G(B) = 0`,

      ∫_δ^B D1·G dv  =  −𝒦(u,δ)·G(δ) − ∫_δ^B 𝒦·G′ dv.

  Chained (with `G = F_u(u,·)`), these give the exact finite-`a` identity: cone
  integrand → gate kernel `𝒦·F_uv` plus two boundary lines.  As `δ → 0` the
  `v`-axis boundary `𝒦(u,δ) → −K4(0)/2 = −1/6` — the axis constant whose
  counterterm cancellation `(3/(2π))·(1/6)·(4π) = 1` is already machine-checked
  (`counterterm_cancellation`); as `ε → 0` the `u`-axis line dies
  (`G4(0) = 0`).  Those two limits plus the rectangle Fubini are the remaining
  assembly, downstream of these exact identities.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalMinkowski4DKernel

open MeasureTheory Real Set
open UnifiedTheory.Audit.KFCausalMinkowski4DKernel
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments

namespace UnifiedTheory.Audit.KFCausalMinkowski4DRectangleIBP

/-- **The inner (u) rectangle IBP** at fixed `v ≠ 0`: the cone integrand is the
`u`-derivative of `D1` against `F`, integrated by parts on `[ε,A]`; the upper
boundary dies on the support (`F A = 0`). -/
theorem corner4_ibp_u (a v ε A : ℝ) (hε : 0 < ε) (hεA : ε ≤ A) (hv : v ≠ 0)
    (F Fu : ℝ → ℝ) (hFd : ∀ x, HasDerivAt F (Fu x) x) (hFuc : Continuous Fu)
    (hFA : F A = 0) :
    ∫ u in ε..A, a*(v-u)^2 * f4D (a*u^2*v^2) * F u
      = -((ε⁻¹ * G4 (a*ε^2*v^2) + ε * (v^2)⁻¹ * H4 (a*ε^2*v^2)
            - a*ε^2*v * K4d (a*ε^2*v^2)) * F ε)
        - ∫ u in ε..A, (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
            - a*u^2*v * K4d (a*u^2*v^2)) * Fu u := by
  have hFC : Continuous F :=
    continuous_iff_continuousAt.mpr (fun x => (hFd x).continuousAt)
  have hmem : ∀ u ∈ uIcc ε A, u ≠ 0 := by
    intro u hu
    rw [uIcc_of_le hεA] at hu
    exact ne_of_gt (lt_of_lt_of_le hε hu.1)
  have hD1 : ∀ u ∈ uIcc ε A, HasDerivAt
      (fun u' => u'⁻¹ * G4 (a*u'^2*v^2) + u' * (v^2)⁻¹ * H4 (a*u'^2*v^2)
        - a*u'^2*v * K4d (a*u'^2*v^2))
      (a*(v-u)^2 * f4D (a*u^2*v^2)) u :=
    fun u hu => kernel4_mixed a u v (hmem u hu) hv
  have hconeC : Continuous (fun u => a*(v-u)^2 * f4D (a*u^2*v^2)) := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DMoments.f4D
    fun_prop
  have hGC : Continuous G4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.G4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hHC : Continuous H4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.H4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hKdC : Continuous K4d := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4d
    fun_prop
  have hD1C : ContinuousOn (fun u => u⁻¹ * G4 (a*u^2*v^2)
      + u * (v^2)⁻¹ * H4 (a*u^2*v^2) - a*u^2*v * K4d (a*u^2*v^2)) (uIcc ε A) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact (continuousOn_id.inv₀ hmem).mul
          (hGC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*v^2))).continuousOn
      · exact (continuousOn_id.mul continuousOn_const).mul
          (hHC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*v^2))).continuousOn
    · exact (((continuous_const.mul (continuous_pow 2)).mul
        continuous_const).continuousOn).mul
        (hKdC.comp (by fun_prop : Continuous (fun u : ℝ => a*u^2*v^2))).continuousOn
  have hX : IntervalIntegrable (fun u => a*(v-u)^2 * f4D (a*u^2*v^2) * F u)
      volume ε A := (hconeC.mul hFC).intervalIntegrable ε A
  have hY : IntervalIntegrable (fun u => (u⁻¹ * G4 (a*u^2*v^2)
      + u * (v^2)⁻¹ * H4 (a*u^2*v^2) - a*u^2*v * K4d (a*u^2*v^2)) * Fu u)
      volume ε A := (hD1C.mul hFuc.continuousOn).intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hD1 (fun x _ => hFd x)
    (hconeC.intervalIntegrable ε A) (hFuc.intervalIntegrable ε A)
  rw [hFA, mul_zero] at hibp
  rw [intervalIntegral.integral_add hX hY] at hibp
  linarith [hibp]

/-- **The outer (v) rectangle IBP** at fixed `u ≠ 0`: `D1` is the
`v`-derivative of the gate kernel `𝒦`, integrated by parts on `[δ,B]`; the
upper boundary dies on the support (`G B = 0`), the lower boundary carries the
axis value `𝒦(u,δ)` (→ `−1/6` as `δ → 0`). -/
theorem corner4_ibp_v (a u δ B : ℝ) (hδ : 0 < δ) (hδB : δ ≤ B) (hu : u ≠ 0)
    (G G' : ℝ → ℝ) (hGd : ∀ x, HasDerivAt G (G' x) x) (hG'c : Continuous G')
    (hGB : G B = 0) :
    ∫ v in δ..B, (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) * G v
      = -(((δ/u) * J4 (a*u^2*δ^2) + u * δ⁻¹ * J4 (a*u^2*δ^2)
            - (1/2) * K4 (a*u^2*δ^2)) * G δ)
        - ∫ v in δ..B, ((v/u) * J4 (a*u^2*v^2) + u * v⁻¹ * J4 (a*u^2*v^2)
            - (1/2) * K4 (a*u^2*v^2)) * G' v := by
  have hGC : Continuous G :=
    continuous_iff_continuousAt.mpr (fun x => (hGd x).continuousAt)
  have hmem : ∀ v ∈ uIcc δ B, v ≠ 0 := by
    intro v hv
    rw [uIcc_of_le hδB] at hv
    exact ne_of_gt (lt_of_lt_of_le hδ hv.1)
  have hK : ∀ v ∈ uIcc δ B, HasDerivAt
      (fun v' => (v'/u) * J4 (a*u^2*v'^2) + u * v'⁻¹ * J4 (a*u^2*v'^2)
        - (1/2) * K4 (a*u^2*v'^2))
      (u⁻¹ * G4 (a*u^2*v^2) + u * (v^2)⁻¹ * H4 (a*u^2*v^2)
        - a*u^2*v * K4d (a*u^2*v^2)) v :=
    fun v hv => kernel4_deriv_v a u v hu (hmem v hv)
  have hGC4 : Continuous G4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.G4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hHC : Continuous H4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.H4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
      UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4d
    fun_prop
  have hKdC : Continuous K4d := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4d
    fun_prop
  have hJC : Continuous J4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.J4
    fun_prop
  have hKC : Continuous K4 := by
    unfold UnifiedTheory.Audit.KFCausalMinkowski4DKernel.K4
    fun_prop
  have hD1C : ContinuousOn (fun v => u⁻¹ * G4 (a*u^2*v^2)
      + u * (v^2)⁻¹ * H4 (a*u^2*v^2) - a*u^2*v * K4d (a*u^2*v^2)) (uIcc δ B) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact continuousOn_const.mul
          (hGC4.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
      · exact (continuousOn_const.mul
          (((continuousOn_id.pow 2).inv₀ (fun v hv => pow_ne_zero 2 (hmem v hv))))).mul
          (hHC.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
    · exact ((continuousOn_const.mul continuousOn_id)).mul
        (hKdC.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
  have hKCon : ContinuousOn (fun v => (v/u) * J4 (a*u^2*v^2)
      + u * v⁻¹ * J4 (a*u^2*v^2) - (1/2) * K4 (a*u^2*v^2)) (uIcc δ B) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact (continuousOn_id.div_const u).mul
          (hJC.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
      · exact (continuousOn_const.mul (continuousOn_id.inv₀ hmem)).mul
          (hJC.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
    · exact continuousOn_const.mul
        (hKC.comp (by fun_prop : Continuous (fun v : ℝ => a*u^2*v^2))).continuousOn
  have hX : IntervalIntegrable (fun v => (u⁻¹ * G4 (a*u^2*v^2)
      + u * (v^2)⁻¹ * H4 (a*u^2*v^2) - a*u^2*v * K4d (a*u^2*v^2)) * G v)
      volume δ B := (hD1C.mul hGC.continuousOn).intervalIntegrable
  have hY : IntervalIntegrable (fun v => ((v/u) * J4 (a*u^2*v^2)
      + u * v⁻¹ * J4 (a*u^2*v^2) - (1/2) * K4 (a*u^2*v^2)) * G' v)
      volume δ B := (hKCon.mul hG'c.continuousOn).intervalIntegrable
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hK (fun x _ => hGd x)
    (hD1C.intervalIntegrable) (hG'c.intervalIntegrable δ B)
  rw [hGB, mul_zero] at hibp
  rw [intervalIntegral.integral_add hX hY] at hibp
  linarith [hibp]

#print axioms corner4_ibp_u
#print axioms corner4_ibp_v

end UnifiedTheory.Audit.KFCausalMinkowski4DRectangleIBP
