/- Uniform static loss for the actual radial Yosida test. Completing a
pointwise square absorbs the genuine symmetric-momentum Leibniz defect.
The derivative estimate is weighted by the cutoff itself, so its constant
is independent of the Yosida parameter. No operator core is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaKinetics
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOutputAccretivity

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStaticLowerBound
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalClockFloorRadialYosidaSymbol (radial symbol action radial_coordinates radial_nonnegative)
open KFCausalClockFloorRadialYosidaDerivative (derivativeSymbol)
open KFCausalClockFloorRadialYosidaKinetics (derivativeAction symmetricCorrection)
open KFCausalClockFloorRotatedAntiSymbol (position symmetricIndex)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalPairedModeCoordinates (scale scale_square)
open KFCausalClockFloorBoundedInverse (inverseL)

private theorem rational_weighted_bound (N C r v : ℝ) (hN : 0 < N) (hC : 0 < C)
    (hr : 0 ≤ r) (hv : v^2 ≤ 2*C*r) :
    ((2*scale)*N^2*v/(C*(N+r)^2))^2 ≤ (4/C)*(N*r/(N+r)) := by
  have hs : 0 < N+r := add_pos_of_pos_of_nonneg hN hr
  have hp : N^3 ≤ (N+r)^3 := pow_le_pow_left₀ hN.le (le_add_of_nonneg_right hr) 3
  have hratio : N^3/(N+r)^3 ≤ 1 := (div_le_one (pow_pos hs 3)).mpr hp
  calc
    _ = 2*N^4*v^2/(C^2*(N+r)^4) := by
      rw [div_pow,mul_pow,mul_pow,mul_pow,scale_square]
      ring
    _ ≤ 2*N^4*(2*C*r)/(C^2*(N+r)^4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (by positivity)) (by positivity)
    _ = ((4/C)*(N*r/(N+r)))*(N^3/(N+r)^3) := by
      field_simp [hC.ne',hs.ne']
      ring
    _ ≤ ((4/C)*(N*r/(N+r)))*1 := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

theorem derivative_square_le (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (x : Joint 2 4) :
    derivativeSymbol ε h N i x^2 ≤ (4/ε)*symbol ε h N x := by
  have hc := clock_positive ε (x (.inr 0)) hε.le
  have hv : position i x^2 ≤ 2*clock ε (x (.inr 0))*radial ε h x := by
    rw [radial_coordinates,mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hc.ne')]
    have hp := mul_nonneg (sq_nonneg (KFCausalNormalizedChargeFlow.momentumScale h))
      (add_nonneg (sq_nonneg (x (.inl 0))) (sq_nonneg (x (.inl 1))))
    fin_cases i <;> simp [position,symmetricIndex]
      <;> nlinarith [sq_nonneg (x (.inr 1)),sq_nonneg (x (.inr 2))]
  have hd := rational_weighted_bound N (clock ε (x (.inr 0))) (radial ε h x)
    (position i x) hN hc (radial_nonnegative ε hε h x) hv
  have he : ε ≤ clock ε (x (.inr 0)) := by
    unfold clock
    exact le_add_of_nonneg_left (Real.exp_pos _).le
  exact hd.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4) hε he)
    (KFCausalClockFloorRadialYosidaSymbol.symbol_nonnegative ε hε h N hN x))

private theorem quadratic_lower (a b c u v : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hb : b^2 ≤ 4*a*c) :
    |b| *u*v ≤ a*u^2+c*v^2 := by
  have hm := mul_le_mul_of_nonneg_right hb (mul_nonneg (sq_nonneg u) (sq_nonneg v))
  have he : (|b| *u*v)^2 ≤ 4*(a*u^2)*(c*v^2) := by
    calc
      _ = b^2*(u^2*v^2) := by rw [mul_pow,mul_pow,sq_abs]; ring
      _ ≤ (4*a*c)*(u^2*v^2) := hm
      _ = _ := by ring
  have hpos : 0 ≤ a*u^2+c*v^2 := by positivity
  have hleft : 0 ≤ |b| *u*v := by positivity
  nlinarith [sq_nonneg (a*u^2-c*v^2)]

private theorem scalar_lower (ε m h d : ℝ) (hε : 0 < ε) (hm : 0 ≤ m)
    (hd : d^2 ≤ (4/ε)*m) (u v : ℂ) :
    -(h^2/ε)*‖v‖^2 ≤
      (inner ℂ u ((m:ℂ) • u+(-Complex.I*(h:ℂ)*(d:ℂ)) • v)).re := by
  have hd' : (h*d)^2 ≤ 4*m*(h^2/ε) := by
    have he := mul_le_mul_of_nonneg_left hd (sq_nonneg h)
    convert he using 1 <;> ring
  have hq := quadratic_lower m (h*d) (h^2/ε) ‖u‖ ‖v‖ hm (by positivity)
    (norm_nonneg _) (norm_nonneg _) hd'
  have hp := re_inner_le_norm (𝕜 := ℂ) (-u) ((-Complex.I*(h:ℂ)*(d:ℂ)) • v)
  change (inner ℂ (-u) ((-Complex.I*(h:ℂ)*(d:ℂ)) • v)).re ≤ _ at hp
  simp only [inner_neg_left,Complex.neg_re,norm_neg,norm_smul,norm_mul,
    Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs] at hp
  rw [abs_mul] at hq
  have hs : (inner ℂ u ((m:ℂ) • u)).re=m*‖u‖^2 := by
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    change (Complex.ofReal m * Complex.ofReal ‖u‖ ^ 2).re = m*‖u‖^2
    rw [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  rw [inner_add_right,Complex.add_re,hs]
  nlinarith only [hq,hp]

theorem symmetric_pairing_lower (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (f z : Hilbert) :
    -(h^2/ε)*‖inverseL ε hε f‖^2 ≤
      (inner ℂ z (action ε hε h N hN z+symmetricCorrection ε hε h N hN i f)).re := by
  let u := chargeCoordinates z
  let v := chargeCoordinates (inverseL ε hε f)
  let w := chargeCoordinates (action ε hε h N hN z+symmetricCorrection ε hε h N hN i f)
  have hi : Integrable (fun x => ‖v x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hw : ∀ᵐ x ∂volume, w x=(symbol ε h N x:ℂ) • u x+
      (-Complex.I*(h:ℂ)*(derivativeSymbol ε h N i x:ℂ)) • v x := by
    have he : w=chargeCoordinates (action ε hε h N hN z)+
        (-Complex.I*(h:ℂ)) • chargeCoordinates
          (derivativeAction ε hε h N hN i (inverseL ε hε f)) := by
      simp only [w,symmetricCorrection,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply,map_add,map_smul]
    rw [he]
    filter_upwards [Lp.coeFn_add (chargeCoordinates (action ε hε h N hN z))
        ((-Complex.I*(h:ℂ)) • chargeCoordinates (derivativeAction ε hε h N hN i (inverseL ε hε f))),
      Lp.coeFn_smul (-Complex.I*(h:ℂ))
        (chargeCoordinates (derivativeAction ε hε h N hN i (inverseL ε hε f))),
      KFCausalClockFloorRadialYosidaSymbol.action_coe ε hε h N hN z,
      KFCausalClockFloorRadialYosidaKinetics.derivativeAction_coe ε hε h N hN i (inverseL ε hε f)]
      with x h1 h2 h3 h4
    simp only [Pi.add_apply] at h1
    rw [h1,h2,Pi.smul_apply,h3,h4]
    simp only [u,v,smul_eq_mul,mul_assoc]
  have hp := integral_mono_ae (hi.const_mul (-(h^2/ε)))
    (L2.integrable_inner (𝕜 := ℂ) u w).re (by
      filter_upwards [hw] with x hx
      rw [hx]
      exact scalar_lower ε (symbol ε h N x) h (derivativeSymbol ε h N i x) hε
        (KFCausalClockFloorRadialYosidaSymbol.symbol_nonnegative ε hε h N hN x)
        (derivative_square_le ε hε h N hN i x) (u x) (v x))
  rw [integral_const_mul,← KFCausalAveragedEnergyGraph.l2_norm_square,
    integral_re (L2.integrable_inner (𝕜 := ℂ) u w)] at hp
  simpa only [v,u,w,LinearIsometryEquiv.norm_map,← L2.inner_def,
    LinearIsometryEquiv.inner_map_map] using hp

#print axioms derivative_square_le
#print axioms symmetric_pairing_lower
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStaticLowerBound
