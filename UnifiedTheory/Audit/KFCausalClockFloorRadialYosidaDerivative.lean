/- The actual rational radial multiplier has a bounded derivative in both
original symmetric momentum directions, including the neutral component
of the second direction. No state or operator domain is assumed here. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSymbol
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDerivative
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalSymmetricMomentumCoordinates (symmetricVector symmetricBlock rightVector)
open KFCausalClockFloorRadialYosidaSymbol (radial symbol radial_coordinates radial_nonnegative)
open KFCausalClockFloorRotatedAntiSymbol (position symmetricIndex)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalPairedModeCoordinates (scale scale_square)

def derivativeSymbol (ε h N : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ :=
  (2*scale)*N^2*position i x/(clock ε (x (.inr 0))*(N+radial ε h x)^2)

theorem radial_translate (ε h : ℝ) (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    radial ε h (x+t • symmetricVector i)=radial ε h x+
      (2*scale*position i x*t+t^2)/clock ε (x (.inr 0)) := by
  rw [radial_coordinates,radial_coordinates]
  fin_cases i <;>
    simp [symmetricVector,symmetricBlock,rightVector,position,symmetricIndex]
    <;> ring_nf <;> rw [scale_square] <;> ring

theorem radial_hasDerivAt (ε h : ℝ) (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    HasDerivAt (fun u : ℝ => radial ε h (x+u • symmetricVector i))
      ((2*scale)*position i (x+t • symmetricVector i)/clock ε (x (.inr 0))) t := by
  simp_rw [radial_translate]
  have hp := (hasDerivAt_const t (radial ε h x)).add
    ((((hasDerivAt_id t).const_mul (2*scale*position i x)).add
      ((hasDerivAt_id t).pow 2)).div_const (clock ε (x (.inr 0))))
  convert hp using 1
  fin_cases i <;>
    simp [symmetricVector,symmetricBlock,rightVector,position,symmetricIndex]
    <;> ring_nf <;> rw [scale_square] <;> ring

theorem symbol_hasDerivAt (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    HasDerivAt (fun u : ℝ => symbol ε h N (x+u • symmetricVector i))
      (derivativeSymbol ε h N i (x+t • symmetricVector i)) t := by
  have hr := radial_hasDerivAt ε h i x t
  have hden : N+radial ε h (x+t • symmetricVector i) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h _)).ne'
  have hc : clock ε ((x+t • symmetricVector i) (.inr 0))=clock ε (x (.inr 0)) := by
    fin_cases i <;> simp [symmetricVector,symmetricBlock,rightVector]
  have hd := (hr.const_mul N).div ((hasDerivAt_const t N).add hr) hden
  change HasDerivAt (fun u : ℝ => N*radial ε h (x+u • symmetricVector i)/
    (N+radial ε h (x+u • symmetricVector i))) _ t
  convert hd using 1
  dsimp only [Pi.add_apply]
  unfold derivativeSymbol
  rw [hc]
  field_simp [hden,(clock_positive ε (x (.inr 0)) hε.le).ne']
  ring

private theorem position_square_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (i : Fin 2) (x : Joint 2 4) :
    position i x^2 ≤ 2*clock ε (x (.inr 0))*radial ε h x := by
  have hc := (clock_positive ε (x (.inr 0)) hε.le).ne'
  rw [radial_coordinates]
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hc)]
  have hp := mul_nonneg (sq_nonneg (KFCausalNormalizedChargeFlow.momentumScale h))
    (add_nonneg (sq_nonneg (x (.inl 0))) (sq_nonneg (x (.inl 1))))
  fin_cases i <;> simp [position,symmetricIndex]
    <;> nlinarith [sq_nonneg (x (.inr 1)),sq_nonneg (x (.inr 2))]

private theorem rational_square_bound (N C r v : ℝ) (hN : 0 < N) (hC : 0 < C)
    (hr : 0 ≤ r) (hv : v^2 ≤ 2*C*r) :
    ((2*scale)*N^2*v/(C*(N+r)^2))^2 ≤ N/C := by
  have hsum : 0 < N+r := add_pos_of_pos_of_nonneg hN hr
  have hp : 4*N^3*r ≤ (N+r)^4 := by
    nlinarith [pow_nonneg hN.le 4,pow_nonneg hr 4,
      mul_nonneg (sq_nonneg N) (sq_nonneg r),mul_nonneg hN.le (pow_nonneg hr 3)]
  have hratio : 4*N^3*r/(N+r)^4 ≤ 1 := (div_le_one (pow_pos hsum 4)).mpr hp
  calc
    ((2*scale)*N^2*v/(C*(N+r)^2))^2 = 2*N^4*v^2/(C^2*(N+r)^4) := by
      rw [div_pow,mul_pow,mul_pow,mul_pow,scale_square]
      ring
    _ ≤ 2*N^4*(2*C*r)/(C^2*(N+r)^4) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hv (by positivity)) (by positivity)
    _ = (N/C)*(4*N^3*r/(N+r)^4) := by
      field_simp [hC.ne',hsum.ne']
      ring
    _ ≤ (N/C)*1 := mul_le_mul_of_nonneg_left hratio (div_nonneg hN.le hC.le)
    _ = N/C := mul_one _

theorem derivativeSymbol_bound (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (x : Joint 2 4) :
    |derivativeSymbol ε h N i x| ≤ Real.sqrt (N/ε) := by
  have hc := clock_positive ε (x (.inr 0)) hε.le
  have hs := rational_square_bound N (clock ε (x (.inr 0))) (radial ε h x)
    (position i x) hN hc (radial_nonnegative ε hε h x) (position_square_bound ε hε h i x)
  have hεc : ε ≤ clock ε (x (.inr 0)) := by
    unfold clock
    exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hdiv := div_le_div_of_nonneg_left hN.le hε hεc
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact hs.trans hdiv

theorem derivativeSymbol_continuous (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) : Continuous (derivativeSymbol ε h N i) := by
  have hr : Continuous (radial ε h) :=
    ((KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 0).add
      (KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 1)).div_const 2
  have hc : Continuous (fun x : Joint 2 4 => clock ε (x (.inr 0))) := by
    unfold clock
    fun_prop
  unfold derivativeSymbol position
  apply Continuous.div (by fun_prop) (hc.mul ((continuous_const.add hr).pow 2))
  intro x
  exact mul_ne_zero (clock_positive ε (x (.inr 0)) hε.le).ne'
    (pow_ne_zero 2 (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x)).ne')

#print axioms radial_translate
#print axioms radial_hasDerivAt
#print axioms symbol_hasDerivAt
#print axioms derivativeSymbol_bound
#print axioms derivativeSymbol_continuous
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaDerivative
