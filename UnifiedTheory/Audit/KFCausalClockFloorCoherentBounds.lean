/- Arbitrary complex linear sources can be absorbed into the positive
sheared Gaussian on the same clock strip. The bound is uniform in the
configuration variables and depends explicitly on the source norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFieldMoments (packet_half_norm)

def neutral (z : ℂ) (x : Grouped) : ℂ :=
  (x.2:ℂ)+2*(complexScale z-1)*(mix x.1:ℂ)

def position (z : ℂ) (x : Grouped) : Fin 5 → ℂ :=
  ![complexScale z*(x.1 0:ℂ),complexScale z*(x.1 1:ℂ),
    complexScale z*(x.1 2:ℂ),complexScale z*(x.1 3:ℂ),neutral z x]

theorem neutral_norm_square (z : ℂ) (x : Grouped) :
    ‖neutral z x‖^2 = (x.2+shift z x.1)^2+(2*(complexScale z).im*mix x.1)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  simp [neutral,shift,Complex.mul_re,Complex.mul_im]
  ring

theorem position_sum_square (z : ℂ) (x : Grouped) :
    ∑ i : Fin 5, ‖position z x i‖^2 =
      Real.exp z.re*squared x.1+(x.2+shift z x.1)^2+(2*(complexScale z).im*mix x.1)^2 := by
  simp [Fin.sum_univ_succ,position,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    sq_abs,complexScale_norm_square,neutral_norm_square,squared]
  ring

theorem position_sum_bound (z : ℂ) (x : Grouped) :
    ∑ i : Fin 5, ‖position z x i‖^2 ≤ 9*Real.exp z.re*squared x.1+(x.2+shift z x.1)^2 := by
  have h := mul_le_mul (complexScale_im_square_bound z) (mix_square_bound x.1)
    (sq_nonneg (mix x.1)) (Real.exp_pos z.re).le
  rw [position_sum_square]
  nlinarith

def positionConstant (α β : ℝ) : ℝ := 36/α+1/β

theorem positionConstant_positive (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < positionConstant α β := by unfold positionConstant; positivity

theorem position_quadratic_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ∑ i : Fin 5, ‖position z x i‖^2 ≤ positionConstant α β*(quadratic α β z x.1 x.2).re := by
  have hc := positionConstant_positive α β hα hβ
  have h1 : 9 ≤ positionConstant α β*(α/4) := by
    have he : positionConstant α β*(α/4) = 9+α/(4*β) := by
      unfold positionConstant
      field_simp
      ring
    rw [he]
    exact le_add_of_nonneg_right (by positivity)
  have h2 : 1 ≤ positionConstant α β*β := by
    have he : positionConstant α β*β = 36*β/α+1 := by
      unfold positionConstant
      field_simp
    rw [he]
    exact le_add_of_nonneg_left (by positivity)
  have hl := mul_le_mul_of_nonneg_left (quadratic_re_lower α β hα.le hβ.le hw z hz x.1 x.2) hc.le
  have ha := mul_le_mul_of_nonneg_right h1 (mul_nonneg (Real.exp_pos z.re).le (squared_nonnegative x.1))
  have hb := mul_le_mul_of_nonneg_right h2 (sq_nonneg (x.2+shift z x.1))
  have hp := position_sum_bound z x
  nlinarith

def source (b : Fin 5 → ℂ) (z : ℂ) (x : Grouped) : ℂ := ∑ i, b i*position z x i
def sourceSize (b : Fin 5 → ℂ) : ℝ := ∑ i, ‖b i‖^2
def sourceConstant (α β : ℝ) (b : Fin 5 → ℂ) : ℝ := sourceSize b*positionConstant α β

theorem sourceConstant_nonnegative (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (b : Fin 5 → ℂ) :
    0 ≤ sourceConstant α β b :=
  mul_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg ‖b i‖)) (positionConstant_positive α β hα hβ).le

theorem source_norm_square_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ‖source b z x‖^2 ≤ sourceConstant α β b*(quadratic α β z x.1 x.2).re := by
  have hn : ‖source b z x‖ ≤ ∑ i : Fin 5, ‖b i‖*‖position z x i‖ := by
    simpa only [source,norm_mul] using norm_sum_le (Finset.univ) (fun i => b i*position z x i)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 5 => ‖b i‖)
    (fun i => ‖position z x i‖)
  have hp := mul_le_mul_of_nonneg_left (position_quadratic_bound α β hα hβ hw z hz x)
    (show 0 ≤ ∑ i : Fin 5, ‖b i‖^2 from Finset.sum_nonneg (fun i _ => sq_nonneg ‖b i‖))
  exact (hs.trans hcs).trans (by simpa only [sourceConstant,sourceSize,mul_assoc] using hp)

theorem source_real_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    (source b z x).re ≤ ((quadratic α β z x.1 x.2).re+sourceConstant α β b)/2 := by
  have hs := source_norm_square_bound α β hα hβ hw b z hz x
  have hR := quadratic_re_nonnegative α β hα.le hβ.le hw z hz x.1 x.2
  have hK := sourceConstant_nonnegative α β hα hβ b
  have hn := norm_nonneg (source b z x)
  have hr := Complex.re_le_norm (source b z x)
  nlinarith [sq_nonneg ((quadratic α β z x.1 x.2).re-sourceConstant α β b)]

def coherentPacket (α β : ℝ) (b : Fin 5 → ℂ) (z : ℂ) (x : Grouped) : ℂ :=
  Complex.exp (source b z x)*packet α β z x

theorem coherentPacket_analytic (α β : ℝ) (b : Fin 5 → ℂ) (x : Grouped) (z : ℂ) :
    AnalyticAt ℂ (fun z => coherentPacket α β b z x) z := by
  have hs : AnalyticAt ℂ (fun z => source b z x) z := by
    unfold source
    apply Finset.analyticAt_fun_sum
    intro i _
    apply analyticAt_const.mul
    fin_cases i <;> dsimp [position,neutral,complexScale] <;> fun_prop
  exact hs.cexp.mul (packet_analytic α β x z)

theorem coherentPacket_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (b : Fin 5 → ℂ) (z : ℂ) (hz : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ‖coherentPacket α β b z x‖ ≤
      Real.exp (sourceConstant α β b/2)*‖packet (α/2) (β/2) z x‖ := by
  rw [coherentPacket,norm_mul,Complex.norm_exp,packet_half_norm,← Real.exp_add]
  rw [packet,Complex.norm_exp,Complex.neg_re,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := source_real_bound α β hα hβ hw b z hz x
  linarith

#print axioms neutral_norm_square
#print axioms position_sum_square
#print axioms position_sum_bound
#print axioms positionConstant_positive
#print axioms position_quadratic_bound
#print axioms sourceConstant_nonnegative
#print axioms source_norm_square_bound
#print axioms source_real_bound
#print axioms coherentPacket_analytic
#print axioms coherentPacket_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds
