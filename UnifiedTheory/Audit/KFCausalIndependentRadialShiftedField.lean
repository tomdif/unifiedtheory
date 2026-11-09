/- The bare physical point field at the opposite half clock shift.
This coefficient acts on the true radial-moment input, before any vacuum
second action. Its bound uses the same independent-width real radius. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialHolomorphicQuotient
import UnifiedTheory.Audit.KFCausalOuterMatterRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialShiftedField
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint Block split)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalIndependentRadialNormalization (normalize)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalTwoShearClockQuotient (shift)
open KFCausalPairedModeCoordinates (scale)

def point (α wR : ℝ) (Y : Space) : ℂ :=
  2*(scale:ℂ)*(Y 3/(Real.sqrt (α*wR):ℂ))+Y 4/(Real.sqrt (α/32):ℂ)

def coefficient (ε h α wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) : ℂ :=
  point α wR (baselineVector ε α wL wR c (shift (-h/2) q) x)

def cap (α wR : ℝ) : ℝ :=
  (20/17:ℝ)*(2*|scale|/Real.sqrt (α*wR)+1/Real.sqrt (α/32))

theorem cap_nonnegative (α wR : ℝ) : 0 ≤ cap α wR := by
  unfold cap
  positivity

theorem shifted_baseline_norm_bound (ε h α wL wR c : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hR : 1 ≤ wR)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖baselineVector ε α wL wR c (shift (-h/2) q) x‖ ≤
      (20/17:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖ := by
  have hm := KFCausalTwoShearClockQuotient.strip_membership ε h hε hh q hq
  have hd := KFCausalComplexClockInverse.complexInverse_norm_bound ε hε
    (shift (-h/2) q) (q.re:ℂ) (KFCausalOuterMatterMultiplier.outer_shift_membership ε h hε hh q hq) hm.2.2
  have he : shift (-h/2) q-(q.re:ℂ)=((q.im+h/2:ℝ):ℂ)*Complex.I := by
    apply Complex.ext <;> simp [shift]
    all_goals ring
  rw [he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hd
  have hi : |q.im+h/2| ≤ 3*|h|/2 := by
    have hb := abs_add_le q.im (h/2)
    rw [abs_div,show |(2:ℝ)|=2 by norm_num] at hb
    linarith
  have hz : ‖complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ)‖ ≤ 1/5 := by
    apply hd.trans
    apply (div_le_iff₀ hε).mpr
    linarith
  let U : Space ≃ₗᵢ[ℂ] Space := LinearIsometryEquiv.refl ℂ Space
  have hb := KFCausalComplexShearPerturbation.baseline_norm U (coupling α wR)
    (KFCausalPhysicalReciprocalNormalization.coupling_bound α wR hα hR)
    (complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ)) hz
    (baselineVector ε α wL wR c (q.re:ℂ) x)
  change ‖flow (coupling α wR) (complexInverse ε (shift (-h/2) q)-complexInverse ε (q.re:ℂ))
    (flow (coupling α wR) (complexInverse ε (q.re:ℂ)) (normalize α wL wR c x))‖ ≤ _ at hb
  rw [KFCausalComplexShearGroup.flow_compose,sub_add_cancel] at hb
  exact hb

theorem coefficient_bound (ε h α wL wR c : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hR : 1 ≤ wR)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    ‖coefficient ε h α wL wR c q x‖ ≤ cap α wR*‖baselineVector ε α wL wR c (q.re:ℂ) x‖ := by
  have hw0 := zero_lt_one.trans_le hR
  have h3 := (PiLp.norm_apply_le (baselineVector ε α wL wR c (shift (-h/2) q) x) 3).trans
    (shifted_baseline_norm_bound ε h α wL wR c hε hh hα hR q hq x)
  have h4 := (PiLp.norm_apply_le (baselineVector ε α wL wR c (shift (-h/2) q) x) 4).trans
    (shifted_baseline_norm_bound ε h α wL wR c hε hh hα hR q hq x)
  have hs : 0 < Real.sqrt (α*wR) := Real.sqrt_pos.2 (mul_pos hα hw0)
  have hn : 0 < Real.sqrt (α/32) := Real.sqrt_pos.2 (by positivity)
  rw [coefficient,point]
  apply (norm_add_le _ _).trans
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hs,abs_of_pos hn]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ (2*|KFCausalPairedModeCoordinates.scale|)*
        (((20/17:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖)/Real.sqrt (α*wR))+
        ((20/17:ℝ)*‖baselineVector ε α wL wR c (q.re:ℂ) x‖)/Real.sqrt (α/32) :=
      add_le_add (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h3 hs.le) (by positivity))
        (div_le_div_of_nonneg_right h4 hn.le)
    _ = _ := by unfold cap; ring

theorem coefficient_analytic (ε h α wL wR c : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (q : ℂ) (hq : |q.im| ≤ |h|) (x : Joint 2 4) :
    AnalyticAt ℂ (fun z => coefficient ε h α wL wR c z x) q := by
  have hs : AnalyticAt ℂ (fun z => complexInverse ε (shift (-h/2) z)) q :=
    (KFCausalComplexClockInverse.complexInverse_analytic ε hε _
      (KFCausalOuterMatterMultiplier.outer_shift_membership ε h hε hb q hq)).comp
        (by unfold shift; fun_prop)
  dsimp [coefficient,point,baselineVector,flow]
  fun_prop

private theorem continuous_flow {T : Type*} [TopologicalSpace T] (σ : ℝ)
    (f : T → ℂ) (g : T → Space) (hf : Continuous f)
    (hg : ∀ i, Continuous (fun z => g z i)) :
    ∀ i, Continuous (fun z => flow σ (f z) (g z) i) := by
  intro i
  fin_cases i <;> dsimp [flow]
  · exact (hf.neg.div_const 2).cexp.mul (hg 0)
  · exact (hf.neg.div_const 2).cexp.mul (hg 1)
  · exact (hf.div_const 2).cexp.mul (hg 2)
  · exact (hf.div_const 2).cexp.mul (hg 3)
  · exact (hg 4).add ((continuous_const.mul ((hf.div_const 2).cexp.sub continuous_const)).mul (hg 3))

private theorem continuous_of_inverse {T : Type*} [TopologicalSpace T]
    (ε h α wL wR c : ℝ) (q : T → ℂ) (x : T → Joint 2 4) (hx : Continuous x)
    (hs : Continuous (fun t => complexInverse ε (shift (-h/2) (q t)))) :
    Continuous (fun t => coefficient ε h α wL wR c (q t) (x t)) := by
  have hn : ∀ i, Continuous (fun t => normalize α wL wR c (x t) i) := by
    intro i
    have he (j : Fin 2 ⊕ Fin 4) : Continuous (fun t => x t j) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ⊕ Fin 4 => ℝ) j).comp hx
    fin_cases i <;> dsimp [KFCausalIndependentRadialNormalization.normalize]
    all_goals exact Complex.continuous_ofReal.comp (continuous_const.mul (he _))
  have hy : ∀ i, Continuous (fun t => baselineVector ε α wL wR c (shift (-h/2) (q t)) (x t) i) :=
    continuous_flow (coupling α wR) _ _ hs hn
  exact (continuous_const.mul ((hy 3).div_const _)).add ((hy 4).div_const _)

theorem coefficient_horizontal_continuous (ε h α wL wR c : ℝ) (hε : 0 < ε)
    (hb : |h| ≤ ε/10) (y : ℝ) (hy : |y| ≤ |h|) :
    Continuous (fun v : ℝ × Joint 2 4 =>
      coefficient ε h α wL wR c ((v.1:ℂ)+(y:ℂ)*Complex.I) v.2) := by
  have hl : Continuous (fun t : ℝ => shift (-h/2) ((t:ℂ)+(y:ℂ)*Complex.I)) := by
    unfold shift
    fun_prop
  have hs : Continuous (fun t : ℝ => complexInverse ε (shift (-h/2) ((t:ℂ)+(y:ℂ)*Complex.I))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (KFCausalComplexClockInverse.complexInverse_analytic ε hε _
      (KFCausalOuterMatterMultiplier.outer_shift_membership ε h hε hb _ (by simpa using hy))).continuousAt.comp
        (f := fun t : ℝ => shift (-h/2) ((t:ℂ)+(y:ℂ)*Complex.I)) hl.continuousAt
  exact continuous_of_inverse ε h α wL wR c _ _ continuous_snd (hs.comp continuous_fst)

theorem point_real (ε α wL wR c : ℝ) (hε : 0 < ε) (hα : 0 < α)
    (hR : 0 < wR) (x : Block 2 × Block 4) :
    point α wR (baselineVector ε α wL wR c (x.2 0:ℂ) ((split 2 4).symm x)) =
      ((2*scale*(KFCausalClockFloorMixedChart.mixedMap ε hε x).2 2+
        (KFCausalClockFloorMixedChart.mixedMap ε hε x).2 3:ℝ):ℂ) := by
  have hs : (Real.sqrt (α*wR):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hα hR)).ne'
  have hn : (Real.sqrt (α/32):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold baselineVector
  rw [KFCausalComplexClockInverse.complexInverse_real ε hε]
  have he := KFCausalIndependentRadialNormalization.normalize_mixedMap ε hε α wL wR c hα hR x
  change _ = flow (coupling α wR)
    (((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm (x.2 0)):ℂ)
    (normalize α wL wR c ((split 2 4).symm x)) at he
  rw [← he]
  dsimp [point,KFCausalIndependentRadialNormalization.normalize]
  push_cast
  field_simp [hs,hn]
  rfl

theorem coefficient_half_line (ε h α wL wR c : ℝ) (q : ℂ) (x : Joint 2 4) :
    coefficient ε h α wL wR c (shift (h/2) q) x=
      point α wR (baselineVector ε α wL wR c q x) := by
  unfold coefficient
  congr 2
  unfold shift
  push_cast
  ring

#print axioms cap_nonnegative
#print axioms shifted_baseline_norm_bound
#print axioms coefficient_bound
#print axioms coefficient_analytic
#print axioms coefficient_horizontal_continuous
#print axioms point_real
#print axioms coefficient_half_line
end
end UnifiedTheory.Audit.KFCausalIndependentRadialShiftedField
