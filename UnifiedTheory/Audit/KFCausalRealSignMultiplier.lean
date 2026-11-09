/- A measurable real sign unitary and the exact equivalence between
signed and absolute weighted L2 domains. Zero has sign +1 here. -/
import UnifiedTheory.Audit.KFCausalUnitModulusMultiplier
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalRealSignMultiplier
noncomputable section
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def realSign (r : ℝ) : ℝ := if r < 0 then -1 else 1

theorem realSign_abs (r : ℝ) : realSign r*|r|=r := by
  unfold realSign
  split_ifs with hr
  · rw [abs_of_neg hr]; ring
  · rw [abs_of_nonneg (le_of_not_gt hr),one_mul]

theorem realSign_norm (r : ℝ) : ‖(realSign r:ℂ)‖=1 := by
  unfold realSign
  split_ifs <;> norm_num

theorem realSign_measurable (w : X → ℝ) (hm : Measurable w) :
    Measurable (fun x => (realSign (w x):ℂ)) := by
  apply Complex.continuous_ofReal.measurable.comp
  exact Measurable.ite (measurableSet_lt hm measurable_const) measurable_const measurable_const

def signUnitary (w : X → ℝ) (hm : Measurable w) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  KFCausalUnitModulusMultiplier.unitary (fun x => (realSign (w x):ℂ))
    (realSign_measurable w hm) (fun x => realSign_norm (w x))

theorem signUnitary_coe (w : X → ℝ) (hm : Measurable w) (f : Lp ℂ 2 μ) :
    signUnitary w hm f =ᵐ[μ] fun x => (realSign (w x):ℂ)*f x :=
  KFCausalUnitModulusMultiplier.unitary_coe _ _ _ f

theorem signUnitary_symmetric (w : X → ℝ) (hm : Measurable w) (f g : Lp ℂ 2 μ) :
    inner ℂ (signUnitary w hm f) g = inner ℂ f (signUnitary w hm g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [signUnitary_coe w hm f,signUnitary_coe w hm g] with x hf hg
  rw [hf,hg]
  change inner ℂ ((realSign (w x):ℂ) • f x) (g x) = inner ℂ (f x) ((realSign (w x):ℂ) • g x)
  rw [inner_smul_left,inner_smul_right,Complex.conj_ofReal]

theorem absolute_weight_memLp_iff (w : X → ℝ) (hm : Measurable w) (f : Lp ℂ 2 μ) :
    MemLp (fun x => ((|w x|:ℝ):ℂ)*f x) 2 μ ↔ MemLp (fun x => (w x:ℂ)*f x) 2 μ := by
  have hs : AEStronglyMeasurable (fun x => (w x:ℂ)*f x) μ :=
    (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
  have ha : AEStronglyMeasurable (fun x => ((|w x|:ℝ):ℂ)*f x) μ :=
    (Complex.continuous_ofReal.measurable.comp (continuous_abs.measurable.comp hm)).aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable
  have hn : ∀ᵐ x ∂μ, ‖((|w x|:ℝ):ℂ)*f x‖=‖(w x:ℂ)*f x‖ := by
    filter_upwards [] with x
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs]
  exact ⟨fun h => h.congr_norm hs hn,fun h => h.congr_norm ha (hn.mono fun _ hx => hx.symm)⟩

#print axioms realSign_abs
#print axioms realSign_norm
#print axioms realSign_measurable
#print axioms signUnitary_coe
#print axioms signUnitary_symmetric
#print axioms absolute_weight_memLp_iff

end
end UnifiedTheory.Audit.KFCausalRealSignMultiplier
