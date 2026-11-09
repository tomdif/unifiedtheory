/- Actual joint integrability of the exponentially weighted clock
Fourier transform for the six-dimensional candidate Gaussian. This
controls one longitudinal factor, not the eight-factor Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianFourier
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian
open UnifiedTheory.Audit.KFCausalClockFloorGaussianFourier
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy (toLp_square_integral)

def fourierLine (ε a α β y : ℝ) (w : ℝ × Grouped) : ℂ :=
  (𝓕 (clockSlice ε a α β y w.2)) w.1

theorem fourierLine_aestronglyMeasurable (ε a α β y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) : AEStronglyMeasurable (fourierLine ε a α β y) volume := by
  have hc : Continuous (fun u : (ℝ × Grouped) × ℝ =>
      (Real.fourierChar (-(u.2*u.1.1)):ℂ)*line ε a α β y (u.2,u.1.2)) := by
    have hl := (line_continuous ε a α β y hε hy).comp
      (show Continuous (fun u : (ℝ × Grouped) × ℝ => (u.2,u.1.2)) by fun_prop)
    fun_prop
  have hcm : AEStronglyMeasurable (fun u : (ℝ × Grouped) × ℝ =>
      (Real.fourierChar (-(u.2*u.1.1)):ℂ)*line ε a α β y (u.2,u.1.2))
      ((volume : Measure (ℝ × Grouped)).prod (volume : Measure ℝ)) := hc.aestronglyMeasurable
  have hm := hcm.integral_prod_right'
  convert hm using 1
  funext w
  simp only [fourierLine,clockSlice,Real.fourier_eq,Circle.smul_def,smul_eq_mul,
    RCLike.inner_apply,conj_trivial,mul_comm]

theorem clockSlice_plancherel (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3)
    (x : Grouped) :
    (∫ k : ℝ, ‖fourierLine ε a α β y (k,x)‖^2) =
      ∫ q : ℝ, ‖line ε a α β y (q,x)‖^2 := by
  have h1 := clockSlice_integrable ε a α β y hε ha hα hβ hw hy x
  have h2 := clockSlice_memLp ε a α β y hε ha hα hβ hw hy x
  change (∫ k : ℝ, ‖(𝓕 (clockSlice ε a α β y x)) k‖^2) = _
  rw [← toLp_square_integral _ (integralFourier_memLp _ h1 h2),← fourier_toLp_eq _ h1 h2,
    LinearIsometryEquiv.norm_map,toLp_square_integral]
  rfl

theorem fourierLine_memLp (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    MemLp (fourierLine ε a α β y) 2 volume := by
  have hm := fourierLine_aestronglyMeasurable ε a α β y hε hy
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  rw [Measure.volume_eq_prod ℝ Grouped]
  apply (integrable_prod_iff' (hm.norm.pow 2)).mpr
  constructor
  · apply ae_of_all
    intro x
    have h1 := clockSlice_integrable ε a α β y hε ha hα.le hβ.le hw hy x
    have h2 := clockSlice_memLp ε a α β y hε ha hα.le hβ.le hw hy x
    have hf := integralFourier_memLp _ h1 h2
    exact (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  · simp only [Pi.pow_apply,Real.norm_eq_abs,abs_sq]
    simp_rw [clockSlice_plancherel ε a α β y hε ha hα.le hβ.le hw hy]
    have hs := line_memLp ε a α β y hε ha hα hβ hw hy
    have hi := (memLp_two_iff_integrable_sq_norm hs.1).mp hs
    rw [Measure.volume_eq_prod ℝ Grouped] at hi
    simpa only [Real.norm_eq_abs,abs_sq] using hi.integral_norm_prod_right

theorem fourierLine_square_integral (ε a α β y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) :
    (∫ w : ℝ × Grouped, ‖fourierLine ε a α β y w‖^2) =
      ∫ z : ℝ × Grouped, ‖line ε a α β y z‖^2 := by
  have hf := fourierLine_memLp ε a α β y hε ha hα hβ hw hy
  have hl := line_memLp ε a α β y hε ha hα hβ hw hy
  have hfi := (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have hli := (memLp_two_iff_integrable_sq_norm hl.1).mp hl
  rw [Measure.volume_eq_prod ℝ Grouped] at hfi hli ⊢
  rw [integral_prod_symm _ hfi,integral_prod_symm _ hli]
  simp_rw [clockSlice_plancherel ε a α β y hε ha hα.le hβ.le hw hy]

def exponentialFourier (ε a α β hbar : ℝ) (w : ℝ × Grouped) : ℂ :=
  (Real.exp (Real.pi*hbar*w.1):ℂ)*fourierLine ε a α β 0 w

theorem exponentialFourier_eq (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    exponentialFourier ε a α β hbar = fourierLine ε a α β (-hbar/2) := by
  funext w
  exact exponential_fourier_identity ε a α β hbar hε ha hα hβ hw hh w.2 w.1

theorem exponentialFourier_memLp (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    MemLp (exponentialFourier ε a α β hbar) 2 volume := by
  rw [exponentialFourier_eq ε a α β hbar hε ha hα.le hβ.le hw hh]
  apply fourierLine_memLp ε a α β (-hbar/2) hε ha hα hβ hw
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem longitudinal_density_integrable (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    Integrable (fun w : ℝ × Grouped => Real.exp (2*Real.pi*hbar*w.1)*
      ‖fourierLine ε a α β 0 w‖^2) := by
  have hm := exponentialFourier_memLp ε a α β hbar hε ha hα hβ hw hh
  have hi := (memLp_two_iff_integrable_sq_norm hm.1).mp hm
  convert hi using 1
  funext w
  rw [exponentialFourier,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  congr 1
  congr 1
  norm_num only [Nat.cast_ofNat]
  ring

theorem exponential_energy_identity (ε a α β hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hh : |hbar| ≤ 2*Real.pi*ε/3) :
    (∫ w : ℝ × Grouped, ‖exponentialFourier ε a α β hbar w‖^2) =
      ∫ z : ℝ × Grouped, ‖line ε a α β (-hbar/2) z‖^2 := by
  rw [exponentialFourier_eq ε a α β hbar hε ha hα.le hβ.le hw hh]
  apply fourierLine_square_integral ε a α β (-hbar/2) hε ha hα hβ hw
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

#print axioms fourierLine_aestronglyMeasurable
#print axioms clockSlice_plancherel
#print axioms fourierLine_memLp
#print axioms fourierLine_square_integral
#print axioms exponentialFourier_eq
#print axioms exponentialFourier_memLp
#print axioms longitudinal_density_integrable
#print axioms exponential_energy_identity

end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianEnergy
