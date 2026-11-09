/- The other homogeneous form factor is multiplication by sqrt(c).
Explicit Gaussian tests supply its graph pairings on the same dense core. -/
import UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRegularizedClockFactor
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalRegularizedGaussianCore
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedFormDomain
open UnifiedTheory.Audit.KFCausalRegularizedAdjointTests
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalFourierUniqueness

theorem modulate_memLp (p : ℝ) (g : ℝ → ℂ) (hg : MemLp g 2) : MemLp (modulate p g) 2 := by
  apply MemLp.of_le hg
    (((continuous_subtype_val.comp Real.continuous_fourierChar).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  filter_upwards [] with q
  exact (modulate_norm p g q).le

theorem modulations_separate (g : ℝ → ℂ) (hg : MemLp g 2) (hn : ∀ q, g q ≠ 0)
    (f : ℝ → ℂ) (hf : MemLp f 2)
    (ho : ∀ p : ℝ, (∫ q, modulate p g q*f q)=0) : ∀ᵐ q, f q=0 := by
  let v : ℝ → ℂ := fun q => g q*f q
  have hv : Integrable v := hg.integrable_mul hf
  have hF : ∀ p : ℝ, (𝓕 v) p=0 := by
    intro p
    rw [Real.fourier_real_eq]
    convert ho (-p) using 1
    congr 1
    funext q
    simp only [v,modulate,Circle.smul_def,smul_eq_mul]
    rw [show -(q*p)=(-p)*q by ring]
    ring
  have hz := integrable_zero_of_fourier_zero v hv hF
  filter_upwards [hz] with q hq
  exact (mul_eq_zero.mp hq).resolve_left (hn q)

theorem gaussian_memLp : MemLp gaussian 2 := by
  apply (memLp_two_iff_integrable_sq_norm gaussian_continuous.aestronglyMeasurable).mpr
  simp only [gaussian_norm_square]
  simpa using quadratic_exp_integrable (2*Real.pi) 0 0 (by positivity)

def clockOutput (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℂ) (q : ℝ) : ℂ :=
  (Real.sqrt (clockQ ε hε q) : ℂ)*f q

theorem clockOutput_square (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℂ) (q : ℝ) :
    ‖clockOutput ε hε f q‖^2=clockQ ε hε q*‖f q‖^2 := by
  simp only [clockOutput,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (clockQ_positive ε hε q).le]

theorem clockOutput_memLp (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : functionCore ε hε hbar) : MemLp (clockOutput ε hε f) 2 := by
  have hm : Measurable (clockOutput ε hε f) :=
    ((Complex.continuous_ofReal.comp (clockQ_continuous ε hε).sqrt).measurable).mul f.property.1
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [clockOutput_square] using f.property.2.2.1

def coreToClock (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) : functionCore ε hε hbar →ₗ[ℂ] Hilbert where
  toFun f := (clockOutput_memLp ε hε hbar f).toLp (clockOutput ε hε f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(clockOutput_memLp ε hε hbar (f+g)).coeFn_toLp,
      Lp.coeFn_add ((clockOutput_memLp ε hε hbar f).toLp _) ((clockOutput_memLp ε hε hbar g).toLp _),
      (clockOutput_memLp ε hε hbar f).coeFn_toLp,
      (clockOutput_memLp ε hε hbar g).coeFn_toLp] with q hfg hadd hf hg
    rw [hfg,hadd]
    dsimp only [Pi.add_apply]
    rw [hf,hg]
    change clockOutput ε hε ((f : ℝ → ℂ)+(g : ℝ → ℂ)) q=_
    simp [clockOutput,mul_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(clockOutput_memLp ε hε hbar (a • f)).coeFn_toLp,
      Lp.coeFn_smul a ((clockOutput_memLp ε hε hbar f).toLp _),
      (clockOutput_memLp ε hε hbar f).coeFn_toLp] with q haf hsm hf
    simp only [RingHom.id_apply]
    rw [haf,hsm]
    dsimp only [Pi.smul_apply]
    rw [hf]
    change clockOutput ε hε (fun q => a*(f : ℝ → ℂ) q) q=a*clockOutput ε hε f q
    simp only [clockOutput]
    ring

def clockInputPairVector (p : ℝ) : Hilbert :=
  star ((modulate_memLp p gaussian gaussian_memLp).toLp (modulate p gaussian))
def clockOutputPairVector (ε : ℝ) (hε : 0 < ε) (p : ℝ) : Hilbert :=
  star ((modulate_memLp p (inputTest ε hε 0) (inputTest_memLp ε hε 0)).toLp
    (modulate p (inputTest ε hε 0)))

theorem clock_pair_vectors_separate (ε : ℝ) (hε : 0 < ε) (f : Hilbert)
    (hf : ∀ p, inner ℂ (clockOutputPairVector ε hε p) f=0) : f=0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hn : ∀ q, inputTest ε hε 0 q ≠ 0 := by
    intro q
    apply div_ne_zero (Complex.exp_ne_zero _)
    exact_mod_cast (Real.sqrt_pos.mpr (clockQ_positive ε hε q)).ne'
  apply modulations_separate (inputTest ε hε 0) (inputTest_memLp ε hε 0) hn f (Lp.memLp f)
  intro p
  simpa only [clockOutputPairVector,inner_star_toLp] using hf p

theorem hilbert_clock_pairing (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : functionCore ε hε hbar) (p : ℝ) :
    inner ℂ (clockOutputPairVector ε hε p) (coreToClock ε hε hbar f)=
      inner ℂ (clockInputPairVector p) (coreToHilbert ε hε hbar f) := by
  rw [clockOutputPairVector,clockInputPairVector,inner_star_toLp,inner_star_toLp]
  apply integral_congr_ae
  filter_upwards [(clockOutput_memLp ε hε hbar f).coeFn_toLp,
    (functionCore_memLp ε hε hbar f).coeFn_toLp] with q hc hf
  change modulate p (inputTest ε hε 0) q*((clockOutput_memLp ε hε hbar f).toLp _) q=
    modulate p gaussian q*((functionCore_memLp ε hε hbar f).toLp _) q
  rw [hc,hf]
  have hn : (Real.sqrt (clockQ ε hε q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (clockQ_positive ε hε q)).ne'
  simp only [modulate,inputTest,clockOutput,sub_zero]
  field_simp

#print axioms modulations_separate
#print axioms clockOutput_memLp
#print axioms clock_pair_vectors_separate
#print axioms hilbert_clock_pairing

end
end UnifiedTheory.Audit.KFCausalRegularizedClockFactor
