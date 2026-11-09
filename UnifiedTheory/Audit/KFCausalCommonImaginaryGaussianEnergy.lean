/- The actual common-purely-imaginary-source quartic energy reflects to a
positive cosh moment sum. No charged interference is discarded. This gives
finite imaginary increments and the actual field derivative for all
nonnegative couplings, before any clock-response conclusion. -/
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianJointDensity
import UnifiedTheory.Audit.KFCausalChargedCoshGaussianMomentSeries

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianEnergy
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment)
open KFCausalCommonRealGaussianWeightedEnergy
  (potential neutralLine coefficient0 coefficient1 coefficient2 coefficients_nonnegative)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedEvenMomentImaginaryBound (gamma)
open KFCausalChargedCoshGaussianMomentSeries (weightedEnergy)
variable (mass2 quartic vacuum : ℝ)

theorem neutralLine_reflect (β L v : ℝ) :
    neutralLine mass2 quartic vacuum β 0 L (-v)=neutralLine mass2 quartic vacuum β 0 L v := by
  unfold neutralLine
  rw [← integral_neg_eq_self (fun x : ℝ => potential mass2 quartic vacuum (x+L*(-v))*neutralWeight β 0 x) volume]
  apply integral_congr_ae
  filter_upwards [] with x
  have hp : potential mass2 quartic vacuum (-x+L*(-v))=potential mass2 quartic vacuum (x+L*v) := by
    unfold potential
    ring
  rw [hp]
  simp [neutralWeight]

theorem neutralLine_zero (β L v : ℝ) (hβ : 0 < β) :
    neutralLine mass2 quartic vacuum β 0 L v=coefficient0 mass2 quartic vacuum β 0+
      coefficient1 mass2 quartic β 0 L*v^2+coefficient2 quartic β 0 L*v^4 := by
  have he := KFCausalCommonRealGaussianWeightedEnergy.neutralLine_even mass2 quartic vacuum β 0 L v hβ
  rw [neutralLine_reflect] at he
  linarith

variable {ι : Type*} [Fintype ι]
def density (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℝ :=
  neutralLine mass2 quartic vacuum β 0 L x.1.2*Real.exp (d*x.1.2^2-q*x.1.2)*‖packet 0 p w c x‖^2
def energy (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, density mass2 quartic vacuum β L p d q w c x ∂chargedMeasure

private theorem density_expansion (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (x : Charged) :
    density mass2 quartic vacuum β L p d q w c x=
      coefficient0 mass2 quartic vacuum β 0*(Real.exp (d*x.1.2^2-q*x.1.2)*‖packet 0 p w c x‖^2)+
      coefficient1 mass2 quartic β 0 L*(Real.exp (d*x.1.2^2-q*x.1.2)*‖packet 1 p w c x‖^2)+
      coefficient2 quartic β 0 L*(Real.exp (d*x.1.2^2-q*x.1.2)*‖packet 2 p w c x‖^2) := by
  have h1 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 1 p w c x
  have h2 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 2 p w c x
  simp only [zero_add,pow_one] at h1
  simp only [zero_add] at h2
  rw [h1,h2,density,neutralLine_zero mass2 quartic vacuum β L x.1.2 hβ]
  ring

theorem density_integrable (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (density mass2 quartic vacuum β L p d q w c) chargedMeasure := by
  have hi (m : ℕ) : Integrable (fun x : Charged => Real.exp (d*x.1.2^2-q*x.1.2)*‖packet m p w c x‖^2) chargedMeasure := by
    simpa only [neg_mul,sub_eq_add_neg] using
      KFCausalChargedCoshGaussianMomentSeries.exponential_square_integrable m p d (-q) w c hp hw hd
  apply (((hi 0).const_mul (coefficient0 mass2 quartic vacuum β 0)).add
    ((hi 1).const_mul (coefficient1 mass2 quartic β 0 L))).add
    ((hi 2).const_mul (coefficient2 quartic β 0 L)) |>.congr
  exact Eventually.of_forall (fun x => (density_expansion mass2 quartic vacuum β L p d q w c hβ x).symm)

private def reflect (x : Charged) : Charged := ((x.1.1,-x.1.2),x.2)
private theorem reflect_preserving : MeasurePreserving reflect chargedMeasure chargedMeasure := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))).prod
      (MeasurePreserving.id (volume.restrict (Set.Ioi (0:ℝ))))
private def reflectEquiv : Charged ≃ᵐ Charged :=
  { toEquiv := ⟨reflect,reflect,by intro x; simp [reflect],by intro x; simp [reflect]⟩
    measurable_toFun := reflect_preserving.measurable
    measurable_invFun := reflect_preserving.measurable }
private theorem packet_reflect (p : ℂ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) :
    packet 0 p w c (reflect x)=packet 0 p w c x := by
  simp [KFCausalChargedEvenMomentFamily.packet_expansion,reflect]
private def evenDensity (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℝ :=
  coefficient0 mass2 quartic vacuum β 0*(Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet 0 p w c x‖^2)+
  coefficient1 mass2 quartic β 0 L*(Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet 1 p w c x‖^2)+
  coefficient2 quartic β 0 L*(Real.exp (d*x.1.2^2)*Real.cosh (q*x.1.2)*‖packet 2 p w c x‖^2)
private theorem density_even (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (x : Charged) :
    density mass2 quartic vacuum β L p d q w c x+
      density mass2 quartic vacuum β L p d q w c (reflect x)=2*evenDensity mass2 quartic vacuum β L p d q w c x := by
  have h1 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 1 p w c x
  have h2 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 2 p w c x
  simp only [zero_add,pow_one] at h1
  simp only [zero_add] at h2
  unfold density evenDensity
  rw [packet_reflect,h1,h2]
  dsimp only [reflect]
  rw [neutralLine_reflect,neutralLine_zero mass2 quartic vacuum β L x.1.2 hβ]
  simp only [neg_sq,Real.cosh_eq,sub_eq_add_neg,Real.exp_add,mul_neg,neg_neg]
  ring

theorem energy_decomposition (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    energy mass2 quartic vacuum β L p d q w c=
      coefficient0 mass2 quartic vacuum β 0*weightedEnergy 0 p d q w c+
      coefficient1 mass2 quartic β 0 L*weightedEnergy 1 p d q w c+
      coefficient2 quartic β 0 L*weightedEnergy 2 p d q w c := by
  have hi := density_integrable mass2 quartic vacuum β L p d q w c hβ hp hw hd
  have hf : Integrable (fun x => density mass2 quartic vacuum β L p d q w c (reflect x)) chargedMeasure :=
    reflect_preserving.integrable_comp_of_integrable hi
  have hv := reflect_preserving.integral_comp reflectEquiv.measurableEmbedding
    (density mass2 quartic vacuum β L p d q w c)
  have he := integral_congr_ae (μ := chargedMeasure)
    (Eventually.of_forall (fun x => density_even mass2 quartic vacuum β L p d q w c hβ x))
  rw [integral_add hi hf,integral_const_mul,hv] at he
  have h0 := (KFCausalChargedCoshGaussianMomentSeries.cosh_square_integrable 0 p d q w c hp hw hd).const_mul (coefficient0 mass2 quartic vacuum β 0)
  have h1 := (KFCausalChargedCoshGaussianMomentSeries.cosh_square_integrable 1 p d q w c hp hw hd).const_mul (coefficient1 mass2 quartic β 0 L)
  have h2 := (KFCausalChargedCoshGaussianMomentSeries.cosh_square_integrable 2 p d q w c hp hw hd).const_mul (coefficient2 quartic β 0 L)
  unfold evenDensity at he
  have he0 := integral_add h0 h1
  have he1 := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at he0 he1
  rw [he1,he0] at he
  simp only [integral_const_mul] at he
  unfold energy weightedEnergy
  linarith

theorem energy_nonnegative (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ energy mass2 quartic vacuum β L p d q w c := by
  apply integral_nonneg
  intro x
  have hn : 0 ≤ neutralLine mass2 quartic vacuum β 0 L x.1.2 := integral_nonneg (fun t =>
    mul_nonneg (KFCausalCommonRealGaussianWeightedEnergy.potential_nonnegative mass2 quartic vacuum _ hm hq hv) (Real.exp_pos _).le)
  unfold density
  positivity

theorem actual_scaled_le (α a β D L b₁ b₂ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < a)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b₂^2 < α*(a^2-b₂^2)*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    b₁^2*energy mass2 quartic vacuum β L (gamma α ((a:ℂ)+Complex.I*(b₁:ℂ))) (8*β*b₁^2) (4*D*b₁) w c ≤
    b₂^2*energy mass2 quartic vacuum β L (gamma α ((a:ℂ)+Complex.I*(b₂:ℂ))) (8*β*b₂^2) (4*D*b₂) w c := by
  have hb₂0 := lt_of_lt_of_le hb₁ hb
  have hb₁a := lt_of_le_of_lt hb hb₂
  have hs : b₁^2 ≤ b₂^2 := by nlinarith
  have hd₁ : ∀ i, 8*β*b₁^2 < α*(a^2-b₁^2)*w i := by
    intro i
    have hwi := hw i
    have hpos : 0 ≤ (8*β+α*w i)*(b₂^2-b₁^2) := mul_nonneg (by positivity) (sub_nonneg.mpr hs)
    nlinarith [hd i]
  have hp (b : ℝ) (hb0 : 0 < b) (hba : b < a) : 0 < (gamma α ((a:ℂ)+Complex.I*(b:ℂ))).re := by
    apply KFCausalChargedCoolingFixedV.actual_gamma_re_positive α _ hα
    simpa [abs_of_pos hb0] using hba
  have hre (b : ℝ) : 2*(gamma α ((a:ℂ)+Complex.I*(b:ℂ))).re=α*(a^2-b^2) := by
    simp [gamma,pow_two,Complex.mul_re,Complex.mul_im]
    ring
  rw [energy_decomposition mass2 quartic vacuum β L _ _ _ w c hβ (hp b₁ hb₁ hb₁a) hw
    (by intro i; rw [hre]; exact hd₁ i),
    energy_decomposition mass2 quartic vacuum β L _ _ _ w c hβ (hp b₂ hb₂0 hb₂) hw
    (by intro i; rw [hre]; exact hd i)]
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative mass2 quartic vacuum β 0 L hm hq hv
  have he (m : ℕ) (hm : m ≤ 2) :=
    KFCausalChargedCoshGaussianMomentSeries.actual_scaled_le α a β D b₁ b₂ hα hβ.le hb₁ hb hb₂ m hm w hw c hd
  nlinarith [mul_le_mul_of_nonneg_left (he 0 (by omega)) h0,
    mul_le_mul_of_nonneg_left (he 1 (by omega)) h1,
    mul_le_mul_of_nonneg_left (he 2 (by omega)) h2]

theorem field_derivative (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    :
    HasDerivAt (fun t => energy mass2 quartic vacuum β t p d q w c)
      (2*L*(mass2*neutralMoment β 0 0/2+3*quartic*neutralMoment β 0 2/2)*weightedEnergy 1 p d q w c+
        quartic*L^3*neutralMoment β 0 0*weightedEnergy 2 p d q w c) L := by
  have he : (fun t => energy mass2 quartic vacuum β t p d q w c) = fun t =>
      coefficient0 mass2 quartic vacuum β 0*weightedEnergy 0 p d q w c+
      t^2*(mass2*neutralMoment β 0 0/2+3*quartic*neutralMoment β 0 2/2)*weightedEnergy 1 p d q w c+
      quartic*t^4*neutralMoment β 0 0/4*weightedEnergy 2 p d q w c := by
    funext t
    exact energy_decomposition mass2 quartic vacuum β t p d q w c hβ hp hw hd
  rw [he]
  convert ((hasDerivAt_const L (coefficient0 mass2 quartic vacuum β 0*weightedEnergy 0 p d q w c)).add
    ((((hasDerivAt_id L).pow 2).mul_const _).mul_const _)).add
    ((((((hasDerivAt_id L).pow 4).const_mul quartic).mul_const _).div_const 4).mul_const _) using 1
  simp only [id_eq]
  ring

theorem field_derivative_bounds (β L : ℝ) (p : ℂ) (d q : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ L*deriv (fun t => energy mass2 quartic vacuum β t p d q w c) L ∧
      L*deriv (fun t => energy mass2 quartic vacuum β t p d q w c) L ≤ 4*energy mass2 quartic vacuum β L p d q w c := by
  rw [(field_derivative mass2 quartic vacuum β L p d q w c hβ hp hw hd).deriv,
    energy_decomposition mass2 quartic vacuum β L p d q w c hβ hp hw hd]
  have henergy (m : ℕ) : 0 ≤ weightedEnergy m p d q w c := integral_nonneg (fun _ => by positivity)
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative mass2 quartic vacuum β 0 L hm hq hv
  have he : L*(2*L*(mass2*neutralMoment β 0 0/2+3*quartic*neutralMoment β 0 2/2)*weightedEnergy 1 p d q w c+
        quartic*L^3*neutralMoment β 0 0*weightedEnergy 2 p d q w c) =
      2*(coefficient1 mass2 quartic β 0 L*weightedEnergy 1 p d q w c)+4*(coefficient2 quartic β 0 L*weightedEnergy 2 p d q w c) := by
    unfold coefficient1 coefficient2
    ring
  rw [he]
  constructor <;> nlinarith [mul_nonneg h0 (henergy 0),mul_nonneg h1 (henergy 1),mul_nonneg h2 (henergy 2)]

theorem joint_integral_eq_energy (n : ℕ) (α β D : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (c : Fin n → ℂ) (hβ : 0 < β) (hp : 0 < (gamma α r).re)
    (hw : ∀ i, 0 < w i) (hd : ∀ i, 8*β*r.im^2 < 2*(gamma α r).re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    (∫ z, KFCausalCommonImaginaryGaussianJointDensity.density mass2 quartic vacuum
      n α β D w r c z ∂KFCausalReciprocalNeutralLaplace.jointMeasure)=
      energy mass2 quartic vacuum β (KFCausalChargedPairCoordinates.fieldSlope r) (gamma α r)
        (8*β*r.im^2) (4*D*r.im) w (fun i => c i*(w i:ℂ)) := by
  rw [KFCausalCommonImaginaryGaussianJointDensity.joint_iterated mass2 quartic vacuum
    n α β D w r c hβ hd hm hq hv]
  symm
  exact KFCausalChargedProductFubini.integral_order _
    (density_integrable mass2 quartic vacuum β (KFCausalChargedPairCoordinates.fieldSlope r)
      (gamma α r) (8*β*r.im^2) (4*D*r.im) w (fun i => c i*(w i:ℂ)) hβ hp hw hd)

#print axioms neutralLine_reflect
#print axioms neutralLine_zero
#print axioms density_integrable
#print axioms energy_decomposition
#print axioms energy_nonnegative
#print axioms actual_scaled_le
#print axioms field_derivative
#print axioms field_derivative_bounds
#print axioms joint_integral_eq_energy
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianEnergy
