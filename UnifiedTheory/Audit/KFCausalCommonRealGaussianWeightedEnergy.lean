/- Arbitrary nonnegative potential couplings for the actual common-real-source
Gaussian integral. All charged widths and complex amplitudes remain coherent.
The neutral integral, integrability, charged reflection, finite imaginary
increments and field derivative are proved. No weighted Hilbert-space
clock-response attachment is asserted in this module. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open KFCausalCommonRealGaussianEnergy (neutralWeight neutralMoment neutral_moment_integrable)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedGaussianMomentSeries (weightedEnergy)
open KFCausalChargedEvenMomentImaginaryBound (gamma)

def potential (mass2 quartic vacuum x : ℝ) : ℝ := vacuum+mass2*x^2/2+quartic*x^4/4

theorem potential_nonnegative (mass2 quartic vacuum x : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ potential mass2 quartic vacuum x := by unfold potential; positivity

variable (mass2 quartic vacuum : ℝ)

def neutralLine (β B L v : ℝ) : ℝ :=
  ∫ x : ℝ, potential mass2 quartic vacuum (x+L*v)*neutralWeight β B x

def coefficient0 (β B : ℝ) : ℝ :=
  vacuum*neutralMoment β B 0+mass2*neutralMoment β B 2/2+quartic*neutralMoment β B 4/4

def coefficient1 (β B L : ℝ) : ℝ :=
  L^2*(mass2*neutralMoment β B 0/2+3*quartic*neutralMoment β B 2/2)

def coefficient2 (β B L : ℝ) : ℝ := quartic*L^4*neutralMoment β B 0/4

private theorem line_polynomial (β B L v x : ℝ) :
    potential mass2 quartic vacuum (x+L*v)*neutralWeight β B x =
      (vacuum+mass2*L^2*v^2/2+quartic*L^4*v^4/4)*(x^0*neutralWeight β B x)+
      (mass2*L*v+quartic*L^3*v^3)*(x^1*neutralWeight β B x)+
      (mass2/2+3*quartic*L^2*v^2/2)*(x^2*neutralWeight β B x)+
      (quartic*L*v)*(x^3*neutralWeight β B x)+(quartic/4)*(x^4*neutralWeight β B x) := by
  unfold potential
  ring

private theorem line_integrable (β B L v : ℝ) (hβ : 0 < β) :
    Integrable (fun x : ℝ => potential mass2 quartic vacuum (x+L*v)*neutralWeight β B x) := by
  simp_rw [line_polynomial]
  exact ((((neutral_moment_integrable β B hβ 0).const_mul _).add
    ((neutral_moment_integrable β B hβ 1).const_mul _)).add
    ((neutral_moment_integrable β B hβ 2).const_mul _)).add
    ((neutral_moment_integrable β B hβ 3).const_mul _) |>.add
    ((neutral_moment_integrable β B hβ 4).const_mul _)

theorem neutralLine_expansion (β B L v : ℝ) (hβ : 0 < β) :
    neutralLine mass2 quartic vacuum β B L v = coefficient0 mass2 quartic vacuum β B+L*(mass2*neutralMoment β B 1+quartic*neutralMoment β B 3)*v+
      coefficient1 mass2 quartic β B L*v^2+quartic*L^3*neutralMoment β B 1*v^3+coefficient2 quartic β B L*v^4 := by
  unfold neutralLine
  simp_rw [line_polynomial]
  have h0 := (neutral_moment_integrable β B hβ 0).const_mul (vacuum+mass2*L^2*v^2/2+quartic*L^4*v^4/4)
  have h1 := (neutral_moment_integrable β B hβ 1).const_mul (mass2*L*v+quartic*L^3*v^3)
  have h2 := (neutral_moment_integrable β B hβ 2).const_mul (mass2/2+3*quartic*L^2*v^2/2)
  have h3 := (neutral_moment_integrable β B hβ 3).const_mul (quartic*L*v)
  have h4 := (neutral_moment_integrable β B hβ 4).const_mul (quartic/4:ℝ)
  have he0 := integral_add h0 h1
  have he1 := integral_add (h0.add h1) h2
  have he2 := integral_add ((h0.add h1).add h2) h3
  have he3 := integral_add (((h0.add h1).add h2).add h3) h4
  simp only [Pi.add_apply] at he0 he1 he2 he3
  rw [he3,he2,he1,he0]
  simp only [integral_const_mul]
  unfold coefficient0 coefficient1 coefficient2 neutralMoment
  ring

theorem neutralLine_even (β B L v : ℝ) (hβ : 0 < β) :
    (neutralLine mass2 quartic vacuum β B L v+neutralLine mass2 quartic vacuum β B L (-v))/2 =
      coefficient0 mass2 quartic vacuum β B+coefficient1 mass2 quartic β B L*v^2+coefficient2 quartic β B L*v^4 := by
  rw [neutralLine_expansion mass2 quartic vacuum β B L v hβ,neutralLine_expansion mass2 quartic vacuum β B L (-v) hβ]
  ring

theorem coefficients_nonnegative (β B L : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ coefficient0 mass2 quartic vacuum β B ∧ 0 ≤ coefficient1 mass2 quartic β B L ∧ 0 ≤ coefficient2 quartic β B L := by
  have h0 : 0 ≤ neutralMoment β B 0 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  have h2 : 0 ≤ neutralMoment β B 2 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  have h4 : 0 ≤ neutralMoment β B 4 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  unfold coefficient0 coefficient1 coefficient2
  exact ⟨by positivity,by positivity,by positivity⟩

variable {ι : Type*} [Fintype ι]

def density (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℝ :=
  neutralLine mass2 quartic vacuum β B L x.1.2*Real.exp (d*x.1.2^2)*‖packet 0 p w c x‖^2
def energy (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, density mass2 quartic vacuum β B L p d w c x ∂chargedMeasure

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

private def evenDensity (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℝ :=
  coefficient0 mass2 quartic vacuum β B*(Real.exp (d*x.1.2^2)*‖packet 0 p w c x‖^2)+
    coefficient1 mass2 quartic β B L*(Real.exp (d*x.1.2^2)*‖packet 1 p w c x‖^2)+
    coefficient2 quartic β B L*(Real.exp (d*x.1.2^2)*‖packet 2 p w c x‖^2)

private theorem density_even (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (x : Charged) :
    density mass2 quartic vacuum β B L p d w c x+density mass2 quartic vacuum β B L p d w c (reflect x) =
      2*evenDensity mass2 quartic vacuum β B L p d w c x := by
  have h := neutralLine_even mass2 quartic vacuum β B L x.1.2 hβ
  have h1 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 1 p w c x
  have h2 := KFCausalChargedGaussianMomentSeries.packet_norm_add 0 2 p w c x
  simp only [zero_add,pow_one] at h1
  simp only [zero_add] at h2
  unfold density evenDensity
  rw [packet_reflect,h1,h2]
  dsimp only [reflect]
  rw [neg_sq]
  linear_combination 2*Real.exp (d*x.1.2^2)*‖packet 0 p w c x‖^2*h

private theorem density_nonnegative (β B L : ℝ) (p : ℂ) (d : ℝ)
    (w : ι → ℝ) (c : ι → ℂ) (x : Charged)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) : 0 ≤ density mass2 quartic vacuum β B L p d w c x := by
  have hn : 0 ≤ neutralLine mass2 quartic vacuum β B L x.1.2 := integral_nonneg (fun t =>
    mul_nonneg (potential_nonnegative mass2 quartic vacuum _ hm hq hv) (Real.exp_pos _).le)
  unfold density
  positivity

private theorem evenDensity_integrable (β B L : ℝ) (p : ℂ) (d : ℝ)
    (w : ι → ℝ) (c : ι → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, d < 2*p.re*w i) : Integrable (evenDensity mass2 quartic vacuum β B L p d w c) chargedMeasure := by
  exact (((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 0 p d w c hp hw hd).const_mul _).add ((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 1 p d w c hp hw hd).const_mul _)).add ((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 2 p d w c hp hw hd).const_mul _)

theorem density_integrable (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    Integrable (density mass2 quartic vacuum β B L p d w c) chargedMeasure := by
  have hline : Continuous (neutralLine mass2 quartic vacuum β B L) := by
    have he : neutralLine mass2 quartic vacuum β B L = fun v => coefficient0 mass2 quartic vacuum β B+
        L*(mass2*neutralMoment β B 1+quartic*neutralMoment β B 3)*v+coefficient1 mass2 quartic β B L*v^2+
        quartic*L^3*neutralMoment β B 1*v^3+coefficient2 quartic β B L*v^4 :=
      funext (fun v => neutralLine_expansion mass2 quartic vacuum β B L v hβ)
    rw [he]
    fun_prop
  have hpkt : Continuous (packet 0 p w c) := by
    unfold packet KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  have hc : Continuous (density mass2 quartic vacuum β B L p d w c) := by unfold density; fun_prop
  apply ((evenDensity_integrable mass2 quartic vacuum β B L p d w c hp hw hd).const_mul 2).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative mass2 quartic vacuum β B L p d w c x hm hq hv)]
    have he := density_even mass2 quartic vacuum β B L p d w c hβ x
    have hn := density_nonnegative mass2 quartic vacuum β B L p d w c (reflect x) hm hq hv
    linarith)

theorem energy_decomposition (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    energy mass2 quartic vacuum β B L p d w c = coefficient0 mass2 quartic vacuum β B*weightedEnergy 0 p d w c+
      coefficient1 mass2 quartic β B L*weightedEnergy 1 p d w c+coefficient2 quartic β B L*weightedEnergy 2 p d w c := by
  have hi := density_integrable mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv
  have hf : Integrable (fun x => density mass2 quartic vacuum β B L p d w c (reflect x)) chargedMeasure :=
    reflect_preserving.integrable_comp_of_integrable hi
  have hv := reflect_preserving.integral_comp reflectEquiv.measurableEmbedding (density mass2 quartic vacuum β B L p d w c)
  have he := integral_congr_ae (μ := chargedMeasure)
    (Eventually.of_forall (fun x => density_even mass2 quartic vacuum β B L p d w c hβ x))
  rw [integral_add hi hf,integral_const_mul,hv] at he
  have h0 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 0 p d w c hp hw hd).const_mul (coefficient0 mass2 quartic vacuum β B)
  have h1 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 1 p d w c hp hw hd).const_mul (coefficient1 mass2 quartic β B L)
  have h2 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 2 p d w c hp hw hd).const_mul (coefficient2 quartic β B L)
  unfold evenDensity at he
  have he0 := integral_add h0 h1
  have he1 := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at he0 he1
  rw [he1,he0] at he
  simp only [integral_const_mul] at he
  unfold energy weightedEnergy
  linarith

theorem energy_ordered (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) :
    energy mass2 quartic vacuum β B L p d w c = ∫ y : Charged, (∫ x : ℝ,
      potential mass2 quartic vacuum (x+L*y.1.2)*neutralWeight β B x*Real.exp (d*y.1.2^2)*‖packet 0 p w c y‖^2) ∂chargedMeasure := by
  simp only [integral_mul_const,energy,density,neutralLine]

theorem energy_nonnegative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ energy mass2 quartic vacuum β B L p d w c := by
  apply integral_nonneg
  intro x
  have hn : 0 ≤ neutralLine mass2 quartic vacuum β B L x.1.2 := integral_nonneg (fun t =>
    mul_nonneg (potential_nonnegative mass2 quartic vacuum _ hm hq hv) (Real.exp_pos _).le)
  unfold density
  positivity

theorem actual_scaled_le (α a β B L b₁ b₂ : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hb₁ : 0 < b₁) (hb : b₁ ≤ b₂) (hb₂ : b₂ < a)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (c : ι → ℂ)
    (hd : ∀ i, 8*β*b₂^2 < α*(a^2-b₂^2)*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    b₁^2*energy mass2 quartic vacuum β B L (gamma α ((a:ℂ)+Complex.I*(b₁:ℂ))) (8*β*b₁^2) w c ≤
    b₂^2*energy mass2 quartic vacuum β B L (gamma α ((a:ℂ)+Complex.I*(b₂:ℂ))) (8*β*b₂^2) w c := by
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
  rw [energy_decomposition mass2 quartic vacuum β B L _ _ w c hβ (hp b₁ hb₁ hb₁a) hw
    (by intro i; rw [hre]; exact hd₁ i) hm hq hv,
    energy_decomposition mass2 quartic vacuum β B L _ _ w c hβ (hp b₂ hb₂0 hb₂) hw
    (by intro i; rw [hre]; exact hd i) hm hq hv]
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative mass2 quartic vacuum β B L hm hq hv
  have he (m : ℕ) (hm : m ≤ 2) :=
    KFCausalChargedGaussianMomentSeries.actual_scaled_le α a β b₁ b₂ hα hβ.le hb₁ hb hb₂ m hm w hw c hd
  nlinarith [mul_le_mul_of_nonneg_left (he 0 (by omega)) h0,
    mul_le_mul_of_nonneg_left (he 1 (by omega)) h1,
    mul_le_mul_of_nonneg_left (he 2 (by omega)) h2]

theorem field_derivative (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    HasDerivAt (fun t => energy mass2 quartic vacuum β B t p d w c)
      (2*L*(mass2*neutralMoment β B 0/2+3*quartic*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
        quartic*L^3*neutralMoment β B 0*weightedEnergy 2 p d w c) L := by
  have he : (fun t => energy mass2 quartic vacuum β B t p d w c) = fun t =>
      coefficient0 mass2 quartic vacuum β B*weightedEnergy 0 p d w c+
      t^2*(mass2*neutralMoment β B 0/2+3*quartic*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
      quartic*t^4*neutralMoment β B 0/4*weightedEnergy 2 p d w c := by
    funext t
    exact energy_decomposition mass2 quartic vacuum β B t p d w c hβ hp hw hd hm hq hv
  rw [he]
  convert ((hasDerivAt_const L (coefficient0 mass2 quartic vacuum β B*weightedEnergy 0 p d w c)).add
    ((((hasDerivAt_id L).pow 2).mul_const _).mul_const _)).add
    ((((((hasDerivAt_id L).pow 4).const_mul quartic).mul_const _).div_const 4).mul_const _) using 1
  simp only [id_eq]
  ring

theorem field_derivative_bounds (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) :
    0 ≤ L*deriv (fun t => energy mass2 quartic vacuum β B t p d w c) L ∧
      L*deriv (fun t => energy mass2 quartic vacuum β B t p d w c) L ≤ 4*energy mass2 quartic vacuum β B L p d w c := by
  rw [(field_derivative mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv).deriv,
    energy_decomposition mass2 quartic vacuum β B L p d w c hβ hp hw hd hm hq hv]
  have henergy (m : ℕ) : 0 ≤ weightedEnergy m p d w c := integral_nonneg (fun _ => by positivity)
  obtain ⟨h0,h1,h2⟩ := coefficients_nonnegative mass2 quartic vacuum β B L hm hq hv
  have he : L*(2*L*(mass2*neutralMoment β B 0/2+3*quartic*neutralMoment β B 2/2)*weightedEnergy 1 p d w c+
        quartic*L^3*neutralMoment β B 0*weightedEnergy 2 p d w c) =
      2*(coefficient1 mass2 quartic β B L*weightedEnergy 1 p d w c)+4*(coefficient2 quartic β B L*weightedEnergy 2 p d w c) := by
    unfold coefficient1 coefficient2
    ring
  rw [he]
  constructor <;> nlinarith [mul_nonneg h0 (henergy 0),mul_nonneg h1 (henergy 1),mul_nonneg h2 (henergy 2)]


#print axioms potential_nonnegative
#print axioms neutralLine_expansion
#print axioms neutralLine_even
#print axioms coefficients_nonnegative
#print axioms density_integrable
#print axioms energy_decomposition
#print axioms energy_ordered
#print axioms energy_nonnegative
#print axioms actual_scaled_le
#print axioms field_derivative
#print axioms field_derivative_bounds
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianWeightedEnergy
