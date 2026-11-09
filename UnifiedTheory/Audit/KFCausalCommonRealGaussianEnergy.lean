/- Exact full quartic energy for a common real neutral source and P=1.
All charged widths and complex amplitudes remain coherent. The neutral
integral and charged reflection are proved, not assumed. -/
import UnifiedTheory.Audit.KFCausalChargedGaussianMomentSeries
import UnifiedTheory.Audit.KFCausalQuarticPlaneDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ComplexConjugate
open KFCausalQuarticPlaneDomination (potential potential_positive)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalChargedEvenMomentFamily (packet)
open KFCausalChargedGaussianMomentSeries (weightedEnergy)

def neutralWeight (β B x : ℝ) : ℝ := Real.exp (-2*β*x^2+2*B*x)
def neutralMoment (β B : ℝ) (j : ℕ) : ℝ := ∫ x : ℝ, x^j*neutralWeight β B x
def neutralLine (β B L v : ℝ) : ℝ := ∫ x : ℝ, potential (x+L*v)*neutralWeight β B x
def coefficient0 (β B : ℝ) : ℝ := neutralMoment β B 0+neutralMoment β B 2/2+neutralMoment β B 4/4
def coefficient1 (β B L : ℝ) : ℝ := L^2*(neutralMoment β B 0/2+3*neutralMoment β B 2/2)
def coefficient2 (β B L : ℝ) : ℝ := L^4*neutralMoment β B 0/4

theorem neutral_moment_integrable (β B : ℝ) (hβ : 0 < β) (j : ℕ) :
    Integrable (fun x : ℝ => x^j*neutralWeight β B x) := by
  have hi := (KFCausalShiftedComplexGaussianMoments.moment_integrable
    ((2*β:ℝ):ℂ) ((2*B:ℝ):ℂ) (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hβ) j).re
  have he (x : ℝ) : KFCausalShiftedComplexGaussianMoments.moment
      ((2*β:ℝ):ℂ) ((2*B:ℝ):ℂ) j x = ((x^j*neutralWeight β B x:ℝ):ℂ) := by
    unfold KFCausalShiftedComplexGaussianMoments.moment neutralWeight
    simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_exp,Complex.ofReal_add,
      Complex.ofReal_neg,Complex.ofReal_ofNat]
    congr 2
    ring
  simpa only [he,Complex.ofReal_re] using hi

private theorem line_polynomial (β B L v x : ℝ) :
    potential (x+L*v)*neutralWeight β B x =
      (1+L^2*v^2/2+L^4*v^4/4)*(x^0*neutralWeight β B x)+
      (L*v+L^3*v^3)*(x^1*neutralWeight β B x)+
      (1/2+3*L^2*v^2/2)*(x^2*neutralWeight β B x)+
      (L*v)*(x^3*neutralWeight β B x)+(1/4)*(x^4*neutralWeight β B x) := by
  unfold potential
  ring

private theorem line_integrable (β B L v : ℝ) (hβ : 0 < β) :
    Integrable (fun x : ℝ => potential (x+L*v)*neutralWeight β B x) := by
  simp_rw [line_polynomial]
  exact ((((neutral_moment_integrable β B hβ 0).const_mul _).add
    ((neutral_moment_integrable β B hβ 1).const_mul _)).add
    ((neutral_moment_integrable β B hβ 2).const_mul _)).add
    ((neutral_moment_integrable β B hβ 3).const_mul _) |>.add
    ((neutral_moment_integrable β B hβ 4).const_mul _)

theorem neutralLine_expansion (β B L v : ℝ) (hβ : 0 < β) :
    neutralLine β B L v = coefficient0 β B+L*(neutralMoment β B 1+neutralMoment β B 3)*v+
      coefficient1 β B L*v^2+L^3*neutralMoment β B 1*v^3+coefficient2 β B L*v^4 := by
  unfold neutralLine
  simp_rw [line_polynomial]
  have h0 := (neutral_moment_integrable β B hβ 0).const_mul (1+L^2*v^2/2+L^4*v^4/4)
  have h1 := (neutral_moment_integrable β B hβ 1).const_mul (L*v+L^3*v^3)
  have h2 := (neutral_moment_integrable β B hβ 2).const_mul (1/2+3*L^2*v^2/2)
  have h3 := (neutral_moment_integrable β B hβ 3).const_mul (L*v)
  have h4 := (neutral_moment_integrable β B hβ 4).const_mul (1/4:ℝ)
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
    (neutralLine β B L v+neutralLine β B L (-v))/2 =
      coefficient0 β B+coefficient1 β B L*v^2+coefficient2 β B L*v^4 := by
  rw [neutralLine_expansion β B L v hβ,neutralLine_expansion β B L (-v) hβ]
  ring

theorem coefficients_nonnegative (β B L : ℝ) :
    0 ≤ coefficient0 β B ∧ 0 ≤ coefficient1 β B L ∧ 0 ≤ coefficient2 β B L := by
  have h0 : 0 ≤ neutralMoment β B 0 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  have h2 : 0 ≤ neutralMoment β B 2 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  have h4 : 0 ≤ neutralMoment β B 4 := integral_nonneg (fun x => by unfold neutralWeight; positivity)
  unfold coefficient0 coefficient1 coefficient2
  exact ⟨by positivity,by positivity,by positivity⟩

variable {ι : Type*} [Fintype ι]

def density (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : ℝ :=
  neutralLine β B L x.1.2*Real.exp (d*x.1.2^2)*‖packet 0 p w c x‖^2
def energy (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) : ℝ :=
  ∫ x : Charged, density β B L p d w c x ∂chargedMeasure

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
  coefficient0 β B*(Real.exp (d*x.1.2^2)*‖packet 0 p w c x‖^2)+
    coefficient1 β B L*(Real.exp (d*x.1.2^2)*‖packet 1 p w c x‖^2)+
    coefficient2 β B L*(Real.exp (d*x.1.2^2)*‖packet 2 p w c x‖^2)

private theorem density_even (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (x : Charged) :
    density β B L p d w c x+density β B L p d w c (reflect x) =
      2*evenDensity β B L p d w c x := by
  have h := neutralLine_even β B L x.1.2 hβ
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
    (w : ι → ℝ) (c : ι → ℂ) (x : Charged) : 0 ≤ density β B L p d w c x := by
  have hn : 0 ≤ neutralLine β B L x.1.2 := integral_nonneg (fun t =>
    mul_nonneg (potential_positive _).le (Real.exp_pos _).le)
  unfold density
  positivity

private theorem evenDensity_integrable (β B L : ℝ) (p : ℂ) (d : ℝ)
    (w : ι → ℝ) (c : ι → ℂ) (hp : 0 < p.re) (hw : ∀ i, 0 < w i)
    (hd : ∀ i, d < 2*p.re*w i) : Integrable (evenDensity β B L p d w c) chargedMeasure := by
  exact (((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 0 p d w c hp hw hd).const_mul _).add ((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 1 p d w c hp hw hd).const_mul _)).add ((KFCausalChargedGaussianMomentSeries.weighted_square_integrable 2 p d w c hp hw hd).const_mul _)

theorem density_integrable (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    Integrable (density β B L p d w c) chargedMeasure := by
  have hline : Continuous (neutralLine β B L) := by
    have he : neutralLine β B L = fun v => coefficient0 β B+
        L*(neutralMoment β B 1+neutralMoment β B 3)*v+coefficient1 β B L*v^2+
        L^3*neutralMoment β B 1*v^3+coefficient2 β B L*v^4 :=
      funext (fun v => neutralLine_expansion β B L v hβ)
    rw [he]
    fun_prop
  have hpkt : Continuous (packet 0 p w c) := by
    unfold packet KFCausalChargedFourierPolynomialGram.atom
    fun_prop
  have hc : Continuous (density β B L p d w c) := by unfold density; fun_prop
  apply ((evenDensity_integrable β B L p d w c hp hw hd).const_mul 2).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (density_nonnegative β B L p d w c x)]
    have he := density_even β B L p d w c hβ x
    have hn := density_nonnegative β B L p d w c (reflect x)
    linarith)

theorem energy_decomposition (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ)
    (hβ : 0 < β) (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (hd : ∀ i, d < 2*p.re*w i) :
    energy β B L p d w c = coefficient0 β B*weightedEnergy 0 p d w c+
      coefficient1 β B L*weightedEnergy 1 p d w c+coefficient2 β B L*weightedEnergy 2 p d w c := by
  have hi := density_integrable β B L p d w c hβ hp hw hd
  have hf : Integrable (fun x => density β B L p d w c (reflect x)) chargedMeasure :=
    reflect_preserving.integrable_comp_of_integrable hi
  have hv := reflect_preserving.integral_comp reflectEquiv.measurableEmbedding (density β B L p d w c)
  have he := integral_congr_ae (μ := chargedMeasure)
    (Eventually.of_forall (fun x => density_even β B L p d w c hβ x))
  rw [integral_add hi hf,integral_const_mul,hv] at he
  have h0 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 0 p d w c hp hw hd).const_mul (coefficient0 β B)
  have h1 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 1 p d w c hp hw hd).const_mul (coefficient1 β B L)
  have h2 := (KFCausalChargedGaussianMomentSeries.weighted_square_integrable 2 p d w c hp hw hd).const_mul (coefficient2 β B L)
  unfold evenDensity at he
  have he0 := integral_add h0 h1
  have he1 := integral_add (h0.add h1) h2
  simp only [Pi.add_apply] at he0 he1
  rw [he1,he0] at he
  simp only [integral_const_mul] at he
  unfold energy weightedEnergy
  linarith

theorem energy_ordered (β B L : ℝ) (p : ℂ) (d : ℝ) (w : ι → ℝ) (c : ι → ℂ) :
    energy β B L p d w c = ∫ y : Charged, (∫ x : ℝ,
      potential (x+L*y.1.2)*neutralWeight β B x*Real.exp (d*y.1.2^2)*‖packet 0 p w c y‖^2) ∂chargedMeasure := by
  simp only [integral_mul_const,energy,density,neutralLine]

#print axioms neutral_moment_integrable
#print axioms neutralLine_expansion
#print axioms neutralLine_even
#print axioms coefficients_nonnegative
#print axioms density_integrable
#print axioms energy_decomposition
#print axioms energy_ordered
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianEnergy
