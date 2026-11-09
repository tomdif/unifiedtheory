/- Full spatial response integrability for arbitrary finite neutral
packets. Gaussian widths control both the actual field and its complete
geometry derivative, with interference retained before integration. -/
import UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteNeutralResponseIntegrability
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalClusteredClockFactors
open KFCausalJointCompactPolynomialBounds
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalJointNeutralFourierOuterDensity (spatialQuarticResponse)

variable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

def value (j : ℕ) (r : ℂ) (p : Joint) : ℂ :=
  ∑ i, (c i*(w i:ℂ))*limitFactor 0 j (w i*α) β r (b i) (P i) p

def slope (j : ℕ) (r rd : ℂ) (p : Joint) : ℂ :=
  ∑ i, (c i*(w i:ℂ))*limitSlope 0 j (w i*α) β r rd (b i) (P i) p

def channelResponse (j : ℕ) (r rd : ℂ) (p : Joint) : ℝ :=
  2*(conj (value n α β w b c P j r p)*slope n α β w b c P j r rd p).re

def response (r rd : ℂ) (p : Joint) : ℝ :=
  channelResponse n α β w b c P 0 r rd p+
    channelResponse n α β w b c P 1 r rd p/2+
    channelResponse n α β w b c P 2 r rd p/4

theorem value_derivative (j : ℕ) (r : ℝ → ℂ) (rd : ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => value n α β w b c P j (r t) p)
      (slope n α β w b c P j (r s) rd p) s :=
  HasDerivAt.fun_sum (fun i _ =>
    (limitFactor_derivative 0 j (w i*α) β r rd (b i) (P i) s p hr).const_mul _)

theorem value_continuous (j : ℕ) (r : ℂ) : Continuous (value n α β w b c P j r) := by
  unfold value limitFactor E Z N G F KFCausalReciprocalWedgeGeometry.chart
    KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem slope_continuous (j : ℕ) (r rd : ℂ) : Continuous (slope n α β w b c P j r rd) := by
  unfold slope limitSlope B0 B1 E Ed Z Zd N Nd G Gd F Fd
    KFCausalReciprocalWedgeGeometry.chart KFCausalReciprocalNeutralKernel.neutral
  fun_prop

theorem finite_envelope (j : ℕ) (r rd : ℂ) (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    ∃ D : Joint → ℝ, Integrable D jointMeasure ∧ (∀ p, 0 ≤ D p) ∧
      ∀ p, 0 ≤ p.2 → ‖value n α β w b c P j r p‖^2+
        ‖slope n α β w b c P j r rd p‖^2 ≤ D p := by
  let K := Set.Icc (-1:ℝ) 1
  let f : Fin n → ℝ → Joint → ℂ := fun i _ p =>
    (c i*(w i:ℂ))*((F r p:ℂ)^j*(P i).eval (N r p))
  let g : Fin n → ℝ → Joint → ℂ := fun i _ p =>
    (c i*(w i:ℂ))*B0 j (w i*α) β r rd (b i) (P i) p
  have hs (i : Fin n) := KFCausalClusteredClockCompactEnvelope.polynomials_controlled
    K isCompact_Icc 0 j (w i*α) β (fun _ => r) (fun _ => rd)
    continuous_const continuous_const (b i) (P i)
  have hf (i : Fin n) : Controlled K (f i) := by
    apply (controlled_const K (c i*(w i:ℂ))).mul
    simpa only [KFCausalClusteredWidthDensityIntegrability.factorPolynomial_eval,pow_zero,mul_one] using (hs i).1
  have hg (i : Fin n) : Controlled K (g i) := by
    apply (controlled_const K (c i*(w i:ℂ))).mul
    simpa only [KFCausalClusteredClockEnvelope.slopePolynomial0_eval,pow_zero,one_mul] using (hs i).2.1
  obtain ⟨D,hDi,hD0,hD⟩ := KFCausalCorrelatedDilationEnvelope.finite_pair_envelope
    n (fun i => w i*α) β 0 r b hβ hA hC f g hf hg
  refine ⟨D,hDi,hD0,?_⟩
  intro p hp
  have hb := hD 0 (by constructor <;> norm_num) p hp
  simpa only [value,slope,limitFactor,limitSlope,B1,pow_zero,mul_one,
    Nat.cast_zero,zero_mul,mul_zero,add_zero,KFCausalCorrelatedDilationEnvelope.geometry,
    KFCausalCorrelatedDilationEnvelope.scale,Real.exp_zero,Complex.ofReal_one,one_mul,f,g,
    mul_assoc,mul_left_comm,mul_comm] using hb

theorem channel_response_integrable (j : ℕ) (r rd : ℂ) (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    Integrable (channelResponse n α β w b c P j r rd) jointMeasure := by
  obtain ⟨D,hDi,_,hD⟩ := finite_envelope n α β w b c P j r rd hβ hA hC
  have hc : Continuous (channelResponse n α β w b c P j r rd) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((Complex.continuous_conj.comp (value_continuous n α β w b c P j r)).mul
        (slope_continuous n α β w b c P j r rd)))
  apply hDi.mono' hc.aestronglyMeasurable
  filter_upwards [KFCausalClusteredWidthEnergyLimit.ae_halfline] with p hp
  exact (KFCausalCorrelatedClusteredBounds.cross_bound _ _).trans (hD p hp)

theorem density_formula (r : ℂ) (p : Joint) :
    positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) p =
      ‖value n α β w b c P 0 r p‖^2+
      ‖value n α β w b c P 1 r p‖^2/2+
      ‖value n α β w b c P 2 r p‖^2/4 := by
  rw [KFCausalJointFourierDilationQuartic.density_identity n α β w b c P r 0]
  simp only [KFCausalJointFourierDilationRepresentation.density_eq,
    KFCausalCorrelatedDilationDifferentiation.value,
    KFCausalCorrelatedDilationPolynomials.packet,
    KFCausalCorrelatedDilationPolynomials.prefactor,
    KFCausalCorrelatedDilationPolynomials.field,
    KFCausalCorrelatedDilationEnvelope.geometry,KFCausalCorrelatedDilationEnvelope.scale,
    zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul,pow_zero,mul_one,value,limitFactor,F,mul_assoc]

theorem density_derivative (r : ℝ → ℂ) (rd : ℂ) (s : ℝ) (p : Joint)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => positiveDensity n α β w (r t) c
      (fun i => exponentialProfile (b i) 1 (P i)) p)
      (response n α β w b c P (r s) rd p) s := by
  have hd (j : ℕ) := KFCausalNeutralQuarticBoundary.norm_square_derivative
    (fun t => value n α β w b c P j (r t) p)
    (fun t => slope n α β w b c P j (r t) rd p) s
    (value_derivative n α β w b c P j r rd s p hr)
  simpa only [density_formula,response,channelResponse] using
    ((hd 0).add ((hd 1).div_const 2)).add ((hd 2).div_const 4)

theorem spatial_response_eq (r rd : ℂ) (p : Joint) :
    spatialQuarticResponse n α β w b c P r rd p.1.1 (p.1.2 0) p.2 (p.1.2 1) =
      response n α β w b c P r rd p := by
  let curve : ℝ → ℂ := fun t => r+(t:ℂ)*rd
  have hr : HasDerivAt curve rd 0 := by
    simpa only [curve,id_eq,Complex.ofReal_one,one_mul] using
      ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const rd).const_add r
  have hp : ((p.1.1,![p.1.2 0,p.1.2 1]),p.2)=p := by
    congr 2
    ext i
    fin_cases i <;> rfl
  have hd := KFCausalJointNeutralFourierOuterDensity.density_derivative
    n α β w b c P curve rd 0 p.1.1 (p.1.2 0) (p.1.2 1) p.2 hr
  rw [hp] at hd
  simpa only [curve,Complex.ofReal_zero,zero_mul,add_zero] using
    hd.unique (density_derivative n α β w b c P curve rd 0 p hr)

theorem spatial_response_integrable (r rd : ℂ) (hβ : 0 < β)
    (hA : ∀ i, 0 < (w i*α)*area r)
    (hC : ∀ i, 0 < (w i*α)*area r-8*β*r.im^2) :
    Integrable (fun p : Joint => spatialQuarticResponse n α β w b c P r rd
      p.1.1 (p.1.2 0) p.2 (p.1.2 1)) jointMeasure := by
  simp_rw [spatial_response_eq]
  have hi := channel_response_integrable n α β w b c P
  exact ((hi 0 r rd hβ hA hC).add ((hi 1 r rd hβ hA hC).div_const 2)).add
    ((hi 2 r rd hβ hA hC).div_const 4)

#print axioms value_derivative
#print axioms value_continuous
#print axioms slope_continuous
#print axioms finite_envelope
#print axioms channel_response_integrable
#print axioms density_formula
#print axioms density_derivative
#print axioms spatial_response_eq
#print axioms spatial_response_integrable
end
end UnifiedTheory.Audit.KFCausalFiniteNeutralResponseIntegrability
