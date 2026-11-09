/- The actual spatial neutral packets have an exact charged Gaussian
half-plane marginal. All finite interference and the quartic weight are
retained, and the marginal is absolutely integrable. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingEnergyContraction
import UnifiedTheory.Audit.KFCausalJointNeutralFourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalMarginal
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalChargedCoolingGramIntegral (planeMeasure fixedCoefficients)
open KFCausalChargedCoolingDerivative (kernel form)
open KFCausalChargedFourierPolynomialGram (atom family)
open KFCausalReciprocalWedgeGeometry (gamma chart)
open KFCausalQuarticPlaneDomination (potential potentialSlope)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalNeutralPositiveForm (positiveDensity)
open KFCausalNeutralExponentialProfiles (exponentialProfile)

def constantArray {n : ℕ} (c : Fin n → ℂ) (i : Fin n) : Fin 3 → ℂ := ![c i,0,0]

def packetSum (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (u v Y : ℝ) : ℂ := ∑ i, c i * atom p (w i) 0 0 u v Y

def neutralCoefficients (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (v x : ℝ) (i : Fin n) : ℂ :=
  c i*(w i:ℂ)*KFCausalNeutralLinePackets.entire β (b i) (P i)
    ((x:ℂ)+(2*r.im*v:ℝ)*Complex.I)

theorem constant_family (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (u v Y : ℝ) :
    family n p w 0 (constantArray c) u v Y = packetSum n p w c u v Y := by
  unfold family packetSum
  rw [Fintype.sum_prod_type]
  simp [constantArray, Fin.sum_univ_succ]

theorem constant_form (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ) (v : ℝ) :
    form p (fun I : Fin n × Fin 3 => w I.1) v (fixedCoefficients (constantArray c) 0 v) =
      form p w v c := by
  simp [form, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
    fixedCoefficients, constantArray, Fin.sum_univ_succ]

theorem packet_square_integrable (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    Integrable (fun q : ℝ × ℝ => ‖packetSum n p w c q.1 v q.2‖^2) planeMeasure := by
  simpa only [constant_family] using
    KFCausalChargedCoolingEnergyContraction.fixed_energy_integrable n p w 0 (constantArray c) hp hw v

theorem packet_square_integral (n : ℕ) (p : ℂ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (hp : 0 < p.re) (hw : ∀ i, 0 < w i) (v : ℝ) :
    (∫ q : ℝ × ℝ, ‖packetSum n p w c q.1 v q.2‖^2 ∂planeMeasure) =
      Real.sqrt Real.pi * (form (conj p) w v c).re := by
  have he := KFCausalChargedCoolingEnergyContraction.fixed_energy_form n p w 0 (constantArray c) hp hw v
  simpa only [KFCausalChargedCoolingEnergyContraction.fixedEnergy,constant_family,constant_form] using he

theorem atom_chart (α : ℝ) (r : ℂ) (w u v Y : ℝ) :
    atom (gamma α r) w 0 0 u v Y = Complex.exp (-(w:ℂ)*chart α r (u^2+v^2) Y) := by
  unfold atom chart
  simp only [pow_zero, Complex.ofReal_zero, zero_div, zero_mul, add_zero, one_mul]
  congr 1
  push_cast
  ring

theorem line_packet (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (u v Y x : ℝ) :
    KFCausalNeutralFourierShift.line n β b
      (KFCausalNeutralJointCurvatureForm.coefficients n w c (chart α r (u^2+v^2) Y))
      P (2*r.im*v) x =
      packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y := by
  unfold KFCausalNeutralFourierShift.line KFCausalGaussianContourShift.horizontal
    KFCausalNeutralLineDomain.family packetSum
  simp only [atom_chart]
  apply Finset.sum_congr rfl
  intro i _
  unfold neutralCoefficients KFCausalNeutralJointCurvatureForm.coefficients
  ring

theorem physical_density (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (u v Y x : ℝ) :
    positiveDensity n α β w r c (fun i => exponentialProfile (b i) 1 (P i)) ((u,![v,x]),Y) =
      potential (x+fieldSlope r*v)*
        ‖packetSum n (gamma α r) w (neutralCoefficients n β w b c P r v x) u v Y‖^2 := by
  rw [KFCausalJointNeutralFourierIntegral.density_slice,
    KFCausalJointNeutralFourierIntegral.jointSlice_line, line_packet]

theorem physical_marginal_integrable (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (v x : ℝ) :
    Integrable (fun q : ℝ × ℝ => positiveDensity n α β w r c
      (fun i => exponentialProfile (b i) 1 (P i)) ((q.1,![v,x]),q.2)) planeMeasure := by
  simp_rw [physical_density]
  exact (packet_square_integrable n (gamma α r) w _
    (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw v).const_mul _

theorem physical_marginal_integral (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (r : ℂ) (hα : 0 < α) (hr : |r.im| < r.re)
    (hw : ∀ i, 0 < w i) (v x : ℝ) :
    (∫ q : ℝ × ℝ, positiveDensity n α β w r c
      (fun i => exponentialProfile (b i) 1 (P i)) ((q.1,![v,x]),q.2) ∂planeMeasure) =
      Real.sqrt Real.pi * potential (x+fieldSlope r*v) *
        (form (conj (gamma α r)) w v (neutralCoefficients n β w b c P r v x)).re := by
  simp_rw [physical_density]
  rw [integral_const_mul, packet_square_integral n (gamma α r) w _
    (KFCausalChargedCoolingFixedV.actual_gamma_re_positive α r hα hr) hw v]
  ring

#print axioms constant_family
#print axioms constant_form
#print axioms packet_square_integrable
#print axioms packet_square_integral
#print axioms atom_chart
#print axioms line_packet
#print axioms physical_density
#print axioms physical_marginal_integrable
#print axioms physical_marginal_integral
end
end UnifiedTheory.Audit.KFCausalChargedCoolingPhysicalMarginal
