/- Packet-dependent absolute bounds for the complex cross kernel and its
clock-normalized derivative. These justify full clock integration; they
are not bounds relative to the energy of arbitrary superpositions. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossDifferentiation
import UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossBounds
noncomputable section
open MeasureTheory
open scoped ComplexConjugate Topology
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalNeutralClockEnvelope (curve slope)
open KFCausalPolynomialOrbitEnvelope (clockSlope)
open KFCausalClockResponseTransport (clock)
open KFCausalReciprocalNeutralCrossDifferentiation (actual)

variable (ε y α β w v : ℝ) (b d : ℂ) (P Q : Polynomial ℂ)
local notation "f" => curve ε y α β w b P
local notation "g" => curve ε y α β v d Q
local notation "f'" => slope ε y α β w b P
local notation "g'" => slope ε y α β v d Q

def density (k : ℕ) (s : ℝ) (q : Transverse) : ℂ := conj (f k s q)*g k s q
def densityDerivative (k : ℕ) (s : ℝ) (q : Transverse) : ℂ :=
  conj (f' k s q)*g k s q+conj (f k s q)*g' k s q
def pairIntegral (k : ℕ) (s : ℝ) : ℂ := ∫ q, density ε y α β w v b d P Q k s q
def pairDerivative (k : ℕ) (s : ℝ) : ℂ := ∫ q, densityDerivative ε y α β w v b d P Q k s q

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hα : 0 < α) (hβ : 0 < β)
  (hwidth : 32*β ≤ α) (hw : 1 ≤ w) (hv : 1 ≤ v)

include hε hy hw hv in
theorem density_continuity (k : ℕ) :
    Continuous (fun x : ℝ × Transverse => density ε y α β w v b d P Q k x.1 x.2) ∧
      Continuous (fun x : ℝ × Transverse => densityDerivative ε y α β w v b d P Q k x.1 x.2) := by
  have hf := KFCausalReciprocalNeutralClockEnvelope.curve_continuous ε y α β w b P k hε hy (by linarith)
  have hg := KFCausalReciprocalNeutralClockEnvelope.curve_continuous ε y α β v d Q k hε hy (by linarith)
  have hfd := KFCausalReciprocalNeutralClockEnvelope.slope_continuous ε y α β w b P k hε hy (by linarith)
  have hgd := KFCausalReciprocalNeutralClockEnvelope.slope_continuous ε y α β v d Q k hε hy (by linarith)
  exact ⟨hf.star.mul hg,(hfd.star.mul hg).add (hf.star.mul hgd)⟩

include hε hy hα hβ hwidth hw hv in
theorem common_bounds (k : ℕ) :
    ∃ D : Transverse → ℝ, Integrable D ∧ (∀ q, 0 ≤ D q) ∧ ∀ s q,
      ‖density ε y α β w v b d P Q k s q‖ ≤ D q ∧
      ‖densityDerivative ε y α β w v b d P Q k s q‖ ≤ ‖clockSlope ε y s‖*(2*D q) := by
  obtain ⟨A,_,hA,hA₀,ha⟩ := KFCausalReciprocalNeutralClockEnvelope.common_envelope
    ε y α β w b P k hε hy hα hβ hwidth hw
  obtain ⟨B,_,hB,hB₀,hb⟩ := KFCausalReciprocalNeutralClockEnvelope.common_envelope
    ε y α β v d Q k hε hy hα hβ hwidth hv
  refine ⟨fun q => A q*B q,hA.integrable_mul hB,fun q => mul_nonneg (hA₀ q) (hB₀ q),?_⟩
  intro s q
  constructor
  · simpa only [density,norm_mul,Complex.norm_conj] using
      mul_le_mul (ha s q).1 (hb s q).1 (norm_nonneg _) (hA₀ q)
  · apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_conj]
    have h1 := mul_le_mul (ha s q).2 (hb s q).1 (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (hA₀ q))
    have h2 := mul_le_mul (ha s q).1 (hb s q).2 (norm_nonneg _) (hA₀ q)
    convert add_le_add h1 h2 using 1; ring

include hε hy hα hβ hwidth hw hv in
theorem density_integrability (k : ℕ) (s : ℝ) :
    Integrable (density ε y α β w v b d P Q k s) ∧
      Integrable (densityDerivative ε y α β w v b d P Q k s) := by
  obtain ⟨D,hD,_,hb⟩ := common_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k
  obtain ⟨hc,hd⟩ := density_continuity ε y α β w v b d P Q hε hy hw hv k
  refine ⟨hD.mono' (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q => (hb s q).1)), ?_⟩
  apply ((hD.const_mul 2).const_mul ‖clockSlope ε y s‖).mono'
    (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun q => (hb s q).2)

include hε hy hα hβ hwidth hw hv in
theorem pair_derivative (k : ℕ) (s : ℝ) :
    HasDerivAt (pairIntegral ε y α β w v b d P Q k) (pairDerivative ε y α β w v b d P Q k s) s := by
  obtain ⟨D,hD,hD₀,hb⟩ := common_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k
  obtain ⟨hc,hd⟩ := density_continuity ε y α β w v b d P Q hε hy hw hv k
  obtain ⟨M,_,hm⟩ := KFCausalTransverseClockDifferentiation.continuous_local_bound
    (clockSlope ε y) (KFCausalReciprocalNeutralClockDerivative.clockSlope_continuous ε y hε hy) s
  have he := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := density ε y α β w v b d P Q k) (F' := densityDerivative ε y α β w v b d P Q k)
    (bound := fun q => M*(2*D q))
    (Icc_mem_nhds (by linarith : s-1<s) (by linarith : s<s+1))
    (Filter.Eventually.of_forall (fun t =>
      (hc.comp ((continuous_const : Continuous (fun _ : Transverse => t)).prodMk continuous_id)).aestronglyMeasurable))
    (density_integrability ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k s).1
    (hd.comp ((continuous_const : Continuous (fun _ : Transverse => s)).prodMk continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q t ht => (hb t q).2.trans
      (mul_le_mul_of_nonneg_right (hm t ht) (mul_nonneg (by norm_num) (hD₀ q)))))
    ((hD.const_mul 2).const_mul M)
    (Filter.Eventually.of_forall (fun q t _ =>
      (KFCausalReciprocalNeutralClockEnvelope.curve_derivative ε y α β w b P k t q hε hy (by linarith)).star.mul
        (KFCausalReciprocalNeutralClockEnvelope.curve_derivative ε y α β v d Q k t q hε hy (by linarith))))
  exact he.2

include hε hy hα hβ hwidth hw hv in
theorem pair_bounds (k : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s,
    ‖pairIntegral ε y α β w v b d P Q k s‖ ≤ M ∧
      ‖pairDerivative ε y α β w v b d P Q k s‖ ≤ ‖clockSlope ε y s‖*(2*M) := by
  obtain ⟨D,hD,hD₀,hb⟩ := common_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k
  refine ⟨∫ q, D q,integral_nonneg hD₀,?_⟩
  intro s
  constructor
  · exact norm_integral_le_of_norm_le hD (Filter.Eventually.of_forall (fun q => (hb s q).1))
  · have he := norm_integral_le_of_norm_le ((hD.const_mul 2).const_mul ‖clockSlope ε y s‖)
      (Filter.Eventually.of_forall (fun q => (hb s q).2))
    simpa only [integral_const_mul] using he

include hε hy hα hβ hwidth hw hv in
theorem actual_eq_sum (s : ℝ) : actual ε y α β w v b d P Q s =
    pairIntegral ε y α β w v b d P Q 0 s+
      pairIntegral ε y α β w v b d P Q 1 s/2+pairIntegral ε y α β w v b d P Q 2 s/4 := by
  have hi (k : ℕ) := (density_integrability ε y α β w v b d P Q hε hy hα hβ hwidth hw hv k s).1
  have he := integral_add ((hi 0).add ((hi 1).div_const 2)) ((hi 2).div_const 4)
  simp only [Pi.add_apply] at he
  unfold actual KFCausalReciprocalNeutralKernel.kernel
  simp_rw [KFCausalReciprocalNeutralSliceIntegrability.density_decomposition]
  change (∫ q, density ε y α β w v b d P Q 0 s q+
    density ε y α β w v b d P Q 1 s q/2+density ε y α β w v b d P Q 2 s q/4) = _
  rw [he,integral_add (hi 0) ((hi 1).div_const 2),integral_div,integral_div]
  rfl

include hε hy hα hβ hwidth hw hv in
theorem actual_derivative_eq (s : ℝ) : deriv (actual ε y α β w v b d P Q) s =
    pairDerivative ε y α β w v b d P Q 0 s+
      pairDerivative ε y α β w v b d P Q 1 s/2+pairDerivative ε y α β w v b d P Q 2 s/4 := by
  have he : actual ε y α β w v b d P Q = fun t => pairIntegral ε y α β w v b d P Q 0 t+
      pairIntegral ε y α β w v b d P Q 1 t/2+pairIntegral ε y α β w v b d P Q 2 t/4 :=
    funext (actual_eq_sum ε y α β w v b d P Q hε hy hα hβ hwidth hw hv)
  rw [he]
  exact (((pair_derivative ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 0 s).add
    ((pair_derivative ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 1 s).div_const 2)).add
    ((pair_derivative ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 2 s).div_const 4)).deriv

include hε hy hα hβ hwidth hw hv in
theorem actual_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ s,
    ‖actual ε y α β w v b d P Q s‖ ≤ M ∧
      ‖deriv (actual ε y α β w v b d P Q) s‖ ≤ ‖clockSlope ε y s‖*(2*M) := by
  obtain ⟨A,hA,ha⟩ := pair_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 0
  obtain ⟨B,hB,hb⟩ := pair_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 1
  obtain ⟨D,hD,hd⟩ := pair_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv 2
  refine ⟨A+B/2+D/4,by positivity,?_⟩
  intro s
  rw [actual_eq_sum ε y α β w v b d P Q hε hy hα hβ hwidth hw hv,
    actual_derivative_eq ε y α β w v b d P Q hε hy hα hβ hwidth hw hv]
  have hn (x z t : ℂ) : ‖x+z/2+t/4‖ ≤ ‖x‖+‖z‖/2+‖t‖/4 := by
    calc
      _ ≤ ‖x+z/2‖+‖t/4‖ := norm_add_le _ _
      _ ≤ (‖x‖+‖z/2‖)+‖t/4‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp only [norm_div]; norm_num
  constructor
  · exact (hn _ _ _).trans (by linarith [(ha s).1,(hb s).1,(hd s).1])
  · exact (hn _ _ _).trans (by nlinarith [(ha s).2,(hb s).2,(hd s).2])

include hε hy hα hβ hwidth hw hv in
theorem normalized_derivative_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ s,
    ‖actual ε y α β w v b d P Q s‖ ≤ M ∧
      ‖deriv (actual ε y α β w v b d P Q) s/(clock ε s:ℂ)‖ ≤ (4/ε)*M := by
  obtain ⟨M,hM,hm⟩ := actual_bounds ε y α β w v b d P Q hε hy hα hβ hwidth hw hv
  refine ⟨M,hM,fun s => ⟨(hm s).1,?_⟩⟩
  have hc : (clock ε s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  have he : clockSlope ε y s/(clock ε s:ℂ) = KFCausalGaussianResponseIntegrability.relativeInverse ε y s := by
    unfold clockSlope KFCausalGaussianResponseIntegrability.relativeInverse
    field_simp
  calc
    _ ≤ (‖clockSlope ε y s‖*(2*M))/‖(clock ε s:ℂ)‖ := by
      rw [norm_div]; exact div_le_div_of_nonneg_right (hm s).2 (norm_nonneg _)
    _ = ‖KFCausalGaussianResponseIntegrability.relativeInverse ε y s‖*(2*M) := by
      rw [← he,norm_div]; ring
    _ ≤ (2/ε)*(2*M) := mul_le_mul_of_nonneg_right
      (KFCausalGaussianResponseIntegrability.relativeInverse_bound ε y s hε hy) (by positivity)
    _ = _ := by ring

#print axioms density_continuity
#print axioms common_bounds
#print axioms density_integrability
#print axioms pair_derivative
#print axioms pair_bounds
#print axioms actual_eq_sum
#print axioms actual_derivative_eq
#print axioms actual_bounds
#print axioms normalized_derivative_bounds
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralCrossBounds
