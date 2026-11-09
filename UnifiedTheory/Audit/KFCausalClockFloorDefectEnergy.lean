/- The positive clock makes norm-defect recovery costly. For a normalized
state in the actual half-clock domain, epsilon <= ||sqrt(C) f||^2 ||D f||.
Thus the clock energy cannot remain uniformly bounded as defect tends to
zero at fixed positive epsilon. This is a domain-explicit estimate, not
an assertion that every L2 state has finite clock energy. -/
import UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
import UnifiedTheory.Audit.KFCausalClockFloorClockHalf
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf

theorem half_inverse_pairing (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) :
    inner ℂ g (inverseAction ε hε f) = inner ℂ f f := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(clockHalf_graph ε f g).mp hg, inverseAction_coe ε hε f] with x hx hi
  rw [hx,hi]
  change inner ℂ ((halfWeight ε x : ℂ) • f x) ((halfWeight ε x : ℂ)⁻¹ • f x) = _
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (halfWeight_positive ε hε x).ne'), one_mul]

theorem inverse_defect_pairing (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    (ε : ℂ) * inner ℂ (inverseAction ε hε f) (inverseAction ε hε f) =
      inner ℂ f (defectOperator ε hε f) := by
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [inverseAction_coe ε hε f, defectOperator_coe ε hε f] with x hi hD
  rw [hi,hD]
  have hs : (halfWeight ε x)^2 = Real.exp x.1+ε := by
    exact Real.sq_sqrt (by positivity)
  have he : ε * ((halfWeight ε x)⁻¹)^2 = defect ε x.1 := by
    rw [inv_pow, hs]
    rfl
  have hc : (ε : ℂ) * ((halfWeight ε x : ℂ)⁻¹)^2 = (defect ε x.1 : ℂ) := by
    exact_mod_cast he
  change (ε : ℂ) * inner ℂ ((halfWeight ε x : ℂ)⁻¹ • f x)
    ((halfWeight ε x : ℂ)⁻¹ • f x) = inner ℂ (f x) ((defect ε x.1 : ℂ) • f x)
  rw [inner_smul_left, inner_smul_right, inner_smul_right]
  simp only [map_inv₀, Complex.conj_ofReal]
  calc
    _ = ((ε:ℂ) * ((halfWeight ε x : ℂ)⁻¹)^2) * inner ℂ (f x) (f x) := by ring
    _ = _ := by rw [hc]

theorem inverse_norm_defect_bound (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ε * ‖inverseAction ε hε f‖^2 ≤ ‖f‖ * ‖defectOperator ε hε f‖ := by
  have h := congrArg norm (inverse_defect_pairing ε hε f)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_coe_norm] at h
  exact h.trans_le (norm_inner_le_norm _ _)

theorem clock_defect_tradeoff (ε : ℝ) (hε : 0 < ε) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph) (hf : ‖f‖ = 1) :
    ε ≤ ‖g‖^2 * ‖defectOperator ε hε f‖ := by
  have hp := congrArg norm (half_inverse_pairing ε hε f g hg)
  rw [inner_self_eq_norm_sq_to_K, hf] at hp
  norm_num at hp
  have hlow : 1 ≤ ‖g‖ * ‖inverseAction ε hε f‖ :=
    hp.symm.trans_le (norm_inner_le_norm _ _)
  have hb := inverse_norm_defect_bound ε hε f
  rw [hf,one_mul] at hb
  have hsq : 1 ≤ ‖g‖^2 * ‖inverseAction ε hε f‖^2 := by
    nlinarith [sq_nonneg (‖g‖ * ‖inverseAction ε hε f‖ - 1)]
  have h1 := mul_le_mul_of_nonneg_left hsq hε.le
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg ‖g‖)
  nlinarith

theorem no_bounded_clock_energy_defect_limit {ι : Type*} (l : Filter ι) [l.NeBot]
    (ε : ℝ) (hε : 0 < ε) (f g : ι → Hilbert) (K : ℝ)
    (hg : ∀ i, (f i,g i) ∈ (clockHalf ε).graph) (hf : ∀ i, ‖f i‖ = 1)
    (hK : ∀ i, ‖g i‖ ≤ K) :
    ¬Tendsto (fun i => ‖defectOperator ε hε (f i)‖) l (𝓝 0) := by
  intro hlim
  have hb (i : ι) : ε ≤ K^2 * ‖defectOperator ε hε (f i)‖ := by
    apply (clock_defect_tradeoff ε hε (f i) (g i) (hg i) (hf i)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hK i) 2
  have he : ε ≤ 0 := by
    have ht : Tendsto (fun i => K^2 * ‖defectOperator ε hε (f i)‖) l (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (K^2)
    exact ge_of_tendsto ht (Eventually.of_forall hb)
  exact hε.not_ge he

theorem defect_limit_forces_clock_norm_atTop {ι : Type*} (l : Filter ι)
    (ε : ℝ) (hε : 0 < ε) (f g : ι → Hilbert)
    (hg : ∀ i, (f i,g i) ∈ (clockHalf ε).graph) (hf : ∀ i, ‖f i‖ = 1)
    (hlim : Tendsto (fun i => ‖defectOperator ε hε (f i)‖) l (𝓝 0)) :
    Tendsto (fun i => ‖g i‖) l atTop := by
  apply tendsto_atTop.2
  intro K
  let M : ℝ := max K 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right K 0]
  have hKM : K < M := by dsimp [M]; linarith [le_max_left K 0]
  have hd : 0 < ε/M^2 := div_pos hε (sq_pos_of_pos hM)
  filter_upwards [hlim.eventually (gt_mem_nhds hd)] with i hi
  by_contra hK
  have hgi : ‖g i‖ ≤ M := (lt_of_not_ge hK).le.trans hKM.le
  have hb := (clock_defect_tradeoff ε hε (f i) (g i) (hg i) (hf i)).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgi 2) (norm_nonneg _))
  have hlt := (lt_div_iff₀ (sq_pos_of_pos hM)).mp hi
  nlinarith

#print axioms half_inverse_pairing
#print axioms inverse_defect_pairing
#print axioms inverse_norm_defect_bound
#print axioms clock_defect_tradeoff
#print axioms no_bounded_clock_energy_defect_limit
#print axioms defect_limit_forces_clock_norm_atTop

end
end UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy
