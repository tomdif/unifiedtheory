/- The full maximal physical standing-charge domain in circular coordinates.
The converse follows from closedness and convergent finite-mode expansions,
not from an unproved interchange of differentiation and an infinite series. -/
import UnifiedTheory.Audit.KFCausalCircularChargeTransform

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCircularChargeDomain
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalHermiteProductBasis (Index)
open KFCausalEuclideanProductCoordinates (BlockHilbert)
open KFCausalJointHermiteFourierTransform (Coefficients)
open KFCausalCircularChargeTransform
open KFCausalFourCircularChargeBasis (charge)
open KFCausalStandingChargeOperator (standingCharge standingCharge_graph standingCharge_closed)

variable (h : ℝ) (hh : h ≠ 0) (b : ℝ) (hb : 0 < b)
local notation "W" => transform h hh b hb
local notation "Q" => standingCharge h hh

theorem graph_coefficient (f g : Hilbert) (hfg : (f,g) ∈ (Q).graph) (i : Index) :
    W g i = (charge i:ℂ) • W f i := by
  let L : Hilbert →L[ℂ] BlockHilbert 2 :=
    (KFCausalProductHilbertExpansion.lpCoordinate i).comp
      (W).toContinuousLinearEquiv.toContinuousLinearMap
  have hd := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((standingCharge_graph h hh f g).mp hfg)
  change HasDerivAt (fun θ => W (KFCausalPhysicalCircleAction.action h hh θ f) i)
    (W (Complex.I • g) i) 0 at hd
  have he : HasDerivAt (fun θ => KFCausalCircularChargeBasis.phase (charge i) θ • W f i)
      (Complex.I • W g i) 0 := by
    simpa only [action_diagonal,map_smul] using hd
  have hv := he.unique ((phase_derivative (charge i)).smul_const (W f i))
  have hc := congrArg (fun v : BlockHilbert 2 => (-Complex.I) • v) hv
  simpa only [smul_smul,← mul_assoc,neg_mul,Complex.I_mul_I,neg_neg,one_mul,one_smul] using hc

/-- Both directions on the maximal graph of the original physical operator. -/
theorem graph_iff (f g : Hilbert) : (f,g) ∈ (Q).graph ↔
    ∀ i : Index, W g i = (charge i:ℂ) • W f i := by
  constructor
  · exact fun hfg i => graph_coefficient h hh b hb f g hfg i
  · intro hg
    have hm (i : Index) :
        (packet h hh b hb i (W f i),packet h hh b hb i (W g i)) ∈ (Q).graph := by
      rw [hg i,packet_smul]
      exact packet_charge_graph h hh b hb i (W f i)
    have hs := (reconstruction h hh b hb f).prodMk_nhds (reconstruction h hh b hb g)
    exact (standingCharge_closed h hh).mem_of_tendsto hs
      (Filter.Eventually.of_forall (fun s : Finset Index => by
        simpa only [← prod_mk_sum] using (Q).graph.sum_mem (fun i (_ : i ∈ s) => hm i)))

theorem domain_iff (f : Hilbert) : f ∈ (Q).domain ↔
    Memℓp (fun i : Index => (charge i:ℂ) • W f i) 2 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g,hg⟩
    have he := (graph_iff h hh b hb f g).mp hg
    have hm := lp.memℓp (W g)
    change Memℓp (fun i => W g i) 2 at hm
    simpa only [he] using hm
  · intro hf
    let G : Coefficients := ⟨(fun i => (charge i:ℂ) • W f i),hf⟩
    refine ⟨(W).symm G,(graph_iff h hh b hb f _).mpr ?_⟩
    intro i
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- The explicit weighted square-summability condition, with spectator L2 norms. -/
theorem domain_iff_summable (f : Hilbert) : f ∈ (Q).domain ↔
    Summable (fun i : Index => (charge i:ℝ)^2*‖W f i‖^2) := by
  rw [domain_iff h hh b hb,memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,norm_smul,mul_pow,
    Complex.norm_intCast,Int.cast_abs,Real.norm_eq_abs,sq_abs]

theorem zero_sector_iff (f : Hilbert) : f ∈ KFCausalStandingChargeOperator.zeroSector h hh ↔
    ∀ i : Index, charge i ≠ 0 → W f i = 0 := by
  rw [← KFCausalStandingChargeOperator.standingCharge_zero_iff,graph_iff h hh b hb]
  simp only [map_zero]
  change (∀ i : Index, (0:BlockHilbert 2) = (charge i:ℂ) • W f i) ↔ _
  constructor
  · intro hf i hi
    exact (smul_eq_zero.mp (hf i).symm).resolve_left (Int.cast_ne_zero.mpr hi)
  · intro hf i
    by_cases hi : charge i = 0
    · simp [hi]
    · rw [hf i hi,smul_zero]

#print axioms graph_coefficient
#print axioms graph_iff
#print axioms domain_iff
#print axioms domain_iff_summable
#print axioms zero_sector_iff
end
end UnifiedTheory.Audit.KFCausalCircularChargeDomain
