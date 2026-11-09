/- A bounded transverse-dependent analytic family preserves the entire natural
half-exponential domain. The graph identity is proved on the actual Gaussian
core and extended by closedness, rather than assumed as a domain hypothesis. -/
import UnifiedTheory.Audit.KFCausalGaussianStripFamily
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGraph
import UnifiedTheory.Audit.KFCausalContractiveMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalGaussianStripFamily
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable (F : ℂ → TailSpace → ℂ) (d M : ℝ)
  (hF : ∀ z q, |q.im| ≤ d → AnalyticAt ℂ (fun q => F q z) q)
  (hC : ∀ y, |y| ≤ d → Continuous (fun w : ℝ × TailSpace => F ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2))
  (hM : 0 ≤ M) (hB : ∀ q, |q.im| ≤ d → ∀ z, ‖F q z‖ ≤ M)

def physicalState (v : Space) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) : Hilbert :=
  (straightening ε hε).symm ((spectralLine_memLp F v d M hC hM hB y hy).toLp _)

theorem physicalState_coe (v : Space) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) :
    straightening ε hε (physicalState F d M hC hM hB v ε hε y hy) =ᵐ[volume] spectralLine F v y := by
  change straightening ε hε ((straightening ε hε).symm _) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (spectralLine_memLp F v d M hC hM hB y hy).coeFn_toLp

theorem physicalState_fourier (v : Space) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) :
    coupledFourier ε hε (physicalState F d M hC hM hB v ε hε y hy) =ᵐ[volume] 𝓕 (spectralLine F v y) := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (straightening ε hε ((straightening ε hε).symm _)) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact fourier_toLp_coe _ (spectralLine_integrable F v d M hC hB y hy)
    (spectralLine_memLp F v d M hC hM hB y hy)

include hF in
theorem physicalState_half_graph (v : Space) (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (h0 : |(0:ℝ)| ≤ d) (hs : |-hbar/2| ≤ d) :
    (physicalState F d M hC hM hB v ε hε 0 h0,
      physicalState F d M hC hM hB v ε hε (-hbar/2) hs) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  apply (longitudinal_exponential_graph ε hε hbar (1/2) _ _).mpr
  filter_upwards [physicalState_fourier F d M hC hM hB v ε hε 0 h0,
    physicalState_fourier F d M hC hM hB v ε hε (-hbar/2) hs] with k hk hl
  rw [hk,hl,← full_fourier_shift F v d M hF hC hM hB hbar hs k]
  congr 3
  unfold KFCausalEuclideanGaussianCore.exponentialWeight KFCausalClockFloorFourierMultiplier.symbol
  ring

def symbol (y : ℝ) (x : Space) : ℂ := F ((x 0:ℂ)+(y:ℂ)*Complex.I) (tail x)

include hC in
theorem symbol_continuous (y : ℝ) (hy : |y| ≤ d) : Continuous (symbol F y) :=
  (hC y hy).comp ((by fun_prop : Continuous (fun x : Space => x 0)).prodMk KFCausalGaussianStrip.tail_continuous)

include hB in
theorem symbol_bound (y : ℝ) (hy : |y| ≤ d) (x : Space) : ‖symbol F y x‖ ≤ M :=
  hB _ (by simpa using hy) _

include hM hB in
theorem normalized_symbol_bound (y : ℝ) (hy : |y| ≤ d) (x : Space) :
    ‖symbol F y x / (M+1:ℝ)‖ ≤ 1 := by
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < M+1)]
  apply (div_le_one (by linarith : 0 < M+1)).mpr
  linarith [symbol_bound F d M hB y hy x]

def frequencyOperator (y : ℝ) (hy : |y| ≤ d) : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  ((M+1:ℝ):ℂ) • multiplyL (fun x => symbol F y x / (M+1:ℝ))
    ((symbol_continuous F d hC y hy).div_const _).measurable
    (normalized_symbol_bound F d M hM hB y hy)

def physicalMultiplier (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) : Hilbert →L[ℂ] Hilbert :=
  ((straightening ε hε).symm : FrequencyHilbert →L[ℂ] Hilbert).comp
    ((frequencyOperator F d M hC hM hB y hy).comp (straightening ε hε : Hilbert →L[ℂ] FrequencyHilbert))

theorem frequencyOperator_coe (y : ℝ) (hy : |y| ≤ d) (f : FrequencyHilbert) :
    frequencyOperator F d M hC hM hB y hy f =ᵐ[volume] fun x => symbol F y x*f x := by
  filter_upwards [Lp.coeFn_smul ((M+1:ℝ):ℂ) (multiplyL (fun x => symbol F y x / (M+1:ℝ))
    ((symbol_continuous F d hC y hy).div_const _).measurable
    (normalized_symbol_bound F d M hM hB y hy) f),
    multiplyL_coe (fun x => symbol F y x / (M+1:ℝ))
      ((symbol_continuous F d hC y hy).div_const _).measurable
      (normalized_symbol_bound F d M hM hB y hy) f] with x hs hm
  change (((M+1:ℝ):ℂ) • multiplyL _ _ _ f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hm]
  have hn : ((M+1:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp

theorem physicalMultiplier_coe (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) (f : Hilbert) :
    straightening ε hε (physicalMultiplier F d M hC hM hB ε hε y hy f) =ᵐ[volume]
      fun x => symbol F y x*(straightening ε hε f) x := by
  change straightening ε hε ((straightening ε hε).symm _) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact frequencyOperator_coe F d M hC hM hB y hy _

theorem physicalMultiplier_norm (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d)
    (b : ℝ) (hb : ∀ x, ‖symbol F y x‖ ≤ b) (f : Hilbert) :
    ‖physicalMultiplier F d M hC hM hB ε hε y hy f‖ ≤ b*‖f‖ := by
  rw [← (straightening ε hε).norm_map (physicalMultiplier F d M hC hM hB ε hε y hy f),
    ← (straightening ε hε).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [physicalMultiplier_coe F d M hC hM hB ε hε y hy f] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

def unitState (v : Space) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) : Hilbert :=
  KFCausalClockFloorGaussianGraph.physicalState (fun _ => 1) v d 1 (fun _ _ => analyticAt_const)
    (by norm_num) (fun _ _ => by simp) ε hε y hy

theorem multiplier_unitState (v : Space) (ε : ℝ) (hε : 0 < ε) (y : ℝ) (hy : |y| ≤ d) :
    physicalMultiplier F d M hC hM hB ε hε y hy (unitState d v ε hε y hy) =
      physicalState F d M hC hM hB v ε hε y hy := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [physicalMultiplier_coe F d M hC hM hB ε hε y hy (unitState d v ε hε y hy),
    KFCausalClockFloorGaussianGraph.physicalState_coe (fun _ => 1) v d 1 (fun _ _ => analyticAt_const)
      (by norm_num) (fun _ _ => by simp) ε hε y hy,
    physicalState_coe F d M hC hM hB v ε hε y hy] with x hd hu hf
  change (straightening ε hε (unitState d v ε hε y hy)) x = _ at hu
  rw [hd,hu,hf]
  simp only [spectralLine,Function.comp_apply,euclideanSplit_apply,line,trial,
    KFCausalGaussianStrip.spectralLine,KFCausalGaussianStrip.line,KFCausalGaussianStrip.trial,
    symbol,one_mul,mul_assoc]

theorem unitState_zero (v : Space) (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (h0 : |(0:ℝ)| ≤ d) :
    unitState d v ε hε 0 h0 = (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1 :=
  KFCausalClockFloorGaussianGraph.physicalState_one_eq_packet ε hε hbar v d h0

theorem unitState_shift (v : Space) (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hs : |-hbar/2| ≤ d) :
    unitState d v ε hε (-hbar/2) hs = (KFCausalClockFloorGaussianCore.packet ε hε hbar v).2 := by
  have h0 : |(0:ℝ)| ≤ d := by simpa only [abs_zero] using (abs_nonneg (-hbar/2)).trans hs
  exact (longitudinalExponential ε hε hbar (1/2)).mem_graph_snd_inj'
    (KFCausalClockFloorGaussianGraph.physicalState_half_graph (fun _ => 1) v d 1 (fun _ _ => analyticAt_const)
      (by norm_num) (fun _ _ => by simp) ε hε hbar h0 hs)
    (KFCausalClockFloorGaussianCore.packet_mem_graph ε hε hbar v)
    (unitState_zero d v ε hε hbar h0)

include hF in
theorem packet_graph (v : Space) (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (h0 : |(0:ℝ)| ≤ d) (hs : |-hbar/2| ≤ d) :
    (physicalMultiplier F d M hC hM hB ε hε 0 h0 (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1,
      physicalMultiplier F d M hC hM hB ε hε (-hbar/2) hs (KFCausalClockFloorGaussianCore.packet ε hε hbar v).2) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph := by
  have hg := physicalState_half_graph F d M hF hC hM hB v ε hε hbar h0 hs
  rw [← multiplier_unitState F d M hC hM hB v ε hε 0 h0,
    ← multiplier_unitState F d M hC hM hB v ε hε (-hbar/2) hs,
    unitState_zero d v ε hε hbar h0,unitState_shift d v ε hε hbar hs] at hg
  exact hg

theorem graph_core_lift (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (S T : Hilbert →L[ℂ] Hilbert)
    (hp : ∀ v, (S (KFCausalClockFloorGaussianCore.packet ε hε hbar v).1,
      T (KFCausalClockFloorGaussianCore.packet ε hε hbar v).2) ∈
        (longitudinalExponential ε hε hbar (1/2)).graph)
    (f g : Hilbert) (hfg : (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph) :
    (S f,T g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph := by
  let P := S.prodMap T
  have hS : Submodule.span ℂ (Set.range (KFCausalClockFloorGaussianCore.packet ε hε hbar)) ≤
      (longitudinalExponential ε hε hbar (1/2)).graph.comap P.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact hp v
  have hc := Submodule.topologicalClosure_minimal _ hS
    ((longitudinal_exponential_closed ε hε hbar (1/2)).preimage P.continuous)
  exact hc ((KFCausalClockFloorGaussianCore.graph_core ε hε hbar).symm ▸ hfg)

include hF in
theorem graph_multiplier (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (h0 : |(0:ℝ)| ≤ d) (hs : |-hbar/2| ≤ d) (f g : Hilbert)
    (hfg : (f,g) ∈ (longitudinalExponential ε hε hbar (1/2)).graph) :
    (physicalMultiplier F d M hC hM hB ε hε 0 h0 f,
      physicalMultiplier F d M hC hM hB ε hε (-hbar/2) hs g) ∈
      (longitudinalExponential ε hε hbar (1/2)).graph :=
  graph_core_lift ε hε hbar _ _ (fun v => packet_graph F d M hF hC hM hB v ε hε hbar h0 hs) f g hfg

#print axioms physicalState_coe
#print axioms physicalState_fourier
#print axioms physicalState_half_graph
#print axioms symbol_continuous
#print axioms symbol_bound
#print axioms normalized_symbol_bound
#print axioms frequencyOperator_coe
#print axioms physicalMultiplier_coe
#print axioms physicalMultiplier_norm
#print axioms multiplier_unitState
#print axioms unitState_zero
#print axioms unitState_shift
#print axioms packet_graph
#print axioms graph_core_lift
#print axioms graph_multiplier

end
end UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph
