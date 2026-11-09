/- Transverse boundaries for the actual displaced charge-orbit sources.
The product of two independent normalized angle measures is used, so
interference between distinct charge angles is retained. Bounds are for
fixed packet data, not uniform over states or the semiclassical parameter. -/
import UnifiedTheory.Audit.KFCausalIntegratedGaussianBoundary
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargeGaussianBoundary
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter parameter_period)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedSources (source amplitude)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedParameterBounds
  (source_curve_continuous amplitude_curve_continuous)
open UnifiedTheory.Audit.KFCausalGaussianSliceEnvelope (slice squareConstant)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def orbitSource (h : ℝ) (q k : Joint 2 4) (θ : ℝ) : Fin 5 → ℂ :=
  source h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)

def orbitAmplitude (h : ℝ) (q k : Joint 2 4) (θ : ℝ) : ℂ :=
  amplitude h (parameter (2*Real.pi*θ) q) (parameter (2*Real.pi*θ) k)

private theorem source_continuous (h : ℝ) (q k : Joint 2 4) : Continuous (orbitSource h q k) :=
  (source_curve_continuous h q k).comp (continuous_const.mul continuous_id)

private theorem amplitude_continuous (h : ℝ) (q k : Joint 2 4) : Continuous (orbitAmplitude h q k) :=
  (amplitude_curve_continuous h q k).comp (continuous_const.mul continuous_id)

theorem orbit_square_bound (ε y α β h : ℝ) (q k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ,
      squareConstant ε y α β (orbitSource h q k θ) (orbitAmplitude h q k θ) l ≤ M := by
  let f : ℝ → ℝ := fun θ => squareConstant ε y α β
    (source h (parameter θ q) (parameter θ k)) (amplitude h (parameter θ q) (parameter θ k)) l
  have hc : Continuous f := by
    have hs := source_curve_continuous h q k
    have ha := amplitude_curve_continuous h q k
    unfold f squareConstant KFCausalGaussianSliceEnvelope.factor
      KFCausalClockFloorCoherentBounds.sourceConstant KFCausalClockFloorCoherentBounds.sourceSize
    fun_prop
  have hp : Function.Periodic f (2*Real.pi) := by
    intro θ
    dsimp only [f]
    rw [parameter_period,parameter_period]
  obtain ⟨M,hM⟩ := (hp.compact_of_continuous (by positivity) hc).bddAbove
  refine ⟨M,?_,fun θ => hM ⟨2*Real.pi*θ,rfl⟩⟩
  exact (KFCausalGaussianSliceEnvelope.squareConstant_nonnegative ε y α β
    (source h (parameter 0 q) (parameter 0 k)) (amplitude h (parameter 0 q) (parameter 0 k)) l).trans
      (hM ⟨0,rfl⟩)

private theorem family_slice_continuous {X : Type*} [TopologicalSpace X]
    (ε y α β : ℝ) (b : X → Fin 5 → ℂ) (C : X → ℂ) (hb : Continuous b) (hC : Continuous C)
    (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (s : ℝ) :
    Continuous (fun z : X × Transverse => slice ε y α β (b z.1) (C z.1) l n s z.2) := by
  have hp (i : Fin 5) : Continuous (fun z : X × Transverse =>
      KFCausalRelativeGaussianDifferential.position (KFCausalClockFloorRelativeShift.scale ε y s) z.2 i) := by
    unfold KFCausalRelativeGaussianDifferential.position
    split_ifs <;> fun_prop
  have hs (i : Fin 5) : Continuous (fun z : X × Transverse => b z.1 i) :=
    (continuous_apply i).comp (hb.comp continuous_fst)
  unfold slice KFCausalGaussianKernelResponse.transverse
    KFCausalRelativeGaussianDifferential.profile KFCausalRelativeGaussianDifferential.exponent
  simp only [one_mul]
  exact ((Complex.continuous_ofReal.comp (l.continuous.comp continuous_snd)).pow n.val).mul
    ((hC.comp continuous_fst).mul
      ((continuous_finset_sum _ (fun i _ => (hs i).mul (hp i))).sub
        (continuous_finset_sum _ (fun i _ => continuous_const.mul ((hp i).pow 2)))).cexp)

variable (ε y α β α' β' h : ℝ) (q k q' k' : Joint 2 4)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "bs" => orbitSource h q k
local notation "cs" => orbitSource h q' k'
local notation "As" => orbitAmplitude h q k
local notation "Ds" => orbitAmplitude h q' k'
local notation "ν" => angleMeasure.prod angleMeasure
local notation "μ" => Measure.prod (Measure.prod angleMeasure angleMeasure) (volume : Measure Transverse)

def orbitBoundary (a a' p p' s : ℝ) (z : (ℝ × ℝ) × Transverse) : ℂ :=
  KFCausalIntegratedGaussianBoundary.boundary ε y α β α' β'
    (bs z.1.1) (cs z.1.2) (As z.1.1) (Ds z.1.2) l n a a' p p' s z.2

def orbitDifference (a a' p p' R : ℝ) (z : (ℝ × ℝ) × Transverse) : ℂ :=
  KFCausalIntegratedGaussianBoundary.intervalDifference ε y α β α' β'
    (bs z.1.1) (cs z.1.2) (As z.1.1) (Ds z.1.2) l n a a' p p' R z.2

local notation "B" => orbitBoundary ε y α β α' β' h q k q' k' l n
local notation "F" => orbitDifference ε y α β α' β' h q k q' k' l n

theorem orbit_cost_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ θ φ,
    KFCausalIntegratedGaussianBoundary.cost ε y α β α' β' (bs θ) (cs φ) (As θ) (Ds φ) l ≤ M := by
  obtain ⟨Mi,hi,hMi⟩ := orbit_square_bound ε y α β h q k l
  obtain ⟨Mj,hj,hMj⟩ := orbit_square_bound ε y α' β' h q' k' l
  refine ⟨(Mi+Mj)/2,by positivity,fun θ φ => ?_⟩
  unfold KFCausalIntegratedGaussianBoundary.cost
  linarith [hMi θ,hMj φ]

theorem orbitBoundary_continuous (a a' p p' s : ℝ) : Continuous (B a a' p p' s) := by
  have hi := family_slice_continuous ε y α β (fun θ : ℝ × ℝ => bs θ.1) (fun θ : ℝ × ℝ => As θ.1)
    ((source_continuous h q k).comp continuous_fst) ((amplitude_continuous h q k).comp continuous_fst) l n s
  have hj := family_slice_continuous ε y α' β' (fun θ : ℝ × ℝ => cs θ.2) (fun θ : ℝ × ℝ => Ds θ.2)
    ((source_continuous h q' k').comp continuous_snd) ((amplitude_continuous h q' k').comp continuous_snd) l n s
  exact (hi.star.mul hj).mul continuous_const

variable (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hα' : 0 < α') (hβ' : 0 < β') (hw' : 32*β' ≤ α')

include hε hy hα hβ hw hα' hβ' hw' in
private theorem boundary_slice_bound (M : ℝ)
    (hM : ∀ θ φ, KFCausalIntegratedGaussianBoundary.cost ε y α β α' β'
      (bs θ) (cs φ) (As θ) (Ds φ) l ≤ M) (a a' p p' s : ℝ) (θ : ℝ × ℝ) :
    (∫ x, ‖B a a' p p' s (θ,x)‖) ≤ M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ :=
  (KFCausalIntegratedGaussianBoundary.boundary_norm_bound ε y α β α' β'
    (bs θ.1) (cs θ.2) (As θ.1) (Ds θ.2) l n hε hy hα hβ hw hα' hβ' hw' a a' p p' s).trans
      (mul_le_mul_of_nonneg_right (hM θ.1 θ.2) (norm_nonneg _))

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitBoundary_integrable (a a' p p' s : ℝ) : Integrable (B a a' p p' s) μ := by
  obtain ⟨M,_,hM⟩ := orbit_cost_bound ε y α β α' β' h q k q' k' l
  have hm : AEStronglyMeasurable (B a a' p p' s) μ :=
    (orbitBoundary_continuous ε y α β α' β' h q k q' k' l n a a' p p' s).aestronglyMeasurable
  apply (integrable_prod_iff hm).mpr
  refine ⟨Eventually.of_forall (fun θ =>
    KFCausalIntegratedGaussianBoundary.boundary_integrable ε y α β α' β'
      (bs θ.1) (cs θ.2) (As θ.1) (Ds θ.2) l n hε hy hα hβ hw hα' hβ' hw' a a' p p' s),?_⟩
  apply (integrable_const (M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖)).mono'
    hm.norm.integral_prod_right'
  filter_upwards [] with θ
  have hn : 0 ≤ ∫ x : Transverse, ‖B a a' p p' s (θ,x)‖ :=
    integral_nonneg (fun x => norm_nonneg (B a a' p p' s (θ,x)))
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using
    boundary_slice_bound ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' M hM a a' p p' s θ

include hε hy hα hβ hw hα' hβ' hw' in
private theorem boundary_product_bound (M : ℝ)
    (hM : ∀ θ φ, KFCausalIntegratedGaussianBoundary.cost ε y α β α' β'
      (bs θ) (cs φ) (As θ) (Ds φ) l ≤ M) (a a' p p' s : ℝ) :
    (∫ z, ‖B a a' p p' s z‖ ∂μ) ≤ M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ := by
  have hi := orbitBoundary_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' s
  rw [integral_prod _ hi.norm]
  calc
    _ ≤ ∫ _ : ℝ × ℝ, M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ ∂ν :=
      integral_mono hi.integral_norm_prod_left (integrable_const _)
        (boundary_slice_bound ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' M hM a a' p p' s)
    _ = _ := by simp

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitBoundary_norm_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ a a' p p' s,
    (∫ z, ‖B a a' p p' s z‖ ∂μ) ≤ M*‖KFCausalClockBoundaryDecay.boundary ε a a' p p' y s‖ := by
  obtain ⟨M,h0,hM⟩ := orbit_cost_bound ε y α β α' β' h q k q' k' l
  exact ⟨M,h0,boundary_product_bound ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' M hM⟩

include hε hy hα hβ hw hα' hβ' hw' in
private theorem boundary_norm_limit (a a' p p' : ℝ) (f : Filter ℝ)
    (hb : Tendsto (KFCausalClockBoundaryDecay.boundary ε a a' p p' y) f (𝓝 0)) :
    Tendsto (fun s => ∫ z, ‖B a a' p p' s z‖ ∂μ) f (𝓝 0) := by
  obtain ⟨M,_,hM⟩ := orbitBoundary_norm_bound ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw'
  apply squeeze_zero (fun s => integral_nonneg (fun z => norm_nonneg _)) (hM a a' p p')
  simpa using hb.norm.const_mul M

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitBoundary_norm_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun s => ∫ z, ‖B a a' p p' s z‖ ∂μ) atTop (𝓝 0) :=
  boundary_norm_limit ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' atTop
    (KFCausalClockBoundaryDecay.boundary_atTop ε a a' p p' y hε ha hy)

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitBoundary_norm_atBot (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun s => ∫ z, ‖B a a' p p' s z‖ ∂μ) atBot (𝓝 0) :=
  boundary_norm_limit ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' atBot
    (KFCausalClockBoundaryDecay.boundary_atBot ε a a' p p' y hε ha hy)

include hε hy in
theorem orbitDifference_eq (a a' p p' R : ℝ) (z : (ℝ × ℝ) × Transverse) :
    F a a' p p' R z = B a a' p p' R z-B a a' p p' (-R) z :=
  KFCausalIntegratedGaussianBoundary.intervalDifference_eq ε y α β α' β'
    (bs z.1.1) (cs z.1.2) (As z.1.1) (Ds z.1.2) l n hε hy a a' p p' R z.2

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitDifference_integrable (a a' p p' R : ℝ) : Integrable (F a a' p p' R) μ := by
  change Integrable (fun z => F a a' p p' R z) μ
  simp_rw [orbitDifference_eq ε y α β α' β' h q k q' k' l n hε hy]
  exact (orbitBoundary_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' R).sub
    (orbitBoundary_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' (-R))

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbitDifference_norm_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R => ∫ z, ‖F a a' p p' R z‖ ∂μ) atTop (𝓝 0) := by
  have ht := (orbitBoundary_norm_atTop ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha).add
    ((orbitBoundary_norm_atBot ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha).comp
      tendsto_neg_atTop_atBot)
  simp only [add_zero] at ht
  apply squeeze_zero (fun R => integral_nonneg (fun z => norm_nonneg _)) _ ht
  intro R
  have hi := orbitBoundary_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' R
  have hj := orbitBoundary_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' (-R)
  simp_rw [orbitDifference_eq ε y α β α' β' h q k q' k' l n hε hy]
  exact (integral_mono (hi.sub hj).norm (hi.norm.add hj.norm) (fun z => norm_sub_le _ _)).trans_eq
    (integral_add hi.norm hj.norm)

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbit_integrated_difference_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R => ∫ z, F a a' p p' R z ∂μ) atTop (𝓝 0) :=
  squeeze_zero_norm (fun _ => norm_integral_le_integral_norm _)
    (orbitDifference_norm_atTop ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha)

include hε hy hα hβ hw hα' hβ' hw' in
theorem orbit_iterated_difference_atTop (a a' p p' : ℝ) (ha : 0 < a+a') :
    Tendsto (fun R => ∫ θ, (∫ φ, (∫ x : Transverse, F a a' p p' R ((θ,φ),x)) ∂angleMeasure) ∂angleMeasure)
      atTop (𝓝 0) := by
  have he (R : ℝ) : (∫ z, F a a' p p' R z ∂μ) =
      ∫ θ, (∫ φ, (∫ x : Transverse, F a a' p p' R ((θ,φ),x)) ∂angleMeasure) ∂angleMeasure := by
    have hi := orbitDifference_integrable ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' R
    rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simpa only [he] using
    orbit_integrated_difference_atTop ε y α β α' β' h q k q' k' l n hε hy hα hβ hw hα' hβ' hw' a a' p p' ha

#print axioms orbit_square_bound
#print axioms orbit_cost_bound
#print axioms orbitBoundary_continuous
#print axioms orbitBoundary_integrable
#print axioms orbitBoundary_norm_bound
#print axioms orbitBoundary_norm_atTop
#print axioms orbitBoundary_norm_atBot
#print axioms orbitDifference_eq
#print axioms orbitDifference_integrable
#print axioms orbitDifference_norm_atTop
#print axioms orbit_integrated_difference_atTop
#print axioms orbit_iterated_difference_atTop
end
end UnifiedTheory.Audit.KFCausalChargeGaussianBoundary
