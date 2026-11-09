/- A surjective physical Hermite/Fourier transform with continuous clock and
neutral-frequency fibers. The actual charge action is identified by a
convergent, explicit charged-coordinate matrix; no diagonal charge labels or
Hamiltonian spectrum are assumed. -/
import UnifiedTheory.Audit.KFCausalHermiteProductBasis
import UnifiedTheory.Audit.KFCausalChargedSpectatorCoordinates
import UnifiedTheory.Audit.KFCausalStandingChargeOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalJointHermiteFourierTransform
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding (productState)
open KFCausalHermiteProductBasis (Index chargedBasis joinCoordinates)
open KFCausalProductHilbertExpansion (partialTransform partialTransform_product partialTransform_lift)
open KFCausalChargedSpectatorCoordinates (physicalCoordinates chargedAction chargedAction_coe flow)
open KFCausalEuclideanTensorUnitary (liftUnitary liftUnitary_product)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)

abbrev Coefficients := ℓ²(Index,BlockHilbert 2)

/-- The spectator coordinates are clock position and neutral Fourier frequency.
Mathlib's Fourier convention uses exp(-2*pi*i*xi*y); physical momentum is 2*pi*h*xi. -/
def neutralFourierBlock : BlockHilbert 2 ≃ₗᵢ[ℂ] BlockHilbert 2 :=
  (joinCoordinates 1 1).symm.trans
    ((KFCausalPartialFourier.rightFourier 1 1).trans (joinCoordinates 1 1))

def neutralFourier : ProductHilbert 4 2 ≃ₗᵢ[ℂ] ProductHilbert 4 2 :=
  liftUnitary 4 2 (LinearIsometryEquiv.refl ℂ _) neutralFourierBlock

theorem neutralFourier_product (f : BlockHilbert 4) (g : BlockHilbert 2) :
    neutralFourier (productState volume volume f g) =
      productState volume volume f (neutralFourierBlock g) := liftUnitary_product 4 2 _ _ f g

variable (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
local notation "B" => chargedBasis a b ha hb
local notation "T" => partialTransform 4 2 B

def transform : Hilbert ≃ₗᵢ[ℂ] Coefficients :=
  physicalCoordinates.trans (neutralFourier.trans T)

def packet (i : Index) (g : BlockHilbert 2) : Hilbert :=
  physicalCoordinates.symm (productState volume volume (B i) (neutralFourierBlock.symm g))

theorem transform_packet (i : Index) (g : BlockHilbert 2) :
    transform a b ha hb (packet a b ha hb i g) = lp.single 2 i g := by
  change T (neutralFourier (physicalCoordinates
    (physicalCoordinates.symm (productState volume volume (B i) (neutralFourierBlock.symm g))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,neutralFourier_product,
    LinearIsometryEquiv.apply_symm_apply,KFCausalProductHilbertExpansion.partialTransform_column]

theorem inverse_single (i : Index) (g : BlockHilbert 2) :
    (transform a b ha hb).symm (lp.single 2 i g) = packet a b ha hb i g := by
  apply (transform a b ha hb).injective
  rw [LinearIsometryEquiv.apply_symm_apply,transform_packet]

theorem reconstruction (f : Hilbert) :
    HasSum (fun i => packet a b ha hb i (transform a b ha hb f i)) f := by
  have hs := (transform a b ha hb).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum
    (lp.hasSum_single (by norm_num : (2:ENNReal) ≠ ⊤) (transform a b ha hb f))
  change HasSum (fun i => (transform a b ha hb).symm (lp.single 2 i (transform a b ha hb f i)))
    ((transform a b ha hb).symm (transform a b ha hb f)) at hs
  simpa only [inverse_single,LinearIsometryEquiv.symm_apply_apply] using hs

def coefficientAction (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : Coefficients ≃ₗᵢ[ℂ] Coefficients :=
  (T).symm.trans ((liftUnitary 4 2 (chargedAction c hc θ) (LinearIsometryEquiv.refl ℂ _)).trans T)

def chargeMatrix (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (i j : Index) : ℂ :=
  inner ℂ (B i) (chargedAction c hc θ (B j))

theorem chargeMatrix_integral (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (i j : Index) :
    chargeMatrix a b ha hb c hc θ i j =
      ∫ x : Block 4, star ((B i) x)*(B j) (flow c hc θ x) := by
  rw [chargeMatrix,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [chargedAction_coe c hc θ (B j)] with x hx
  rw [hx,RCLike.inner_apply']
  rfl

theorem coefficientAction_series (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : Coefficients) (i : Index) :
    HasSum (fun j => chargeMatrix a b ha hb c hc θ i j • f j)
      (coefficientAction a b ha hb c hc θ f i) := by
  have hs := partialTransform_lift 4 2 B (chargedAction c hc θ)
    (LinearIsometryEquiv.refl ℂ _) ((T).symm f) i
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hs

/-- The original physical circle action, on all Hilbert vectors. -/
theorem charge_intertwining (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) :
    transform a b ha hb (KFCausalPhysicalCircleAction.action h hh θ f) =
      coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
        (transform a b ha hb f) := by
  let U := chargedAction (momentumScale h) (momentumScale_ne_zero h hh) θ
  change T (neutralFourier (physicalCoordinates (KFCausalPhysicalCircleAction.action h hh θ f))) =
    T (liftUnitary 4 2 U (LinearIsometryEquiv.refl ℂ _)
      ((T).symm (T (neutralFourier (physicalCoordinates f)))))
  rw [LinearIsometryEquiv.symm_apply_apply,KFCausalChargedSpectatorCoordinates.physical_action]
  exact congrArg T
    (KFCausalEuclideanTensorUnitary.independent_actions_commute 4 2 U neutralFourierBlock
      (physicalCoordinates f)).symm

theorem physical_charge_series (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Hilbert) (i : Index) :
    HasSum (fun j => chargeMatrix a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ i j •
      transform a b ha hb f j)
      (transform a b ha hb (KFCausalPhysicalCircleAction.action h hh θ f) i) := by
  rw [charge_intertwining]
  exact coefficientAction_series a b ha hb _ _ θ _ i

theorem zero_charge_iff (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    f ∈ KFCausalStandingChargeOperator.zeroSector h hh ↔
      ∀ θ, coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
        (transform a b ha hb f) = transform a b ha hb f := by
  constructor
  · intro hf θ
    exact (charge_intertwining a b ha hb h hh θ f).symm.trans (congrArg (transform a b ha hb) (hf θ))
  · intro hf θ
    apply (transform a b ha hb).injective
    exact (charge_intertwining a b ha hb h hh θ f).trans (hf θ)

theorem inverse_charge_intertwining (h : ℝ) (hh : h ≠ 0) (θ : ℝ) (f : Coefficients) :
    (transform a b ha hb).symm
      (coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ f) =
    KFCausalPhysicalCircleAction.action h hh θ ((transform a b ha hb).symm f) := by
  apply (transform a b ha hb).injective
  rw [LinearIsometryEquiv.apply_symm_apply,charge_intertwining,
    LinearIsometryEquiv.apply_symm_apply]

/-- An equivalence of the full maximal charge graphs, including their domains.
The derivative is in the norm of the whole coefficient Hilbert space; no
coordinatewise differentiability or interchange of infinite sums is assumed. -/
theorem charge_graph_iff (h : ℝ) (hh : h ≠ 0) (f g : Hilbert) :
    (f,g) ∈ (KFCausalStandingChargeOperator.standingCharge h hh).graph ↔
    HasDerivAt (fun θ =>
      coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
        (transform a b ha hb f)) (Complex.I • transform a b ha hb g) 0 := by
  rw [KFCausalStandingChargeOperator.standingCharge_graph]
  constructor
  · intro hd
    let L : Hilbert →L[ℂ] Coefficients := transform a b ha hb
    have he := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun θ => transform a b ha hb (KFCausalPhysicalCircleAction.action h hh θ f))
      (transform a b ha hb (Complex.I • g)) 0 at he
    simpa only [charge_intertwining,map_smul] using he
  · intro hd
    let L : Coefficients →L[ℂ] Hilbert := (transform a b ha hb).symm
    have he := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    change HasDerivAt (fun θ => (transform a b ha hb).symm
      (coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
        (transform a b ha hb f)))
      ((transform a b ha hb).symm (Complex.I • transform a b ha hb g)) 0 at he
    simpa only [← charge_intertwining a b ha hb h hh,map_smul,
      LinearIsometryEquiv.symm_apply_apply] using he

theorem charge_domain_iff (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    f ∈ (KFCausalStandingChargeOperator.standingCharge h hh).domain ↔
      ∃ g : Coefficients, HasDerivAt (fun θ =>
        coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
          (transform a b ha hb f)) (Complex.I • g) 0 := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨transform a b ha hb g,(charge_graph_iff a b ha hb h hh f g).mp hg⟩
  · rintro ⟨g,hg⟩
    refine ⟨(transform a b ha hb).symm g,(charge_graph_iff a b ha hb h hh f _).mpr ?_⟩
    simpa only [LinearIsometryEquiv.apply_symm_apply] using hg

/-- The actual physical zero-charge projection in the new representation. -/
theorem zero_projection_integral (h : ℝ) (hh : h ≠ 0) (f : Hilbert) :
    transform a b ha hb (KFCausalStandingChargeOperator.zeroProjection h hh f) =
      (2*Real.pi)⁻¹ • ∫ θ in (0:ℝ)..2*Real.pi,
        coefficientAction a b ha hb (momentumScale h) (momentumScale_ne_zero h hh) θ
          (transform a b ha hb f) := by
  let L : Hilbert →L[ℂ] Coefficients := transform a b ha hb
  have hi := L.intervalIntegral_comp_comm
    ((KFCausalPhysicalCircleAction.action_strong_continuous h hh f).intervalIntegrable
      (μ := volume) 0 (2*Real.pi))
  change (∫ θ in (0:ℝ)..2*Real.pi, transform a b ha hb (KFCausalPhysicalCircleAction.action h hh θ f)) =
    transform a b ha hb (∫ θ in (0:ℝ)..2*Real.pi, KFCausalPhysicalCircleAction.action h hh θ f) at hi
  have hs (r : ℝ) (x : Hilbert) : transform a b ha hb (r • x) = r • transform a b ha hb x :=
    L.map_smul_of_tower r x
  rw [KFCausalStandingChargeOperator.zeroProjection_integral,hs,← hi]
  simp_rw [charge_intertwining]

/-- The spectral width suggested by the free oscillator coefficients. This
definition does not claim diagonalization of the Hamiltonian. -/
def oscillatorWidth (h t : ℝ) : ℝ := Real.exp t/(2*h)

theorem oscillatorWidth_positive (h t : ℝ) (hh : 0 < h) : 0 < oscillatorWidth h t := by
  unfold oscillatorWidth
  positivity

def matchedTransform (h t : ℝ) (hh : 0 < h) : Hilbert ≃ₗᵢ[ℂ] Coefficients :=
  transform (oscillatorWidth h t*momentumScale h^2) (oscillatorWidth h t)
    (mul_pos (oscillatorWidth_positive h t hh) (sq_pos_of_ne_zero (momentumScale_ne_zero h hh.ne')))
    (oscillatorWidth_positive h t hh)

#print axioms transform
#print axioms transform_packet
#print axioms reconstruction
#print axioms chargeMatrix_integral
#print axioms coefficientAction_series
#print axioms charge_intertwining
#print axioms physical_charge_series
#print axioms zero_charge_iff
#print axioms charge_graph_iff
#print axioms charge_domain_iff
#print axioms zero_projection_integral
#print axioms matchedTransform
end
end UnifiedTheory.Audit.KFCausalJointHermiteFourierTransform
