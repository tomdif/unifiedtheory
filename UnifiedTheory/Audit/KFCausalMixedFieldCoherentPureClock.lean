/- The actual mixed-shift coherent spectral states have pure-clock
graphs with source-continuous outputs. Both field and Gaussian shifts
are retained, including their distinct derivatives. -/
import UnifiedTheory.Audit.KFCausalWeightedShiftedPureClockGraphs
import UnifiedTheory.Audit.KFCausalMixedFieldCoherentPhysical

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalMixedFieldCoherentPureClock
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalRadialMultipliers
open KFCausalClockFloorRelativeShift (scale)
open KFCausalMixedFieldPhysicalProfile (field field_smooth)
open KFCausalMixedFieldPureClockDifferential (fieldRate)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalCanonicalClockDerivative (clockDerivative)
open KFCausalMixedFieldGaussianStrip (degree)
open KFCausalMixedFieldCoherentSpectral (state)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalClockFloorCoherentBounds (sourceSize)

def multiplier (ε y : ℝ) (k : ℕ) (x : Configuration) : ℂ := field (scale ε y x.1) x.2^k
def rate (ε y : ℝ) (k : ℕ) (x : Configuration) : ℂ :=
  (k:ℂ)*field (scale ε y x.1) x.2^(k-1)*fieldRate ε y x

theorem multiplier_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (k : ℕ) :
    Controlled (multiplier ε y k) :=
  controlled_pow _ (KFCausalMixedFieldPureClockDomain.field_controlled ε y hε hy) k

theorem rate_controlled (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (k : ℕ) :
    Controlled (rate ε y k) :=
  controlled_mul _ _ (controlled_mul _ _ (controlled_const (k:ℂ))
    (controlled_pow _ (KFCausalMixedFieldPureClockDomain.field_controlled ε y hε hy) (k-1)))
    (KFCausalMixedFieldPureClockDomain.fieldRate_controlled ε y hε hy)

theorem multiplier_differentiable (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (k : ℕ) :
    Differentiable ℝ (multiplier ε y k) :=
  ((field_smooth (scale ε y) (KFCausalClockFloorRelativeShift.scale_smooth ε y hε hy)).pow k).differentiable
    (by norm_num)

theorem multiplier_rate (ε y : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (k : ℕ) (x : Configuration) :
    realInverse ε x.1*clockDerivative (multiplier ε y k) x = rate ε y k x := by
  have hd := ((multiplier_differentiable ε y hε hy k) x).hasFDerivAt.comp_hasDerivAt x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  change HasDerivAt (fun s => field (scale ε y s) x.2^k)
    (clockDerivative (multiplier ε y k) x) x.1 at hd
  have he := hd.unique ((KFCausalMixedFieldPureClockDifferential.field_derivative ε y hε hy x).pow k)
  rw [he]
  unfold rate
  linear_combination (k:ℂ)*field (scale ε y x.1) x.2^(k-1)*
    (KFCausalMixedFieldPureClockDifferential.field_normalized_derivative ε y hε x)

theorem state_profile (ε a α β δ p y : ℝ) (b : Fin 5 → ℂ) (j : Fin 2)
    (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) :
    state ε a α β δ p b y j hε ha hα hβ hw hy hyr =ᵐ[volume] fun x =>
      multiplier ε y (degree j) x*KFCausalRelativeGaussianDifferential.profile
        (KFCausalShiftedGaussianPhysicalProfile.clockAmplitude ε a p (y+δ)) (scale ε (y+δ)) α β b x := by
  have hc (x : Configuration) : KFCausalMixedFieldCoherentSpectral.configurationLine ε a α β δ p b y j x =
      KFCausalMixedFieldGaussianStrip.fieldLine ε y (KFCausalClockFloorGroupedCoordinates.grouping x)^degree j*
        KFCausalClockFloorCoherentSpectral.configurationLine ε a α β p b (y+δ) x :=
    KFCausalMixedFieldCoherentStrip.line_formula ε a α β δ p b y j _
  filter_upwards [KFCausalMixedFieldCoherentSpectral.state_coe ε a α β δ p b y j hε ha hα hβ hw hy hyr]
    with x hx
  have hg := KFCausalShiftedGaussianPhysicalProfile.physical_profile ε a α β p (y+δ) b hε x
  rw [hx]
  unfold KFCausalClockFloorLpCoordinates.weightedFunction at hg ⊢
  rw [hc,KFCausalMixedFieldPhysicalProfile.fieldLine_at_coordinate ε y hε x]
  unfold multiplier
  rw [← hg]
  ring

variable (ε a α β δ p y : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3)

def output (h : ℝ) (C : ℂ) (b : Fin 5 → ℂ) (j : Fin 2) : Hilbert :=
  KFCausalWeightedShiftedPureClockGraphs.output ε a α β p (y+δ) hε ha hα hβ hw hyr
    (multiplier ε y (degree j)) (rate ε y (degree j))
    (multiplier_controlled ε y hε hy (degree j)) (rate_controlled ε y hε hy (degree j)) h C b

theorem graph (h : ℝ) (hh : h ≠ 0) (C : ℂ) (b : Fin 5 → ℂ) (j : Fin 2) :
    (C • state ε a α β δ p b y j hε ha hα hβ hw hy hyr,
      output ε a α β δ p y hε ha hα hβ hw hy hyr h C b j) ∈ (pureMomentum ε hε h).graph := by
  have hi : KFCausalWeightedShiftedPureClockGraphs.input ε a α β p (y+δ) hε ha hα hβ hw hyr
      (multiplier ε y (degree j)) (multiplier_controlled ε y hε hy (degree j)) C b =
      C • state ε a α β δ p b y j hε ha hα hβ hw hy hyr := by
    apply Lp.ext
    filter_upwards [KFCausalWeightedShiftedPureClockGraphs.input_coe ε a α β p (y+δ) hε ha hα hβ hw hyr
      (multiplier ε y (degree j)) (multiplier_controlled ε y hε hy (degree j)) C b,
      Lp.coeFn_smul C (state ε a α β δ p b y j hε ha hα hβ hw hy hyr),
      state_profile ε a α β δ p y b j hε ha hα hβ hw hy hyr] with x hx hc hs
    simp only [hx,hc,Pi.smul_apply,smul_eq_mul,hs]
  rw [← hi]
  exact KFCausalWeightedShiftedPureClockGraphs.graph ε a α β p (y+δ) hε ha hα hβ hw hyr
    (multiplier ε y (degree j)) (rate ε y (degree j))
    (multiplier_controlled ε y hε hy (degree j)) (rate_controlled ε y hε hy (degree j))
    (multiplier_differentiable ε y hε hy (degree j)) (multiplier_rate ε y hε hy (degree j)) h hh C b

theorem output_continuous (B : ℝ) (C : ℝ → ℂ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hbc : Continuous b) (hbB : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) (j : Fin 2) :
    Continuous (fun θ => output ε a α β δ p y hε ha hα hβ hw hy hyr h (C θ) (b θ) j) :=
  KFCausalWeightedShiftedPureClockGraphs.output_continuous ε a α β p (y+δ) hε ha hα hβ hw hyr
    (multiplier ε y (degree j)) (rate ε y (degree j))
    (multiplier_controlled ε y hε hy (degree j)) (rate_controlled ε y hε hy (degree j))
    B C b hCc hbc hbB h

#print axioms multiplier_controlled
#print axioms rate_controlled
#print axioms multiplier_differentiable
#print axioms multiplier_rate
#print axioms state_profile
#print axioms graph
#print axioms output_continuous
end
end UnifiedTheory.Audit.KFCausalMixedFieldCoherentPureClock
