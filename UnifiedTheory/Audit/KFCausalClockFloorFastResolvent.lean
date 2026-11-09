/- Actual shifted resolvents in exponential time satisfy a quadratic
penalty equation on the constructed growing form. No limit is assumed. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian
import UnifiedTheory.Audit.KFCausalClockFloorResolventTests

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorFastResolvent
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorFastTimeEnergy (physicalTime exp_physicalTime)
open UnifiedTheory.Audit.KFCausalClockFloorGrowingHamiltonian (GrowingForm referenceLift referenceLift_dense)
open UnifiedTheory.Audit.KFCausalClockFloorResolventTests

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hb m g k 0
local notation "J" => embedding ε hε h hne hb m g k 0
local notation "A" => staticMap ε hε h hne hb m g k
local notation "B" => growingMap ε hε h hne hb m g k
local notation "W" => GrowingForm ε hε h hne hb m g k
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hne hb m g k
local notation "JW" => KFCausalClosedGraphForm.embedding D

def inclusion : V →L[ℂ] W where
  toFun := referenceLift ε hε h hne hb m g k
  map_add' := by
    intro x y
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext ((J).map_add x y) ((B).map_add x y)
  map_smul' := by
    intro c x
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext ((J).map_smul c x) ((B).map_smul c x)
  cont := ((WithLp.prodContinuousLinearEquiv 2 ℂ Hilbert EnergyOutputSpace).symm.continuous.comp
    ((J).continuous.prodMk (B).continuous)).subtype_mk _

theorem inclusion_dense : DenseRange (inclusion ε hε h hne hb m g k) :=
  referenceLift_dense ε hε h hne hb m g k

theorem inclusion_embedding (v : V) : JW (inclusion ε hε h hne hb m g k v) = J v := rfl

theorem inclusion_inner (v z : V) :
    inner ℂ (inclusion ε hε h hne hb m g k v) (inclusion ε hε h hne hb m g k z) =
      inner ℂ (J v) (J z)+inner ℂ (B v) (B z) := rfl

def formLift (u : ℝ) : Hilbert →L[ℂ] V := regularizerLift ε hε h hne hb m g k u (physicalTime u)
def resolvent (u : ℝ) : Hilbert →L[ℂ] Hilbert := regularizer ε hε h hne hb m g k u (physicalTime u)
def target : Hilbert →L[ℂ] W := (JW).adjoint
def limitResolvent : Hilbert →L[ℂ] Hilbert := (JW).comp (target ε hε h hne hb m g k)

theorem formLift_embedding (u : ℝ) (f : Hilbert) :
    J (formLift ε hε h hne hb m g k u f) = resolvent ε hε h hne hb m g k u f :=
  regularizerLift_embedding ε hε h hne hb m g k u (physicalTime u) f

theorem resolvent_contraction (u : ℝ) (hu : 0 < u) (f : Hilbert) :
    ‖resolvent ε hε h hne hb m g k u f‖ ≤ ‖f‖ :=
  regularizer_contraction ε hε h hne hb m g k u (physicalTime u) hu f

private theorem rescale_algebra (u : ℝ) (hu : u ≠ 0) (p a b c : ℂ)
    (he : a+(u:ℂ)*b=(u:ℂ)*(c-p)) : p+b+((1/u:ℝ):ℂ)*a=c := by
  have ha : a=(u:ℂ)*(c-p-b) := by linear_combination he
  rw [ha]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hu]
  ring

theorem variational (u : ℝ) (hu : 0 < u) (f : Hilbert) (z : V) :
    inner ℂ (inclusion ε hε h hne hb m g k (formLift ε hε h hne hb m g k u f))
      (inclusion ε hε h hne hb m g k z)+
      ((1/u:ℝ):ℂ)*inner ℂ (A (formLift ε hε h hne hb m g k u f)) (A z) =
      inner ℂ (target ε hε h hne hb m g k f) (inclusion ε hε h hne hb m g k z) := by
  let r : V := formLift ε hε h hne hb m g k u f
  have hp := regularizer_variational ε hε h hne hb m g k u (physicalTime u) hu f z
  have hs : inner ℂ r (referenceFormOperator ε hε h hne hb m g k (physicalTime u) z) =
      inner ℂ (A r) (A z)+(u:ℂ)*inner ℂ (B r) (B z) := by
    simpa only [exp_physicalTime u hu] using
      KFCausalBoundedFormCurve.formOperator_pairing A B (physicalTime u) r z
  change inner ℂ r (referenceFormOperator ε hε h hne hb m g k (physicalTime u) z) =
    (u:ℂ)*inner ℂ (f-resolvent ε hε h hne hb m g k u f) (J z) at hp
  have he : J r = resolvent ε hε h hne hb m g k u f := formLift_embedding ε hε h hne hb m g k u f
  have hr : inner ℂ (f-resolvent ε hε h hne hb m g k u f) (J z) =
      inner ℂ f (J z)-inner ℂ (J r) (J z) := by
    rw [inner_sub_left]
    exact congrArg (fun y : Hilbert => inner ℂ f (J z)-inner ℂ y (J z)) he.symm
  have hp' := hs.symm.trans (hp.trans (congrArg (fun q : ℂ => (u:ℂ)*q) hr))
  have ht : inner ℂ (target ε hε h hne hb m g k f) (inclusion ε hε h hne hb m g k z) =
      inner ℂ f (J z) := (JW).adjoint_inner_left (inclusion ε hε h hne hb m g k z) f
  change inner ℂ (J r) (J z)+inner ℂ (B r) (B z)+((1/u:ℝ):ℂ)*inner ℂ (A r) (A z) =
    inner ℂ ((JW).adjoint f) (inclusion ε hε h hne hb m g k z)
  exact (rescale_algebra u hu.ne' _ _ _ _ hp').trans ht.symm

#print axioms inclusion_dense
#print axioms inclusion_embedding
#print axioms inclusion_inner
#print axioms formLift_embedding
#print axioms resolvent_contraction
#print axioms variational
end
end UnifiedTheory.Audit.KFCausalClockFloorFastResolvent
