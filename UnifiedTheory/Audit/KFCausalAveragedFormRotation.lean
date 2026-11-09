/- The full periodic unitary action lifts to the completed averaged
form domain. Translation of its L2 section preserves every averaged
energy pairing. No invariance of the unaveraged operator is assumed. -/
import UnifiedTheory.Audit.KFCausalAngleTranslation
import UnifiedTheory.Audit.KFCausalAveragedFormProjection
import UnifiedTheory.Audit.KFCausalClosedGraphForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalAveragedFormRotation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection (averagedOutput)
open UnifiedTheory.Audit.KFCausalAngleTranslation

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (U : StrongUnitaryGroup H) (T : ℝ) (hperiod : ∀ f, U.action T f = f)
  (J : E →L[ℂ] H)

include hperiod in
theorem orbit_periodic (f : H) : Function.Periodic (fun θ => U.action (T*θ) f) 1 := by
  intro θ
  change U.action (T*(θ+1)) f = U.action (T*θ) f
  rw [mul_add, mul_one, ← U.compose, hperiod]

include hperiod in
theorem pullback_orbit (a : ℝ) (f : H) :
    pullback a (orbit U T f) = orbit U T (U.action (T*a) f) := by
  apply Lp.ext
  filter_upwards [pullback_coe a (orbit U T f),
    (shift_preserving a).quasiMeasurePreserving.ae (orbitState_coe U T f),
    orbitState_coe U T (U.action (T*a) f)] with θ hP ho ha
  change orbit U T f (shift a θ) = U.action (T*shift a θ) f at ho
  change orbit U T (U.action (T*a) f) θ = U.action (T*θ) (U.action (T*a) f) at ha
  rw [hP, ho, ha]
  have hp := periodic_shift _ (orbit_periodic U T hperiod f) a θ
  change U.action (T*shift a θ) f = U.action (T*(θ+a)) f at hp
  rw [hp, U.compose, mul_add]
  rw [add_comm]

def rotate (a : ℝ) (u : FormSpace U T J) : FormSpace U T J :=
  ⟨WithLp.toLp 2 (U.action (T*a) (embedding U T J u), pullback a (sectionMap U T J u)), by
    change J.compLp (pullback a (sectionMap U T J u)) -
      orbit U T (U.action (T*a) (embedding U T J u)) = 0
    rw [pullback_compLp, compatibility, pullback_orbit U T hperiod, sub_self]⟩

theorem rotate_embedding (a : ℝ) (u : FormSpace U T J) :
    embedding U T J (rotate U T hperiod J a u) = U.action (T*a) (embedding U T J u) := rfl

theorem rotate_section (a : ℝ) (u : FormSpace U T J) :
    sectionMap U T J (rotate U T hperiod J a u) = pullback a (sectionMap U T J u) := rfl

theorem rotate_reverse (hJ : Function.Injective J) (a : ℝ) (u : FormSpace U T J) :
    rotate U T hperiod J (-a) (rotate U T hperiod J a u) = u := by
  apply embedding_injective U T J hJ
  rw [rotate_embedding, rotate_embedding, U.compose, mul_neg, add_neg_cancel, U.initial]

theorem rotate_norm (a : ℝ) (u : FormSpace U T J) :
    ‖rotate U T hperiod J a u‖ = ‖u‖ := by
  have he := norm_identity U T J (rotate U T hperiod J a u)
  rw [rotate_embedding, rotate_section, (U.action (T*a)).norm_map, (pullback a).norm_map] at he
  have hu := norm_identity U T J u
  nlinarith [norm_nonneg (rotate U T hperiod J a u), norm_nonneg u]

theorem rotate_output (A : E →L[ℂ] K) (a : ℝ) (u : FormSpace U T J) :
    averagedOutput U T J A (rotate U T hperiod J a u) = pullback a (averagedOutput U T J A u) :=
  pullback_compLp a A (sectionMap U T J u)

theorem rotate_energy_pairing (A : E →L[ℂ] K) (a : ℝ) (u v : FormSpace U T J) :
    inner ℂ (averagedOutput U T J A (rotate U T hperiod J a u))
      (averagedOutput U T J A (rotate U T hperiod J a v)) =
        inner ℂ (averagedOutput U T J A u) (averagedOutput U T J A v) := by
  rw [rotate_output, rotate_output]
  exact (pullback (E := K) a).inner_map_map _ _

theorem rotate_energy_transport (hJ : Function.Injective J) (A : E →L[ℂ] K)
    (a : ℝ) (u v : FormSpace U T J) :
    inner ℂ (averagedOutput U T J A (rotate U T hperiod J a u)) (averagedOutput U T J A v) =
      inner ℂ (averagedOutput U T J A u)
        (averagedOutput U T J A (rotate U T hperiod J (-a) v)) := by
  have he := rotate_energy_pairing U T hperiod J A a u (rotate U T hperiod J (-a) v)
  have hi := rotate_reverse U T hperiod J hJ (-a) v
  rw [neg_neg] at hi
  rwa [hi] at he

variable (D : KFCausalClosedGraphForm.Data H K)

abbrev graphRotate (a : ℝ) :=
  rotate U T hperiod (KFCausalClosedGraphForm.embedding D) a

theorem graphRotate_embedding (a : ℝ)
    (u : FormSpace U T (KFCausalClosedGraphForm.embedding D)) :
    embedding U T (KFCausalClosedGraphForm.embedding D) (graphRotate U T hperiod D a u) =
      U.action (T*a) (embedding U T (KFCausalClosedGraphForm.embedding D) u) :=
  rotate_embedding U T hperiod (KFCausalClosedGraphForm.embedding D) a u

theorem graphRotate_output (a : ℝ)
    (u : FormSpace U T (KFCausalClosedGraphForm.embedding D)) :
    averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D)
      (graphRotate U T hperiod D a u) =
        pullback a (averagedOutput U T (KFCausalClosedGraphForm.embedding D)
          (KFCausalClosedGraphForm.energyOutput D) u) :=
  rotate_output U T hperiod (KFCausalClosedGraphForm.embedding D)
    (KFCausalClosedGraphForm.energyOutput D) a u

theorem graphRotate_pairing (a : ℝ)
    (u v : FormSpace U T (KFCausalClosedGraphForm.embedding D)) :
    inner ℂ (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D)
      (graphRotate U T hperiod D a u))
      (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D)
        (graphRotate U T hperiod D a v)) =
      inner ℂ (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D) u)
        (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D) v) :=
  rotate_energy_pairing U T hperiod (KFCausalClosedGraphForm.embedding D)
    (KFCausalClosedGraphForm.energyOutput D) a u v

theorem graphRotate_transport (a : ℝ)
    (u v : FormSpace U T (KFCausalClosedGraphForm.embedding D)) :
    inner ℂ (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D)
      (graphRotate U T hperiod D a u))
      (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D) v) =
      inner ℂ (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D) u)
        (averagedOutput U T (KFCausalClosedGraphForm.embedding D) (KFCausalClosedGraphForm.energyOutput D)
          (graphRotate U T hperiod D (-a) v)) :=
  rotate_energy_transport U T hperiod (KFCausalClosedGraphForm.embedding D)
    (KFCausalClosedGraphForm.embedding_injective D) (KFCausalClosedGraphForm.energyOutput D) a u v

#print axioms orbit_periodic
#print axioms pullback_orbit
#print axioms rotate_embedding
#print axioms rotate_section
#print axioms rotate_reverse
#print axioms rotate_norm
#print axioms rotate_output
#print axioms rotate_energy_pairing
#print axioms rotate_energy_transport
#print axioms graphRotate_embedding
#print axioms graphRotate_output
#print axioms graphRotate_pairing
#print axioms graphRotate_transport

end
end UnifiedTheory.Audit.KFCausalAveragedFormRotation
