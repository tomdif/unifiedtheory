/- Transport of actual inhomogeneous Wilson actions and finite histories.
The coupling profile, field and finite deleted set move together. -/
import UnifiedTheory.Clay.YangMills.WilsonPlaquetteFrames
import UnifiedTheory.Clay.YangMills.WilsonDeletionReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonProfileTransport
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSingleLinkStaples SpatialPlaquetteCutGeometry
open SpatialWilsonReflectionKernel SpatialWilsonHistoryKernel SpatialWilsonCutSchwarz
open WilsonPlaquetteFrames

variable (n : ℕ) [NeZero n]

def push (F : Frame n) (γ : Plaquette n → ℝ) (p : Plaquette n) : ℝ :=
  γ (F.plaquettes.symm p)

theorem push_inverse (F : Frame n) (γ : Plaquette n → ℝ) :
    push n (inverse n F) (push n F γ) = γ := by
  funext p
  exact congrArg γ (F.plaquettes.symm_apply_apply p)

theorem inverse_push (F : Frame n) (γ : Plaquette n → ℝ) :
    push n F (push n (inverse n F) γ) = γ := by
  funext p
  exact congrArg γ (F.plaquettes.apply_symm_apply p)

theorem push_nonneg (F : Frame n) (γ : Plaquette n → ℝ) (hγ : ∀ p, 0 ≤ γ p) (p : Plaquette n) :
    0 ≤ push n F γ p := hγ _

theorem push_sum (F : Frame n) (γ : Plaquette n → ℝ) :
    ∑ p, push n F γ p = ∑ p, γ p := Equiv.sum_comp F.plaquettes.symm γ

theorem push_deficit (F : Frame n) (γ : Plaquette n → ℝ) (s : ℝ) :
    (∑ p, (s - push n F γ p)) = ∑ p, (s - γ p) :=
  Equiv.sum_comp F.plaquettes.symm (fun p => s - γ p)

theorem action_push (F : Frame n) (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    action n (push n F γ) u = action n γ (F.symmetry.map u) := by
  unfold action push
  simp_rw [F.defect_map]
  have h := Equiv.sum_comp F.plaquettes
    (fun p => γ (F.plaquettes.symm p) * SpatialWilsonPlaquetteKernels.defect n p u)
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem weight_push (F : Frame n) (γ : Plaquette n → ℝ) (u : SpatialLinks (2 * n) Q) :
    weight n (push n F γ) u = weight n γ (F.symmetry.map u) := by
  simp only [weight, action_push]

def pushSet (F : Frame n) (S : Finset (Plaquette n)) : Finset (Plaquette n) :=
  S.map F.plaquettes.toEmbedding

theorem pushSet_card (F : Frame n) (S : Finset (Plaquette n)) :
    (pushSet n F S).card = S.card := Finset.card_map _

theorem pushSet_mem (F : Frame n) (S : Finset (Plaquette n)) (p : Plaquette n) :
    p ∈ pushSet n F S ↔ F.plaquettes.symm p ∈ S := by
  classical
  simp only [pushSet, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨q,hq,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hq
  · intro hp
    exact ⟨F.plaquettes.symm p,hp,F.plaquettes.apply_symm_apply p⟩

theorem pushSet_inverse (F : Frame n) (S : Finset (Plaquette n)) :
    pushSet n (inverse n F) (pushSet n F S) = S := by
  classical
  ext p
  simp only [pushSet_mem, inverse, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem push_omitted (F : Frame n) (S : Finset (Plaquette n)) (s : ℝ) :
    push n F (SpatialWilsonPatchWeights.omitted n S s) =
      SpatialWilsonPatchWeights.omitted n (pushSet n F S) s := by
  classical
  funext p
  simp only [push, SpatialWilsonPatchWeights.omitted, pushSet_mem]

variable (T : Type*) [Fintype T]

def historyEquiv (F : Frame n) : History n T ≃ᵐ History n T :=
  MeasurableEquiv.piCongrRight (fun _ => F.symmetry.map)

theorem history_preserving (F : Frame n) :
    MeasurePreserving (historyEquiv n T F) (measure n T) (measure n T) :=
  measurePreserving_pi (fun _ => WilsonSlabGauge.spatialHaar)
    (fun _ => WilsonSlabGauge.spatialHaar) (fun _ => F.symmetry.preserving)

variable {E : Type*} [Fintype E]

theorem density_push (F : Frame n) (γ : T → Plaquette n → ℝ)
    (β : E → ℝ) (l r : E → T) (u : History n T) :
    density n T (fun t => push n F (γ t)) β l r u =
      density n T γ β l r (historyEquiv n T F u) := by
  unfold density
  simp only [weight_push]
  change (∏ t, weight n (γ t) (F.symmetry.map (u t))) *
    (∏ e, kineticWeight character (β e) 2 (u (l e)) (u (r e))) =
      (∏ t, weight n (γ t) (F.symmetry.map (u t))) *
    (∏ e, kineticWeight character (β e) 2 (F.symmetry.map (u (l e))) (F.symmetry.map (u (r e))))
  simp only [F.kinetic_map]

theorem partition_push (F : Frame n) (γ : T → Plaquette n → ℝ)
    (β : E → ℝ) (l r : E → T) :
    partition n T (fun t => push n F (γ t)) β l r = partition n T γ β l r := by
  unfold partition
  simp_rw [density_push]
  exact (history_preserving n T F).integral_comp' _

end
end UnifiedTheory.Clay.YangMills.WilsonProfileTransport
