/- Separable weights and Fourier modulations in the two spectator coordinates. -/
import UnifiedTheory.Audit.KFCausalSpectatorEnergyPackets
import UnifiedTheory.Audit.KFCausalModulatedGraphCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalJoinedModulatedWeights
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates
open KFCausalPhysicalSpectatorPackets (one)
open KFCausalJoinedMultiplierSum (joinProduct)
open KFCausalJoinedFourierProduct (separate separate_preserves)
open KFCausalModulatedLpTotality (state state_coe)
open KFCausalEuclideanFourierUniqueness (modulate)

def weight (f g : Block 1 → ℂ) (x : Block 2) : ℂ := f (one (x 0))*g (one (x 1))

theorem left_ae {p : Block 1 → Prop} (hp : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ x : Block 2 ∂volume, p (one (x 0)) := by
  have he := (Measure.quasiMeasurePreserving_fst.comp
    (separate_preserves 1 1).quasiMeasurePreserving).ae hp
  filter_upwards [he] with x hx
  have hs : (separate 1 1 x).1 = one (x 0) := by ext j; fin_cases j <;> rfl
  simpa only [Function.comp_apply, hs] using hx

theorem right_ae {p : Block 1 → Prop} (hp : ∀ᵐ x ∂volume, p x) :
    ∀ᵐ x : Block 2 ∂volume, p (one (x 1)) := by
  have he := (Measure.quasiMeasurePreserving_snd.comp
    (separate_preserves 1 1).quasiMeasurePreserving).ae hp
  filter_upwards [he] with x hx
  have hs : (separate 1 1 x).2 = one (x 1) := by ext j; fin_cases j <;> rfl
  simpa only [Function.comp_apply, hs] using hx

theorem joined_functions_coe (f g : Block 1 → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) :
    joinProduct 1 1 (hf.toLp f) (hg.toLp g) =ᵐ[volume] weight f g := by
  filter_upwards [KFCausalSpectatorEnergyPackets.joined_coe (hf.toLp f) (hg.toLp g),
    left_ae hf.coeFn_toLp, right_ae hg.coeFn_toLp] with x h1 h2 h3
  rw [h1,h2,h3]
  rfl

theorem weight_memLp (f g : Block 1 → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) :
    MemLp (weight f g) 2 :=
  (Lp.memLp (joinProduct 1 1 (hf.toLp f) (hg.toLp g))).ae_eq
    (joined_functions_coe f g hf hg)

theorem modulate_weight (f g : Block 1 → ℂ) (k x : Block 2) :
    modulate k (weight f g) x =
      modulate (one (k 0)) f (one (x 0))*modulate (one (k 1)) g (one (x 1)) := by
  have hi : inner ℝ x k = inner ℝ (one (x 0)) (one (k 0))+
      inner ℝ (one (x 1)) (one (k 1)) := by
    simp [PiLp.inner_apply, Fin.sum_univ_succ, one, RCLike.inner_apply]
  simp only [modulate, hi, AddChar.map_add_eq_mul, Circle.coe_mul, weight]
  ring

theorem state_join (f g : Block 1 → ℂ) (hf : MemLp f 2) (hg : MemLp g 2) (k : Block 2) :
    state (weight f g) (weight_memLp f g hf hg) k =
      joinProduct 1 1 (state f hf (one (k 0))) (state g hg (one (k 1))) := by
  apply Lp.ext
  filter_upwards [state_coe (weight f g) (weight_memLp f g hf hg) k,
    KFCausalSpectatorEnergyPackets.joined_coe (state f hf (one (k 0))) (state g hg (one (k 1))),
    left_ae (state_coe f hf (one (k 0))), right_ae (state_coe g hg (one (k 1)))]
      with x h1 h2 h3 h4
  rw [h1,h2,h3,h4,modulate_weight]

#print axioms weight_memLp
#print axioms state_join
end
end UnifiedTheory.Audit.KFCausalJoinedModulatedWeights
