/- Strong continuity of the squeeze on every full angle-dependent output.
The L2 lift uses dominated convergence, not an unbounded generator domain. -/
import UnifiedTheory.Audit.KFCausalHilbertLpContinuity
import UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalSqueezeOutputContinuity
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalPairedSqueezeTransport (transport transport_initial)
open UnifiedTheory.Audit.KFCausalPairedSqueezeContinuity (transport_strong_continuous)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace)

def pureOutput (a : ℝ) : Output (Fin 8) Hilbert ≃ₗᵢ[ℂ] Output (Fin 8) Hilbert :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 8 => transport a)

theorem pureOutput_apply (a : ℝ) (x : Output (Fin 8) Hilbert) (i : Fin 8) :
    pureOutput a x i = transport a (x i) := rfl

theorem pureOutput_zero (x : Output (Fin 8) Hilbert) : pureOutput 0 x = x := by
  apply PiLp.ext
  intro i
  exact transport_initial (x i)

theorem pureOutput_continuous (x : Output (Fin 8) Hilbert) : Continuous (fun a => pureOutput a x) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun i => transport_strong_continuous (x i)))

def pureLp (a : ℝ) : OutputSpace →L[ℂ] OutputSpace :=
  (pureOutput a : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert).compLpL 2 angleMeasure

theorem pureLp_zero (x : OutputSpace) : pureLp 0 x = x := by
  apply Lp.ext
  filter_upwards [(pureOutput 0 : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert).coeFn_compLp x] with θ hθ
  exact hθ.trans (pureOutput_zero (x θ))

theorem pureLp_norm (a : ℝ) (x : OutputSpace) : ‖pureLp a x‖ = ‖x‖ := by
  have he : (fun θ => ‖pureLp a x θ‖) =ᵐ[angleMeasure] fun θ => ‖x θ‖ := by
    filter_upwards [(pureOutput a : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert).coeFn_compLp x] with θ hθ
    exact (congrArg norm hθ).trans ((pureOutput a).norm_map (x θ))
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono (fun _ hx => hx.le)))
    (Lp.norm_le_norm_of_ae_le (he.mono (fun _ hx => hx.ge)))

theorem pureLp_continuous (x : OutputSpace) : Continuous (fun a => pureLp a x) := by
  let F := fun a θ => pureOutput a (x θ)
  have hF (a : ℝ) : MemLp (F a) 2 angleMeasure :=
    (Lp.memLp (pureLp a x)).ae_eq ((pureOutput a : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert).coeFn_compLp x)
  have he : (fun a => (hF a).toLp (F a)) = fun a => pureLp a x := by
    funext a
    have hp : pureLp a x =ᵐ[angleMeasure] F a :=
      (pureOutput a : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert).coeFn_compLp x
    exact Lp.ext ((hF a).coeFn_toLp.trans hp.symm)
  rw [← he]
  apply KFCausalHilbertLpContinuity.continuous_toLp F hF x (Lp.memLp x)
  · intro a
    exact Eventually.of_forall (fun θ => ((pureOutput a).norm_map (x θ)).le)
  · exact Eventually.of_forall (fun θ => pureOutput_continuous (x θ))

theorem pureLp_joint_continuous : Continuous (fun p : ℝ × OutputSpace => pureLp p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q : ℝ × OutputSpace => pureLp q.1 q.2) (𝓝 p) (𝓝 (pureLp p.1 p.2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := ((continuous_snd.tendsto p).sub (tendsto_const_nhds (x := p.2))).norm
  have h2 := (((pureLp_continuous p.2).comp continuous_fst).tendsto p |>.sub
    (tendsto_const_nhds (x := pureLp p.1 p.2))).norm
  have hb (q : ℝ × OutputSpace) :
      ‖pureLp q.1 q.2-pureLp p.1 p.2‖ ≤ ‖q.2-p.2‖+‖pureLp q.1 p.2-pureLp p.1 p.2‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (pureLp q.1 q.2) (pureLp q.1 p.2) (pureLp p.1 p.2)
    simpa only [← map_sub,pureLp_norm] using hh
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa only [Function.comp_apply,sub_self,norm_zero,zero_add] using h1.add h2

#print axioms pureOutput_apply
#print axioms pureOutput_zero
#print axioms pureOutput_continuous
#print axioms pureLp_zero
#print axioms pureLp_norm
#print axioms pureLp_continuous
#print axioms pureLp_joint_continuous
end
end UnifiedTheory.Audit.KFCausalSqueezeOutputContinuity
