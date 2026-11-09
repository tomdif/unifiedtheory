/- Two actual transverse momentum graphs for arbitrary coherent sources
and L2 clock profiles. The second vector is constructed from three
proved directional moments and varies continuously with bounded sources. -/
import UnifiedTheory.Audit.KFCausalSourcedSecondCalculus
import UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalSourcedSecondMomentum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalClockFloorCoherentSources (linearSource)
open KFCausalClockFloorCoherentBounds (sourceSize)
open KFCausalClockFloorCoherentDerivative
open KFCausalSourcedSecondCalculus (secondProfile second_expansion second_derivative first_differentiable)
open KFCausalDirectionalGaussianStates (linearForm)
open KFCausalGaussianSecondMomentum (direction)
open KFCausalTransverseTrialDerivative (derivative)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalTransverseMomentumDerivative (derivative_momentum_graph)
open KFCausalClockFloorSourcedClockMomentum (profileState)

variable (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
local notation "W" => KFCausalSourcedDirectionalMoments.state C p α β hα hβ hw b g hg

def firstOutput (h : ℝ) (v : Transverse) : Hilbert := (-Complex.I*(h:ℂ)) •
  (physicalProfile_derivative_memLp C p α β hα hβ hw b g hg v).toLp
    (derivative v (physicalProfile C p α β b g))

def secondState (v : Transverse) : Hilbert :=
  W (direction α β v) 2+(2*linearSource b v) • W (direction α β v) 1+
    (linearSource b v^2+(linearForm (direction α β v) v:ℂ)) • W (direction α β v) 0

def secondOutput (h : ℝ) (v : Transverse) : Hilbert :=
  (-Complex.I*(h:ℂ))^2 • secondState α β hα hβ hw C p b g hg v

theorem secondState_coe (v : Transverse) :
    secondState α β hα hβ hw C p b g hg v =ᵐ[volume] secondProfile C p α β b g v := by
  let c := 2*linearSource b v
  let d := linearSource b v^2+(linearForm (direction α β v) v:ℂ)
  filter_upwards [Lp.coeFn_add (W (direction α β v) 2+c • W (direction α β v) 1)
      (d • W (direction α β v) 0),
    Lp.coeFn_add (W (direction α β v) 2) (c • W (direction α β v) 1),
    Lp.coeFn_smul c (W (direction α β v) 1),Lp.coeFn_smul d (W (direction α β v) 0),
    KFCausalSourcedDirectionalMoments.state_coe C p α β hα hβ hw b g hg (direction α β v) 2,
    KFCausalSourcedDirectionalMoments.state_coe C p α β hα hβ hw b g hg (direction α β v) 1,
    KFCausalSourcedDirectionalMoments.state_coe C p α β hα hβ hw b g hg (direction α β v) 0]
    with x hx hy hc hd h2 h1 h0
  change secondState α β hα hβ hw C p b g hg v x = _ at hx
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx hy hc hd
  rw [hx,hy,hc,hd,h2,h1,h0]
  exact (second_expansion C p α β b g v x).symm

include hα hβ hw hg in
theorem second_memLp (v : Transverse) : MemLp (secondProfile C p α β b g v) 2 volume :=
  (memLp_congr_ae (secondState_coe α β hα hβ hw C p b g hg v)).mp
    (Lp.memLp (secondState α β hα hβ hw C p b g hg v))

theorem first_graph (h : ℝ) (v : Transverse) :
    (profileState α β hα hβ hw C p b g hg,firstOutput α β hα hβ hw C p b g hg h v) ∈
      (transverseMomentum h v).graph :=
  derivative_momentum_graph h _ v (physicalProfile_memLp C p α β hα hβ hw b g hg)
    (physicalProfile_derivative_memLp C p α β hα hβ hw b g hg v)
    (physicalProfile_transverse_differentiable C p α β b g)

theorem second_graph (h : ℝ) (v : Transverse) :
    (firstOutput α β hα hβ hw C p b g hg h v,secondOutput α β hα hβ hw C p b g hg h v) ∈
      (transverseMomentum h v).graph := by
  have hd : MemLp (derivative v (derivative v (physicalProfile C p α β b g))) 2 volume := by
    rw [second_derivative]
    exact second_memLp α β hα hβ hw C p b g hg v
  have he : hd.toLp (derivative v (derivative v (physicalProfile C p α β b g))) =
      secondState α β hα hβ hw C p b g hg v := by
    apply Lp.ext
    filter_upwards [hd.coeFn_toLp,secondState_coe α β hα hβ hw C p b g hg v] with x hx hy
    rw [hx,hy,second_derivative]
  have hG := derivative_momentum_graph h _ v
    (physicalProfile_derivative_memLp C p α β hα hβ hw b g hg v) hd
    (first_differentiable C p α β b g v)
  rw [he] at hG
  have hs := (transverseMomentum h v).graph.smul_mem (-Complex.I*(h:ℂ)) hG
  simpa only [firstOutput,secondOutput,Prod.smul_mk,smul_smul,← pow_two] using hs

omit C p b in
theorem secondOutput_curve_continuous (B : ℝ) (C : ℝ → ℂ) (p : ℝ → ℝ) (b : ℝ → Fin 5 → ℂ)
    (hCc : Continuous C) (hpc : Continuous p) (hbc : Continuous b)
    (hC : ∀ θ, ‖C θ‖ ≤ 1) (hb : ∀ θ, sourceSize (b θ) ≤ B) (h : ℝ) (v : Transverse) :
    Continuous (fun θ => secondOutput α β hα hβ hw (C θ) (p θ) (b θ) g hg h v) := by
  have hc : Continuous (fun θ => linearSource (b θ) v) := by unfold linearSource; fun_prop
  have hW (n : ℕ) := KFCausalSourcedDirectionalMoments.state_curve_continuous α β B hα hβ hw
    C p b g hg hCc hpc hbc hC hb (direction α β v) n
  exact continuous_const.smul (((hW 2).add ((continuous_const.mul hc).smul (hW 1))).add
    (((hc.pow 2).add continuous_const).smul (hW 0)))

#print axioms secondState_coe
#print axioms second_memLp
#print axioms first_graph
#print axioms second_graph
#print axioms secondOutput_curve_continuous
end
end UnifiedTheory.Audit.KFCausalSourcedSecondMomentum
