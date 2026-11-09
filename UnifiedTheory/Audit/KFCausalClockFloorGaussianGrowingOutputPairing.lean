/- Exact Gaussian adjoint defect on the original growing output. The
ordered rows have the half-clock shift; only the two radial kinetic
rows contribute to the defect. All orbit pairings use actual L2 data. -/
import UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingForm
import UnifiedTheory.Audit.KFCausalClockFloorGrowingRadialMultiplierForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingOutputPairing
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalFiniteJointGraph (Output)
open KFCausalUnitIntervalOrbit (angleMeasure)
open KFCausalAveragedOutputRescaling (EnergyOutputSpace)
open KFCausalClockFloorAveragedSqueezeEnergy (coordinate coordinateLp)
open KFCausalClockFloorGaussianGrowingTransport (action action_pairing)
open KFCausalAnalyticClockSecondTransport (firstShift)
open KFCausalClockFloorGaussianGrowingForm
  (growingAction growingActionLp growingAction_apply formAction formAction_output)
open KFCausalClockFloorGrowingRadialMultiplierForm (rootOutput rootOutput_inner)

variable (ε a : ℝ) (ha : 0 ≤ a) (h : ℝ)

theorem coordinate_action (y : ℝ) (f : EnergyOutputSpace) (i : Fin 8) :
    coordinateLp i (growingActionLp ε a ha h y f)=
      if i.val<3 then 0 else
        (action ε a ha (y+firstShift h i)).compLpL 2 angleMeasure (coordinateLp i f) := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (growingActionLp ε a ha h y f),
    (growingAction ε a ha h y).coeFn_compLp f,(coordinate i).coeFn_compLp f,
    (action ε a ha (y+firstShift h i)).coeFn_compLp (coordinateLp i f),
    Lp.coeFn_zero (E := Hilbert) (p := 2) (μ := angleMeasure)]
      with θ h1 h2 h3 h4 h0
  change coordinateLp i (growingActionLp ε a ha h y f) θ=_
  change coordinateLp i (growingActionLp ε a ha h y f) θ=
    growingActionLp ε a ha h y f θ i at h1
  change growingActionLp ε a ha h y f θ=growingAction ε a ha h y (f θ) at h2
  change coordinateLp i f θ=f θ i at h3
  rw [h1,h2,growingAction_apply]
  split_ifs
  · exact h0.symm
  · exact (h4.trans (congrArg (action ε a ha (y+firstShift h i)) h3)).symm

theorem output_pairing (f g : Output (Fin 8) Hilbert) :
    inner ℂ (growingAction ε a ha h 0 f) g+
      (inner ℂ (f 3) (growingAction ε a ha h h g 3)+
        inner ℂ (f 4) (growingAction ε a ha h h g 4))=
    inner ℂ f (growingAction ε a ha h h g)+
      (inner ℂ (f 3) (growingAction ε a ha h 0 g 3)+
        inner ℂ (f 4) (growingAction ε a ha h 0 g 4)) := by
  have hs : h+-(h/2)=h/2 := by ring
  simp [PiLp.inner_apply,Fin.sum_univ_succ,growingAction_apply,firstShift,
    action_pairing,hs,neg_div]
  abel

theorem orbit_pairing (f g : EnergyOutputSpace) :
    inner ℂ (growingActionLp ε a ha h 0 f) g+
      (inner ℂ (coordinateLp 3 f) (coordinateLp 3 (growingActionLp ε a ha h h g))+
        inner ℂ (coordinateLp 4 f) (coordinateLp 4 (growingActionLp ε a ha h h g)))=
    inner ℂ f (growingActionLp ε a ha h h g)+
      (inner ℂ (coordinateLp 3 f) (coordinateLp 3 (growingActionLp ε a ha h 0 g))+
        inner ℂ (coordinateLp 4 f) (coordinateLp 4 (growingActionLp ε a ha h 0 g))) := by
  let f0 := growingActionLp ε a ha h 0 f
  let gh := growingActionLp ε a ha h h g
  let g0 := growingActionLp ε a ha h 0 g
  have hfg := L2.integrable_inner (𝕜 := ℂ) f0 g
  have hfh := L2.integrable_inner (𝕜 := ℂ) f gh
  have h3h := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 3 f) (coordinateLp 3 gh)
  have h4h := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 4 f) (coordinateLp 4 gh)
  have h30 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 3 f) (coordinateLp 3 g0)
  have h40 := L2.integrable_inner (𝕜 := ℂ) (coordinateLp 4 f) (coordinateLp 4 g0)
  have he := integral_congr_ae (μ := angleMeasure) (by
    filter_upwards [(growingAction ε a ha h 0).coeFn_compLp f,
      (growingAction ε a ha h h).coeFn_compLp g,
      (growingAction ε a ha h 0).coeFn_compLp g,
      (coordinate 3).coeFn_compLp f,(coordinate 4).coeFn_compLp f,
      (coordinate 3).coeFn_compLp gh,(coordinate 4).coeFn_compLp gh,
      (coordinate 3).coeFn_compLp g0,(coordinate 4).coeFn_compLp g0]
        with θ hf0 hgh hg0 h3f h4f h3h h4h h30 h40
    change f0 θ=growingAction ε a ha h 0 (f θ) at hf0
    change gh θ=growingAction ε a ha h h (g θ) at hgh
    change g0 θ=growingAction ε a ha h 0 (g θ) at hg0
    change coordinateLp 3 f θ=f θ 3 at h3f
    change coordinateLp 4 f θ=f θ 4 at h4f
    change coordinateLp 3 gh θ=gh θ 3 at h3h
    change coordinateLp 4 gh θ=gh θ 4 at h4h
    change coordinateLp 3 g0 θ=g0 θ 3 at h30
    change coordinateLp 4 g0 θ=g0 θ 4 at h40
    show inner ℂ (f0 θ) (g θ)+
      (inner ℂ (coordinateLp 3 f θ) (coordinateLp 3 gh θ)+
        inner ℂ (coordinateLp 4 f θ) (coordinateLp 4 gh θ))=
      inner ℂ (f θ) (gh θ)+
      (inner ℂ (coordinateLp 3 f θ) (coordinateLp 3 g0 θ)+
        inner ℂ (coordinateLp 4 f θ) (coordinateLp 4 g0 θ))
    rw [h3f,h4f,h3h,h4h,h30,h40,hf0,hgh,hg0]
    exact output_pairing ε a ha h (f θ) (g θ))
  have hsh : Integrable (fun θ => inner ℂ (coordinateLp 3 f θ) (coordinateLp 3 gh θ)+
      inner ℂ (coordinateLp 4 f θ) (coordinateLp 4 gh θ)) angleMeasure := h3h.add h4h
  have hs0 : Integrable (fun θ => inner ℂ (coordinateLp 3 f θ) (coordinateLp 3 g0 θ)+
      inner ℂ (coordinateLp 4 f θ) (coordinateLp 4 g0 θ)) angleMeasure := h30.add h40
  rw [integral_add hfg hsh,integral_add h3h h4h,
    integral_add hfh hs0,integral_add h30 h40] at he
  exact he

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "D" => KFCausalClockFloorGrowingHamiltonian.formData ε hε h hh hb m g k
local notation "V" => KFCausalClockFloorGrowingHamiltonian.GrowingForm ε hε h hh hb m g k
local notation "B" => KFCausalClosedGraphForm.energyOutput D
local notation "R" => rootOutput ε hε h hh hb m g k
local notation "F" => formAction ε hε a ha h hh hb

theorem form_pairing (u v : V) :
    inner ℂ (B (F 0 m g k u)) (B v)+inner ℂ (R u) (R (F h m g k v))=
      inner ℂ (B u) (B (F h m g k v))+inner ℂ (R u) (R (F 0 m g k v)) := by
  let kp : EnergyOutputSpace → EnergyOutputSpace → ℂ := fun f g =>
    inner ℂ (coordinateLp 3 f) (coordinateLp 3 g)+
      inner ℂ (coordinateLp 4 f) (coordinateLp 4 g)
  have e0 := formAction_output ε hε a ha h hh hb 0 m g k u
  have eh := formAction_output ε hε a ha h hh hb h m g k v
  have ev := formAction_output ε hε a ha h hh hb 0 m g k v
  have kh : inner ℂ (R u) (R (F h m g k v))=kp (B u) (growingActionLp ε a ha h h (B v)) :=
    (rootOutput_inner ε hε h hh hb m g k u (F h m g k v)).trans
      (congrArg (kp (B u)) eh)
  have k0 : inner ℂ (R u) (R (F 0 m g k v))=kp (B u) (growingActionLp ε a ha h 0 (B v)) :=
    (rootOutput_inner ε hε h hh hb m g k u (F 0 m g k v)).trans
      (congrArg (kp (B u)) ev)
  exact (congrArg₂ (fun x y : ℂ => x+y)
    (congrArg (fun z : EnergyOutputSpace => inner ℂ z (B v)) e0) kh).trans
      ((orbit_pairing ε a ha h (B u) (B v)).trans
        (congrArg₂ (fun x y : ℂ => x+y)
          (congrArg (fun z : EnergyOutputSpace => inner ℂ (B u) z) eh).symm k0.symm))

#print axioms coordinate_action
#print axioms output_pairing
#print axioms orbit_pairing
#print axioms form_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorGaussianGrowingOutputPairing
