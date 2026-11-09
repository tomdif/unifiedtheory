/- The speed -1/2 squeeze balances both kinetic pairs at exp(t) in the
actual weak equation. The clock, quartic and vacuum terms and the added
-1/2 squeeze generator remain present. -/
import UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingDynamics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorBalancedSqueeze
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSqueezeEnergy (OutputSpace coordinate coordinateLp)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeEnergy (degree)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingPairing (weightedPairing)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (timeScale)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)

def timeDegree (i : Fin 8) : ℝ := if i.val<3 then 0 else 1
def balancedDegree (i : Fin 8) : ℝ := 2*timeDegree i-degree i

theorem balanced_degrees : balancedDegree = ![0,1,1,1,1,1,0,2] := by
  funext i
  fin_cases i <;> simp [balancedDegree,timeDegree,degree] <;> norm_num

theorem timeScale_exp (t : ℝ) (i : Fin 8) : timeScale 0 t i = (Real.exp (timeDegree i*t):ℂ) := by
  by_cases hi : i.val<3 <;> simp [timeScale,timeDegree,hi]

theorem coordinate_time (t : ℝ) (i : Fin 8) (x : OutputSpace) :
    coordinateLp i (timeOutputLp 0 t x) = timeScale 0 t i • coordinateLp i x := by
  apply Lp.ext
  filter_upwards [(coordinate i).coeFn_compLp (timeOutputLp 0 t x),
    (KFCausalPhysicalEnergyTransport.timeOutput 0 t).coeFn_compLp x,
    Lp.coeFn_smul (timeScale 0 t i) (coordinateLp i x),(coordinate i).coeFn_compLp x]
    with θ hc ht hs hx
  change (coordinate i).compLp (timeOutputLp 0 t x) θ = _
  rw [hc,hs]
  simp only [Pi.smul_apply]
  change coordinate i ((KFCausalPhysicalEnergyTransport.timeOutput 0 t).compLp x θ) =
    timeScale 0 t i • (coordinate i).compLp x θ
  rw [ht,hx]
  rfl

def balancedPairing (t : ℝ) (x y : OutputSpace) : ℂ :=
  ∑ i : Fin 8, (Real.exp (balancedDegree i*t):ℂ)*inner ℂ (coordinateLp i x) (coordinateLp i y)

theorem balanced_output_pairing (t : ℝ) (x y : OutputSpace) :
    weightedPairing ((-1/2:ℝ)*t) (timeOutputLp 0 t x) (timeOutputLp 0 t y) = balancedPairing t x y := by
  unfold weightedPairing balancedPairing
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinate_time,coordinate_time,inner_smul_left,inner_smul_right,timeScale_exp,Complex.conj_ofReal]
  have he : (Real.exp (2*degree i*((-1/2)*t)):ℂ)*
      ((Real.exp (timeDegree i*t):ℂ)*(Real.exp (timeDegree i*t):ℂ)) =
      (Real.exp (balancedDegree i*t):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add,← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    unfold balancedDegree
    ring
  calc
    _ = ((Real.exp (2*degree i*((-1/2)*t)):ℂ)*
        ((Real.exp (timeDegree i*t):ℂ)*(Real.exp (timeDegree i*t):ℂ)))*
        inner ℂ (coordinateLp i x) (coordinateLp i y) := by ring
    _ = _ := by rw [he]

theorem balancedPairing_explicit (t : ℝ) (x y : OutputSpace) :
    balancedPairing t x y = inner ℂ (coordinateLp 0 x) (coordinateLp 0 y)+
      (Real.exp t:ℂ)*(inner ℂ (coordinateLp 1 x) (coordinateLp 1 y)+
        inner ℂ (coordinateLp 2 x) (coordinateLp 2 y)+inner ℂ (coordinateLp 3 x) (coordinateLp 3 y)+
        inner ℂ (coordinateLp 4 x) (coordinateLp 4 y)+inner ℂ (coordinateLp 5 x) (coordinateLp 5 y))+
      inner ℂ (coordinateLp 6 x) (coordinateLp 6 y)+
      (Real.exp (2*t):ℂ)*inner ℂ (coordinateLp 7 x) (coordinateLp 7 y) := by
  simp [balancedPairing,balanced_degrees,Fin.sum_univ_succ]
  ring

open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorSqueezePairing (timeOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSqueezeMovingDynamics
open UnifiedTheory.Audit.KFCausalPairedSqueezeGenerator (squeezeMomentum)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0) (hh : |h| ≤ 2*Real.pi*ε/3)
  (m q k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m q k 0
local notation "J" => embedding ε hε h hne hh m q k 0
local notation "A" => energyOutput ε hε h hne hh m q k 0

theorem balanced_form_pairing (t : ℝ) (u v : V) (z : Hilbert) :
    transformedPairing ε hε h hne hh m q k (-1/2) t u v z =
      balancedPairing t (A u) (A v)-(1/2:ℂ)*inner ℂ (J u) z := by
  have hu : timeOutput ε hε h hne hh m q k t u = timeOutputLp 0 t (A u) :=
    transfer_energyOutput ε hε h hne hh m q k 0 t u
  have hv : timeOutput ε hε h hne hh m q k t v = timeOutputLp 0 t (A v) :=
    transfer_energyOutput ε hε h hne hh m q k 0 t v
  have he : weightedPairing ((-1/2:ℝ)*t) (timeOutput ε hε h hne hh m q k t u)
      (timeOutput ε hε h hne hh m q k t v) = balancedPairing t (A u) (A v) :=
    (congrArg₂ (weightedPairing ((-1/2:ℝ)*t)) hu hv).trans (balanced_output_pairing t (A u) (A v))
  have ha (P Z : ℂ) : P+(((-1/2:ℝ):ℂ))*Z = P-(1/2:ℂ)*Z := by
    push_cast
    ring
  exact (congrArg (fun P : ℂ => P+(((-1/2:ℝ):ℂ))*inner ℂ (J u) z) he).trans (ha _ _)

theorem balanced_weak_derivative (s t : ℝ) (w v : V) (z : Hilbert)
    (hvz : (J v,z) ∈ (squeezeMomentum h).graph) :
    HasDerivAt (fun b => inner ℂ (transformedState ε hε h hne hh m q k (-1/2) s b (J w)) (J v))
      (coefficient h*(balancedPairing t
        (A (transformedFormState ε hε h hne hh m q k (-1/2) s t w)) (A v)-
          (1/2:ℂ)*inner ℂ
            (J (transformedFormState ε hε h hne hh m q k (-1/2) s t w)) z)) t := by
  simpa only [balanced_form_pairing] using
    transformed_weak_derivative ε hε h hne hh m q k (-1/2) s t w v z hvz

#print axioms balanced_degrees
#print axioms timeScale_exp
#print axioms coordinate_time
#print axioms balanced_output_pairing
#print axioms balancedPairing_explicit
#print axioms balanced_form_pairing
#print axioms balanced_weak_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorBalancedSqueeze
