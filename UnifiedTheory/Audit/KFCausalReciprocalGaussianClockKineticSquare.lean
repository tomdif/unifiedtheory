/- Second clock and kinetic actions for the reciprocal family and its
actual clock momentum. The kinetic squeeze weights are squared. -/
import UnifiedTheory.Audit.KFCausalGaussianClockSquare
import UnifiedTheory.Audit.KFCausalKineticSquareClockOutput
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianClockKineticSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalSqueezeFlow (squeeze squeeze_directions)
open KFCausalReciprocalSqueezeClockCommutation (inverse_half_commutes)
open KFCausalReciprocalSqueezeKinetic (kineticScale half_graph)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorKineticSquare (square square_graph)
open KFCausalClockFloorClockHalf (clockHalf)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalPhysicalEnergyFactors (modelDirections)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalReciprocalGaussianDomain
open KFCausalReciprocalGaussianMomentum (momentum state_eq_transport output momentumOutput)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

theorem kinetic_square_transport (ε : ℝ) (hε : 0 < ε) (h a q : ℝ) (v : Transverse)
    (hv : squeeze a v = Real.exp q • v) (f z : Hilbert)
    (hfz : (f,z) ∈ (square ε h v).graph) :
    (transport a f,(Real.exp (-q):ℂ)^2 • transport a z) ∈ (square ε h v).graph := by
  obtain ⟨u,r,hdu,hur,hz⟩ := (square_graph ε hε h v f z).mp hfz
  have h1 := KFCausalReciprocalSqueezeKinetic.momentum_graph h a q v hv _ _ hdu
  rw [inverse_half_commutes] at h1
  have h2 := (transverseMomentum h v).graph.smul_mem (Real.exp (-q):ℂ)
    (KFCausalReciprocalSqueezeKinetic.momentum_graph h a q v hv _ _ hur)
  apply (square_graph ε hε h v _ _).mpr
  refine ⟨_,_,h1,h2,?_⟩
  change (Real.exp (-q):ℂ)^2 • transport a z =
    inverseL ε hε ((Real.exp (-q):ℂ) • ((Real.exp (-q):ℂ) • transport a r))
  rw [hz,inverse_half_commutes,map_smul,map_smul,smul_smul,pow_two]

theorem model_square_transport (ε : ℝ) (hε : 0 < ε) (h a : ℝ) (i : Fin 4)
    (f z : Hilbert) (hfz : (f,z) ∈ (square ε h (modelDirections i)).graph) :
    (transport a f,kineticScale a i ^ 2 • transport a z) ∈
      (square ε h (modelDirections i)).graph := by
  by_cases hi : i=1 ∨ i=2
  · have hv : squeeze a (modelDirections i) = Real.exp a • modelDirections i := by
      simpa only [hi,if_true] using squeeze_directions a i
    simpa only [kineticScale,hi,if_true] using kinetic_square_transport ε hε h a a _ hv f z hfz
  · have hv : squeeze a (modelDirections i) = Real.exp (-a) • modelDirections i := by
      simpa only [hi,if_false] using squeeze_directions a i
    simpa only [kineticScale,hi,if_false,neg_neg] using kinetic_square_transport ε hε h a (-a) _ hv f z hfz

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "ψ" => KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith)
local notation "c" => (Real.exp (-t/2):ℂ)

def kineticOutput (i : Fin 4) : Hilbert := c • (kineticScale (-t) i ^ 2 • transport (-t)
  (KFCausalGaussianKineticSquare.squareOutput ε a α β hε ha hα hβ h (modelDirections i)))

def momentumKineticOutput (i : Fin 4) : Hilbert := c • (kineticScale (-t) i ^ 2 • transport (-t)
  (KFCausalKineticSquareClockOutput.momentumOutput ε a h hε ha α β hα hβ (modelDirections i)))

def clockOutput : Hilbert := c • transport (-t)
  (KFCausalGaussianClockSquare.output ε a α β hε ha hα hβ hbw 1 0 0)

def momentumClockOutput : Hilbert := c • transport (-t)
  (KFCausalGaussianClockSquare.momentumOutput ε a α β hε ha hα hβ hbw 1 0 0 h)

theorem kinetic_graph (i : Fin 4) :
    (ψ,kineticOutput ε a h w hε ha hh i) ∈ (square ε h (modelDirections i)).graph := by
  rw [state_eq_transport ε a h w hε ha hh hw]
  exact (square ε h (modelDirections i)).graph.smul_mem c
    (model_square_transport ε hε h (-t) i _ _
      (KFCausalGaussianKineticSquare.squareOutput_graph ε a α β hε ha hα hβ hbw h (modelDirections i)))

theorem momentum_kinetic_graph (i : Fin 4) :
    (momentum ε a h w hε ha hh hw,momentumKineticOutput ε a h w hε ha hh i) ∈
      (square ε h (modelDirections i)).graph :=
  (square ε h (modelDirections i)).graph.smul_mem c
    (model_square_transport ε hε h (-t) i _ _
      (KFCausalKineticSquareClockOutput.momentum_graph ε a h hε ha α β hα hβ hbw hh (modelDirections i)))

theorem clock_graph (hb : |h| ≤ 2*Real.pi*ε/3) :
    (output ε a h w hε ha hh hw hb 0,clockOutput ε a h w hε ha hh hw) ∈ (clockHalf ε).graph := by
  have he : output ε a h w hε ha hh hw hb 0 =
      c • transport (-t) (KFCausalClockFloorSourcedClockMomentum.clockOutput
        ε a α β hε ha hα hβ hbw 1 0 0) := by
    simp [output,KFCausalReciprocalSqueezeEnergy.factorScale,KFCausalReciprocalSqueezeEnergy.degree,
      KFCausalClockFloorSourcedCommonDomain.factorOutput]
  rw [he]
  exact (clockHalf ε).graph.smul_mem c (half_graph ε (-t) _ _
    (KFCausalGaussianClockSquare.second_graph ε a α β hε ha hα hβ hbw 1 0 0))

theorem momentum_clock_graph (hb : |h| ≤ 2*Real.pi*ε/3) :
    (momentumOutput ε a h w hε ha hh hw hb 0,momentumClockOutput ε a h w hε ha hh hw) ∈
      (clockHalf ε).graph := by
  have he : momentumOutput ε a h w hε ha hh hw hb 0 =
      c • transport (-t) (KFCausalSourcedMomentumFactors.factorOutput
        ε a α β hε ha hα hβ hbw 1 0 0 h hb modelDirections pointField 0) := by
    simp [momentumOutput,KFCausalReciprocalSqueezeEnergy.factorScale,KFCausalReciprocalSqueezeEnergy.degree]
  rw [he]
  exact (clockHalf ε).graph.smul_mem c (half_graph ε (-t) _ _
    (KFCausalGaussianClockSquare.momentum_second_graph ε a α β hε ha hα hβ hbw 1 0 0 h hb
      modelDirections pointField))

#print axioms kinetic_square_transport
#print axioms model_square_transport
#print axioms kinetic_graph
#print axioms momentum_kinetic_graph
#print axioms clock_graph
#print axioms momentum_clock_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianClockKineticSquare
