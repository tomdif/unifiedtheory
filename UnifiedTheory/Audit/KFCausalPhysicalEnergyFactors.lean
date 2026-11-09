/- The eight natural unaveraged energy factors: clock, four ordered
transverse momenta, linear and quadratic field potential factors, and
the vacuum exponential factor. Their common domain is proved dense. -/
import UnifiedTheory.Audit.KFCausalFiniteJointGraph
import UnifiedTheory.Audit.KFCausalClosedMatterFactorDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers
open UnifiedTheory.Audit.KFCausalClockMomentumClosure
open UnifiedTheory.Audit.KFCausalOrderedExponentialClosure
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalMatterFactorClosure
open UnifiedTheory.Audit.KFCausalMomentumMatterDomain
open UnifiedTheory.Audit.KFCausalClosedOrderedFactorDomain
open UnifiedTheory.Audit.KFCausalFiniteJointGraph

def modelDirections : Fin 4 → Transverse :=
  ![![1,1,0,0,0],![0,0,1,1,1],![1,-1,0,0,0],![0,0,1,-1,0]]

def energyFactor (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Fin 8 → Hilbert →ₗ.[ℂ] Hilbert :=
  ![clockPower (1/2),clockMomentum (-(1/2)) hbar (v 0),clockMomentum (-(1/2)) hbar (v 1),
    clockMomentum (-(1/2)) hbar (v 2),clockMomentum (-(1/2)) hbar (v 3),
    matterFactor ε hε hbar (physicalField l),matterFactor ε hε hbar (fieldSquare l),
    orderedExponential ε hε hbar]

theorem energyFactor_closable (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) (i : Fin 8) :
    (energyFactor ε hε hbar v l i).IsClosable := by
  fin_cases i
  · exact (clockPower_closed (1/2)).isClosable
  · exact clockMomentum_closable (-(1/2)) hbar (v 0)
  · exact clockMomentum_closable (-(1/2)) hbar (v 1)
  · exact clockMomentum_closable (-(1/2)) hbar (v 2)
  · exact clockMomentum_closable (-(1/2)) hbar (v 3)
  · exact linearMatter_closable ε hbar hε hh l
  · exact quadraticMatter_closable ε hbar hε hh l
  · exact orderedExponential_closable ε hbar hε hh

def commonEnergyDomain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) : Submodule ℂ Hilbert :=
  commonDomain (energyFactor ε hε hbar v l)

theorem orderedSpace_le_commonEnergyDomain (ε hbar : ℝ) (hε : 0 < ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    operatorOrderedSpace ε hε hbar l ≤ commonEnergyDomain ε hε hbar v l := by
  intro f hf
  apply (Submodule.mem_iInf _).mpr
  intro i
  fin_cases i
  · exact hf.1
  · exact orderedSpace_le_clockMomentum ε hbar hε l (v 0) hf
  · exact orderedSpace_le_clockMomentum ε hbar hε l (v 1) hf
  · exact orderedSpace_le_clockMomentum ε hbar hε l (v 2) hf
  · exact orderedSpace_le_clockMomentum ε hbar hε l (v 3) hf
  · exact orderedSpace_le_matterFactor ε hbar hε l _ (fieldSquare_domain_le_physicalField l) hf
  · exact orderedSpace_le_matterFactor ε hbar hε l _ le_rfl hf
  · exact orderedSpace_le_orderedExponential ε hbar hε l hf

theorem commonEnergyDomain_dense (ε hbar : ℝ) (hε : 0 < ε) (hh : |hbar| ≤ Real.pi*ε)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    Dense (commonEnergyDomain ε hε hbar v l : Set Hilbert) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hc := Submodule.topologicalClosure_mono (orderedSpace_le_commonEnergyDomain ε hbar hε v l)
  rw [operatorOrderedSpace_dense ε hbar hε hh l] at hc
  exact top_unique hc

def energyWeight (mass2 quartic vacuum t : ℝ) : Fin 8 → ℂ :=
  ![(Real.sqrt (1/2):ℂ),(Real.sqrt (1/2):ℂ),(Real.sqrt (1/2):ℂ),
    (Real.exp t*Real.sqrt (1/2):ℝ),(Real.exp t*Real.sqrt (1/2):ℝ),
    (Real.exp t*Real.sqrt (mass2/2):ℝ),(Real.exp t*Real.sqrt (quartic/4):ℝ),
    (Real.exp t*Real.sqrt vacuum:ℝ)]

theorem energyWeight_norm_square (mass2 quartic vacuum t : ℝ)
    (hm : 0 ≤ mass2) (hq : 0 ≤ quartic) (hv : 0 ≤ vacuum) (i : Fin 8) :
    ‖energyWeight mass2 quartic vacuum t i‖^2 =
      (![1/2,1/2,1/2,Real.exp (2*t)/2,Real.exp (2*t)/2,
        Real.exp (2*t)*mass2/2,Real.exp (2*t)*quartic/4,Real.exp (2*t)*vacuum] : Fin 8 → ℝ) i := by
  have he : (Real.exp t)^2=Real.exp (2*t) := by rw [← Real.exp_nat_mul]; norm_num
  have hs (r : ℝ) (hr : 0 ≤ r) : ‖(Real.sqrt r : ℂ)‖^2=r := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt hr]
  have ht : ‖(Real.exp t : ℂ)‖^2=Real.exp (2*t) := by
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs,he]
  fin_cases i <;> simp only [energyWeight,Matrix.cons_val_zero',Matrix.cons_val_succ',
    Complex.ofReal_mul,norm_mul,mul_pow,ht,
    hs (1/2) (by norm_num),hs (mass2/2) (by positivity),
    hs (quartic/4) (by positivity),hs vacuum hv] <;> ring


#print axioms energyFactor_closable
#print axioms orderedSpace_le_commonEnergyDomain
#print axioms commonEnergyDomain_dense
#print axioms energyWeight_norm_square

end
end UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors
