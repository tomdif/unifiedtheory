/- The physical linear, quadratic and mixed field outputs of the actual
shifted Gaussian have continuous charge orbits. Polarization constructs
the neutral mixed moment from existing quadratic field outputs. -/
import UnifiedTheory.Audit.KFCausalCoherentShearPolynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalCoherentShearMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoherentShearPolynomial (coordinate mix)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentShiftedOrbit (shiftedOutput_eq_scalarOutput)
open UnifiedTheory.Audit.KFCausalChargeModulationFlow (parameter)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
variable (hbound : |h| ≤ 2*Real.pi*ε/3)

def linear (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  KFCausalClockFloorCoherentMatterOrbit.linearOutput ε a h hε ha hh (-h/2) (shift_bound ε h hbound) k l

def quadratic (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) : Hilbert :=
  KFCausalClockFloorCoherentMatterOrbit.quadraticOutput ε a h hε ha hh (-h/2) (shift_bound ε h hbound) k l

theorem linear_coe (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    linear ε a h hε ha hh hbound k l =ᵐ[volume] fun x =>
      (l x.2:ℂ)*shiftedOutput ε a h hε ha hh hbound k x := by
  have hg := KFCausalClockFloorCoherentMatterOrbit.linearOutput_graph ε a h hε ha hh
    (-h/2) (shift_bound ε h hbound) k l
  rw [← shiftedOutput_eq_scalarOutput ε a h hε ha hh hbound k] at hg
  exact (KFCausalPhysicalField.physicalField_graph l _ _).mp hg

theorem quadratic_coe (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    quadratic ε a h hε ha hh hbound k l =ᵐ[volume] fun x =>
      (l x.2:ℂ)^2*shiftedOutput ε a h hε ha hh hbound k x := by
  have hg := KFCausalClockFloorCoherentMatterOrbit.quadraticOutput_graph ε a h hε ha hh
    (-h/2) (shift_bound ε h hbound) k l
  rw [← shiftedOutput_eq_scalarOutput ε a h hε ha hh hbound k] at hg
  exact (KFCausalTransverseFieldSquare.fieldSquare_graph l _ _).mp hg

theorem linear_orbit_continuous (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => linear ε a h hε ha hh hbound (parameter θ k) l) :=
  KFCausalClockFloorCoherentMatterOrbit.linearOutput_orbit_continuous ε a h hε ha hh
    (-h/2) (shift_bound ε h hbound) k l

theorem quadratic_orbit_continuous (k : Joint 2 4) (l : Transverse →L[ℝ] ℝ) :
    Continuous (fun θ => quadratic ε a h hε ha hh hbound (parameter θ k) l) :=
  KFCausalClockFloorCoherentMatterOrbit.quadraticOutput_orbit_continuous ε a h hε ha hh
    (-h/2) (shift_bound ε h hbound) k l

def mixed (k : Joint 2 4) : Hilbert := (1/2:ℂ) •
  (quadratic ε a h hε ha hh hbound k (coordinate 4+mix)-
    quadratic ε a h hε ha hh hbound k (coordinate 4)-quadratic ε a h hε ha hh hbound k mix)

theorem mixed_coe (k : Joint 2 4) :
    mixed ε a h hε ha hh hbound k =ᵐ[volume] fun x =>
      (x.2 4:ℂ)*(mix x.2:ℂ)*shiftedOutput ε a h hε ha hh hbound k x := by
  let Q := quadratic ε a h hε ha hh hbound k
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (Q (coordinate 4+mix)-Q (coordinate 4)-Q mix),
    Lp.coeFn_sub (Q (coordinate 4+mix)-Q (coordinate 4)) (Q mix),
    Lp.coeFn_sub (Q (coordinate 4+mix)) (Q (coordinate 4)),
    quadratic_coe ε a h hε ha hh hbound k (coordinate 4+mix),
    quadratic_coe ε a h hε ha hh hbound k (coordinate 4),
    quadratic_coe ε a h hε ha hh hbound k mix] with x hs hsub hsub' hp hq hr
  change ((1/2:ℂ) • (Q (coordinate 4+mix)-Q (coordinate 4)-Q mix)) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hsub']
  change Q (coordinate 4+mix) x = _ at hp
  change Q (coordinate 4) x = _ at hq
  change Q mix x = _ at hr
  simp only [Pi.sub_apply]
  rw [hp,hq,hr]
  simp only [ContinuousLinearMap.add_apply,coordinate,ContinuousLinearMap.proj_apply,Complex.ofReal_add]
  ring

theorem mixed_orbit_continuous (k : Joint 2 4) :
    Continuous (fun θ => mixed ε a h hε ha hh hbound (parameter θ k)) :=
  (((quadratic_orbit_continuous ε a h hε ha hh hbound k (coordinate 4+mix)).sub
    (quadratic_orbit_continuous ε a h hε ha hh hbound k (coordinate 4))).sub
      (quadratic_orbit_continuous ε a h hε ha hh hbound k mix)).const_smul _

#print axioms linear_coe
#print axioms quadratic_coe
#print axioms linear_orbit_continuous
#print axioms quadratic_orbit_continuous
#print axioms mixed_coe
#print axioms mixed_orbit_continuous
end
end UnifiedTheory.Audit.KFCausalCoherentShearMoments
