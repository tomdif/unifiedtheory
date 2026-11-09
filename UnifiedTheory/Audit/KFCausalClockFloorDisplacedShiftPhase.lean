/- The longitudinal imaginary shift produces the physical shear weight
at a displaced centre. The inverse-hbar phase is treated through a proved
derivative, retaining the neutral shear. No energy-integral limit follows
from this pointwise phase result alone. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedCentering

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorBoostedClockPhase
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect (realClock)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (complexScale)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse velocity)

def grouped (Q : Transverse) : KFCausalClockFloorShearBounds.Grouped :=
  (![Q 0,Q 1,Q 2,Q 3],Q 4)

theorem complexScale_sub_real (z : ℂ) (s : ℝ) :
    complexScale (z-(s:ℂ)) = complexScale z*(KFCausalTransverseDilationFlow.scale (-s):ℂ) := by
  simp only [complexScale,KFCausalTransverseDilationFlow.scale,Complex.ofReal_exp,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat,← Complex.exp_add]
  congr 1
  ring

theorem position_recenter (z : ℂ) (s : ℝ) (Q : Transverse) (i : Fin 5) :
    KFCausalClockFloorCoherentBounds.position z
      (grouped (KFCausalTransverseDilationFlow.flow (-s) Q)) i =
      if i = 4 then (Q 4:ℂ)+2*(complexScale (z-(s:ℂ))-1)*((Q 2+Q 3:ℝ):ℂ)
      else complexScale (z-(s:ℂ))*(Q i:ℂ) := by
  rw [complexScale_sub_real]
  fin_cases i <;> simp [KFCausalClockFloorCoherentBounds.position,
    KFCausalClockFloorCoherentBounds.neutral,KFCausalClockFloorShearBounds.mix,
    grouped,KFCausalTransverseDilationFlow.flow] <;> ring

def relativeScale (ε q h : ℝ) : ℂ :=
  complexScale (inverseShift ε q h-inverseShift ε q 0)

theorem relativeScale_zero (ε q : ℝ) : relativeScale ε q 0 = 1 := by
  simp [relativeScale,complexScale]

theorem relativeScale_derivative (ε q : ℝ) (hε : 0 < ε) :
    HasDerivAt (relativeScale ε q) (-Complex.I/(4*(realClock ε hε q:ℂ))) 0 := by
  have hd := (((inverseShift_derivative ε q hε).sub_const (inverseShift ε q 0)).div_const 2).cexp
  convert hd using 1
  simp only [sub_self,zero_div,Complex.exp_zero,one_mul]
  ring

def shiftedPosition (ε q h : ℝ) (Q : Transverse) (i : Fin 5) : ℂ :=
  if i = 4 then (Q 4:ℂ)+2*(relativeScale ε q h-1)*((Q 2+Q 3:ℝ):ℂ)
  else relativeScale ε q h*(Q i:ℂ)

theorem shiftedPosition_zero (ε q : ℝ) (Q : Transverse) (i : Fin 5) :
    shiftedPosition ε q 0 Q i = (Q i:ℂ) := by
  by_cases hi : i = 4 <;> simp [shiftedPosition,relativeScale_zero,hi]

theorem shiftedPosition_actual (ε q h : ℝ) (hε : 0 < ε) (Q : Transverse) (i : Fin 5) :
    KFCausalClockFloorCoherentBounds.position (inverseShift ε q h)
      (grouped (KFCausalTransverseDilationFlow.flow
        (-((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm q)) Q)) i =
      shiftedPosition ε q h Q i := by
  rw [position_recenter]
  simp only [shiftedPosition,relativeScale,inverseShift_zero,
    KFCausalComplexClockInverse.complexInverse_real ε hε]

theorem shiftedPosition_derivative (ε q : ℝ) (hε : 0 < ε) (Q : Transverse) (i : Fin 5) :
    HasDerivAt (fun h => shiftedPosition ε q h Q i)
      ((-Complex.I/(2*(realClock ε hε q:ℂ)))*(velocity Q i:ℂ)) 0 := by
  by_cases hi : i = 4
  · subst i
    have hd := ((((relativeScale_derivative ε q hε).sub_const 1).const_mul 2).mul_const
      ((Q 2+Q 3:ℝ):ℂ)).const_add (Q 4:ℂ)
    convert hd using 1
    change (-Complex.I/(2*(realClock ε hε q:ℂ)))*((Q 2+Q 3:ℝ):ℂ) =
      2*(-Complex.I/(4*(realClock ε hε q:ℂ)))*((Q 2+Q 3:ℝ):ℂ)
    ring
  · have hd := (relativeScale_derivative ε q hε).mul_const (Q i:ℂ)
    convert hd using 1 <;> simp [shiftedPosition,velocity,hi]
    ring

def shear (Q P : Transverse) : ℝ := ∑ i, velocity Q i*P i
def transverseRatio (ε q h : ℝ) (Q P : Transverse) : ℂ :=
  Complex.exp (Complex.I*∑ i, ((P i:ℝ):ℂ)*(h:ℂ)⁻¹*(shiftedPosition ε q h Q i-(Q i:ℂ)))

theorem transverseRatio_tendsto (ε q : ℝ) (hε : 0 < ε) (Q P : Transverse) :
    Tendsto (fun h => transverseRatio ε q h Q P) (𝓝[≠] (0:ℝ))
      (𝓝 (Complex.exp ((shear Q P/(2*realClock ε hε q):ℝ):ℂ))) := by
  have ht (i : Fin 5) := ((shiftedPosition_derivative ε q hε Q i).tendsto_slope).const_mul (P i:ℂ)
  have hs := (tendsto_finset_sum Finset.univ (fun i _ => ht i)).const_mul Complex.I
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hs
  convert he using 1
  · funext h
    simp only [transverseRatio,slope_def_module,sub_zero,Complex.real_smul,Complex.ofReal_inv,
      shiftedPosition_zero]
    congr 1
    apply congrArg (fun z : ℂ => Complex.I*z)
    apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 2
    simp only [shear,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem transverseRatio_energy_tendsto (ε q : ℝ) (hε : 0 < ε) (Q P : Transverse) :
    Tendsto (fun h => ‖transverseRatio ε q h Q P‖^2) (𝓝[≠] (0:ℝ))
      (𝓝 (Real.exp (shear Q P/realClock ε hε q))) := by
  have ht := (transverseRatio_tendsto ε q hε Q P).norm.pow 2
  rw [Complex.norm_exp,Complex.ofReal_re,← Real.exp_nat_mul] at ht
  convert ht using 1
  congr 2
  norm_num only [Nat.cast_ofNat]
  ring

theorem full_phase_energy_tendsto (ε q r : ℝ) (hε : 0 < ε) (Q P : Transverse) :
    Tendsto (fun h => ‖phaseRatio ε r q h*transverseRatio ε q h Q P‖^2) (𝓝[≠] (0:ℝ))
      (𝓝 (Real.exp ((r+shear Q P)/realClock ε hε q))) := by
  have ht := (phaseRatio_energy_tendsto ε r q hε).mul (transverseRatio_energy_tendsto ε q hε Q P)
  simpa only [norm_mul,mul_pow,← Real.exp_add,← add_div] using ht

#print axioms complexScale_sub_real
#print axioms position_recenter
#print axioms relativeScale_zero
#print axioms relativeScale_derivative
#print axioms shiftedPosition_zero
#print axioms shiftedPosition_actual
#print axioms shiftedPosition_derivative
#print axioms transverseRatio_tendsto
#print axioms transverseRatio_energy_tendsto
#print axioms full_phase_energy_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase
