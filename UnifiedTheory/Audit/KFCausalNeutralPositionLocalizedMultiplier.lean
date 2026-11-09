/- An explicit Gaussian-localized physical neutral-position observable has a
bounded analytic continuation on the actual clock strip. The resulting
operator is identified on all physical L2 vectors, not only on packets. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase
import UnifiedTheory.Audit.KFCausalStripFamilyPhysicalMultiplier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow scale)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped mix)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space split)
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit (TailSpace tail)
open UnifiedTheory.Audit.KFCausalClockFloorGaussianL1 (tailGrouping tailGrouping_apply tailGrouping_continuous)
open UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase
open UnifiedTheory.Audit.KFCausalStripFamilyExponentialGraph
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorFullGaussian (third_strip_subset inverse_line_continuous)

def family (ε δ v : ℝ) (q : ℂ) (z : TailSpace) : ℂ := multiplier ε δ v q (tailGrouping z)
def stripBound (ε δ v : ℝ) : ℝ := Real.exp (v^2*(Real.pi*ε/3)^2/(2*δ*ε^2))

theorem family_analytic (ε δ v : ℝ) (hε : 0 < ε) (z : TailSpace) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) : AnalyticAt ℂ (fun q => family ε δ v q z) q :=
  multiplier_analytic ε δ v hε q (third_strip_subset ε hε q hq) _

theorem family_line_continuous (ε δ v : ℝ) (hε : 0 < ε) (y : ℝ)
    (hy : |y| ≤ Real.pi*ε/3) :
    Continuous (fun w : ℝ × TailSpace => family ε δ v ((w.1:ℂ)+(y:ℂ)*Complex.I) w.2) := by
  have hi := (inverse_line_continuous ε y hε hy).comp (continuous_fst (Y := TailSpace))
  have hg := tailGrouping_continuous.comp (continuous_snd (X := ℝ))
  unfold family multiplier localized phase KFCausalClockFloorCoherentBounds.neutral
    KFCausalClockFloorShearBounds.complexScale mix
  fun_prop

theorem family_bound (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) (z : TailSpace) : ‖family ε δ v q z‖ ≤ stripBound ε δ v := by
  apply (multiplier_bound ε δ v hε hδ q hq _).trans
  apply Real.exp_le_exp.mpr
  have hs := pow_le_pow_left₀ (abs_nonneg _) hq 2
  rw [sq_abs] at hs
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (sq_nonneg v)) (by positivity)

def action (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) :
    Hilbert →L[ℂ] Hilbert :=
  physicalMultiplier (family ε δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε δ v hε) (Real.exp_pos _).le (family_bound ε δ v hε hδ) ε hε y hy

def physicalPhase (δ v : ℝ) (x : Configuration) : ℂ :=
  Complex.exp (-(δ:ℂ)*((x.2 2+x.2 3:ℝ):ℂ)^2)*KFCausalCanonicalWeylAlgebra.scalar (v*x.2 4)

theorem localized_real (δ v s : ℝ) (x : Transverse) :
    localized δ v (s:ℂ) (fun i : Fin 4 => x i.castSucc,x 4) = physicalPhase δ v (s,flow s x) := by
  have hx : ![x 0,x 1,x 2,x 3,x 4] = x := by funext i; fin_cases i <;> rfl
  have hs : scale s*scale s = Real.exp s := by
    rw [scale,← Real.exp_add]
    congr 1
    ring
  have hm : (flow s x 2+flow s x 3)^2 = Real.exp s*(x 2+x 3)^2 := by
    simp only [flow,Fin.reduceEq,ite_false]
    calc
      (scale s*x 2+scale s*x 3)^2 = (scale s*scale s)*(x 2+x 3)^2 := by ring
      _ = _ := by rw [hs]
  rw [localized,phase_real]
  change Complex.exp _*KFCausalCanonicalWeylAlgebra.scalar (v*flow s ![x 0,x 1,x 2,x 3,x 4] 4) = _
  rw [hx]
  unfold physicalPhase
  apply congrArg (fun c : ℂ => Complex.exp c*KFCausalCanonicalWeylAlgebra.scalar (v*flow s x 4))
  change -(δ:ℂ)*Complex.exp (s:ℂ)*((x 2+x 3:ℝ):ℂ)^2 =
    -(δ:ℂ)*((flow s x 2+flow s x 3:ℝ):ℂ)^2
  rw [← Complex.ofReal_exp,← Complex.ofReal_pow,← Complex.ofReal_pow,hm,Complex.ofReal_mul]
  ring

theorem family_zero_physical (ε δ v : ℝ) (hε : 0 < ε) (x : Space) :
    symbol (family ε δ v) 0 x =
      physicalPhase δ v ((coordinateHomeomorph ε hε).symm (split x)) := by
  simp only [symbol,family,multiplier,Complex.ofReal_zero,zero_mul,add_zero,
    KFCausalComplexClockInverse.complexInverse_real ε hε,tailGrouping_apply]
  exact localized_real δ v _ _

theorem action_coe (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    action ε δ v hε hδ y hy f =ᵐ[volume]
      fun x => KFCausalStripFamilyPhysicalMultiplier.physicalSymbol ε hε (family ε δ v) y x*f x :=
  KFCausalStripFamilyPhysicalMultiplier.physicalMultiplier_representative ε hε
    (family ε δ v) (Real.pi*ε/3) (stripBound ε δ v)
    (family_line_continuous ε δ v hε) (Real.exp_pos _).le (family_bound ε δ v hε hδ) y hy f

theorem action_zero_coe (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (f : Hilbert) :
    action ε δ v hε hδ 0 h0 f =ᵐ[volume] fun x => physicalPhase δ v x*f x := by
  filter_upwards [action_coe ε δ v hε hδ 0 h0 f] with x hx
  rw [hx]
  unfold KFCausalStripFamilyPhysicalMultiplier.physicalSymbol
  rw [family_zero_physical ε δ v hε,MeasurableEquiv.apply_symm_apply,Homeomorph.symm_apply_apply]

theorem action_norm (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/3) (f : Hilbert) :
    ‖action ε δ v hε hδ y hy f‖ ≤ Real.exp (v^2*y^2/(2*δ*ε^2))*‖f‖ := by
  apply physicalMultiplier_norm
  intro x
  exact (multiplier_bound ε δ v hε hδ _ (by simpa using hy) _).trans_eq (by simp)

theorem action_zero_contractive (ε δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/3) (f : Hilbert) : ‖action ε δ v hε hδ 0 h0 f‖ ≤ ‖f‖ := by
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_div,Real.exp_zero,one_mul]
    using action_norm ε δ v hε hδ 0 h0 f

#print axioms family_analytic
#print axioms family_line_continuous
#print axioms family_bound
#print axioms localized_real
#print axioms family_zero_physical
#print axioms action_coe
#print axioms action_zero_coe
#print axioms action_norm
#print axioms action_zero_contractive

end
end UnifiedTheory.Audit.KFCausalNeutralPositionLocalizedMultiplier
