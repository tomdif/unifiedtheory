/- Two independently variable charged radial widths in the original
physical charge chart. The clock, charge action and shear are unchanged.
The reciprocal family is recovered exactly on the diagonal. -/
import UnifiedTheory.Audit.KFCausalNormalizedComplexRotation
import UnifiedTheory.Audit.KFCausalBroadPairedGaussianSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialNormalization
noncomputable section
open KFCausalEuclideanProductCoordinates (Block Joint split)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexQuadraticPerturbation (mass weightedQuadratic)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalNormalizedComplexRotation (rotationIsometry rotationEquiv rotate)
open KFCausalClockFloorMixedChart (mixedMap)
open KFCausalClockFloorPairedStraightening (clockInverse dilation)

def normalize (α wL wR c : ℝ) (x : Joint 2 4) : Space := WithLp.toLp 2
  ![((Real.sqrt (α/wL)*c*x (.inl 0):ℝ):ℂ),
    ((Real.sqrt (α*wR)*c*x (.inl 1):ℝ):ℂ),
    ((Real.sqrt (α/wL)*x (.inr 1):ℝ):ℂ),
    ((Real.sqrt (α*wR)*x (.inr 2):ℝ):ℂ),
    ((Real.sqrt (α/32)*x (.inr 3):ℝ):ℂ)]

def weights (W wL wR : ℝ) : Fin 5 → ℝ :=
  ![wL/(4*W),1/(4*W*wR),wL/(4*W),1/(4*W*wR),1/(16*W)]

def physicalMass (α wL wR c : ℝ) (x : Joint 2 4) : ℝ :=
  (α/wL)*((c*x (.inl 0))^2+(x (.inr 1))^2)+
    (α*wR)*((c*x (.inl 1))^2+(x (.inr 2))^2)+(α/32)*(x (.inr 3))^2

theorem normalize_diagonal (α w c : ℝ) (x : Joint 2 4) :
    normalize α w w c x=KFCausalPhysicalReciprocalNormalization.normalize α w c x := rfl

theorem weights_diagonal (W w : ℝ) :
    weights W w w=KFCausalPhysicalReciprocalNormalization.weights W w := rfl

theorem normalize_real (α wL wR c : ℝ) (x : Joint 2 4) :
    ∀ i, (normalize α wL wR c x i).im=0 := by
  intro i
  fin_cases i <;> simp [normalize]

theorem weights_bound (W wL wR : ℝ) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (hW : wL ≤ W) :
    ∀ i, 0 ≤ weights W wL wR i ∧ weights W wL wR i ≤ 1/4 := by
  have hp : 0 < wL := by linarith
  have hq : 0 < wR := by linarith
  have hP : 0 < W := by linarith
  have hww : 1 ≤ W*wR := by nlinarith
  intro i
  fin_cases i <;> dsimp [weights]
  all_goals constructor
  all_goals first | positivity | (apply (div_le_iff₀ (by positivity)).mpr; nlinarith)

theorem normalize_mass (α wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL)
    (hR : 0 < wR) (x : Joint 2 4) :
    mass (fun i => normalize α wL wR c x i)=physicalMass α wL wR c x := by
  have h₁ := Real.sq_sqrt (div_nonneg hα.le hL.le)
  have h₂ := Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have h₃ := Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  simp only [mass,Fin.sum_univ_succ,Fin.sum_univ_zero,normalize,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Complex.norm_real,Real.norm_eq_abs,sq_abs,physicalMass]
  simp only [mul_pow,h₁,h₂,h₃]
  ring

theorem baseline_quadratic (α W wL wR c : ℝ) (hα : 0 < α) (hL : 0 < wL)
    (hR : 0 < wR) (hW : 0 < W) (x : Joint 2 4) :
    weightedQuadratic (weights W wL wR) (fun i => normalize α wL wR c x i)=
      (((α/(4*W))*KFCausalChargeGaussianGeometry.radius c x+
        (α/(512*W))*(x (.inr 3))^2:ℝ):ℂ) := by
  have h₁ := Real.sq_sqrt (div_nonneg hα.le hL.le)
  have h₂ := Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have h₃ := Real.sq_sqrt (show 0 ≤ α/32 by positivity)
  simp only [weightedQuadratic,Fin.sum_univ_succ,Fin.sum_univ_zero,normalize,weights,
    Matrix.cons_val_zero,Matrix.cons_val_succ,← Complex.ofReal_pow,← Complex.ofReal_mul]
  norm_cast
  rw [KFCausalChargeGaussianGeometry.radius_coordinates]
  simp only [mul_pow,h₁,h₂,h₃]
  field_simp
  ring

theorem normalize_shear (α wL wR c t : ℝ) (hα : 0 < α) (hR : 0 < wR) (x : Joint 2 4) :
    normalize α wL wR c (KFCausalChargeShearJointFlow.flow t x)=
      flow (coupling α wR) (t:ℂ) (normalize α wL wR c x) := by
  have hb : Real.sqrt (α*wR) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mul_pos hα hR))
  have he₁ : Complex.exp (-(t:ℂ)/2)=(Real.exp (-t/2):ℝ) := by
    rw [show -(t:ℂ)/2=((-t/2:ℝ):ℂ) by push_cast; rfl,Complex.ofReal_exp]
  have he₂ : Complex.exp ((t:ℂ)/2)=(Real.exp (t/2):ℝ) := by
    rw [show (t:ℂ)/2=((t/2:ℝ):ℂ) by push_cast; rfl,Complex.ofReal_exp]
  ext i
  fin_cases i <;> simp only [normalize,flow,Matrix.cons_val_zero,
    KFCausalChargeShearJointFlow.flow_first,
    KFCausalChargeShearJointFlow.flow_second,he₁,he₂]
  all_goals push_cast
  all_goals try ring
  simp only [coupling]
  push_cast
  have hbc : (Real.sqrt (α*wR):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp [hbc]
  ring

theorem physical_rotation (α wL wR c θ : ℝ) (hc : c ≠ 0) (x : Joint 2 4) :
    normalize α wL wR c (KFCausalNormalizedChargeFlow.flowEquiv c hc θ x)=
      rotationIsometry θ (normalize α wL wR c x) := by
  have h₁ := KFCausalNormalizedChargeFlow.flow_first_plane c hc θ x
  have h₂ := KFCausalNormalizedChargeFlow.flow_second_plane c hc θ x
  have h₁a := congrArg Prod.fst h₁
  have h₁b := congrArg Prod.snd h₁
  have h₂a := congrArg Prod.fst h₂
  have h₂b := congrArg Prod.snd h₂
  dsimp only at h₁a h₁b h₂a h₂b
  have hcc : (c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  ext i
  fin_cases i <;> simp [normalize,rotationIsometry,rotationEquiv,rotate,h₁a,h₁b,h₂a,h₂b,
    KFCausalNormalizedChargeFlow.flow_neutral]
  all_goals try field_simp [hcc]

theorem normalize_mixedMap (ε : ℝ) (hε : 0 < ε) (α wL wR c : ℝ)
    (hα : 0 < α) (hR : 0 < wR) (x : Block 2 × Block 4) :
    normalize α wL wR c ((split 2 4).symm (mixedMap ε hε x))=
      flow (coupling α wR) (clockInverse ε hε x.2:ℂ)
        (normalize α wL wR c ((split 2 4).symm x)) := by
  rw [← normalize_shear α wL wR c _ hα hR]
  have hl (v : Block 2 × Block 4) (i : Fin 2) : (split 2 4).symm v (.inl i)=v.1 i := rfl
  have hr (v : Block 2 × Block 4) (i : Fin 4) : (split 2 4).symm v (.inr i)=v.2 i := rfl
  ext i
  fin_cases i <;> simp [normalize,mixedMap,dilation,KFCausalClockFloorSpectatorChart.backward,
    KFCausalClockFloorSpectatorChart.changeClock,KFCausalClockFloorSpectatorChart.flow,
    KFCausalChargeShearJointFlow.flow_first,KFCausalChargeShearJointFlow.flow_second,
    clockInverse,hl,hr,← Real.exp_neg,← neg_div]

#print axioms normalize_diagonal
#print axioms weights_diagonal
#print axioms normalize_real
#print axioms weights_bound
#print axioms normalize_mass
#print axioms baseline_quadratic
#print axioms normalize_shear
#print axioms physical_rotation
#print axioms normalize_mixedMap
end
end UnifiedTheory.Audit.KFCausalIndependentRadialNormalization
