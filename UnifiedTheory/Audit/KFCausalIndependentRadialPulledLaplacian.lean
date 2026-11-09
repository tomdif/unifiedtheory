/- The proved ordered static representative is a differential expression
of the actual shifted sourced numerator. All widths and neutral derivatives
remain linked; this establishes no integration-by-parts estimate by itself. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialEntireLaplacian
import UnifiedTheory.Audit.KFCausalOrderedStaticOutputRepresentative

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPulledLaplacian
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalComplexShearPerturbation (Space flow)
open KFCausalComplexShearGroup (flow_compose)
open KFCausalIndependentRadialNormalization (normalize)
open KFCausalPhysicalReciprocalNormalization (coupling)
open KFCausalIndependentRadialHolomorphicQuotient (baselineVector)
open KFCausalIndependentRadialMomentInput (numerator left right neutral)
open KFCausalIndependentRadialEntireLaplacian (profile first second basis radiusLeft radiusRight)
open KFCausalComplexClockInverse (complexInverse)
open KFCausalClockFloorCoherentStrip (clockPhase)
open KFCausalPairedModeCoordinates (scale)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalNormalizedChargeFlow (momentumScale)
open KFCausalGaussianHolomorphicClockWeight (clockPower)

def coordinate (c : ℝ) (x : Joint 2 4) : Space := WithLp.toLp 2
  ![(c:ℂ)*(x (.inl 0):ℂ),(c:ℂ)*(x (.inl 1):ℂ),
    (x (.inr 1):ℂ),(x (.inr 2):ℂ),(x (.inr 3):ℂ)]

def scaledPoint (α wL wR : ℝ) (x : Space) : Space := WithLp.toLp 2
  ![(Real.sqrt (α/wL):ℂ)*x 0,(Real.sqrt (α*wR):ℂ)*x 1,
    (Real.sqrt (α/wL):ℂ)*x 2,(Real.sqrt (α*wR):ℂ)*x 3,
    (Real.sqrt (α/32):ℂ)*x 4]

def scalar (ε a α : ℝ) (C : ℂ) (p : ℝ) (q : ℂ) : ℂ :=
  (Real.pi/α:ℝ)*C*clockPhase p (complexInverse ε q)*
    Complex.exp (-complexInverse ε q)*Complex.exp (-(a:ℂ)*q^2)

def entireOutput (ε a α wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (x : Space) : ℂ :=
  scalar ε a α C p q*profile (α/wL:ℝ) (α*wR:ℝ) (α/32) b P
    (flow (2*scale) (complexInverse ε q) x)

private theorem normalize_coordinate (α wL wR c : ℝ) (x : Joint 2 4) :
    normalize α wL wR c x=scaledPoint α wL wR (coordinate c x) := by
  ext i
  fin_cases i <;> simp [KFCausalIndependentRadialNormalization.normalize,scaledPoint,coordinate,mul_assoc]

theorem flow_scaled (α wL wR : ℝ) (hα : 0<α) (hR : 0<wR) (z : ℂ) (x : Space) :
    flow (coupling α wR) z (scaledPoint α wL wR x)=
      scaledPoint α wL wR (flow (2*scale) z x) := by
  have hs : (Real.sqrt (α*wR):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (mul_pos hα hR)).ne'
  ext i
  fin_cases i <;> simp only [flow,scaledPoint,coupling,Matrix.cons_val_zero]
  all_goals push_cast
  all_goals field_simp [hs]

private theorem scaled_coordinates (α wL wR : ℝ) (hα : 0<α) (hL : 0<wL) (hR : 0<wR)
    (x : Space) :
    left α wL (scaledPoint α wL wR x)=radiusLeft x ∧
    right α wR (scaledPoint α wL wR x)=radiusRight x ∧
    neutral α (scaledPoint α wL wR x)=x 4 ∧
    KFCausalComplexQuadraticPerturbation.quadratic (fun i=>scaledPoint α wL wR x i)=
      KFCausalIndependentRadialEntireLaplacian.quadratic (α/wL:ℝ) (α*wR:ℝ) x+
        (α/32:ℝ)*(x 4)^2 := by
  have hs : (Real.sqrt (α/wL):ℂ)^2=(α/wL:ℝ) := by
    exact_mod_cast Real.sq_sqrt (div_nonneg hα.le hL.le)
  have ht : (Real.sqrt (α*wR):ℂ)^2=(α*wR:ℝ) := by
    exact_mod_cast Real.sq_sqrt (mul_nonneg hα.le hR.le)
  have hn : (Real.sqrt (α/32):ℂ)^2=(α/32:ℝ) := by
    exact_mod_cast Real.sq_sqrt (show 0≤α/32 by positivity)
  have hz : (Real.sqrt (α/32):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ⟨?_,?_,?_,?_⟩
  · change (((Real.sqrt (α/wL):ℂ)*x 0)^2+((Real.sqrt (α/wL):ℂ)*x 2)^2)/(α/wL:ℝ)=_
    simp only [mul_pow,hs,radiusLeft]
    field_simp [Complex.ofReal_ne_zero.mpr hα.ne',Complex.ofReal_ne_zero.mpr hL.ne']
  · change (((Real.sqrt (α*wR):ℂ)*x 1)^2+((Real.sqrt (α*wR):ℂ)*x 3)^2)/(α*wR:ℝ)=_
    simp only [mul_pow,ht,radiusRight]
    field_simp [Complex.ofReal_ne_zero.mpr hα.ne',Complex.ofReal_ne_zero.mpr hR.ne']
  · change ((Real.sqrt (α/32):ℂ)*x 4)/(Real.sqrt (α/32):ℂ)=_
    exact mul_div_cancel_left₀ _ hz
  · simp only [KFCausalComplexQuadraticPerturbation.quadratic,scaledPoint,
      Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
      mul_pow,hs,ht,hn,add_zero]
    unfold KFCausalIndependentRadialEntireLaplacian.quadratic radiusLeft radiusRight
    ring

theorem numerator_formula (ε a α wL wR c : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (m n : ℕ) (hα : 0<α) (hL : 0<wL) (hR : 0<wR)
    (q : ℂ) (x : Joint 2 4) :
    numerator ε a α wL wR c C p b P m n q x=
      radiusLeft (flow (2*scale) (complexInverse ε q) (coordinate c x))^m*
      radiusRight (flow (2*scale) (complexInverse ε q) (coordinate c x))^n*
      entireOutput ε a α wL wR C p b P q (coordinate c x) := by
  have hy : baselineVector ε α wL wR c q x=
      scaledPoint α wL wR (flow (2*scale) (complexInverse ε q) (coordinate c x)) := by
    unfold baselineVector
    rw [normalize_coordinate,flow_scaled α wL wR hα hR]
  obtain ⟨hl,hr,hn,hq⟩ := scaled_coordinates α wL wR hα hL hR
    (flow (2*scale) (complexInverse ε q) (coordinate c x))
  unfold numerator
  dsimp only
  rw [hy,hl,hr,hn,hq]
  simp only [entireOutput,scalar,profile,KFCausalNeutralLinePackets.entire,
    neg_add,Complex.exp_add]
  ring

theorem entireOutput_first_derivative (ε a α wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => entireOutput ε a α wL wR C p b P q
      (x+t • flow (2*scale) (-complexInverse ε q) (basis i)))
      (scalar ε a α C p q*first (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i
        (flow (2*scale) (complexInverse ε q) x)) 0 :=
  (KFCausalIndependentRadialEntireLaplacian.pulled_first_derivative
    (α/wL:ℝ) (α*wR:ℝ) (α/32) b P (2*scale) (complexInverse ε q) i x).const_mul _

theorem entireOutput_second_derivative (ε a α wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (i : Fin 5) (x : Space) :
    HasDerivAt (fun t : ℂ => scalar ε a α C p q*
      first (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i
        (flow (2*scale) (complexInverse ε q)
          (x+t • flow (2*scale) (-complexInverse ε q) (basis i))))
      (scalar ε a α C p q*second (α/wL:ℝ) (α*wR:ℝ) (α/32) b P i
        (flow (2*scale) (complexInverse ε q) x)) 0 :=
  (KFCausalIndependentRadialEntireLaplacian.pulled_second_derivative
    (α/wL:ℝ) (α*wR:ℝ) (α/32) b P (2*scale) (complexInverse ε q) i x).const_mul _

theorem real_reference (ε a α wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (q : ℂ) (s : ℝ) (x : Space) :
    entireOutput ε a α wL wR C p b P q (flow (2*scale) (-s:ℝ) x)=
      scalar ε a α C p q*profile (α/wL:ℝ) (α*wR:ℝ) (α/32) b P
        (flow (2*scale) (complexInverse ε q-(s:ℂ)) x) := by
  unfold entireOutput
  rw [flow_compose]
  congr 3
  push_cast
  ring

theorem ordered_profile_laplacian (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (hα : 0<groundWidth h) (hL : 0<wL) (hR : 0<wR)
    (q : ℂ) (x : Joint 2 4) :
    KFCausalOrderedStaticOutputRepresentative.profile ε a h wL wR C p b P q x=
      (clockPower ε false q/2)*
        entireOutput ε a (groundWidth h) wL wR C p b P q (coordinate (momentumScale h) x)-
      ((h:ℂ)^2/2)*clockPower ε true q*scalar ε a (groundWidth h) C p q*
        ∑ i : Fin 5,second (groundWidth h/wL:ℝ) (groundWidth h*wR:ℝ)
          (groundWidth h/32) b P i
          (flow (2*scale) (complexInverse ε q) (coordinate (momentumScale h) x)) := by
  unfold KFCausalOrderedStaticOutputRepresentative.profile
  simp only [numerator_formula ε a (groundWidth h) wL wR (momentumScale h) C p b _ _ _ hα hL hR,
    pow_zero,pow_one,mul_one,one_mul]
  rw [KFCausalIndependentRadialEntireLaplacian.laplacian_sum]
  simp only [entireOutput,KFCausalClockFloorInvariantTrial.neutralWidth]
  push_cast
  ring

#print axioms flow_scaled
#print axioms numerator_formula
#print axioms entireOutput_first_derivative
#print axioms entireOutput_second_derivative
#print axioms real_reference
#print axioms ordered_profile_laplacian
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPulledLaplacian
