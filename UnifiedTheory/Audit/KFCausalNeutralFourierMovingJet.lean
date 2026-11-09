/- Actual derivatives of moving neutral fields, including the charged
holomorphic coefficients. These are pointwise jets; passing a derivative
through an integral requires the separate domination theorem. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierResponseSplit
import UnifiedTheory.Audit.KFCausalClusteredClockFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierMovingJet
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralFourierShift (line)
open KFCausalNeutralFourierField (fieldLine)
open KFCausalNeutralFourierResponseSplit (slope response)
open KFCausalNeutralLinePackets (entire step)
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralJointCurvatureForm (coefficients)
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalReciprocalWedgeGeometry (chart)

variable (n : ℕ) (β : ℝ) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

theorem line_derivative (C : ℝ → Fin n → ℂ) (cd : Fin n → ℂ)
    (y : ℝ → ℝ) (yd s x : ℝ) (hC : ∀ i, HasDerivAt (fun t => C t i) (cd i) s)
    (hy : HasDerivAt y yd s) :
    HasDerivAt (fun t => line n β b (C t) P (y t) x)
      (line n β b cd P (y s) x+Complex.I*(yd:ℂ)*line n β b (C s) (fun i => step β (b i) (P i)) (y s) x) s := by
  have hz := (hy.ofReal_comp.mul_const Complex.I).const_add (x:ℂ)
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hC i).mul ((KFCausalNeutralLinePackets.entire_derivative β (b i) (P i) _).scomp s hz))
  convert hd using 1
  dsimp [line,KFCausalGaussianContourShift.horizontal,family]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem field_derivative (C : ℝ → Fin n → ℂ) (cd : Fin n → ℂ)
    (a y : ℝ → ℝ) (ad yd s x : ℝ) (j : ℕ)
    (hC : ∀ i, HasDerivAt (fun t => C t i) (cd i) s)
    (ha : HasDerivAt a ad s) (hy : HasDerivAt y yd s) :
    HasDerivAt (fun t => fieldLine n β b (C t) P j (a t) (y t) x)
      (slope n β b (C s) cd P j (a s) (y s) ad yd x) s := by
  have hd := ((ha.const_add x).ofReal_comp.pow j).mul
    (line_derivative n β b P C cd y yd s x hC hy)
  convert hd using 1
  dsimp [KFCausalNeutralFourierResponseSplit.slope,fieldLine]
  ring

theorem square_derivative (C : ℝ → Fin n → ℂ) (cd : Fin n → ℂ)
    (a y : ℝ → ℝ) (ad yd s x : ℝ) (j : ℕ)
    (hC : ∀ i, HasDerivAt (fun t => C t i) (cd i) s)
    (ha : HasDerivAt a ad s) (hy : HasDerivAt y yd s) :
    HasDerivAt (fun t => ‖fieldLine n β b (C t) P j (a t) (y t) x‖^2)
      (response n β b (C s) cd P j (a s) (y s) ad yd x) s :=
  KFCausalNeutralQuarticBoundary.norm_square_derivative _ (fun _ => _) s
    (field_derivative n β b P C cd a y ad yd s x j hC ha hy)

omit β b P in
theorem coefficients_derivative (w : Fin n → ℝ) (c : Fin n → ℂ)
    (z : ℝ → ℂ) (zd : ℂ) (s : ℝ) (hz : HasDerivAt z zd s) (i : Fin n) :
    HasDerivAt (fun t => coefficients n w c (z t) i)
      (-(w i:ℂ)*zd*coefficients n w c (z s) i) s := by
  have hd := ((hz.const_mul (-(w i:ℂ))).cexp).const_mul (c i*(w i:ℂ))
  convert hd using 1
  unfold coefficients
  ring

def chargedSlope (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r rd : ℂ) (u v Y : ℝ) (i : Fin n) : ℂ :=
  -(w i:ℂ)*KFCausalClusteredClockFactors.Zd α r rd ((u,![v,0]),Y)*
    coefficients n w c (chart α r (u^2+v^2) Y) i

omit β b P in
theorem actual_coefficients_derivative (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r : ℝ → ℂ) (rd : ℂ) (s u v Y : ℝ) (hr : HasDerivAt r rd s) (i : Fin n) :
    HasDerivAt (fun t => coefficients n w c (chart α (r t) (u^2+v^2) Y) i)
      (chargedSlope n α w c (r s) rd u v Y i) s :=
  coefficients_derivative n w c _ _ s
    (KFCausalClusteredClockFactors.Z_derivative α r rd s ((u,![v,0]),Y) hr) i

omit n β b P in
theorem actual_field_derivative (r : ℝ → ℂ) (rd : ℂ) (s v : ℝ)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => fieldSlope (r t)*v) (-2*rd.re*v) s := by
  have hd := (((Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2).const_sub 3).mul_const v
  convert hd using 1
  dsimp [fieldSlope]
  ring

omit n β b P in
theorem actual_translation_derivative (r : ℝ → ℂ) (rd : ℂ) (s v : ℝ)
    (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => 2*(r t).im*v) (2*rd.im*v) s :=
  ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hr).const_mul 2).mul_const v

theorem actual_square_derivative (α : ℝ) (w : Fin n → ℝ) (c : Fin n → ℂ)
    (r : ℝ → ℂ) (rd : ℂ) (s u v x Y : ℝ) (j : ℕ) (hr : HasDerivAt r rd s) :
    HasDerivAt (fun t => ‖fieldLine n β b
      (coefficients n w c (chart α (r t) (u^2+v^2) Y)) P j
      (fieldSlope (r t)*v) (2*(r t).im*v) x‖^2)
      (response n β b (coefficients n w c (chart α (r s) (u^2+v^2) Y))
        (chargedSlope n α w c (r s) rd u v Y) P j
        (fieldSlope (r s)*v) (2*(r s).im*v) (-2*rd.re*v) (2*rd.im*v) x) s :=
  square_derivative n β b P _ _ _ _ _ _ s x j
    (actual_coefficients_derivative n α w c r rd s u v Y hr)
    (actual_field_derivative r rd s v hr) (actual_translation_derivative r rd s v hr)

#print axioms line_derivative
#print axioms field_derivative
#print axioms square_derivative
#print axioms coefficients_derivative
#print axioms actual_coefficients_derivative
#print axioms actual_field_derivative
#print axioms actual_translation_derivative
#print axioms actual_square_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralFourierMovingJet
