/- Exact finite weighted Wick kernels and their actual local derivatives.
The Gaussian masses, neutral mean and variance vary together. These are
identities for all real coupling coefficients; no response estimate is assumed. -/
import UnifiedTheory.Audit.KFCausalGaussianWeightedSourcePlaneKernel
import UnifiedTheory.Audit.KFCausalGaussianSourceKernelDerivative

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianWeightedSourceKernelDerivative
noncomputable section
open scoped ComplexConjugate
open KFCausalGaussianSourcePlaneKernel (mean variance)
open KFCausalGaussianWeightedSourcePlaneKernel (wick)
open KFCausalGaussianSourceKernelDerivative (prefactor prefactor_derivative logSlope
  meanSlope varianceSlope chargedVelocity)
open KFCausalGaussianSourceJointKernel (sourceV sourceX)
open KFCausalReciprocalCrossGeometry (B C)
open KFCausalChargedPairCoordinates (fieldSlope)

private theorem nonzero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  simp [h] at hz

variable (mass2 quartic vacuum : ℝ)

theorem wick_derivative {m s : ℝ → ℂ} {md sd : ℂ} {x : ℝ}
    (hm : HasDerivAt m md x) (hs : HasDerivAt s sd x) :
    HasDerivAt (fun t => wick mass2 quartic vacuum (m t) (s t))
      (((mass2:ℂ)*m x+(quartic:ℂ)*((m x)^3+3*m x*s x))*md+
        ((mass2:ℂ)/2+3*(quartic:ℂ)/2*((m x)^2+s x))*sd) x := by
  have hd := ((hasDerivAt_const x (vacuum:ℂ)).add
    ((((hm.pow 2).add hs).const_mul (mass2:ℂ)).div_const 2)).add
    (((((hm.pow 4).add (((hm.pow 2).const_mul 6).mul hs)).add
      ((hs.pow 2).const_mul 3)).const_mul (quartic:ℂ)).div_const 4)
  convert hd using 1
  simp only [Pi.pow_apply]
  ring

def kernel (S T H e f : ℂ) (β L : ℝ) : ℂ :=
  prefactor S T H e f β*wick mass2 quartic vacuum
    (mean H (2*(β:ℂ)) e f L) (variance H (2*(β:ℂ)) L)

def slope (S T H e f Sd Td Hd ed : ℂ) (β L Ld : ℝ) : ℂ :=
  let m := mean H (2*(β:ℂ)) e f L
  let σ := variance H (2*(β:ℂ)) L
  prefactor S T H e f β*
    (logSlope S T H e Sd Td Hd ed*wick mass2 quartic vacuum m σ+
      ((mass2:ℂ)*m+(quartic:ℂ)*(m^3+3*m*σ))*meanSlope H e Hd ed L Ld+
      ((mass2:ℂ)/2+3*(quartic:ℂ)/2*(m^2+σ))*varianceSlope H Hd L Ld)

private theorem mean_derivative {H e : ℝ → ℂ} {L : ℝ → ℝ}
    {Hd ed : ℂ} {Ld x : ℝ} (hH : HasDerivAt H Hd x) (he : HasDerivAt e ed x)
    (hL : HasDerivAt L Ld x) (hHn : H x ≠ 0) (f : ℂ) (β : ℝ) :
    HasDerivAt (fun t => mean (H t) (2*(β:ℂ)) (e t) f (L t))
      (meanSlope (H x) (e x) Hd ed (L x) Ld) x := by
  have hd := (hasDerivAt_const x (f/(2*(2*(β:ℂ))))).add
    ((hL.ofReal_comp.mul he).div (hH.const_mul 2) (mul_ne_zero (by norm_num) hHn))
  convert hd using 1
  unfold meanSlope
  simp only [Pi.mul_apply]
  field_simp
  ring

private theorem variance_derivative {H : ℝ → ℂ} {L : ℝ → ℝ}
    {Hd : ℂ} {Ld x : ℝ} (hH : HasDerivAt H Hd x)
    (hL : HasDerivAt L Ld x) (hHn : H x ≠ 0) (β : ℝ) :
    HasDerivAt (fun t => variance (H t) (2*(β:ℂ)) (L t))
      (varianceSlope (H x) Hd (L x) Ld) x := by
  have hd := (hasDerivAt_const x ((1:ℂ)/(2*(2*(β:ℂ))))).add
    ((hL.ofReal_comp.pow 2).div (hH.const_mul 2) (mul_ne_zero (by norm_num) hHn))
  convert hd using 1
  unfold varianceSlope
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem kernel_derivative {S T H e : ℝ → ℂ} {L : ℝ → ℝ}
    {Sd Td Hd ed : ℂ} {Ld x : ℝ}
    (hS : HasDerivAt S Sd x) (hT : HasDerivAt T Td x)
    (hH : HasDerivAt H Hd x) (he : HasDerivAt e ed x) (hL : HasDerivAt L Ld x)
    (hSp : 0 < (S x).re) (hHp : 0 < (H x).re) (hTn : T x ≠ 0)
    (f : ℂ) (β : ℝ) :
    HasDerivAt (fun t => kernel mass2 quartic vacuum (S t) (T t) (H t) (e t) f β (L t))
      (slope mass2 quartic vacuum (S x) (T x) (H x) (e x) f Sd Td Hd ed β (L x) Ld) x := by
  have hHn := nonzero_of_re_pos hHp
  have hw := wick_derivative mass2 quartic vacuum (mean_derivative hH he hL hHn f β)
    (variance_derivative hH hL hHn β)
  have hd := (prefactor_derivative hS hT hH he hSp hHp hTn f β).mul hw
  convert hd using 1
  unfold slope
  ring

def pairKernel (α β w v : ℝ) (r si sj : ℂ) : ℂ :=
  kernel mass2 quartic vacuum (B α w v r) (conj (B α w v r))
    (C α β w v r) (sourceV r si sj) (sourceX si sj) β (fieldSlope r)

def familyForm (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r : ℂ) (b c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    pairKernel mass2 quartic vacuum α β (w i) (w j) r (b i) (b j)

def pairSlope (α β w v : ℝ) (r rd si sj : ℂ) : ℂ :=
  slope mass2 quartic vacuum (B α w v r) (conj (B α w v r)) (C α β w v r)
    (sourceV r si sj) (sourceX si sj)
    (chargedVelocity α w v r rd) (conj (chargedVelocity α w v r rd))
    (chargedVelocity α w v r rd-((16*β*r.im*rd.im:ℝ):ℂ))
    (sourceV rd si sj) β (fieldSlope r) (-2*rd.re)

private theorem charged_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (α w v : ℝ) :
    HasDerivAt (fun t => B α w v (r t)) (chargedVelocity α w v (r x) rd) x := by
  have hd := (((hr.star.pow 2).mul_const (w:ℂ)).add
    ((hr.pow 2).mul_const (v:ℂ))).const_mul ((α/2:ℝ):ℂ)
  convert hd using 1
  unfold chargedVelocity
  simp only [Complex.star_def]
  push_cast
  ring

private theorem normal_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (α β w v : ℝ) :
    HasDerivAt (fun t => C α β w v (r t))
      (chargedVelocity α w v (r x) rd-((16*β*(r x).im*rd.im:ℝ):ℂ)) x := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hr
  have hd := (charged_derivative hr α w v).sub (((hi.pow 2).const_mul (8*β)).ofReal_comp)
  convert hd using 1
  simp only [Function.comp_apply,Complex.imCLM_apply]
  push_cast
  ring

private theorem sourceV_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (si sj : ℂ) :
    HasDerivAt (fun t => sourceV (r t) si sj) (sourceV rd si sj) x := by
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hr
  exact ((hi.const_mul 2).ofReal_comp.mul_const Complex.I).mul_const (sj-conj si)

private theorem fieldSlope_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) :
    HasDerivAt (fun t => fieldSlope (r t)) (-2*rd.re) x := by
  have ha := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hr
  simpa only [neg_mul] using (ha.const_mul 2).const_sub 3

theorem pairKernel_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (α β w v : ℝ) (si sj : ℂ)
    (hB : 0 < (B α w v (r x)).re) (hC : 0 < (C α β w v (r x)).re) :
    HasDerivAt (fun t => pairKernel mass2 quartic vacuum α β w v (r t) si sj)
      (pairSlope mass2 quartic vacuum α β w v (r x) rd si sj) x := by
  have hT := (charged_derivative hr α w v).star
  simp only [Complex.star_def] at hT
  have hTn : conj (B α w v (r x)) ≠ 0 := by
    exact nonzero_of_re_pos (by simpa only [Complex.conj_re] using hB)
  unfold pairKernel
  exact kernel_derivative mass2 quartic vacuum (charged_derivative hr α w v) hT
    (normal_derivative hr α β w v) (sourceV_derivative hr si sj)
    (fieldSlope_derivative hr) hB hC hTn (sourceX si sj) β

theorem slope_add (S T H e f Sd Td Hd ed Sd' Td' Hd' ed' : ℂ)
    (β L Ld Ld' : ℝ) :
    slope mass2 quartic vacuum S T H e f (Sd+Sd') (Td+Td') (Hd+Hd') (ed+ed') β L (Ld+Ld') =
      slope mass2 quartic vacuum S T H e f Sd Td Hd ed β L Ld+slope mass2 quartic vacuum S T H e f Sd' Td' Hd' ed' β L Ld' := by
  unfold slope logSlope meanSlope varianceSlope
  push_cast
  ring

theorem dilation_slope (S T H e f : ℂ) (β L ell : ℝ)
    (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    slope mass2 quartic vacuum S T H e f (2*(ell:ℂ)*S) (2*(ell:ℂ)*T) (2*(ell:ℂ)*H)
      ((ell:ℂ)*e) β L (ell*L) = (-4*(ell:ℂ))*kernel mass2 quartic vacuum S T H e f β L := by
  unfold slope logSlope meanSlope varianceSlope kernel
  push_cast
  field_simp
  ring

def familySlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r rd : ℂ) (b c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    pairSlope mass2 quartic vacuum α β (w i) (w j) r rd (b i) (b j)

theorem familyForm_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (hB : ∀ i j, 0 < (B α (w i) (w j) (r x)).re)
    (hC : ∀ i j, 0 < (C α β (w i) (w j) (r x)).re) :
    HasDerivAt (fun t => familyForm mass2 quartic vacuum n α β w (r t) b c)
      (familySlope mass2 quartic vacuum n α β w (r x) rd b c) x := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (pairKernel_derivative mass2 quartic vacuum hr α β (w i) (w j) (b i) (b j) (hB i j) (hC i j)).const_mul
      ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))))
  convert hd using 1
  funext t
  simp only [familyForm,Finset.sum_apply]

#print axioms wick_derivative
#print axioms kernel_derivative
#print axioms pairKernel_derivative
#print axioms slope_add
#print axioms dilation_slope
#print axioms familyForm_derivative
end
end UnifiedTheory.Audit.KFCausalGaussianWeightedSourceKernelDerivative
