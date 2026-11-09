/- Exact differentiation of the complete sourced quartic Gaussian kernel.
The mean and variance move together with the Gaussian masses. These are
identities; no uniform response positivity assumption is introduced. -/
import UnifiedTheory.Audit.KFCausalGaussianSourceJointKernel
import UnifiedTheory.Audit.KFCausalJointFourierDilationQuartic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalGaussianSourceKernelDerivative
noncomputable section
open scoped ComplexConjugate
open KFCausalComplexGaussianMoments (gaussianValue)
open KFCausalShiftedComplexGaussianMoments (mass)
open KFCausalGaussianSourcePlaneKernel (mean variance wick formula)
open KFCausalGaussianSourceJointKernel (sourceV sourceX pairKernel)
open KFCausalReciprocalCrossGeometry (B C)
open KFCausalChargedPairCoordinates (fieldSlope)

private theorem nonzero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro h
  simp [h] at hz

theorem gaussianValue_derivative {f : ℝ → ℂ} {fd : ℂ} {x : ℝ}
    (hf : HasDerivAt f fd x) (hp : 0 < (f x).re) :
    HasDerivAt (fun t => gaussianValue (f t))
      (gaussianValue (f x)*(-fd/(2*f x))) x := by
  have hn := nonzero_of_re_pos hp
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hq := (hasDerivAt_const x (Real.pi:ℂ)).div hf hn
  have hqn : (Real.pi:ℂ)/f x ≠ 0 := div_ne_zero hpi hn
  have hqp : (Real.pi:ℂ)/f x ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [Complex.div_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
    exact div_pos (mul_pos Real.pi_pos hp) (Complex.normSq_pos.mpr hn)
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := (1/2:ℂ)) hqp).hasDerivAt.scomp x hq
  simp only [smul_eq_mul,Complex.cpow_sub _ _ hqn,Complex.cpow_one] at hd
  convert hd using 1
  unfold gaussianValue
  field_simp
  ring

theorem mass_derivative {f g : ℝ → ℂ} {fd gd : ℂ} {x : ℝ}
    (hf : HasDerivAt f fd x) (hg : HasDerivAt g gd x) (hp : 0 < (f x).re) :
    HasDerivAt (fun t => mass (f t) (g t))
      (mass (f x) (g x)*(-fd/(2*f x)+g x*gd/(2*f x)-(g x)^2*fd/(4*(f x)^2))) x := by
  have hn := nonzero_of_re_pos hp
  have he := ((hg.pow 2).div (hf.const_mul 4) (mul_ne_zero (by norm_num) hn)).cexp
  have hd := (gaussianValue_derivative hf hp).mul he
  convert hd using 1
  unfold mass
  simp only [Pi.pow_apply,Pi.div_apply]
  field_simp
  ring

theorem wick_derivative {m s : ℝ → ℂ} {md sd : ℂ} {x : ℝ}
    (hm : HasDerivAt m md x) (hs : HasDerivAt s sd x) :
    HasDerivAt (fun t => wick (m t) (s t))
      (m x*(1+(m x)^2+3*s x)*md+(1/2+3/2*((m x)^2+s x))*sd) x := by
  have hd := ((hasDerivAt_const x (1:ℂ)).add (((hm.pow 2).add hs).div_const 2)).add
    ((((hm.pow 4).add (((hm.pow 2).const_mul 6).mul hs)).add
      ((hs.pow 2).const_mul 3)).div_const 4)
  convert hd using 1
  simp only [Pi.pow_apply]
  ring

def prefactor (S T H e f : ℂ) (β : ℝ) : ℂ :=
  gaussianValue S*mass H e*mass (2*(β:ℂ)) f/T

def kernel (S T H e f : ℂ) (β L : ℝ) : ℂ :=
  prefactor S T H e f β*wick (mean H (2*(β:ℂ)) e f L) (variance H (2*(β:ℂ)) L)

def logSlope (S T H e Sd Td Hd ed : ℂ) : ℂ :=
  -Sd/(2*S)-Td/T-Hd/(2*H)+e*ed/(2*H)-e^2*Hd/(4*H^2)

def meanSlope (H e Hd ed : ℂ) (L Ld : ℝ) : ℂ :=
  ((Ld:ℂ)*e+(L:ℂ)*ed)/(2*H)-(L:ℂ)*e*Hd/(2*H^2)

def varianceSlope (H Hd : ℂ) (L Ld : ℝ) : ℂ :=
  (L:ℂ)*(Ld:ℂ)/H-(L:ℂ)^2*Hd/(2*H^2)

def slope (S T H e f Sd Td Hd ed : ℂ) (β L Ld : ℝ) : ℂ :=
  prefactor S T H e f β*
    (logSlope S T H e Sd Td Hd ed*wick (mean H (2*(β:ℂ)) e f L) (variance H (2*(β:ℂ)) L)+
      mean H (2*(β:ℂ)) e f L*(1+(mean H (2*(β:ℂ)) e f L)^2+3*variance H (2*(β:ℂ)) L)*
        meanSlope H e Hd ed L Ld+
      (1/2+3/2*((mean H (2*(β:ℂ)) e f L)^2+variance H (2*(β:ℂ)) L))*
        varianceSlope H Hd L Ld)

theorem prefactor_derivative {S T H e : ℝ → ℂ} {Sd Td Hd ed : ℂ} {x : ℝ}
    (hS : HasDerivAt S Sd x) (hT : HasDerivAt T Td x)
    (hH : HasDerivAt H Hd x) (he : HasDerivAt e ed x)
    (hSp : 0 < (S x).re) (hHp : 0 < (H x).re) (hTn : T x ≠ 0)
    (f : ℂ) (β : ℝ) :
    HasDerivAt (fun t => prefactor (S t) (T t) (H t) (e t) f β)
      (prefactor (S x) (T x) (H x) (e x) f β*logSlope (S x) (T x) (H x) (e x) Sd Td Hd ed) x := by
  have hSn := nonzero_of_re_pos hSp
  have hHn := nonzero_of_re_pos hHp
  have hd := (((gaussianValue_derivative hS hSp).mul (mass_derivative hH he hHp)).mul_const
    (mass (2*(β:ℂ)) f)).div hT hTn
  convert hd using 1
  unfold prefactor logSlope
  simp only [Pi.mul_apply]
  field_simp
  ring

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
    HasDerivAt (fun t => kernel (S t) (T t) (H t) (e t) f β (L t))
      (slope (S x) (T x) (H x) (e x) f Sd Td Hd ed β (L x) Ld) x := by
  have hHn := nonzero_of_re_pos hHp
  have hw := wick_derivative (mean_derivative hH he hL hHn f β)
    (variance_derivative hH hL hHn β)
  have hd := (prefactor_derivative hS hT hH he hSp hHp hTn f β).mul hw
  convert hd using 1
  unfold slope
  ring

theorem pairKernel_eq_kernel (α β w v : ℝ) (r si sj : ℂ) :
    pairKernel α β w v r si sj = kernel (B α w v r) (conj (B α w v r))
      (C α β w v r) (sourceV r si sj) (sourceX si sj) β (fieldSlope r) := by
  unfold pairKernel kernel prefactor formula
  ring

def chargedVelocity (α w v : ℝ) (r rd : ℂ) : ℂ :=
  (α:ℂ)*(conj r*conj rd*(w:ℂ)+r*rd*(v:ℂ))

def pairSlope (α β w v : ℝ) (r rd si sj : ℂ) : ℂ :=
  slope (B α w v r) (conj (B α w v r)) (C α β w v r)
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
    HasDerivAt (fun t => pairKernel α β w v (r t) si sj)
      (pairSlope α β w v (r x) rd si sj) x := by
  have hT := (charged_derivative hr α w v).star
  simp only [Complex.star_def] at hT
  have hTn : conj (B α w v (r x)) ≠ 0 := by
    exact nonzero_of_re_pos (by simpa only [Complex.conj_re] using hB)
  simp_rw [pairKernel_eq_kernel]
  exact kernel_derivative (charged_derivative hr α w v) hT
    (normal_derivative hr α β w v) (sourceV_derivative hr si sj)
    (fieldSlope_derivative hr) hB hC hTn (sourceX si sj) β

theorem slope_add (S T H e f Sd Td Hd ed Sd' Td' Hd' ed' : ℂ)
    (β L Ld Ld' : ℝ) :
    slope S T H e f (Sd+Sd') (Td+Td') (Hd+Hd') (ed+ed') β L (Ld+Ld') =
      slope S T H e f Sd Td Hd ed β L Ld+slope S T H e f Sd' Td' Hd' ed' β L Ld' := by
  unfold slope logSlope meanSlope varianceSlope
  push_cast
  ring

theorem dilation_slope (S T H e f : ℂ) (β L ell : ℝ)
    (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    slope S T H e f (2*(ell:ℂ)*S) (2*(ell:ℂ)*T) (2*(ell:ℂ)*H)
      ((ell:ℂ)*e) β L (ell*L) = (-4*(ell:ℂ))*kernel S T H e f β L := by
  unfold slope logSlope meanSlope varianceSlope kernel
  push_cast
  field_simp
  ring

def realWidthVelocity (α w v : ℝ) (r : ℂ) : ℂ :=
  (α:ℂ)*(conj r*(w:ℂ)+r*(v:ℂ))

def coolingSlope (α β w v : ℝ) (r si sj : ℂ) (δ κ : ℝ) : ℂ :=
  slope (B α w v r) (conj (B α w v r)) (C α β w v r)
    (sourceV r si sj) (sourceX si sj)
    ((δ:ℂ)*realWidthVelocity α w v r) ((δ:ℂ)*conj (realWidthVelocity α w v r))
    ((δ:ℂ)*realWidthVelocity α w v r) 0 β (fieldSlope r) κ

theorem pairSlope_split (α β w v : ℝ) (r rd si sj : ℂ) (ell : ℝ)
    (hi : rd.im=ell*r.im) (hB : 0 < (B α w v r).re) (hC : 0 < (C α β w v r).re) :
    pairSlope α β w v r rd si sj =
      (-4*(ell:ℂ))*pairKernel α β w v r si sj+
        coolingSlope α β w v r si sj (rd.re-ell*r.re) (-2*(rd.re-ell*r.re)-3*ell) := by
  let δ := rd.re-ell*r.re
  have hv : rd=(δ:ℂ)+(ell:ℂ)*r := by
    apply Complex.ext
    · simp [δ,Complex.mul_re]
    · simp [Complex.mul_im,hi]
  have hs : chargedVelocity α w v r rd =
      (δ:ℂ)*realWidthVelocity α w v r+2*(ell:ℂ)*B α w v r := by
    rw [hv]
    unfold chargedVelocity realWidthVelocity B
    simp only [map_add,map_mul,Complex.conj_ofReal]
    push_cast
    ring
  have ht : conj (chargedVelocity α w v r rd) =
      (δ:ℂ)*conj (realWidthVelocity α w v r)+2*(ell:ℂ)*conj (B α w v r) := by
    rw [hs]
    simp only [map_add,map_mul,Complex.conj_ofReal,map_ofNat]
  have hh : chargedVelocity α w v r rd-((16*β*r.im*rd.im:ℝ):ℂ) =
      (δ:ℂ)*realWidthVelocity α w v r+2*(ell:ℂ)*C α β w v r := by
    rw [hs,hi]
    unfold C
    push_cast
    ring
  have he : sourceV rd si sj = (0:ℂ)+(ell:ℂ)*sourceV r si sj := by
    unfold sourceV
    rw [hi]
    push_cast
    ring
  have hL : -2*rd.re=(-2*δ-3*ell)+ell*fieldSlope r := by
    unfold δ fieldSlope
    ring
  unfold pairSlope
  rw [ht,hh,hs,he,hL,slope_add,dilation_slope _ _ _ _ _ β (fieldSlope r) ell
    (nonzero_of_re_pos hB) (nonzero_of_re_pos (by simpa only [Complex.conj_re] using hB))
    (nonzero_of_re_pos hC),← pairKernel_eq_kernel]
  unfold coolingSlope
  rw [add_comm]

def familySlope (n : ℕ) (α β : ℝ) (w : Fin n → ℝ)
    (r rd : ℂ) (b c : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))*
    pairSlope α β (w i) (w j) r rd (b i) (b j)

theorem familyForm_derivative {r : ℝ → ℂ} {rd : ℂ} {x : ℝ}
    (hr : HasDerivAt r rd x) (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
    (hB : ∀ i j, 0 < (B α (w i) (w j) (r x)).re)
    (hC : ∀ i j, 0 < (C α β (w i) (w j) (r x)).re) :
    HasDerivAt (fun t => KFCausalGaussianSourceJointKernel.familyForm n α β w (r t) b c)
      (familySlope n α β w (r x) rd b c) x := by
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.sum (u := Finset.univ) (fun j _ =>
    (pairKernel_derivative hr α β (w i) (w j) (b i) (b j) (hB i j) (hC i j)).const_mul
      ((conj (c i)*c j)*(w i:ℂ)*(w j:ℂ))))
  convert hd using 1
  funext t
  simp only [KFCausalGaussianSourceJointKernel.familyForm,Finset.sum_apply]

theorem actual_integral_derivative (n : ℕ) (α β ε y s : ℝ) (w : Fin n → ℝ)
    (b c : Fin n → ℂ) (hα : 0 < α) (hβ : 0 < β) (hwidth : 32*β ≤ α)
    (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hw : ∀ i, 1 ≤ w i) :
    HasDerivAt (fun t => ∫ p,
      (KFCausalReciprocalNeutralPositiveForm.positiveDensity n α β w
        (KFCausalClockFloorRelativeShift.scale ε y t) c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 1) p:ℂ)
          ∂KFCausalReciprocalNeutralLaplace.jointMeasure)
      (familySlope n α β w (KFCausalClockFloorRelativeShift.scale ε y s)
        (deriv (KFCausalClockFloorRelativeShift.scale ε y) s) b c) s := by
  have hf (t : ℝ) (i : Fin n) :
      0 < (w i*α)*KFCausalReciprocalGaussianCoordinates.area
        (KFCausalClockFloorRelativeShift.scale ε y t)-
          8*β*(KFCausalClockFloorRelativeShift.scale ε y t).im^2 := by
    have hp := KFCausalChargedPairCompactGeometry.actual_mem_region α β ε y t
      hα hβ.le hwidth hε hy
    obtain ⟨hc,ha⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive α β hα _ hp
    exact (KFCausalJointFourierDilationQuartic.width_floors α _ (w i) β (hw i) ha hc).2
  have he : (fun t => ∫ p,
      (KFCausalReciprocalNeutralPositiveForm.positiveDensity n α β w
        (KFCausalClockFloorRelativeShift.scale ε y t) c
        (fun i => KFCausalNeutralExponentialProfiles.exponentialProfile (b i) 1 1) p:ℂ)
          ∂KFCausalReciprocalNeutralLaplace.jointMeasure) =
      fun t => KFCausalGaussianSourceJointKernel.familyForm n α β w
        (KFCausalClockFloorRelativeShift.scale ε y t) b c := by
    funext t
    exact KFCausalGaussianSourceJointKernel.family_integral n α β w _ b c hβ (hf t)
  rw [he]
  have hr := KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity ε y s hε hy
  rw [hr.deriv]
  exact familyForm_derivative hr n α β w b c
    (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) _ hβ (hf s i) (hf s j)).1)
    (fun i j => (KFCausalGaussianSourceJointKernel.pair_floors α β (w i) (w j) _ hβ (hf s i) (hf s j)).2)

#print axioms gaussianValue_derivative
#print axioms mass_derivative
#print axioms wick_derivative
#print axioms prefactor_derivative
#print axioms kernel_derivative
#print axioms pairKernel_eq_kernel
#print axioms pairKernel_derivative
#print axioms slope_add
#print axioms dilation_slope
#print axioms pairSlope_split
#print axioms familyForm_derivative
#print axioms actual_integral_derivative
end
end UnifiedTheory.Audit.KFCausalGaussianSourceKernelDerivative
