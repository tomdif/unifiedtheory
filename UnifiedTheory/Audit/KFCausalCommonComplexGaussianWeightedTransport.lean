/- Exact weighted original physical transport bound for a common complex
neutral source and constant neutral polynomial P=1 across all nonnegative
mass, quartic and vacuum couplings. The clock amplitudes are frozen only
for the geometric derivative; full clock integration by parts separately
retains their motion. -/
import UnifiedTheory.Audit.KFCausalCommonComplexMassPotentialResponse
import UnifiedTheory.Audit.KFCausalCommonComplexQuarticPotentialResponse
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianWeightedTransport

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianWeightedTransport
noncomputable section
open scoped ComplexConjugate
open KFCausalGaussianWeightedSourceKernelDerivative
  (kernel slope pairKernel pairSlope familyForm familySlope)
open KFCausalGaussianSourceKernelDerivative (prefactor)
open KFCausalGaussianSourceJointKernel (sourceV sourceX)
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalChargeGaussianGeometry (groundWidth)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalWeightedReciprocalNeutralWholeClock
  (clockPairing positiveSlice transportResponse)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)

private theorem prefactor_source (S T H e : ℂ) (β A : ℝ) :
    prefactor S T H e (2*(A:ℂ)) β =
      (Real.exp (A^2/(2*β)):ℂ)*prefactor S T H e 0 β := by
  unfold prefactor KFCausalShiftedComplexGaussianMoments.mass
  have he : (2*(A:ℂ))^2/(4*(2*(β:ℂ))) = ((A^2/(2*β):ℝ):ℂ) := by
    push_cast
    ring
  rw [he,Complex.ofReal_exp]
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_div,Complex.exp_zero,mul_one]
  ring

private theorem kernel_vacuum_translation (S T H e : ℂ) (β L A : ℝ) :
    kernel 0 0 1 S T H e (2*(A:ℂ)) β L =
      (Real.exp (A^2/(2*β)):ℂ)*kernel 0 0 1 S T H e 0 β L := by
  unfold kernel KFCausalGaussianWeightedSourcePlaneKernel.wick
  rw [prefactor_source]
  push_cast
  ring

private theorem slope_vacuum_translation (S T H e Sd Td Hd ed : ℂ) (β L Ld A : ℝ) :
    slope 0 0 1 S T H e (2*(A:ℂ)) Sd Td Hd ed β L Ld =
      (Real.exp (A^2/(2*β)):ℂ)*slope 0 0 1 S T H e 0 Sd Td Hd ed β L Ld := by
  unfold KFCausalGaussianWeightedSourceKernelDerivative.slope
    KFCausalGaussianWeightedSourcePlaneKernel.wick
  rw [prefactor_source]
  push_cast
  ring

private theorem sourceV_common (r : ℂ) (A D : ℝ) :
    sourceV r (source A D) (source A D) = sourceV r ((D:ℂ)*Complex.I) ((D:ℂ)*Complex.I) := by
  simp only [sourceV,source,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  ring

private theorem sourceX_common (A D : ℝ) :
    sourceX (source A D) (source A D) = 2*(A:ℂ) := by
  simp only [sourceX,source,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  ring

private theorem sourceX_imag (D : ℝ) :
    sourceX ((D:ℂ)*Complex.I) ((D:ℂ)*Complex.I) = 0 := by
  simp only [sourceX,map_mul,Complex.conj_ofReal,Complex.conj_I]
  ring

private theorem family_vacuum_translation (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ)
    (A D : ℝ) (c : Fin n → ℂ) :
    familyForm 0 0 1 n α β w r (fun _ => source A D) c =
      (Real.exp (A^2/(2*β)):ℂ)*familyForm 0 0 1 n α β w r (fun _ => (D:ℂ)*Complex.I) c := by
  simp only [familyForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairKernel,sourceV_common,sourceX_common,sourceX_imag]
  rw [kernel_vacuum_translation]
  ring

private theorem familySlope_vacuum_translation (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r rd : ℂ)
    (A D : ℝ) (c : Fin n → ℂ) :
    familySlope 0 0 1 n α β w r rd (fun _ => source A D) c =
      (Real.exp (A^2/(2*β)):ℂ)*familySlope 0 0 1 n α β w r rd (fun _ => (D:ℂ)*Complex.I) c := by
  simp only [familySlope,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairSlope,sourceV_common,sourceX_common,sourceX_imag]
  rw [slope_vacuum_translation]
  ring

private theorem kernel_decomposition (mass2 quartic vacuum : ℝ)
    (S T H e f : ℂ) (β L : ℝ) :
    kernel mass2 quartic vacuum S T H e f β L =
      (vacuum:ℂ)*kernel 0 0 1 S T H e f β L+
        ((mass2/2:ℝ):ℂ)*kernel 2 0 0 S T H e f β L+
        ((quartic/4:ℝ):ℂ)*kernel 0 4 0 S T H e f β L := by
  unfold kernel KFCausalGaussianWeightedSourcePlaneKernel.wick
  push_cast
  ring

private theorem slope_decomposition (mass2 quartic vacuum : ℝ)
    (S T H e f Sd Td Hd ed : ℂ) (β L Ld : ℝ) :
    slope mass2 quartic vacuum S T H e f Sd Td Hd ed β L Ld =
      (vacuum:ℂ)*slope 0 0 1 S T H e f Sd Td Hd ed β L Ld+
        ((mass2/2:ℝ):ℂ)*slope 2 0 0 S T H e f Sd Td Hd ed β L Ld+
        ((quartic/4:ℝ):ℂ)*slope 0 4 0 S T H e f Sd Td Hd ed β L Ld := by
  unfold KFCausalGaussianWeightedSourceKernelDerivative.slope
    KFCausalGaussianWeightedSourcePlaneKernel.wick
  push_cast
  ring

private theorem family_decomposition (mass2 quartic vacuum : ℝ)
    (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r : ℂ) (b c : Fin n → ℂ) :
    familyForm mass2 quartic vacuum n α β w r b c =
      (vacuum:ℂ)*familyForm 0 0 1 n α β w r b c+
        ((mass2/2:ℝ):ℂ)*familyForm 2 0 0 n α β w r b c+
        ((quartic/4:ℝ):ℂ)*familyForm 0 4 0 n α β w r b c := by
  simp only [familyForm,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairKernel]
  rw [kernel_decomposition]
  ring

private theorem familySlope_decomposition (mass2 quartic vacuum : ℝ)
    (n : ℕ) (α β : ℝ) (w : Fin n → ℝ) (r rd : ℂ) (b c : Fin n → ℂ) :
    familySlope mass2 quartic vacuum n α β w r rd b c =
      (vacuum:ℂ)*familySlope 0 0 1 n α β w r rd b c+
        ((mass2/2:ℝ):ℂ)*familySlope 2 0 0 n α β w r rd b c+
        ((quartic/4:ℝ):ℂ)*familySlope 0 4 0 n α β w r rd b c := by
  simp only [familySlope,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [pairSlope]
  rw [slope_decomposition]
  ring

theorem vacuum_positiveSlice_translation (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    positiveSlice 0 0 1 n ε h a w p C (fun _=>source A D) (fun _=>1) s=
      Real.exp (A^2/(2*neutralWidth h))*
        positiveSlice 0 0 1 n ε h a w p C (fun _=>(D:ℂ)*Complex.I) (fun _=>1) s := by
  have hE (b : Fin n → ℂ) :
      positiveSlice 0 0 1 n ε h a w p C b (fun _=>1) s=
        Real.pi/4*(familyForm 0 0 1 n (groundWidth h) (neutralWidth h) w
          (KFCausalClockFloorRelativeShift.scale ε (-h/2) s) b
          (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C s)).re := by
    have he := KFCausalCommonRealGaussianWeightedTransport.clockPairing_family
      0 0 1 n ε h a w p C b hε hh hw hb s
    have hr := congrArg Complex.re he
    simpa only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_div,zero_mul,sub_zero] using hr
  rw [hE (fun _=>source A D),hE (fun _=>(D:ℂ)*Complex.I),family_vacuum_translation]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem vacuum_transport_translation (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    transportResponse 0 0 1 n ε h a w p C (fun _=>source A D) (fun _=>1) s=
      Real.exp (A^2/(2*neutralWidth h))*
        transportResponse 0 0 1 n ε h a w p C (fun _=>(D:ℂ)*Complex.I) (fun _=>1) s := by
  rw [KFCausalCommonRealGaussianWeightedTransport.transport_family
    0 0 1 n ε h a w p C (fun _=>source A D) hε hh hw hb s,
    KFCausalCommonRealGaussianWeightedTransport.transport_family
    0 0 1 n ε h a w p C (fun _=>(D:ℂ)*Complex.I) hε hh hw hb s,
    familySlope_vacuum_translation]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem positiveSlice_decomposition (mass2 quartic vacuum : ℝ)
    (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
    (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    positiveSlice mass2 quartic vacuum n ε h a w p C b (fun _=>1) s=
      vacuum*positiveSlice 0 0 1 n ε h a w p C b (fun _=>1) s+
        (mass2/2)*positiveSlice 2 0 0 n ε h a w p C b (fun _=>1) s+
        (quartic/4)*positiveSlice 0 4 0 n ε h a w p C b (fun _=>1) s := by
  have hE (m q v : ℝ) :
      positiveSlice m q v n ε h a w p C b (fun _=>1) s=
        Real.pi/4*(familyForm m q v n (groundWidth h) (neutralWidth h) w
          (KFCausalClockFloorRelativeShift.scale ε (-h/2) s) b
          (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p C s)).re := by
    have he := KFCausalCommonRealGaussianWeightedTransport.clockPairing_family
      m q v n ε h a w p C b hε hh hw hb s
    have hr := congrArg Complex.re he
    simpa only [Complex.mul_re,Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_div,zero_mul,sub_zero] using hr
  rw [hE mass2 quartic vacuum,hE 0 0 1,hE 2 0 0,hE 0 4 0,family_decomposition]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

theorem transportResponse_decomposition (mass2 quartic vacuum : ℝ)
    (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
    (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    transportResponse mass2 quartic vacuum n ε h a w p C b (fun _=>1) s=
      vacuum*transportResponse 0 0 1 n ε h a w p C b (fun _=>1) s+
        (mass2/2)*transportResponse 2 0 0 n ε h a w p C b (fun _=>1) s+
        (quartic/4)*transportResponse 0 4 0 n ε h a w p C b (fun _=>1) s := by
  simp_rw [KFCausalCommonRealGaussianWeightedTransport.transport_family
    _ _ _ n ε h a w p C b hε hh hw hb s]
  rw [familySlope_decomposition]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

private theorem vacuum_slice_nonnegative (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    0≤positiveSlice 0 0 1 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [vacuum_positiveSlice_translation n ε h A D a w p C hε hh hw hb s]
  exact mul_nonneg (Real.exp_pos _).le
    (KFCausalCommonImaginaryGaussianWeightedTransport.positiveSlice_nonnegative
      0 0 1 n ε h a w p C hε hh hw hb D le_rfl le_rfl zero_le_one s)

private theorem mass_slice_nonnegative (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    0≤positiveSlice 2 0 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [KFCausalCommonComplexMassPotentialResponse.positiveSlice_joint n ε h A D a w p C hε hh hw hb s]
  apply mul_nonneg (by positivity)
  apply MeasureTheory.integral_nonneg
  intro z
  unfold KFCausalCommonComplexMassJointEnergy.energyDensity
    KFCausalCommonComplexQuarticJointAngular.channel
    KFCausalCommonComplexQuarticJointAngular.jointBase
  positivity

private theorem quartic_slice_nonnegative (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    0≤positiveSlice 0 4 0 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [KFCausalCommonComplexQuarticPotentialResponse.positiveSlice_joint n ε h A D a w p C hε hh hw hb s]
  apply mul_nonneg (by positivity)
  apply MeasureTheory.integral_nonneg
  intro z
  unfold KFCausalCommonComplexQuarticJointAngular.energyDensity
    KFCausalCommonComplexQuarticJointAngular.channel
    KFCausalCommonComplexQuarticJointAngular.jointBase
  positivity

theorem positiveSlice_nonnegative (mass2 quartic vacuum : ℝ)
    (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i) (hb : |h|≤2*Real.pi*ε/3)
    (hmass : 0≤mass2) (hquartic : 0≤quartic) (hvacuum : 0≤vacuum) (s : ℝ) :
    0≤positiveSlice mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [positiveSlice_decomposition mass2 quartic vacuum n ε h a w p C
    (fun _=>source A D) hε hh hw hb s]
  have hv := vacuum_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have hm := mass_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have hq := quartic_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  positivity

private theorem vacuum_transport_bound (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ)
    (C : Fin n → ℂ) (hε : 0<ε) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (s : ℝ) :
    transportResponse 0 0 1 n ε h a w p C (fun _=>source A D) (fun _=>1) s≤
      536*fraction ε s*positiveSlice 0 0 1 n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  rw [vacuum_transport_translation n ε h A D a w p C hε hh hw hb s,
    vacuum_positiveSlice_translation n ε h A D a w p C hε hh hw hb s]
  have ht := KFCausalCommonImaginaryGaussianWeightedTransport.transport_bound
    0 0 1 n ε h a w p C hε hh hw hb D le_rfl le_rfl zero_le_one s
  have he := mul_le_mul_of_nonneg_left ht (Real.exp_pos (A^2/(2*neutralWidth h))).le
  linarith

theorem transport_bound : ∃ K : ℝ,0≤K ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ),
    0<ε→h≠0→(∀i,1≤w i)→|h|≤2*Real.pi*ε/3→∀s:ℝ,
    transportResponse mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s≤
      K*fraction ε s*
        positiveSlice mass2 quartic vacuum n ε h a w p C (fun _=>source A D) (fun _=>1) s := by
  obtain ⟨Km,hKm,hbm⟩ := KFCausalCommonComplexMassPotentialResponse.transport_bound
  obtain ⟨Kq,hKq,hbq⟩ := KFCausalCommonComplexQuarticPotentialResponse.transport_bound
  let K := max 536 (max Km Kq)
  have hK0 : 0≤K := le_trans (by norm_num) (le_max_left 536 (max Km Kq))
  have h536 : 536≤K := le_max_left 536 (max Km Kq)
  have hKmK : Km≤K := le_trans (le_max_left Km Kq) (le_max_right 536 (max Km Kq))
  have hKqK : Kq≤K := le_trans (le_max_right Km Kq) (le_max_right 536 (max Km Kq))
  refine ⟨K,hK0,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε hh hw hb s
  have hf : 0≤fraction ε s := by unfold fraction; positivity
  have hv0 := vacuum_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have hm0 := mass_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have hq0 := quartic_slice_nonnegative n ε h A D a w p C hε hh hw hb s
  have htv := (vacuum_transport_bound n ε h A D a w p C hε hh hw hb s).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h536 hf) hv0)
  have htm := (hbm n ε h A D a w p C hε hh hw hb s).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKmK hf) hm0)
  have htq := (hbq n ε h A D a w p C hε hh hw hb s).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKqK hf) hq0)
  rw [transportResponse_decomposition mass2 quartic vacuum n ε h a w p C
      (fun _=>source A D) hε hh hw hb s,
    positiveSlice_decomposition mass2 quartic vacuum n ε h a w p C
      (fun _=>source A D) hε hh hw hb s]
  have h1 := mul_le_mul_of_nonneg_left htv hvacuum
  have h2 := mul_le_mul_of_nonneg_left htm (by positivity : 0≤mass2/2)
  have h3 := mul_le_mul_of_nonneg_left htq (by positivity : 0≤quartic/4)
  linarith

#print axioms vacuum_positiveSlice_translation
#print axioms vacuum_transport_translation
#print axioms positiveSlice_decomposition
#print axioms transportResponse_decomposition
#print axioms positiveSlice_nonnegative
#print axioms transport_bound
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianWeightedTransport
