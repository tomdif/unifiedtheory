/- The rational radial multiplier has a uniformly bounded second directional
derivative along both symmetric momentum directions. Consequently the first-order
symmetric Leibniz correction maps the clock-weighted symmetric momentum graph into
the transverse momentum graph, yielding an integration-by-parts identity and bound
against any second graph element that depends only on its L2 norm. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaKinetics

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSecondDerivative
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint JointHilbert)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum transverseMomentum_selfAdjoint)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection symmetricVector symmetricBlock rightVector)
open KFCausalSymmetricMomentumGraphEquivalence (symmetric_graph_iff)
open KFCausalClockFloorBoundedInverse (inverseL)
open KFCausalClockFloorAntisymmetricGraph (inverseL_charge_coe clockMomentum_graph_iff)
open KFCausalClockFloorTrialMomentum (clockMomentum)
open KFCausalClockFloorRadialYosidaSymbol (radial radial_coordinates radial_nonnegative)
open KFCausalClockFloorRadialYosidaDerivative
  (derivativeSymbol radial_hasDerivAt derivativeSymbol_continuous derivativeSymbol_bound)
open KFCausalClockFloorRadialYosidaKinetics
  (derivativeAction derivativeAction_coe derivativeAction_norm
    symmetricCorrection symmetricCorrection_norm)
open KFCausalClockFloorRotatedAntiSymbol (position symmetricIndex)
open KFCausalClockFloorFlow (clock)
open KFCausalClockFloorCanonicalDefect (clock_positive)
open KFCausalPairedModeCoordinates (scale scale_square)

def secondDerivativeSymbol (ε h N : ℝ) (i : Fin 2) (x : Joint 2 4) : ℝ :=
  2*N^2*(clock ε (x (.inr 0))*(N+radial ε h x)-2*position i x^2)/
    (clock ε (x (.inr 0))^2*(N+radial ε h x)^3)

theorem position_translate (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    position i (x+t • symmetricVector i)=position i x+(2*scale)*t := by
  fin_cases i <;>
    simp [symmetricVector,symmetricBlock,rightVector,position,symmetricIndex] <;>
    ring

theorem position_hasDerivAt (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    HasDerivAt (fun u : ℝ => position i (x+u • symmetricVector i)) (2*scale) t := by
  simp_rw [position_translate]
  simpa only [zero_add,mul_one] using
    (hasDerivAt_const t (position i x)).add ((hasDerivAt_id t).const_mul (2*scale))

theorem derivativeSymbol_hasDerivAt (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    HasDerivAt (fun u : ℝ => derivativeSymbol ε h N i (x+u • symmetricVector i))
      (secondDerivativeSymbol ε h N i (x+t • symmetricVector i)) t := by
  have hp := (position_hasDerivAt i x t).const_mul ((2*scale)*N^2)
  have hr := (hasDerivAt_const t N).add (radial_hasDerivAt ε h i x t)
  have hsum : 0 < N+radial ε h (x+t • symmetricVector i) :=
    add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h _)
  have hcpos : 0 < clock ε (x (.inr 0)) := clock_positive ε (x (.inr 0)) hε.le
  have hden_ne : clock ε (x (.inr 0))*(N+radial ε h (x+t • symmetricVector i))^2 ≠ 0 :=
    mul_ne_zero hcpos.ne' (pow_ne_zero 2 hsum.ne')
  have hden := (hr.pow 2).const_mul (clock ε (x (.inr 0)))
  have hd := hp.div hden hden_ne
  have hclock (u : ℝ) : clock ε ((x+u • symmetricVector i) (.inr 0))=clock ε (x (.inr 0)) := by
    fin_cases i <;> simp [symmetricVector,symmetricBlock,rightVector]
  change HasDerivAt (fun u : ℝ => (2*scale)*N^2*position i (x+u • symmetricVector i)/
    (clock ε ((x+u • symmetricVector i) (.inr 0))*(N+radial ε h (x+u • symmetricVector i))^2)) _ t
  simp_rw [hclock]
  convert hd using 1
  dsimp only [Pi.add_apply,Pi.pow_apply]
  unfold secondDerivativeSymbol
  rw [hclock t]
  field_simp [hcpos.ne',hsum.ne']
  ring_nf
  rw [scale_square]
  ring

private theorem position_square_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (i : Fin 2) (x : Joint 2 4) :
    position i x^2 ≤ 2*clock ε (x (.inr 0))*radial ε h x := by
  have hc := (clock_positive ε (x (.inr 0)) hε.le).ne'
  rw [radial_coordinates]
  rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hc)]
  have hp := mul_nonneg (sq_nonneg (KFCausalNormalizedChargeFlow.momentumScale h))
    (add_nonneg (sq_nonneg (x (.inl 0))) (sq_nonneg (x (.inl 1))))
  fin_cases i <;> simp [position,symmetricIndex]
    <;> nlinarith [sq_nonneg (x (.inr 1)),sq_nonneg (x (.inr 2))]

private theorem second_rational_bound (N C r v : ℝ) (hN : 0 < N) (hC : 0 < C)
    (hr : 0 ≤ r) (hv : v^2 ≤ 2*C*r) :
    |2*N^2*(C*(N+r)-2*v^2)/(C^2*(N+r)^3)| ≤ 6/C := by
  have hsum : 0 < N+r := add_pos_of_pos_of_nonneg hN hr
  have hden : 0 < C^2*(N+r)^3 := by positivity
  rw [abs_div,abs_of_pos hden,div_le_div_iff₀ hden hC]
  have habs : |2*N^2*(C*(N+r)-2*v^2)| ≤ 6*C*(N+r)^3 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg v,mul_nonneg hN.le hr,sq_nonneg r,
        mul_nonneg (sq_nonneg N) (mul_nonneg hC.le hr),
        mul_nonneg (sq_nonneg N) (mul_nonneg hC.le hN.le),
        mul_nonneg hC.le (pow_nonneg hsum.le 3)]
    · nlinarith [sq_nonneg v,mul_nonneg hN.le hr,sq_nonneg r,
        mul_nonneg (sq_nonneg N) (mul_nonneg hC.le hr),
        mul_nonneg (sq_nonneg N) (mul_nonneg hC.le hN.le),
        mul_nonneg hC.le (pow_nonneg hsum.le 3)]
  nlinarith [mul_le_mul_of_nonneg_right habs hC.le]

theorem secondDerivativeSymbol_bound (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) (x : Joint 2 4) :
    |secondDerivativeSymbol ε h N i x| ≤ 6/ε := by
  have hc := clock_positive ε (x (.inr 0)) hε.le
  have hs := second_rational_bound N (clock ε (x (.inr 0))) (radial ε h x)
    (position i x) hN hc (radial_nonnegative ε hε h x) (position_square_bound ε hε h i x)
  have hεc : ε ≤ clock ε (x (.inr 0)) := by
    unfold clock
    exact le_add_of_nonneg_left (Real.exp_pos _).le
  exact hs.trans (div_le_div_of_nonneg_left (by norm_num) hε hεc)

theorem secondDerivativeSymbol_continuous (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (i : Fin 2) : Continuous (secondDerivativeSymbol ε h N i) := by
  have hr : Continuous (radial ε h) :=
    ((KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 0).add
      (KFCausalClockFloorRotatedAntiSymbol.chargedWeight_continuous ε hε h 1)).div_const 2
  have hc : Continuous (fun x : Joint 2 4 => clock ε (x (.inr 0))) := by
    unfold clock
    fun_prop
  have hp : Continuous (position i) := by
    unfold position
    fun_prop
  unfold secondDerivativeSymbol
  apply Continuous.div
  · exact continuous_const.mul ((hc.mul (continuous_const.add hr)).sub (continuous_const.mul (hp.pow 2)))
  · exact (hc.pow 2).mul ((continuous_const.add hr).pow 3)
  · intro x
    exact mul_ne_zero (pow_ne_zero 2 (clock_positive ε (x (.inr 0)) hε.le).ne')
      (pow_ne_zero 3 (add_pos_of_pos_of_nonneg hN (radial_nonnegative ε hε h x)).ne')

variable (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)

include hε hN in
private theorem derivative_measurable (i : Fin 2) :
    Measurable (fun x : Joint 2 4 => (derivativeSymbol ε h N i x:ℂ)) :=
  (Complex.continuous_ofReal.comp (derivativeSymbol_continuous ε hε h N hN i)).measurable

include hε hN in
private theorem complex_derivative_bound (i : Fin 2) (x : Joint 2 4) :
    ‖(derivativeSymbol ε h N i x:ℂ)‖ ≤ Real.sqrt (N/ε) := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact derivativeSymbol_bound ε hε h N hN i x

include hε hN in
private theorem secondDerivative_measurable (i : Fin 2) :
    Measurable (fun x : Joint 2 4 => (secondDerivativeSymbol ε h N i x:ℂ)) :=
  (Complex.continuous_ofReal.comp (secondDerivativeSymbol_continuous ε hε h N hN i)).measurable

include hε hN in
private theorem complex_secondDerivative_bound (i : Fin 2) (x : Joint 2 4) :
    ‖(secondDerivativeSymbol ε h N i x:ℂ)‖ ≤ 6/ε := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact secondDerivativeSymbol_bound ε hε h N hN i x

def secondDerivativeAction (i : Fin 2) : Hilbert →L[ℂ] Hilbert :=
  (chargeCoordinates.symm : JointHilbert 2 4 →L[ℂ] Hilbert).comp
    ((KFCausalBoundedLpMultiplier.operator (fun x => (secondDerivativeSymbol ε h N i x:ℂ))
      (secondDerivative_measurable ε hε h N hN i) (6/ε) (by positivity)
      (complex_secondDerivative_bound ε hε h N hN i)).comp
        (chargeCoordinates : Hilbert →L[ℂ] JointHilbert 2 4))

private theorem derivativeAction_coordinates (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (derivativeAction ε hε h N hN i f)=
      KFCausalBoundedLpMultiplier.operator (fun x => (derivativeSymbol ε h N i x:ℂ))
        (derivative_measurable ε hε h N hN i) (Real.sqrt (N/ε)) (Real.sqrt_nonneg _)
        (complex_derivative_bound ε hε h N hN i) (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

private theorem secondDerivativeAction_coordinates (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (secondDerivativeAction ε hε h N hN i f)=
      KFCausalBoundedLpMultiplier.operator (fun x => (secondDerivativeSymbol ε h N i x:ℂ))
        (secondDerivative_measurable ε hε h N hN i) (6/ε) (by positivity)
        (complex_secondDerivative_bound ε hε h N hN i) (chargeCoordinates f) :=
  chargeCoordinates.apply_symm_apply _

theorem secondDerivativeAction_coe (i : Fin 2) (f : Hilbert) :
    chargeCoordinates (secondDerivativeAction ε hε h N hN i f) =ᵐ[volume]
      fun x => (secondDerivativeSymbol ε h N i x:ℂ)*(chargeCoordinates f) x := by
  rw [secondDerivativeAction_coordinates]
  exact KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ _

theorem secondDerivativeAction_norm (i : Fin 2) (f : Hilbert) :
    ‖secondDerivativeAction ε hε h N hN i f‖ ≤ (6/ε)*‖f‖ := by
  rw [← chargeCoordinates.norm_map (secondDerivativeAction ε hε h N hN i f),
    secondDerivativeAction_coordinates,← chargeCoordinates.norm_map f]
  exact KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ _

theorem derivativeAction_inverseL (i : Fin 2) (f : Hilbert) :
    inverseL ε hε (derivativeAction ε hε h N hN i f)=
      derivativeAction ε hε h N hN i (inverseL ε hε f) := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [inverseL_charge_coe ε hε (derivativeAction ε hε h N hN i f),
    derivativeAction_coe ε hε h N hN i f,
    derivativeAction_coe ε hε h N hN i (inverseL ε hε f),
    inverseL_charge_coe ε hε f] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  ring

theorem derivative_symmetric_graph (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (symmetricDirection i)).graph) :
    (derivativeAction ε hε h N hN i f,
      derivativeAction ε hε h N hN i g+
        (-Complex.I*(h:ℂ)) • secondDerivativeAction ε hε h N hN i f) ∈
      (transverseMomentum h (symmetricDirection i)).graph := by
  have hg := KFCausalBoundedDirectionalLeibniz.spectral_graph (symmetricVector i)
    (fun x => (derivativeSymbol ε h N i x:ℂ))
    (fun x => (secondDerivativeSymbol ε h N i x:ℂ))
    (derivative_measurable ε hε h N hN i)
    (secondDerivative_measurable ε hε h N hN i)
    (Real.sqrt (N/ε)) (6/ε) (Real.sqrt_nonneg _) (by positivity)
    (complex_derivative_bound ε hε h N hN i)
    (complex_secondDerivative_bound ε hε h N hN i)
    (fun x t => (derivativeSymbol_hasDerivAt ε hε h N hN i x t).ofReal_comp)
    h hh (chargeCoordinates f) (chargeCoordinates g) ((symmetric_graph_iff h hh i f g).mp hfg)
  apply (symmetric_graph_iff h hh i _ _).mpr
  simpa only [map_add,map_smul,derivativeAction_coordinates,
    secondDerivativeAction_coordinates] using hg

def symmetricSecondCorrection (i : Fin 2) : Hilbert →L[ℂ] Hilbert :=
  (-((h^2:ℝ):ℂ)) • (inverseL ε hε).comp
    ((secondDerivativeAction ε hε h N hN i).comp (inverseL ε hε))

theorem symmetricSecondCorrection_norm (i : Fin 2) (f : Hilbert) :
    ‖symmetricSecondCorrection ε hε h N hN i f‖ ≤ (6*h^2/ε^2)*‖f‖ := by
  change ‖(-((h^2:ℝ):ℂ)) • inverseL ε hε
    (secondDerivativeAction ε hε h N hN i (inverseL ε hε f))‖ ≤ _
  rw [norm_smul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg h)]
  have h1 : ‖inverseL ε hε (secondDerivativeAction ε hε h N hN i (inverseL ε hε f))‖ ≤
      (Real.sqrt ε)⁻¹*‖secondDerivativeAction ε hε h N hN i (inverseL ε hε f)‖ :=
    KFCausalClockFloorBoundedInverse.inverseAction_norm_bound ε hε _
  have h2 : ‖secondDerivativeAction ε hε h N hN i (inverseL ε hε f)‖ ≤
      (6/ε)*‖inverseL ε hε f‖ :=
    secondDerivativeAction_norm ε hε h N hN i (inverseL ε hε f)
  have h3 : ‖inverseL ε hε f‖ ≤ (Real.sqrt ε)⁻¹*‖f‖ :=
    KFCausalClockFloorBoundedInverse.inverseAction_norm_bound ε hε f
  have h12 : ‖inverseL ε hε (secondDerivativeAction ε hε h N hN i (inverseL ε hε f))‖ ≤
      (Real.sqrt ε)⁻¹*((6/ε)*((Real.sqrt ε)⁻¹*‖f‖)) :=
    h1.trans (mul_le_mul_of_nonneg_left
      (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) (by positivity))
  have hbound := mul_le_mul_of_nonneg_left h12 (sq_nonneg h)
  apply hbound.trans_eq
  have hsq : (Real.sqrt ε)⁻¹*(Real.sqrt ε)⁻¹ = ε⁻¹ := by
    rw [← mul_inv,Real.mul_self_sqrt hε.le]
  calc
    h^2*((Real.sqrt ε)⁻¹*((6/ε)*((Real.sqrt ε)⁻¹*‖f‖))) =
        6*h^2*(6⁻¹*(6/ε)*((Real.sqrt ε)⁻¹*(Real.sqrt ε)⁻¹))*‖f‖ := by ring
    _ = (6*h^2/ε^2)*‖f‖ := by
      rw [hsq]
      field_simp [hε.ne']

theorem symmetricCorrection_transverse_graph (hh : h ≠ 0) (i : Fin 2) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    (symmetricCorrection ε hε h N hN i f,
      (-Complex.I*(h:ℂ)) • derivativeAction ε hε h N hN i g+
        (-((h^2:ℝ):ℂ)) • secondDerivativeAction ε hε h N hN i (inverseL ε hε f)) ∈
      (transverseMomentum h (symmetricDirection i)).graph := by
  have hg := derivative_symmetric_graph ε hε h N hN hh i (inverseL ε hε f) g
    ((clockMomentum_graph_iff ε hε h (symmetricDirection i) f g).mp hfg)
  have hs := (transverseMomentum h (symmetricDirection i)).graph.smul_mem (-Complex.I*(h:ℂ)) hg
  change ((-Complex.I*(h:ℂ)) • derivativeAction ε hε h N hN i (inverseL ε hε f),
    (-Complex.I*(h:ℂ)) • (derivativeAction ε hε h N hN i g+
      (-Complex.I*(h:ℂ)) • secondDerivativeAction ε hε h N hN i (inverseL ε hε f))) ∈
    (transverseMomentum h (symmetricDirection i)).graph at hs
  have hsq : (-Complex.I*(h:ℂ))*(-Complex.I*(h:ℂ)) = -((h^2:ℝ):ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [smul_add,smul_smul,hsq] at hs
  exact hs

theorem inverseL_selfAdjoint_pairing (f g : Hilbert) :
    inner ℂ f (inverseL ε hε g) = inner ℂ (inverseL ε hε f) g := by
  rw [← chargeCoordinates.inner_map_map f (inverseL ε hε g),
    ← chargeCoordinates.inner_map_map (inverseL ε hε f) g,
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [inverseL_charge_coe ε hε g,inverseL_charge_coe ε hε f] with x hg hf
  rw [hg,hf,← Complex.ofReal_inv]
  change inner ℂ ((chargeCoordinates f) x)
      ((((Real.sqrt (clock ε (x (.inr 0))))⁻¹:ℝ):ℂ) • (chargeCoordinates g) x) =
    inner ℂ ((((Real.sqrt (clock ε (x (.inr 0))))⁻¹:ℝ):ℂ) • (chargeCoordinates f) x)
      ((chargeCoordinates g) x)
  rw [inner_smul_right,inner_smul_left,Complex.conj_ofReal]

private theorem selfAdjoint_graph_pairing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (u₁ w₁ u₂ w₂ : H) (h1 : (u₁,w₁) ∈ A.graph) (h2 : (u₂,w₂) ∈ A.graph) :
    inner ℂ u₁ w₂ = inner ℂ w₁ u₂ := by
  let x₁ : A.domain := ⟨u₁,LinearPMap.mem_domain_of_mem_graph h1⟩
  let x₂ : A.domain := ⟨u₂,LinearPMap.mem_domain_of_mem_graph h2⟩
  have hw₁ : A x₁ = w₁ := A.mem_graph_snd_inj' (A.mem_graph x₁) h1 rfl
  have hw₂ : A x₂ = w₂ := A.mem_graph_snd_inj' (A.mem_graph x₂) h2 rfl
  have hF := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hF
  have hp := hF x₁ x₂
  change inner ℂ (A x₁) u₂ = inner ℂ u₁ (A x₂) at hp
  rw [hw₁,hw₂] at hp
  exact hp.symm

theorem symmetricCorrection_clockMomentum_pairing (hh : h ≠ 0) (i : Fin 2)
    (f₁ g₁ f₂ g₂ : Hilbert)
    (h1 : (f₁,g₁) ∈ (clockMomentum ε h (symmetricDirection i)).graph)
    (h2 : (f₂,g₂) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    inner ℂ (symmetricCorrection ε hε h N hN i f₁) g₂ =
      inner ℂ (symmetricCorrection ε hε h N hN i g₁+
        symmetricSecondCorrection ε hε h N hN i f₁) f₂ := by
  have ht1 := symmetricCorrection_transverse_graph ε hε h N hN hh i f₁ g₁ h1
  have ht2 := (clockMomentum_graph_iff ε hε h (symmetricDirection i) f₂ g₂).mp h2
  have hp := selfAdjoint_graph_pairing
    (transverseMomentum h (symmetricDirection i))
    (transverseMomentum_selfAdjoint h (symmetricDirection i))
    _ _ _ _ ht1 ht2
  rw [hp,inverseL_selfAdjoint_pairing ε hε]
  congr 1
  simp only [map_add,map_smul,derivativeAction_inverseL]
  rfl

theorem symmetricCorrection_clockMomentum_bound (hh : h ≠ 0) (i : Fin 2)
    (f₁ g₁ f₂ g₂ : Hilbert)
    (h1 : (f₁,g₁) ∈ (clockMomentum ε h (symmetricDirection i)).graph)
    (h2 : (f₂,g₂) ∈ (clockMomentum ε h (symmetricDirection i)).graph) :
    ‖inner ℂ (symmetricCorrection ε hε h N hN i f₁) g₂‖ ≤
      ((|h| *Real.sqrt (N/ε)*(Real.sqrt ε)⁻¹)*‖g₁‖+(6*h^2/ε^2)*‖f₁‖)*‖f₂‖ := by
  rw [symmetricCorrection_clockMomentum_pairing ε hε h N hN hh i f₁ g₁ f₂ g₂ h1 h2]
  apply (norm_inner_le_norm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f₂)
  exact (norm_add_le _ _).trans (add_le_add
    (symmetricCorrection_norm ε hε h N hN i g₁)
    (symmetricSecondCorrection_norm ε hε h N hN i f₁))

#print axioms position_translate
#print axioms position_hasDerivAt
#print axioms derivativeSymbol_hasDerivAt
#print axioms secondDerivativeSymbol_bound
#print axioms secondDerivativeSymbol_continuous
#print axioms secondDerivativeAction_coe
#print axioms secondDerivativeAction_norm
#print axioms derivativeAction_inverseL
#print axioms derivative_symmetric_graph
#print axioms symmetricSecondCorrection_norm
#print axioms symmetricCorrection_transverse_graph
#print axioms inverseL_selfAdjoint_pairing
#print axioms symmetricCorrection_clockMomentum_pairing
#print axioms symmetricCorrection_clockMomentum_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaSecondDerivative
