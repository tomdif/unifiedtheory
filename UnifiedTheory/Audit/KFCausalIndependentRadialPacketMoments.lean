/- Actual Hilbert states for all radial polynomial insertions of the
two-width sourced packet. Gaussian comparison proves their integrability;
no Hamiltonian graph derivative or limiting domain assertion is used. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPacketDerivatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeQuadratic_coordinates)
open KFCausalIndependentRadialPacketDerivatives (leftRadius rightRadius momentProfile radii_nonnegative)
open KFCausalIndependentRadialPackets (genericState generic_charge_coe clock clock_continuous clock_memLp state)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive groundWidth_matching)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale)

private theorem power_decay_bound (d x : ℝ) (hd : 0 < d) (hx : 0 ≤ x) (n : ℕ) :
    x^n*Real.exp (-d*x) ≤ (n.factorial:ℝ)/d^n := by
  have hf : 0 < (n.factorial:ℝ) := by positivity
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (d*x) (mul_nonneg hd.le hx) n)
  have he := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-d*x)).le
  have hex : Real.exp (d*x)*Real.exp (-d*x)=1 := by rw [← Real.exp_add]; simp
  have hc : (d*x)^n*Real.exp (-d*x) ≤ (n.factorial:ℝ) := by
    calc
      _ ≤ (Real.exp (d*x)*(n.factorial:ℝ))*Real.exp (-d*x) := he
      _ = _ := by rw [mul_right_comm,hex,one_mul]
  apply (le_div_iff₀ (pow_pos hd n)).mpr
  simpa only [mul_pow,mul_comm (d^n),mul_assoc] using hc

theorem profile_split (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (x : Joint 2 4) :
    chargeProfile α β wL wR c b P g x=
      Complex.exp (-((α/(2*wL):ℝ):ℂ)*(leftRadius c x:ℂ)-
        ((α*wR/2:ℝ):ℂ)*(rightRadius c x:ℂ))*chargeProfile α β (2*wL) (wR/2) c b P g x := by
  simp only [chargeProfile,chargeQuadratic_coordinates]
  have he : -(α:ℂ)*(((1/wL)*leftRadius c x+wR*rightRadius c x:ℝ):ℂ)=
      (-((α/(2*wL):ℝ):ℂ)*(leftRadius c x:ℂ)-((α*wR/2:ℝ):ℂ)*(rightRadius c x:ℂ))+
        (-(α:ℂ)*(((1/(2*wL))*leftRadius c x+(wR/2)*rightRadius c x:ℝ):ℂ)) := by
    push_cast
    ring
  change (Real.pi/α:ℝ)*g (x (.inr 0))*Complex.exp
      (-(α:ℂ)*(((1/wL)*leftRadius c x+wR*rightRadius c x:ℝ):ℂ))*_=_
  rw [he,Complex.exp_add]
  unfold leftRadius rightRadius
  ring

theorem moment_memLp (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (m n : ℕ) : MemLp (momentProfile α β wL wR c b P g m n) 2 volume := by
  let dl := α/(2*wL)
  let dr := α*wR/2
  have hl : 0 < dl := div_pos hα (mul_pos (by norm_num) hL)
  have hr : 0 < dr := div_pos (mul_pos hα hR) (by norm_num)
  let cap := ((m.factorial:ℝ)/dl^m)*((n.factorial:ℝ)/dr^n)
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  have hm : MemLp (chargeProfile α β (2*wL) (wR/2) c b P g) 2 volume :=
    (memLp_congr_ae (generic_charge_coe α β (2*wL) (wR/2) hα hβ
      (mul_pos (by norm_num) hL) (div_pos hR (by norm_num)) b P g hc hg c hmatch)).mp
      (Lp.memLp (chargeCoordinates (genericState α β (2*wL) (wR/2) hα hβ
        (mul_pos (by norm_num) hL) (div_pos hR (by norm_num)) b P g hc hg)))
  have hcont : Continuous (momentProfile α β wL wR c b P g m n) := by
    unfold momentProfile chargeProfile
    simp only [chargeQuadratic_coordinates,leftRadius,rightRadius,
      KFCausalNeutralLinePackets.packet,KFCausalNeutralLinePackets.entire]
    fun_prop
  apply (hm.const_mul (cap:ℂ)).of_le hcont.aestronglyMeasurable
  filter_upwards [] with x
  obtain ⟨hx,hy⟩ := radii_nonnegative c x
  have hp := mul_le_mul (power_decay_bound dl (leftRadius c x) hl hx m)
    (power_decay_bound dr (rightRadius c x) hr hy n) (by positivity) (by positivity)
  have he : ‖Complex.exp (-((α/(2*wL):ℝ):ℂ)*(leftRadius c x:ℂ)-
      ((α*wR/2:ℝ):ℂ)*(rightRadius c x:ℂ))‖=
      Real.exp (-dl*leftRadius c x)*Real.exp (-dr*rightRadius c x) := by
    rw [Complex.norm_exp]
    simp only [Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
      Complex.neg_im,Complex.ofReal_im,neg_zero,mul_zero,sub_zero]
    dsimp [dl,dr]
    rw [show -(α/(2*wL))*leftRadius c x-(α*wR/2)*rightRadius c x=
      -(α/(2*wL))*leftRadius c x+(-(α*wR/2)*rightRadius c x) by ring,Real.exp_add]
  simp only [momentProfile,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hx,abs_of_nonneg hy,abs_of_nonneg hcap]
  rw [profile_split α β wL wR c b P g x,norm_mul,he]
  have hb := mul_le_mul_of_nonneg_right hp (norm_nonneg (chargeProfile α β (2*wL) (wR/2) c b P g x))
  dsimp [cap] at *
  nlinarith [norm_nonneg (chargeProfile α β (2*wL) (wR/2) c b P g x)]

def genericMomentState (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (m n : ℕ) : Hilbert := chargeCoordinates.symm
      ((moment_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg m n).toLp
        (momentProfile α β wL wR c b P g m n))

theorem generic_charge_coe (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hL : 0 < wL) (hR : 0 < wR) (hmatch : Real.pi^2/α=α*c^2)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)
    (m n : ℕ) :
    chargeCoordinates (genericMomentState α β wL wR c hα hβ hL hR hmatch b P g hc hg m n)=ᵐ[volume]
      momentProfile α β wL wR c b P g m n := by
  simp only [genericMomentState,LinearIsometryEquiv.apply_symm_apply]
  exact (moment_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg m n).coeFn_toLp

def momentState (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (m n : ℕ) : Hilbert :=
  genericMomentState (groundWidth h) (neutralWidth h) wL wR (momentumScale h)
    (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (zero_lt_one.trans_le hL) (zero_lt_one.trans_le hR) (groundWidth_matching h hh)
    b P (clock ε a C p) (clock_continuous ε a C p) (clock_memLp ε a C p hε ha) m n

theorem momentState_charge_coe (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) (m n : ℕ) :
    chargeCoordinates (momentState ε a h wL wR C p b P hε ha hh hL hR m n)=ᵐ[volume]
      momentProfile (groundWidth h) (neutralWidth h) wL wR (momentumScale h) b P (clock ε a C p) m n :=
  generic_charge_coe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem momentState_zero (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR) :
    momentState ε a h wL wR C p b P hε ha hh hL hR 0 0=state ε a h wL wR C p b P hε ha hh hL hR := by
  apply chargeCoordinates.injective
  apply Lp.ext
  filter_upwards [momentState_charge_coe ε a h wL wR C p b P hε ha hh hL hR 0 0,
    KFCausalIndependentRadialPackets.state_charge_coe ε a h wL wR C p b P hε ha hh hL hR] with x hx hy
  rw [hx,hy]
  simp only [momentProfile,pow_zero,mul_one,one_mul]

#print axioms profile_split
#print axioms moment_memLp
#print axioms generic_charge_coe
#print axioms momentState_charge_coe
#print axioms momentState_zero
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPacketMoments
