/- Exact linked differential constraints for the correlated charged Fourier
polynomial.  The u annihilator and CR lowering are both retained.  No
adjoint, boundary identity, or uniform response inequality is asserted. -/
import UnifiedTheory.Audit.KFCausalJointFourierQuadraticJet
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationCRJet
noncomputable section
open KFCausalNeutralJointCurvatureForm (coefficients)
open scoped FourierTransform

variable (n : ℕ) (w : Fin n → ℝ) (c : Fin n → ℂ) (Q : Fin n → Polynomial ℂ)

def profile (z v : ℂ) : ℂ := ∑ i, coefficients n w c z i*(Q i).eval v

def charged (z v : ℂ) : ℂ :=
  ∑ i, -(w i:ℂ)*coefficients n w c z i*(Q i).eval v

def phase (κ u v : ℂ) : ℂ := Complex.exp (Complex.I*κ*(u+Complex.I*v))

def wave (p q κ u v Y : ℂ) : ℂ :=
  phase κ u v*profile n w c Q (p*(u^2+v^2)+q*Y) v

private theorem profile_path {z v : ℂ → ℂ} {zd vd s : ℂ}
    (hz : HasDerivAt z zd s) (hv : HasDerivAt v vd s) :
    HasDerivAt (fun t => profile n w c Q (z t) (v t))
      (zd*charged n w c Q (z s) (v s)+
        vd*profile n w c (fun i => (Q i).derivative) (z s) (v s)) s := by
  have hc (i : Fin n) :=
    ((hz.const_mul (-(w i:ℂ))).cexp).const_mul (c i*(w i:ℂ))
  have hi (i : Fin n) := (hc i).mul (((Q i).hasDerivAt (v s)).comp s hv)
  have hs := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  convert hs using 1
  dsimp [profile,charged,coefficients]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem derivative_u (p q κ u v Y : ℂ) :
    HasDerivAt (fun t => wave n w c Q p q κ t v Y)
      (Complex.I*κ*wave n w c Q p q κ u v Y+
        2*p*u*phase κ u v*charged n w c Q (p*(u^2+v^2)+q*Y) v) u := by
  have hz := (((hasDerivAt_id u).pow 2).add_const (v^2)).const_mul p |>.add_const (q*Y)
  have hp := ((((hasDerivAt_id u).add_const (Complex.I*v)).const_mul (Complex.I*κ)).cexp)
  have hd := hp.mul (profile_path n w c Q hz (hasDerivAt_const u v))
  convert hd using 1
  dsimp [wave,phase]
  ring

theorem derivative_v (p q κ u v Y : ℂ) :
    HasDerivAt (fun t => wave n w c Q p q κ u t Y)
      (-κ*wave n w c Q p q κ u v Y+
        2*p*v*phase κ u v*charged n w c Q (p*(u^2+v^2)+q*Y) v+
        wave n w c (fun i => (Q i).derivative) p q κ u v Y) v := by
  have hz := (((hasDerivAt_id v).pow 2).const_add (u^2)).const_mul p |>.add_const (q*Y)
  have hp := (((((hasDerivAt_id v).const_mul Complex.I).const_add u).const_mul
    (Complex.I*κ)).cexp)
  have hd := hp.mul (profile_path n w c Q hz (hasDerivAt_id v))
  convert hd using 1
  dsimp [wave,phase]
  linear_combination -(κ*Complex.exp (Complex.I*κ*(u+Complex.I*v))*
    profile n w c Q (p*(u^2+v^2)+q*Y) v)*Complex.I_mul_I

theorem derivative_Y (p q κ u v Y : ℂ) :
    HasDerivAt (fun t => wave n w c Q p q κ u v t)
      (q*phase κ u v*charged n w c Q (p*(u^2+v^2)+q*Y) v) Y := by
  have hz := ((hasDerivAt_id Y).const_mul q).const_add (p*(u^2+v^2))
  have hd := (profile_path n w c Q hz (hasDerivAt_const Y v)).const_mul (phase κ u v)
  convert hd using 1
  dsimp [wave]
  ring

def CR (p q κ u v Y : ℂ) : ℂ :=
  (deriv (fun t => wave n w c Q p q κ t v Y) u+
    Complex.I*deriv (fun t => wave n w c Q p q κ u t Y) v)/2-
    (p/q)*(u+Complex.I*v)*deriv (fun t => wave n w c Q p q κ u v t) Y

theorem ground_constraint (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    deriv (fun t => wave n w c Q p q κ t v Y) u-
      (2*p/q)*u*deriv (fun t => wave n w c Q p q κ u v t) Y-
      Complex.I*κ*wave n w c Q p q κ u v Y = 0 := by
  rw [(derivative_u n w c Q p q κ u v Y).deriv,
    (derivative_Y n w c Q p q κ u v Y).deriv]
  field_simp
  ring

theorem CR_lowering (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    CR n w c Q p q κ u v Y =
      (Complex.I/2)*wave n w c (fun i => (Q i).derivative) p q κ u v Y := by
  unfold CR
  rw [(derivative_u n w c Q p q κ u v Y).deriv,
    (derivative_v n w c Q p q κ u v Y).deriv,
    (derivative_Y n w c Q p q κ u v Y).deriv]
  field_simp
  ring

omit Q in
def channel (ν : ℂ) (m : Fin n → ℕ → ℂ) : ℕ → Fin n → Polynomial ℂ
  | 0, i => Polynomial.C (m i 0)
  | 1, i => Polynomial.C (m i 1)+Polynomial.C (ν*m i 0)*Polynomial.X
  | _, i => Polynomial.C (m i 2)+Polynomial.C (2*ν*m i 1)*Polynomial.X+
      Polynomial.C (ν^2*m i 0)*Polynomial.X^2

private theorem wave_const_mul (d p q κ u v Y : ℂ) :
    wave n w c (fun i => Polynomial.C d*Q i) p q κ u v Y =
      d*wave n w c Q p q κ u v Y := by
  simp only [wave,profile,Polynomial.eval_mul,Polynomial.eval_C,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit Q in
theorem CR_channel_zero (ν : ℂ) (m : Fin n → ℕ → ℂ)
    (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    CR n w c (channel n ν m 0) p q κ u v Y = 0 := by
  rw [CR_lowering n w c _ p q κ u v Y hq]
  simp [channel,wave,profile]

omit Q in
theorem CR_channel_one (ν : ℂ) (m : Fin n → ℕ → ℂ)
    (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    CR n w c (channel n ν m 1) p q κ u v Y =
      (Complex.I*ν/2)*wave n w c (channel n ν m 0) p q κ u v Y := by
  have he : (fun i => (channel n ν m 1 i).derivative) =
      fun i => Polynomial.C ν*channel n ν m 0 i := by
    funext i
    simp [channel]
  rw [CR_lowering n w c _ p q κ u v Y hq,he,wave_const_mul]
  ring

omit Q in
theorem CR_channel_two (ν : ℂ) (m : Fin n → ℕ → ℂ)
    (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    CR n w c (channel n ν m 2) p q κ u v Y =
      (Complex.I*ν)*wave n w c (channel n ν m 1) p q κ u v Y := by
  have he : (fun i => (channel n ν m 2 i).derivative) =
      fun i => Polynomial.C (2*ν)*channel n ν m 1 i := by
    funext i
    simp [channel,Polynomial.derivative_mul,Polynomial.derivative_pow]
    ring
  rw [CR_lowering n w c _ p q κ u v Y hq,he,wave_const_mul]
  ring

omit n w c Q in
theorem phase_norm (κ u v : ℝ) :
    ‖phase (κ:ℂ) (u:ℂ) (v:ℂ)‖^2 = Real.exp (-2*κ*v) := by
  rw [phase,Complex.norm_exp,pow_two,← Real.exp_add]
  congr 1
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  ring

omit Q in
theorem wave_energy (ν : ℂ) (m : Fin n → ℕ → ℂ)
    (p q : ℂ) (κ u v : ℝ) (Y : ℂ) :
    let z := p*((u:ℂ)^2+(v:ℂ)^2)+q*Y
    let G := fun j => ∑ i, coefficients n w c z i*m i j
    ‖wave n w c (channel n ν m 0) p q κ u v Y‖^2+
      ‖wave n w c (channel n ν m 1) p q κ u v Y‖^2/2+
      ‖wave n w c (channel n ν m 2) p q κ u v Y‖^2/4 =
      Real.exp (-2*κ*v)*KFCausalNeutralFourierQuadraticJet.jetEnergy
        (ν*(v:ℂ)) (G 0) (G 1) (G 2) := by
  dsimp only
  let z := p*((u:ℂ)^2+(v:ℂ)^2)+q*Y
  let G := fun j => ∑ i, coefficients n w c z i*m i j
  have h0 : profile n w c (channel n ν m 0) z v = G 0 := by
    simp [profile,channel,G]
  have h1 : profile n w c (channel n ν m 1) z v = G 1+ν*(v:ℂ)*G 0 := by
    simp only [profile,channel,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,G,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : profile n w c (channel n ν m 2) z v =
      G 2+2*(ν*(v:ℂ))*G 1+(ν*(v:ℂ))^2*G 0 := by
    simp only [profile,channel,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X,G,Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change ‖phase κ u v*profile n w c (channel n ν m 0) z v‖^2+
    ‖phase κ u v*profile n w c (channel n ν m 1) z v‖^2/2+
    ‖phase κ u v*profile n w c (channel n ν m 2) z v‖^2/4 = _
  rw [h0,h1,h2]
  simp only [norm_mul,mul_pow,phase_norm,KFCausalNeutralFourierQuadraticJet.jetEnergy]
  ring

omit Q in
theorem actual_energy_bridge (β α : ℝ) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (r : ℂ) (u v Y k : ℝ) :
    let m := fun i j => (𝓕 (KFCausalNeutralFourierQuadraticJet.packetMoment β (b i) (P i) j)) k
    let ν := KFCausalJointFourierQuadraticJet.complexShear r
    let p := KFCausalReciprocalWedgeGeometry.gamma α r
    let q := star p
    let κ := 4*Real.pi*k*r.im
    ‖wave n w c (channel n ν m 0) p q κ u v Y‖^2+
      ‖wave n w c (channel n ν m 1) p q κ u v Y‖^2/2+
      ‖wave n w c (channel n ν m 2) p q κ u v Y‖^2/4 =
      KFCausalJointFourierQuadraticJet.jetSlice n β w b c P r
        (KFCausalReciprocalWedgeGeometry.chart α r (u^2+v^2) Y) v k := by
  dsimp only
  rw [wave_energy]
  unfold KFCausalJointFourierQuadraticJet.jetSlice
    KFCausalJointFourierQuadraticJet.chargedJet KFCausalReciprocalWedgeGeometry.chart
  congr 2
  · ring
  all_goals
    push_cast
    rfl

theorem real_constraints (p q : ℂ) (κ u v Y : ℝ) (hq : q ≠ 0) :
    let du := deriv (fun t : ℝ => wave n w c Q p q κ t v Y) u
    let dv := deriv (fun t : ℝ => wave n w c Q p q κ u t Y) v
    let dy := deriv (fun t : ℝ => wave n w c Q p q κ u v t) Y
    du-(2*p/q)*(u:ℂ)*dy-Complex.I*(κ:ℂ)*wave n w c Q p q κ u v Y = 0 ∧
      (du+Complex.I*dv)/2-(p/q)*((u:ℂ)+Complex.I*(v:ℂ))*dy =
        (Complex.I/2)*wave n w c (fun i => (Q i).derivative) p q κ u v Y := by
  dsimp only
  rw [(derivative_u n w c Q p q κ u v Y).comp_ofReal.deriv,
    (derivative_v n w c Q p q κ u v Y).comp_ofReal.deriv,
    (derivative_Y n w c Q p q κ u v Y).comp_ofReal.deriv]
  constructor <;> field_simp <;> ring

omit Q in
theorem CR_energy_bound (ν : ℂ) (m : Fin n → ℕ → ℂ)
    (p q κ u v Y : ℂ) (hq : q ≠ 0) :
    ‖CR n w c (channel n ν m 0) p q κ u v Y‖^2+
      ‖CR n w c (channel n ν m 1) p q κ u v Y‖^2/2+
      ‖CR n w c (channel n ν m 2) p q κ u v Y‖^2/4 ≤
      ‖ν‖^2/2*(‖wave n w c (channel n ν m 0) p q κ u v Y‖^2+
        ‖wave n w c (channel n ν m 1) p q κ u v Y‖^2/2+
        ‖wave n w c (channel n ν m 2) p q κ u v Y‖^2/4) := by
  rw [CR_channel_zero n w c ν m p q κ u v Y hq,
    CR_channel_one n w c ν m p q κ u v Y hq,
    CR_channel_two n w c ν m p q κ u v Y hq]
  norm_num only [norm_zero,zero_pow,zero_add,norm_mul,norm_div,Complex.norm_I,
    one_mul,Complex.norm_ofNat]
  nlinarith [mul_nonneg (sq_nonneg ‖ν‖)
    (sq_nonneg ‖wave n w c (channel n ν m 0) p q κ u v Y‖),
    mul_nonneg (sq_nonneg ‖ν‖)
    (sq_nonneg ‖wave n w c (channel n ν m 2) p q κ u v Y‖)]

#print axioms derivative_u
#print axioms derivative_v
#print axioms derivative_Y
#print axioms ground_constraint
#print axioms CR_lowering
#print axioms CR_channel_zero
#print axioms CR_channel_one
#print axioms CR_channel_two
#print axioms phase_norm
#print axioms wave_energy
#print axioms actual_energy_bridge
#print axioms real_constraints
#print axioms CR_energy_bound
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationCRJet
