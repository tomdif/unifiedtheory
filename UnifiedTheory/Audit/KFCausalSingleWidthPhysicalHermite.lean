/- The original one-source neutral Fourier fields, at one charged Gaussian
width, have the linked Hermite representation. Polynomial degree and source
are unrestricted. This scalar endpoint does not discard cross-width terms
or assert the unrestricted-width response estimate. -/
import UnifiedTheory.Audit.KFCausalNeutralAngularFourierPacket
import UnifiedTheory.Audit.KFCausalSingleWidthHermiteMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalSingleWidthPhysicalHermite
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralLinePackets (packet entire step)
open KFCausalNeutralAngularFourierPacket
open KFCausalSingleWidthHermiteMoments
open KFCausalNeutralFourierField (fieldLine spectrum fieldPolynomial)

def field (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (L η : ℝ) (j : ℕ) (ξ v : ℝ) : ℂ :=
  angularTransform (fieldLine 1 β (fun _ => b) (fun _ => 1) (fun _ => P) j (L*v) (η*v)) ξ

def channelEnergy (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : ℕ) : ℝ :=
  ∫ ξ : ℝ, ∫ v : ℝ, Real.exp (-h*v^2)*‖field β b P L η j ξ v‖^2

private theorem single_spectrum (β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (j : ℕ) (q : ℂ) (ξ : ℝ) :
    spectrum 1 β (fun _ => b) (fun _ => 1) (fun _ => P) j q (ξ/(2*Real.pi)) =
      angularTransform (packet β b (fieldPolynomial j q P)) ξ := by
  unfold KFCausalNeutralFourierField.spectrum angularTransform
  have he : KFCausalNeutralFourierShift.line 1 β (fun _ => b) (fun _ => 1)
      (fun _ => fieldPolynomial j q P) 0 = packet β b (fieldPolynomial j q P) := by
    funext x
    simp [KFCausalNeutralFourierShift.line,KFCausalGaussianContourShift.horizontal,
      KFCausalNeutralLineDomain.family,packet]
  rw [he]

theorem field_shift (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (L η : ℝ)
    (hβ : 0 < β) (j : ℕ) (ξ v : ℝ) :
    field β b P L η j ξ v = (Real.exp (-η*ξ*v):ℂ)*
      angularTransform (packet β b (fieldPolynomial j (slope L η*(v:ℂ)) P)) ξ := by
  unfold field angularTransform
  rw [KFCausalNeutralFourierField.fieldLine_fourier 1 β hβ]
  have hq : ((L*v:ℝ):ℂ)-((η*v:ℝ):ℂ)*Complex.I = slope L η*(v:ℂ) := by
    unfold KFCausalSingleWidthHermiteMoments.slope
    push_cast
    ring
  rw [hq,single_spectrum]
  congr 2
  field_simp

private theorem field_one (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (L η : ℝ)
    (hβ : 0 < β) (ξ v : ℝ) :
    field β b P L η 1 ξ v = (Real.exp (-η*ξ*v):ℂ)*
      (angularTransform (packet β b (Polynomial.X*P)) ξ+
        slope L η*(v:ℂ)*angularTransform (packet β b P) ξ) := by
  unfold field angularTransform
  rw [KFCausalNeutralFourierField.fieldLine_fourier 1 β hβ,
    KFCausalNeutralFourierQuadraticJet.spectrum_one 1 β _ _ _ hβ]
  rw [single_spectrum,single_spectrum]
  simp only [fieldPolynomial,map_zero,add_zero,pow_one,pow_zero,one_mul,angularTransform]
  have hq : ((L*v:ℝ):ℂ)-((η*v:ℝ):ℂ)*Complex.I = slope L η*(v:ℂ) := by
    unfold KFCausalSingleWidthHermiteMoments.slope
    push_cast
    ring
  rw [hq]
  congr 2
  field_simp

private theorem field_two (β : ℝ) (b : ℂ) (P : Polynomial ℂ) (L η : ℝ)
    (hβ : 0 < β) (ξ v : ℝ) :
    field β b P L η 2 ξ v = (Real.exp (-η*ξ*v):ℂ)*
      (angularTransform (packet β b (Polynomial.X^2*P)) ξ+
        2*(slope L η*(v:ℂ))*angularTransform (packet β b (Polynomial.X*P)) ξ+
        (slope L η*(v:ℂ))^2*angularTransform (packet β b P) ξ) := by
  unfold field angularTransform
  rw [KFCausalNeutralFourierField.fieldLine_fourier 1 β hβ,
    KFCausalNeutralFourierQuadraticJet.spectrum_two 1 β _ _ _ hβ]
  rw [single_spectrum,single_spectrum,single_spectrum]
  simp only [fieldPolynomial,map_zero,add_zero,pow_one,pow_zero,one_mul,angularTransform]
  have hq : ((L*v:ℝ):ℂ)-((η*v:ℝ):ℂ)*Complex.I = slope L η*(v:ℂ) := by
    unfold KFCausalSingleWidthHermiteMoments.slope
    push_cast
    ring
  rw [hq]
  congr 2
  field_simp

private theorem width_packet (B q : ℝ) (b : ℂ) (P : Polynomial ℂ) (ξ : ℝ) :
    packet (B+q/2) b P ξ = (Real.exp (-q*ξ^2/2):ℂ)*packet B b P ξ := by
  simp only [packet,entire,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem width_step (B q : ℝ) (b : ℂ) (P : Polynomial ℂ) (ξ : ℝ) :
    packet B b (step (B+q/2) b P) ξ =
      packet B b (step B b P) ξ-(q:ℂ)*(ξ:ℂ)*packet B b P ξ := by
  simp only [packet,entire,step,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  push_cast
  ring

private theorem width_step_two (B q : ℝ) (b : ℂ) (P : Polynomial ℂ) (ξ : ℝ) :
    packet B b (step (B+q/2) b (step (B+q/2) b P)) ξ =
      packet B b (step B b (step B b P)) ξ-
        2*(q:ℂ)*(ξ:ℂ)*packet B b (step B b P) ξ-
        (q:ℂ)*packet B b P ξ+(q:ℂ)^2*(ξ:ℂ)^2*packet B b P ξ := by
  simp only [packet,entire,step,Polynomial.derivative_add,Polynomial.derivative_sub,
    Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_X,
    Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_zero,Polynomial.eval_one]
  push_cast
  ring

private theorem covariant_one (B d : ℝ) (b : ℂ) (P : Polynomial ℂ) (ξ : ℝ) :
    packet B b (covariantStep B b d P) ξ =
      Complex.I*packet B b (step B b P) ξ-(d:ℂ)*(ξ:ℂ)*packet B b P ξ := by
  simp only [packet,entire,covariantStep,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  ring

private theorem covariant_two (B d : ℝ) (b : ℂ) (P : Polynomial ℂ) (ξ : ℝ) :
    packet B b (covariantStep B b d (covariantStep B b d P)) ξ =
      -packet B b (step B b (step B b P)) ξ-
        2*Complex.I*(d:ℂ)*(ξ:ℂ)*packet B b (step B b P) ξ-
        Complex.I*(d:ℂ)*packet B b P ξ+(d:ℂ)^2*(ξ:ℂ)^2*packet B b P ξ := by
  simp only [packet,entire,covariantStep,step,Polynomial.derivative_add,
    Polynomial.derivative_sub,Polynomial.derivative_mul,Polynomial.derivative_C,
    Polynomial.derivative_X,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_zero,
    Polynomial.eval_one]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem completed_norm (h η ξ t : ℝ) (hh : h ≠ 0) (z : ℂ) :
    Real.exp (-h*(t-η*ξ/h)^2)*
      ‖(Real.exp (-η*ξ*(t-η*ξ/h)):ℂ)*(Real.exp (-(η^2/h)*ξ^2/2):ℂ)*z‖^2 =
        Real.exp (-h*t^2)*‖z‖^2 := by
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  rw [← mul_assoc,← Real.exp_add,← Real.exp_add]
  congr 2
  norm_num
  field_simp
  ring

theorem first_channel_pointwise (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) (ξ t : ℝ) :
    let B := gaugeWidth β h η
    let z := -Complex.I*b/(2*(β:ℂ))
    let R := transformedPolynomial β b P
    Real.exp (-h*(t-η*ξ/h)^2)*‖field β b P L η 1 ξ (t-η*ξ/h)‖^2 =
      Real.exp (-h*t^2)*‖packet B z (covariantStep B z (L*η/h) R) ξ+
        slope L η*(t:ℂ)*packet B z R ξ‖^2 := by
  let B := gaugeWidth β h η
  let z := -Complex.I*b/(2*(β:ℂ))
  let R := transformedPolynomial β b P
  have hb : 1/(4*β) = B+(η^2/h)/2 := by dsimp [B,gaugeWidth]; ring
  rw [field_one _ _ _ _ _ hβ,angular_moment_one _ _ _ hβ,packet_transform _ _ _ hβ,hb]
  rw [width_packet,width_packet,width_step]
  have hn := (gauged_channel_identities h L η ξ t (packet B z R ξ)
    (packet B z (step B z R) ξ) (packet B z (step B z (step B z R)) ξ) (ne_of_gt hh)).1
  rw [← covariant_one] at hn
  have he : Complex.I*((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (packet B z (step B z R) ξ-(η^2/h:ℝ)*(ξ:ℂ)*packet B z R ξ))+
      slope L η*((t-η*ξ/h:ℝ):ℂ)*
        ((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*packet B z R ξ) =
      (Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (packet B z (covariantStep B z (L*η/h) R) ξ+slope L η*(t:ℂ)*packet B z R ξ) := by
    rw [← hn]
    ring
  change Real.exp _*‖(Real.exp _:ℂ)*(_+_)‖^2 = _
  rw [he,← mul_assoc]
  exact completed_norm h η ξ t (ne_of_gt hh) _

theorem second_channel_pointwise (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) (ξ t : ℝ) :
    let B := gaugeWidth β h η
    let z := -Complex.I*b/(2*(β:ℂ))
    let R := transformedPolynomial β b P
    Real.exp (-h*(t-η*ξ/h)^2)*‖field β b P L η 2 ξ (t-η*ξ/h)‖^2 =
      Real.exp (-h*t^2)*‖packet B z (covariantStep B z (L*η/h) (covariantStep B z (L*η/h) R)) ξ+
        (variance h L η:ℂ)*packet B z R ξ+
        2*slope L η*(t:ℂ)*packet B z (covariantStep B z (L*η/h) R) ξ+
        (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*packet B z R ξ‖^2 := by
  let B := gaugeWidth β h η
  let z := -Complex.I*b/(2*(β:ℂ))
  let R := transformedPolynomial β b P
  have hb : 1/(4*β) = B+(η^2/h)/2 := by dsimp [B,gaugeWidth]; ring
  rw [field_two _ _ _ _ _ hβ,angular_moment_one _ _ _ hβ,
    angular_moment_two _ _ _ hβ,packet_transform _ _ _ hβ,hb]
  rw [width_packet,width_packet,width_packet,width_step_two,width_step]
  have hn := (gauged_channel_identities h L η ξ t (packet B z R ξ)
    (packet B z (step B z R) ξ) (packet B z (step B z (step B z R)) ξ) (ne_of_gt hh)).2
  rw [← covariant_one,← covariant_two] at hn
  have he : -((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (packet B z (step B z (step B z R)) ξ-
          2*(η^2/h:ℝ)*(ξ:ℂ)*packet B z (step B z R) ξ-
          (η^2/h:ℝ)*packet B z R ξ+(η^2/h:ℝ)^2*(ξ:ℂ)^2*packet B z R ξ))+
      2*(slope L η*((t-η*ξ/h:ℝ):ℂ))*
        (Complex.I*((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
          (packet B z (step B z R) ξ-(η^2/h:ℝ)*(ξ:ℂ)*packet B z R ξ)))+
      (slope L η*((t-η*ξ/h:ℝ):ℂ))^2*
        ((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*packet B z R ξ) =
      (Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (packet B z (covariantStep B z (L*η/h) (covariantStep B z (L*η/h) R)) ξ+
          (variance h L η:ℂ)*packet B z R ξ+
          2*slope L η*(t:ℂ)*packet B z (covariantStep B z (L*η/h) R) ξ+
          (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*packet B z R ξ) := by
    rw [← hn]
    ring
  change Real.exp _*‖(Real.exp _:ℂ)*(_+_+_)‖^2 = _
  rw [he,← mul_assoc]
  exact completed_norm h η ξ t (ne_of_gt hh) _

theorem first_energy_identity (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) :
    channelEnergy h L η β b P 1 =
      firstEnergy h L η (gaugeWidth β h η) (-Complex.I*b/(2*(β:ℂ)))
        (L*η/h) (transformedPolynomial β b P) := by
  unfold channelEnergy firstEnergy
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← integral_sub_right_eq_self (fun v : ℝ => Real.exp (-h*v^2)*‖field β b P L η 1 ξ v‖^2) (η*ξ/h)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact first_channel_pointwise h L η β b P hh hβ ξ t

theorem second_energy_identity (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) :
    channelEnergy h L η β b P 2 =
      secondEnergy h L η (gaugeWidth β h η) (-Complex.I*b/(2*(β:ℂ)))
        (L*η/h) (transformedPolynomial β b P) := by
  unfold channelEnergy secondEnergy
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← integral_sub_right_eq_self (fun v : ℝ => Real.exp (-h*v^2)*‖field β b P L η 2 ξ v‖^2) (η*ξ/h)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact second_channel_pointwise h L η β b P hh hβ ξ t

theorem physical_channel_lower (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) (hfloor : 2*β*η^2 < h) :
    3*variance h L η*channelEnergy h L η β b P 1 ≤ channelEnergy h L η β b P 2 := by
  rw [first_energy_identity h L η β b P hh hβ,second_energy_identity h L η β b P hh hβ]
  exact linked_second_lower _ _ _ _ _ _ _ hh (gaugeWidth_positive β h η hβ hh hfloor)

def frequencyEnergy (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : ℕ) : ℝ :=
  ∫ k : ℝ, ∫ v : ℝ, Real.exp (-h*v^2)*
    ‖(𝓕 (fieldLine 1 β (fun _ => b) (fun _ => 1) (fun _ => P) j (L*v) (η*v))) k‖^2

theorem frequency_normalization (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : ℕ) :
    channelEnergy h L η β b P j = (2*Real.pi)*frequencyEnergy h L η β b P j := by
  unfold channelEnergy field angularTransform frequencyEnergy
  simpa only [abs_of_pos (show 0 < 2*Real.pi by positivity),smul_eq_mul] using
    Measure.integral_comp_div (fun k : ℝ => ∫ v : ℝ, Real.exp (-h*v^2)*
      ‖(𝓕 (fieldLine 1 β (fun _ => b) (fun _ => 1) (fun _ => P) j (L*v) (η*v))) k‖^2)
      (2*Real.pi)

theorem original_frequency_lower (h L η β : ℝ) (b : ℂ) (P : Polynomial ℂ)
    (hh : 0 < h) (hβ : 0 < β) (hfloor : 2*β*η^2 < h) :
    3*variance h L η*frequencyEnergy h L η β b P 1 ≤ frequencyEnergy h L η β b P 2 := by
  have he := physical_channel_lower h L η β b P hh hβ hfloor
  rw [frequency_normalization,frequency_normalization] at he
  have hp : 0 < 2*Real.pi := by positivity
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith only [he]

#print axioms field_shift
#print axioms first_channel_pointwise
#print axioms second_channel_pointwise
#print axioms first_energy_identity
#print axioms second_energy_identity
#print axioms physical_channel_lower
#print axioms frequency_normalization
#print axioms original_frequency_lower
end
end UnifiedTheory.Audit.KFCausalSingleWidthPhysicalHermite
