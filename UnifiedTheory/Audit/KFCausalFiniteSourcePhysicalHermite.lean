/- Physical Hermite uncertainty for arbitrary finite neutral-source families
at one charged Gaussian width. The common gauge acts on the summed profile;
all cross-source terms remain in both field energies. -/
import UnifiedTheory.Audit.KFCausalFiniteSourceHermiteMoments
import UnifiedTheory.Audit.KFCausalSingleWidthPhysicalHermite

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFiniteSourcePhysicalHermite
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralLinePackets (packet entire step)
open KFCausalNeutralAngularFourierPacket
open KFCausalSingleWidthHermiteMoments (gaussianMass variance slope)
open KFCausalFiniteSourceHermiteMoments
open KFCausalNeutralFourierField (fieldLine spectrum fieldPolynomial)

def field (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (L η : ℝ) (j : ℕ) (ξ v : ℝ) : ℂ :=
  angularTransform (fieldLine n β b c P j (L*v) (η*v)) ξ

def channelEnergy (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (j : ℕ) : ℝ :=
  ∫ ξ : ℝ, ∫ v : ℝ, Real.exp (-h*v^2)*‖field n β b c P L η j ξ v‖^2

def transformedSources {n : ℕ} (β : ℝ) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => -Complex.I*b i/(2*(β:ℂ))

def transformedPolynomials {n : ℕ} (β : ℝ) (b : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) : Fin n → Polynomial ℂ :=
  fun i => transformedPolynomial β (b i) (P i)

private theorem spectrum_sum (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hβ : 0 < β) (j : ℕ) (ξ : ℝ) :
    spectrum n β b c P j 0 (ξ/(2*Real.pi)) =
      ∑ i, c i*angularTransform (packet β (b i) (Polynomial.X^j*P i)) ξ := by
  rw [KFCausalNeutralFourierQuadraticJet.spectrum_sum n β b c P hβ]
  apply Finset.sum_congr rfl
  intro i _
  have he : KFCausalNeutralFourierQuadraticJet.packetMoment β (b i) (P i) j =
      packet β (b i) (Polynomial.X^j*P i) := by
    funext x
    simp only [KFCausalNeutralFourierQuadraticJet.packetMoment,packet,entire,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]
    ring
  rw [he]
  rfl

private theorem moment_zero (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hβ : 0 < β) (ξ : ℝ) :
    spectrum n β b c P 0 0 (ξ/(2*Real.pi)) =
      profile n (1/(4*β)) (transformedSources β b) c (transformedPolynomials β b P) ξ := by
  rw [spectrum_sum n β b c P hβ]
  simp only [pow_zero,one_mul,profile,transformedSources,transformedPolynomials]
  apply Finset.sum_congr rfl
  intro i _
  rw [packet_transform β (b i) (P i) hβ]

private theorem moment_one (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hβ : 0 < β) (ξ : ℝ) :
    spectrum n β b c P 1 0 (ξ/(2*Real.pi)) =
      Complex.I*profile n (1/(4*β)) (transformedSources β b) c
        (polyStep (1/(4*β)) (transformedSources β b) (transformedPolynomials β b P)) ξ := by
  rw [spectrum_sum n β b c P hβ]
  simp only [pow_one,profile,transformedSources,transformedPolynomials,polyStep,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [angular_moment_one β (b i) (P i) hβ]
  ring

private theorem moment_two (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hβ : 0 < β) (ξ : ℝ) :
    spectrum n β b c P 2 0 (ξ/(2*Real.pi)) =
      -profile n (1/(4*β)) (transformedSources β b) c
        (polyStep (1/(4*β)) (transformedSources β b)
          (polyStep (1/(4*β)) (transformedSources β b) (transformedPolynomials β b P))) ξ := by
  rw [spectrum_sum n β b c P hβ]
  simp only [profile,transformedSources,transformedPolynomials,polyStep,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [angular_moment_two β (b i) (P i) hβ]
  ring

theorem field_shift (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (L η : ℝ) (hβ : 0 < β) (j : ℕ) (ξ v : ℝ) :
    field n β b c P L η j ξ v = (Real.exp (-η*ξ*v):ℂ)*
      spectrum n β b c P j (slope L η*(v:ℂ)) (ξ/(2*Real.pi)) := by
  unfold field angularTransform
  rw [KFCausalNeutralFourierField.fieldLine_fourier n β hβ]
  have hq : ((L*v:ℝ):ℂ)-((η*v:ℝ):ℂ)*Complex.I = slope L η*(v:ℂ) := by
    unfold KFCausalSingleWidthHermiteMoments.slope
    push_cast
    ring
  rw [hq]
  congr 2
  field_simp

private theorem field_one (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (L η : ℝ) (hβ : 0 < β) (ξ v : ℝ) :
    let B := 1/(4*β)
    let z := transformedSources β b
    let R := transformedPolynomials β b P
    field n β b c P L η 1 ξ v = (Real.exp (-η*ξ*v):ℂ)*
      (Complex.I*profile n B z c (polyStep B z R) ξ+
        slope L η*(v:ℂ)*profile n B z c R ξ) := by
  rw [field_shift n β b c P L η hβ,
    KFCausalNeutralFourierQuadraticJet.spectrum_one n β b c P hβ,
    moment_one n β b c P hβ,moment_zero n β b c P hβ]

private theorem field_two (n : ℕ) (β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (L η : ℝ) (hβ : 0 < β) (ξ v : ℝ) :
    let B := 1/(4*β)
    let z := transformedSources β b
    let R := transformedPolynomials β b P
    field n β b c P L η 2 ξ v = (Real.exp (-η*ξ*v):ℂ)*
      (-profile n B z c (polyStep B z (polyStep B z R)) ξ+
        2*(slope L η*(v:ℂ))*(Complex.I*profile n B z c (polyStep B z R) ξ)+
        (slope L η*(v:ℂ))^2*profile n B z c R ξ) := by
  rw [field_shift n β b c P L η hβ,
    KFCausalNeutralFourierQuadraticJet.spectrum_two n β b c P hβ,
    moment_two n β b c P hβ,moment_one n β b c P hβ,moment_zero n β b c P hβ]

private theorem width_profile (n : ℕ) (B q : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    profile n (B+q/2) b c P ξ = (Real.exp (-q*ξ^2/2):ℂ)*profile n B b c P ξ := by
  simp only [profile,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : packet (B+q/2) (b i) (P i) ξ =
      (Real.exp (-q*ξ^2/2):ℂ)*packet B (b i) (P i) ξ := by
    simp only [packet,entire,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he]
  ring

private theorem width_step (n : ℕ) (B q : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    profile n B b c (polyStep (B+q/2) b P) ξ =
      profile n B b c (polyStep B b P) ξ-(q:ℂ)*(ξ:ℂ)*profile n B b c P ξ := by
  simp only [profile,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [polyStep,packet,entire,step,Polynomial.eval_add,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  push_cast
  ring

private theorem width_step_two (n : ℕ) (B q : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (ξ : ℝ) :
    profile n B b c (polyStep (B+q/2) b (polyStep (B+q/2) b P)) ξ =
      profile n B b c (polyStep B b (polyStep B b P)) ξ-
        2*(q:ℂ)*(ξ:ℂ)*profile n B b c (polyStep B b P) ξ-
        (q:ℂ)*profile n B b c P ξ+(q:ℂ)^2*(ξ:ℂ)^2*profile n B b c P ξ := by
  simp only [profile,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [polyStep,packet,entire,step,Polynomial.derivative_add,Polynomial.derivative_sub,
    Polynomial.derivative_mul,Polynomial.derivative_C,Polynomial.derivative_X,
    Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_zero,Polynomial.eval_one]
  push_cast
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

theorem first_channel_pointwise (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) (ξ t : ℝ) :
    let B := gaugeWidth β h η
    let z := transformedSources β b
    let R := transformedPolynomials β b P
    Real.exp (-h*(t-η*ξ/h)^2)*‖field n β b c P L η 1 ξ (t-η*ξ/h)‖^2 =
      Real.exp (-h*t^2)*‖profile n B z c (covariant B z (L*η/h) R) ξ+
        slope L η*(t:ℂ)*profile n B z c R ξ‖^2 := by
  let B := gaugeWidth β h η
  let z := transformedSources β b
  let R := transformedPolynomials β b P
  have hb : 1/(4*β) = B+(η^2/h)/2 := by dsimp [B,gaugeWidth]; ring
  rw [field_one n β b c P L η hβ,hb,width_profile,width_profile,width_step]
  have hn := (KFCausalSingleWidthHermiteMoments.gauged_channel_identities h L η ξ t
    (profile n B z c R ξ) (profile n B z c (polyStep B z R) ξ)
    (profile n B z c (polyStep B z (polyStep B z R)) ξ) (ne_of_gt hh)).1
  rw [← covariant_one] at hn
  have he : Complex.I*((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (profile n B z c (polyStep B z R) ξ-(η^2/h:ℝ)*(ξ:ℂ)*profile n B z c R ξ))+
      slope L η*((t-η*ξ/h:ℝ):ℂ)*
        ((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*profile n B z c R ξ) =
      (Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (profile n B z c (covariant B z (L*η/h) R) ξ+slope L η*(t:ℂ)*profile n B z c R ξ) := by
    rw [← hn]
    ring
  change Real.exp _*‖(Real.exp _:ℂ)*(_+_)‖^2 = _
  rw [he,← mul_assoc]
  exact completed_norm h η ξ t (ne_of_gt hh) _

theorem second_channel_pointwise (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) (ξ t : ℝ) :
    let B := gaugeWidth β h η
    let z := transformedSources β b
    let R := transformedPolynomials β b P
    Real.exp (-h*(t-η*ξ/h)^2)*‖field n β b c P L η 2 ξ (t-η*ξ/h)‖^2 =
      Real.exp (-h*t^2)*‖profile n B z c (covariant B z (L*η/h) (covariant B z (L*η/h) R)) ξ+
        (variance h L η:ℂ)*profile n B z c R ξ+
        2*slope L η*(t:ℂ)*profile n B z c (covariant B z (L*η/h) R) ξ+
        (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*profile n B z c R ξ‖^2 := by
  let B := gaugeWidth β h η
  let z := transformedSources β b
  let R := transformedPolynomials β b P
  have hb : 1/(4*β) = B+(η^2/h)/2 := by dsimp [B,gaugeWidth]; ring
  rw [field_two n β b c P L η hβ,hb,width_profile,width_profile,width_profile,width_step_two,width_step]
  have hn := (KFCausalSingleWidthHermiteMoments.gauged_channel_identities h L η ξ t
    (profile n B z c R ξ) (profile n B z c (polyStep B z R) ξ)
    (profile n B z c (polyStep B z (polyStep B z R)) ξ) (ne_of_gt hh)).2
  rw [← covariant_one,← covariant_two] at hn
  have he : -((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (profile n B z c (polyStep B z (polyStep B z R)) ξ-
          2*(η^2/h:ℝ)*(ξ:ℂ)*profile n B z c (polyStep B z R) ξ-
          (η^2/h:ℝ)*profile n B z c R ξ+(η^2/h:ℝ)^2*(ξ:ℂ)^2*profile n B z c R ξ))+
      2*(slope L η*((t-η*ξ/h:ℝ):ℂ))*
        (Complex.I*((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
          (profile n B z c (polyStep B z R) ξ-(η^2/h:ℝ)*(ξ:ℂ)*profile n B z c R ξ)))+
      (slope L η*((t-η*ξ/h:ℝ):ℂ))^2*
        ((Real.exp (-(η^2/h)*ξ^2/2):ℂ)*profile n B z c R ξ) =
      (Real.exp (-(η^2/h)*ξ^2/2):ℂ)*
        (profile n B z c (covariant B z (L*η/h) (covariant B z (L*η/h) R)) ξ+
          (variance h L η:ℂ)*profile n B z c R ξ+
          2*slope L η*(t:ℂ)*profile n B z c (covariant B z (L*η/h) R) ξ+
          (slope L η)^2*((t:ℂ)^2-(1/(2*h):ℝ))*profile n B z c R ξ) := by
    rw [← hn]
    ring
  change Real.exp _*‖(Real.exp _:ℂ)*(_+_+_)‖^2 = _
  rw [he,← mul_assoc]
  exact completed_norm h η ξ t (ne_of_gt hh) _

theorem first_energy_identity (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) :
    channelEnergy n h L η β b c P 1 =
      firstEnergy n h L η (gaugeWidth β h η) (transformedSources β b) c
        (L*η/h) (transformedPolynomials β b P) := by
  unfold channelEnergy firstEnergy
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← integral_sub_right_eq_self
    (fun v : ℝ => Real.exp (-h*v^2)*‖field n β b c P L η 1 ξ v‖^2) (η*ξ/h)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact first_channel_pointwise n h L η β b c P hh hβ ξ t

theorem second_energy_identity (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) :
    channelEnergy n h L η β b c P 2 =
      secondEnergy n h L η (gaugeWidth β h η) (transformedSources β b) c
        (L*η/h) (transformedPolynomials β b P) := by
  unfold channelEnergy secondEnergy
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [← integral_sub_right_eq_self
    (fun v : ℝ => Real.exp (-h*v^2)*‖field n β b c P L η 2 ξ v‖^2) (η*ξ/h)]
  apply integral_congr_ae
  filter_upwards [] with t
  exact second_channel_pointwise n h L η β b c P hh hβ ξ t

theorem physical_channel_lower (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) (hfloor : 2*β*η^2 < h) :
    3*variance h L η*channelEnergy n h L η β b c P 1 ≤ channelEnergy n h L η β b c P 2 := by
  rw [first_energy_identity n h L η β b c P hh hβ,second_energy_identity n h L η β b c P hh hβ]
  exact second_lower _ _ _ _ _ _ _ _ _ hh (gaugeWidth_positive β h η hβ hh hfloor)

def frequencyEnergy (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (j : ℕ) : ℝ :=
  ∫ k : ℝ, ∫ v : ℝ, Real.exp (-h*v^2)*‖(𝓕 (fieldLine n β b c P j (L*v) (η*v))) k‖^2

theorem frequency_normalization (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (j : ℕ) :
    channelEnergy n h L η β b c P j = (2*Real.pi)*frequencyEnergy n h L η β b c P j := by
  unfold channelEnergy field angularTransform frequencyEnergy
  simpa only [abs_of_pos (show 0 < 2*Real.pi by positivity),smul_eq_mul] using
    Measure.integral_comp_div (fun k : ℝ => ∫ v : ℝ, Real.exp (-h*v^2)*
      ‖(𝓕 (fieldLine n β b c P j (L*v) (η*v))) k‖^2) (2*Real.pi)

theorem original_frequency_lower (n : ℕ) (h L η β : ℝ) (b c : Fin n → ℂ)
    (P : Fin n → Polynomial ℂ) (hh : 0 < h) (hβ : 0 < β) (hfloor : 2*β*η^2 < h) :
    3*variance h L η*frequencyEnergy n h L η β b c P 1 ≤ frequencyEnergy n h L η β b c P 2 := by
  have he := physical_channel_lower n h L η β b c P hh hβ hfloor
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
end UnifiedTheory.Audit.KFCausalFiniteSourcePhysicalHermite
