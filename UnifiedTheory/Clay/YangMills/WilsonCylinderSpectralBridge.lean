/- Actual-cylinder covariance decay controls the original full transfer spectrum.
The covariance estimate is an explicit analytic premise in this module.
Compactness and genuine continuous eigenfunction representatives supply the
full complex Hilbert-space conclusion; no alternate update clock is used. -/
import UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum
import UnifiedTheory.Clay.YangMills.ObservableMomentGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCylinderSpectralBridge
noncomputable section
open MeasureTheory Filter WilsonSlabOperator WilsonSlabContraction
open WilsonPositiveGroundState WilsonGroundLocalComparison WilsonInteriorVacuum
open ContinuousBoundaryMoments TransferEnergySurvival
open scoped Topology

variable (n : ℕ) [NeZero n]

/-- Decay in the physical temporal separation of the actual raw cylinders.
The prefactor may depend on the observable but not on padding or separation. -/
def CylinderDecay (β q : ℝ) : Prop :=
  ∀ F : C(Slice n, ℝ), ∃ C : ℝ, ∀ j k : ℕ,
    |covariance n β j k F F| ≤ C * q ^ k

/-- The already constructed raw-cylinder vacuum limit preserves this decay. -/
theorem vacuum_moment_bound (β : ℝ) (hβ : 0 ≤ β) (q : ℝ)
    (hdec : CylinderDecay n β q) (F : C(Slice n, ℝ)) :
    ∃ C : ℝ, ∀ k : ℕ,
      |vacuumCorrelation n β hβ k F F - (groundMean n β hβ F)^2| ≤ C * q ^ k := by
  obtain ⟨C, hC⟩ := hdec F
  refine ⟨C, fun k => ?_⟩
  have ht := (covariance_tendsto n β hβ F F k).abs
  have hh := le_of_tendsto ht (Filter.Eventually.of_forall (fun j => hC j k))
  simpa only [pow_two] using hh

/-- Real continuous amplitudes have the ordinary real integral as their complex inner product. -/
theorem embed_inner (f g : C(Slice n, ℝ)) :
    inner ℂ (embed (measure n) f) (embed (measure n) g) =
      ((∫ u, f u * g u ∂measure n : ℝ) : ℂ) := by
  rw [embed, embed, MeasureTheory.ContinuousMap.inner_toLp]
  simp only [complexify, ContinuousMap.coe_mk, Complex.conj_ofReal, ← Complex.ofReal_mul,
    integral_complex_ofReal]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Positivity of the constructed ground state makes every continuous real
amplitude an actual ground-state-weighted observable. -/
def observable (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  PositiveKernelRatio.quotient (ground n β hβ) f (ground_pos n β hβ)

theorem observable_mul_ground (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    observable n β hβ f * ground n β hβ = f := by
  ext u
  exact div_mul_cancel₀ (f u) (ground_pos n β hβ u).ne'

theorem observable_mean (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    groundMean n β hβ (observable n β hβ f) =
      ∫ u, ground n β hβ u * f u ∂measure n := by
  unfold groundMean
  apply integral_congr_ae
  filter_upwards [] with u
  change (ground n β hβ u)^2 * (f u / ground n β hβ u) = _
  field_simp [(ground_pos n β hβ u).ne']

/-- Existing physical-time iteration is the ordinary power of the same operator. -/
theorem iterate_eq_power (A : Hilbert n →L[ℂ] Hilbert n) (k : ℕ) (v : Hilbert n) :
    iterate A k v = (A ^ k) v := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ, ih, pow_succ', ContinuousLinearMap.mul_apply]

/-- Observable-dependent decay constants disappear from the one-step bound. -/
theorem real_amplitude_contraction (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (f : C(Slice n, ℝ))
    (hmean : (∫ u, ground n β hβ u * f u ∂measure n) = 0) :
    ‖normalized n β (embed (measure n) f)‖ ≤ q * ‖embed (measure n) f‖ := by
  obtain ⟨C, hC⟩ := vacuum_moment_bound n β hβ q hdec (observable n β hβ f)
  have hm : groundMean n β hβ (observable n β hβ f) = 0 := by
    rw [observable_mean, hmean]
  apply ObservableMomentGap.norm_le_of_power_bound (normalized n β)
    (normalized_symmetric n β) (embed (measure n) f) q C hq
  intro k
  rw [← ObservableMomentGap.even_moment (normalized n β) (normalized_symmetric n β)]
  have hh := hC (2 * k)
  simp only [hm, zero_pow (by decide : 2 ≠ 0), sub_zero, vacuumCorrelation,
    observable_mul_ground, iterate_eq_power] at hh
  exact (le_abs_self _).trans hh

/-- Continuous complex representatives split inside the actual complex L2 space. -/
theorem complex_embedding_decomposition (f : C(Slice n, ℂ)) :
    ContinuousMap.toLp 2 (measure n) ℂ f =
      embed (measure n) ⟨fun u => (f u).re, Complex.continuous_re.comp f.continuous⟩ +
      Complex.I • embed (measure n)
        ⟨fun u => (f u).im, Complex.continuous_im.comp f.continuous⟩ := by
  let fr : C(Slice n, ℝ) := ⟨fun u => (f u).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Slice n, ℝ) := ⟨fun u => (f u).im, Complex.continuous_im.comp f.continuous⟩
  have hf : f = complexify fr + Complex.I • complexify fi := by
    ext u
    apply Complex.ext <;> simp [complexify, fr, fi, Complex.mul_re, Complex.mul_im]
  conv_lhs => rw [hf, map_add, map_smul]
  rfl

/-- Orthogonality to the actual positive vacuum centers both real components. -/
theorem real_components_centered (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℂ))
    (horth : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ)
      (ContinuousMap.toLp 2 (measure n) ℂ f) = 0) :
    (∫ u, ground n β hβ u * (f u).re ∂measure n) = 0 ∧
    (∫ u, ground n β hβ u * (f u).im ∂measure n) = 0 := by
  rw [complex_embedding_decomposition, inner_add_right, inner_smul_right] at horth
  change inner ℂ (embed (measure n) (ground n β hβ)) _ +
    Complex.I * inner ℂ (embed (measure n) (ground n β hβ)) _ = 0 at horth
  rw [embed_inner, embed_inner] at horth
  constructor
  · have h := congrArg Complex.re horth
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero,
      Complex.zero_re, ContinuousMap.coe_mk] using h
  · have h := congrArg Complex.im horth
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im, ContinuousMap.coe_mk] using h

/-- Each real component satisfies the genuine real kernel equation. -/
theorem real_component_equations (β ρ : ℝ) (f : C(Slice n, ℂ))
    (heig : ∀ u, (∫ v, (kernelMap n β (u, v) : ℂ) * f v ∂measure n) =
      (ρ : ℂ) * f u) :
    (∀ u, (∫ v, kernelMap n β (u, v) * (f v).re ∂measure n) = ρ * (f u).re) ∧
    (∀ u, (∫ v, kernelMap n β (u, v) * (f v).im ∂measure n) = ρ * (f u).im) := by
  have hi (u : Slice n) : Integrable (fun v => (kernelMap n β (u, v) : ℂ) * f v)
      (measure n) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    fun_prop
  constructor
  · intro u
    have h := congrArg Complex.re (heig u)
    change RCLike.re (∫ v, (kernelMap n β (u, v) : ℂ) * f v ∂measure n) =
      RCLike.re ((ρ : ℂ) * f u) at h
    rw [← integral_re (hi u)] at h
    simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using h
  · intro u
    have h := congrArg Complex.im (heig u)
    change RCLike.im (∫ v, (kernelMap n β (u, v) : ℂ) * f v ∂measure n) =
      RCLike.im ((ρ : ℂ) * f u) at h
    rw [← integral_im (hi u)] at h
    simpa only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using h

/-- A real continuous eigenfunction embeds into the actual normalized transfer equation. -/
theorem real_normalized_eigenfunction (β ρ : ℝ) (f : C(Slice n, ℝ))
    (heig : ∀ u, (∫ v, kernelMap n β (u, v) * f v ∂measure n) = ρ * f u) :
    normalized n β (embed (measure n) f) =
      (ρ / ‖transfer n β‖) • embed (measure n) f := by
  have he := WilsonSlabSpectralRatio.embedded_eigenfunction n β ρ (complexify f) (by
    intro u
    simp only [complexify, ContinuousMap.coe_mk, ← Complex.ofReal_mul, integral_complex_ofReal]
    exact congrArg (fun x : ℝ => (x : ℂ)) (heig u))
  change transfer n β (embed (measure n) f) = ρ • embed (measure n) f at he
  change ‖transfer n β‖⁻¹ • transfer n β (embed (measure n) f) = _
  rw [he, smul_smul]
  congr 1
  ring


/-- The actual covariance premise bounds each nonzero centered real eigenfunction. -/
theorem real_eigenvalue_bound (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (ρ : ℝ) (hρ : 0 < ρ) (f : C(Slice n, ℝ))
    (hf : embed (measure n) f ≠ 0)
    (hmean : (∫ u, ground n β hβ u * f u ∂measure n) = 0)
    (heig : ∀ u, (∫ v, kernelMap n β (u, v) * f v ∂measure n) = ρ * f u) :
    ρ / ‖transfer n β‖ ≤ q := by
  have hl := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have h := real_amplitude_contraction n β hβ q hq hdec f hmean
  rw [real_normalized_eigenfunction n β ρ f heig, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hρ hl)] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hf)).mp h

/-- Compact-kernel smoothing and real-component extraction cover every genuine
complex eigenvector; no real-observable or gauge-sector restriction remains. -/
theorem orthogonal_eigenvalue_bound (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (ρ : ℝ) (hρ : 0 < ρ) (v : Hilbert n) (hv : v ≠ 0)
    (horth : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0)
    (heig : transfer n β v = ρ • v) : ρ / ‖transfer n β‖ ≤ q := by
  obtain ⟨f, hf, _, hfeig⟩ := WilsonSlabSpectralRatio.continuous_eigenfunction
    n β ρ hρ.ne' v heig
  let fr : C(Slice n, ℝ) := ⟨fun u => (f u).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(Slice n, ℝ) := ⟨fun u => (f u).im, Complex.continuous_im.comp f.continuous⟩
  have hc := real_components_centered n β hβ f (by rw [hf]; exact horth)
  have he := real_component_equations n β ρ f hfeig
  by_cases hr : embed (measure n) fr = 0
  · have hi : embed (measure n) fi ≠ 0 := by
      intro hz
      apply hv
      rw [← hf, complex_embedding_decomposition]
      change embed (measure n) fr + Complex.I • embed (measure n) fi = 0
      rw [hr, hz, smul_zero, add_zero]
    exact real_eigenvalue_bound n β hβ q hq hdec ρ hρ fi hi hc.2 he.2
  · exact real_eigenvalue_bound n β hβ q hq hdec ρ hρ fr hr hc.1 he.1

/-- Actual cylinder decay implies a norm bound on the full vacuum-orthogonal
space of the original normalized transfer, with precisely the same rate q. -/
theorem full_orthogonal_contraction (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (v : Hilbert n)
    (hv : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0) :
    ‖normalized n β v‖ ≤ q * ‖v‖ := by
  have hl := (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1
  have h := CompactGroundContraction.norm_contraction (transfer n β)
    (WilsonSlabPositiveOperator.transfer_positive n β hβ) (transfer_compact n β)
    (WilsonVacuumConvergence.vacuum n β hβ) ‖transfer n β‖ q hl hq
    (WilsonVacuumConvergence.vacuum_eigenvector n β hβ)
    (fun ρ w hρ hw ho he => orthogonal_eigenvalue_bound n β hβ q hq hdec ρ hρ w hw ho he) v hv
  calc
    ‖normalized n β v‖ = ‖transfer n β‖⁻¹ * ‖transfer n β v‖ := by
      simp only [normalized, ContinuousLinearMap.smul_apply, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hl]
    _ ≤ ‖transfer n β‖⁻¹ * ((‖transfer n β‖ * q) * ‖v‖) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hl.le)
    _ = q * ‖v‖ := by
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]

/-- The same rate controls all physical-time powers and connected matrix elements. -/
theorem all_step_decay (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (v : Hilbert n)
    (hv : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0) (k : ℕ) :
    ‖iterate (normalized n β) k v‖ ≤ q ^ k * ‖v‖ ∧
      ∀ u, ‖inner ℂ u (iterate (normalized n β) k v)‖ ≤ q ^ k * ‖u‖ * ‖v‖ := by
  have hc : ∀ w, inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) w = 0 →
      ‖iterate (normalized n β) 1 w‖ ≤ q * ‖w‖ := by
    simpa only [iterate_succ, iterate_zero] using full_orthogonal_contraction n β hβ q hq hdec
  constructor
  · simpa only [Nat.mul_one] using TransferPhysicalRatio.iterate_blocks_norm
      (normalized n β) (normalized_symmetric n β) (WilsonVacuumConvergence.vacuum n β hβ)
      (WilsonVacuumConvergence.vacuum_fixed n β hβ) q hq 1 hc v hv k
  · intro u
    simpa only [Nat.mul_one] using TransferPhysicalRatio.block_pairing_bound
      (normalized n β) (normalized_symmetric n β) (WilsonVacuumConvergence.vacuum n β hβ)
      (WilsonVacuumConvergence.vacuum_fixed n β hβ) q hq 1 hc u v hv k


/-- The full norm contraction bounds all real eigenvalues in the orthogonal space. -/
theorem eigenvalue_ratio (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (ρ : ℝ) (v : Hilbert n) (hv : v ≠ 0)
    (horth : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0)
    (heig : transfer n β v = ρ • v) : |ρ / ‖transfer n β‖| ≤ q := by
  have h := full_orthogonal_contraction n β hβ q hq hdec v horth
  have he : normalized n β v = (ρ / ‖transfer n β‖) • v := by
    change ‖transfer n β‖⁻¹ • transfer n β v = _
    rw [heig, smul_smul]
    congr 1
    ring
  rw [he, norm_smul, Real.norm_eq_abs] at h
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hv)).mp h

/-- The actual compact full-transfer spectrum, away from its unique top,
inherits the cylinder rate. This is the physical operator, not the sampler. -/
theorem spectral_ratio (β : ℝ) (hβ : 0 ≤ β) (q : ℝ) (hq : 0 ≤ q)
    (hdec : CylinderDecay n β q) (ρ : ℝ)
    (hspec : ρ ∈ spectrum ℝ (transfer n β)) (hρ : ρ ≠ ‖transfer n β‖) :
    |ρ / ‖transfer n β‖| ≤ q := by
  by_cases hz : ρ = 0
  · simpa only [hz, zero_div, abs_zero] using hq
  obtain ⟨v, hv, heig⟩ := PositiveKernelGroundState.eigenvector_of_nonzero_spectral
    (transfer n β) (transfer_selfAdjoint n β) (transfer_compact n β) ρ hspec hz
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have horth : inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0 := by
    have hs := (transfer_selfAdjoint n β).isSymmetric
      (WilsonVacuumConvergence.vacuum n β hβ) v
    change inner ℂ (transfer n β (WilsonVacuumConvergence.vacuum n β hβ)) v =
      inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) (transfer n β v) at hs
    rw [WilsonVacuumConvergence.vacuum_eigenvector, heig] at hs
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_real_left, inner_smul_real_right, smul_eq_mul] at hs
    have hd : ((‖transfer n β‖ : ℂ) - (ρ : ℂ)) *
        inner ℂ (WilsonVacuumConvergence.vacuum n β hβ) v = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.mpr hs
    have hn : (‖transfer n β‖ : ℂ) - (ρ : ℂ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hρ.symm
    exact (mul_eq_zero.mp hd).resolve_left hn
  exact eigenvalue_ratio n β hβ q hq hdec ρ v hv0 horth heig

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderSpectralBridge
