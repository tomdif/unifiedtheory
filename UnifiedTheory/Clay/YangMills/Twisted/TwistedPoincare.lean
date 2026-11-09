/- The neutral gap as a Poincaré inequality. With `Ω = η`, the ground-state identity writes the
transfer form of `g η` through the Dirichlet form of the reversible chain with stationary law `η²`.
A Poincaré inequality for gauge-invariant neutral observables bounds the neutral eigenvalues. The
inequality itself is not proved. It is the open content of the gap half of Target A. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFluxSector
import UnifiedTheory.Clay.YangMills.GibbsFullSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator TwistedTransfer TwistedFluxSector

variable (n : ℕ) [NeZero n] (β : ℝ)

local notation "μ'" => WilsonSlabOperator.measure n
local notation "T" => TwistedTransfer.transfer n β

/-- The Dirichlet form of the chain, in unnormalized form. -/
def dirichlet (η g : C(Slice n, ℝ)) : ℝ :=
  ∫ u, η u * (∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ') ∂μ'

/-- **The ground-state identity.** -/
theorem ground_state_identity (η g : C(Slice n, ℝ))
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) :
    dirichlet n β η g = 2 * ‖T‖ * (∫ u, g u ^ 2 * η u ^ 2 ∂μ') -
      2 * ∫ u, (g u * η u) * (∫ v, twistedKernel n β (u, v) * (g v * η v) ∂μ') ∂μ' := by
  set lam := ‖T‖ with hlam
  let f₁ : C(Slice n, ℝ) := g * η
  let f₂ : C(Slice n, ℝ) := g * g * η
  have hf₁ (u : Slice n) : f₁ u = g u * η u := rfl
  have hf₂ (u : Slice n) : f₂ u = g u * g u * η u := rfl
  have hin (u : Slice n) : (∫ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 ∂μ') =
      g u ^ 2 * (lam * η u) - 2 * g u * sm n β f₁ u + sm n β f₂ u := by
    have hK : Continuous fun v => twistedKernel n β (u, v) :=
      (twistedKernel n β).continuous.comp (continuous_const.prodMk continuous_id)
    rw [sm_apply, sm_apply, ← heig u]
    have e : ∀ v, twistedKernel n β (u, v) * η v * (g u - g v) ^ 2 =
        g u ^ 2 * (twistedKernel n β (u, v) * η v) -
          2 * g u * (twistedKernel n β (u, v) * f₁ v) + twistedKernel n β (u, v) * f₂ v := by
      intro v
      rw [hf₁, hf₂]
      ring
    simp only [e]
    exact integral_three n _ _ _ (hK.mul η.continuous) (hK.mul f₁.continuous)
      (hK.mul f₂.continuous) _ _
  unfold dirichlet
  simp only [hin]
  have hpt (u : Slice n) : η u * (g u ^ 2 * (lam * η u) - 2 * g u * sm n β f₁ u + sm n β f₂ u) =
      lam * (g u ^ 2 * η u ^ 2) - 2 * (f₁ u * sm n β f₁ u) + sm n β f₂ u * η u := by
    rw [hf₁]
    ring
  simp only [hpt]
  have hthree := integral_three n (fun u => g u ^ 2 * η u ^ 2) (fun u => f₁ u * sm n β f₁ u)
    (fun u => sm n β f₂ u * η u) ((g.continuous.pow 2).mul (η.continuous.pow 2))
    (f₁.continuous.mul (sm n β f₁).continuous) ((sm n β f₂).continuous.mul η.continuous) lam 2
  rw [hthree]
  have h2 : ∫ u, f₁ u * sm n β f₁ u ∂μ' =
      ∫ u, (g u * η u) * (∫ v, twistedKernel n β (u, v) * (g v * η v) ∂μ') ∂μ' := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [sm_apply]
    rfl
  have h3 : ∫ u, sm n β f₂ u * η u ∂μ' = lam * ∫ u, g u ^ 2 * η u ^ 2 ∂μ' := by
    have hp := TwistedCollatz.pairing_symm n β f₂ η
    simp only [heig, ← sm_apply] at hp
    rw [hp, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    rw [hf₂]
    ring
  rw [h2, h3]
  ring

/-- Gauge-invariant, flip-invariant observables of vanishing mean under `η²`. -/
structure NeutralObservable (η g : C(Slice n, ℝ)) : Prop where
  gauge : ∀ (h : SliceGauge n Q) u, g (gaugeSlice h u) = g u
  flip : ∀ i c u, g (TwistedTransfer.flip n i c u) = g u
  mean : ∫ u, g u * η u ^ 2 ∂μ' = 0

/-- The Poincaré inequality with constant `C` for the neutral sector. Open. -/
def NeutralPoincare (η : C(Slice n, ℝ)) (C : ℝ) : Prop :=
  ∀ g, NeutralObservable n η g →
    2 * ‖T‖ * ∫ u, g u ^ 2 * η u ^ 2 ∂μ' ≤ C * dirichlet n β η g

/-- **Poincaré bounds neutral eigenvalues.** A real continuous eigenfunction `f = g η` in the neutral
sector has eigenvalue at most `(1 - 1/C) ‖T‖`. -/
theorem eigenvalue_of_poincare (η f g : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (C : ℝ) (hC : 0 < C)
    (hP : NeutralPoincare n β η C) (hg : NeutralObservable n η g) (hfg : ∀ u, f u = g u * η u)
    (hne : ∃ u, f u ≠ 0) (lam' : ℝ)
    (hfeig : ∀ u, (∫ v, twistedKernel n β (u, v) * f v ∂μ') = lam' * f u) :
    lam' ≤ (1 - 1 / C) * ‖T‖ := by
  have hid := ground_state_identity n β η g heig
  have hp := hP g hg
  set X := ∫ u, g u ^ 2 * η u ^ 2 ∂μ' with hX
  have hXpos : 0 < X := by
    have hc : Continuous fun u => g u ^ 2 * η u ^ 2 := (g.continuous.pow 2).mul (η.continuous.pow 2)
    have hnn : ∀ u, 0 ≤ g u ^ 2 * η u ^ 2 := fun u => by positivity
    obtain ⟨u₀, hu₀⟩ := hne
    have hpos : 0 < g u₀ ^ 2 * η u₀ ^ 2 := by
      have : (g u₀ * η u₀) ≠ 0 := by rwa [← hfg]
      have h2 := sq_pos_of_ne_zero this
      rwa [mul_pow] at h2
    haveI hmeas : Measure.IsOpenPosMeasure (μ') := by
      change (Measure.pi fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q).IsOpenPosMeasure
      haveI : (RegulatedGauge.compactHaar Q).IsOpenPosMeasure := GibbsFullSupport.compactHaar_openPos Q
      infer_instance
    exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      hnn hpos.ne'
  have hQ : ∫ u, (g u * η u) * (∫ v, twistedKernel n β (u, v) * (g v * η v) ∂μ') ∂μ' = lam' * X := by
    rw [hX, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    dsimp only
    have h1 := hfeig u
    simp only [hfg] at h1
    rw [h1]
    ring
  rw [hQ] at hid
  have h1 : 2 * ‖T‖ * X ≤ C * (2 * ‖T‖ * X - 2 * (lam' * X)) := by
    rw [hid] at hp
    exact hp
  have h2 : lam' * X ≤ (1 - 1 / C) * ‖T‖ * X := by
    have e : (1 - 1 / C) * ‖T‖ * X = ‖T‖ * X - (‖T‖ * X) / C := by
      field_simp
    rw [e]
    have h3 : (‖T‖ * X) / C ≤ ‖T‖ * X - lam' * X := by
      rw [div_le_iff₀ hC]
      nlinarith only [h1]
    linarith only [h3]
  exact le_of_mul_le_mul_right h2 hXpos

/-! ### From Poincaré to the norm bound on the neutral complement -/

open TwistedVacuum
open WilsonPositiveGroundState (complexify)
open scoped InnerProductSpace

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive compact operator on an invariant closed subspace is bounded by the top eigenvalue
occurring in that subspace. -/
theorem invariant_bound (A : H →L[ℂ] H) (hpos : A.IsPositive) (hc : IsCompactOperator A)
    (M : Submodule ℂ H) (hcl : IsClosed (M : Set H)) (hinv : ∀ f ∈ M, A f ∈ M) (B : ℝ) (hB : 0 ≤ B)
    (heig : ∀ w ∈ M, w ≠ 0 → ∀ μ : ℝ, 0 < μ → A w = μ • w → μ ≤ B) :
    ∀ f ∈ M, ‖A f‖ ≤ B * ‖f‖ := by
  haveI : CompleteSpace M := hcl.completeSpace_coe
  let R : M →L[ℂ] M := (A.comp M.subtypeL).codRestrict M fun x => hinv x x.2
  have hRc : IsCompactOperator R :=
    (hc.comp_clm M.subtypeL).codRestrict (fun x => hinv x x.2) hcl
  have hRpos : R.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · change inner ℂ (A (x : H)) (y : H) = inner ℂ (x : H) (A (y : H))
      exact hpos.isSymmetric _ _
    · exact hpos.2 (x : H)
  have hbound : ‖R‖ ≤ B := by
    by_cases hR0 : R = 0
    · have h0 : ‖R‖ = 0 := by
        rw [hR0]
        exact ContinuousLinearMap.opNorm_zero
      rw [h0]
      exact hB
    obtain ⟨hRp, v, hv, hRv⟩ := PositiveKernelGroundState.positive_compact_top_eigenvector R hRpos hRc hR0
    refine heig (v : H) v.2 ?_ ‖R‖ hRp ?_
    · intro h0
      have : ‖v‖ = 0 := by
        change ‖(v : H)‖ = 0
        rw [h0, norm_zero]
      rw [this] at hv
      exact zero_ne_one hv
    · exact congrArg Subtype.val hRv
  intro f hf
  have h1 := R.le_opNorm ⟨f, hf⟩
  exact h1.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg f))

end Abstract

/-- The neutral complement of a vector, as a submodule. -/
def neutralComplement (Ω : Hilbert n) : Submodule ℂ (Hilbert n) where
  carrier := {f | Neutral n f ∧ inner ℂ Ω f = 0}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun i c => ?_, by rw [inner_add_right, ha', hb', add_zero]⟩
    rw [map_add, ha i c, hb i c]
  zero_mem' := by
    refine ⟨fun i c => map_zero _, inner_zero_right _⟩
  smul_mem' := by
    rintro k a ⟨ha, ha'⟩
    refine ⟨fun i c => ?_, by rw [inner_smul_right, ha', mul_zero]⟩
    rw [map_smulₛₗ, ha i c]
    rfl

theorem neutralComplement_closed (Ω : Hilbert n) :
    IsClosed (neutralComplement n Ω : Set (Hilbert n)) := by
  have h1 : IsClosed {f : Hilbert n | Neutral n f} := by
    have : {f : Hilbert n | Neutral n f} = ⋂ i, ⋂ c, {f | flipOp n i c f = f} := by
      ext f
      simp [Neutral]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun c =>
      isClosed_eq (flipOp n i c).continuous continuous_id
  have h2 : IsClosed {f : Hilbert n | inner ℂ Ω f = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact h1.inter h2

variable (hβ : 0 ≤ β)

include hβ

/-- **The gap half of the target, from the Poincaré inequality.** If the neutral Poincaré inequality
holds with constant `C ≥ 1`, then `T` contracts the neutral complement of the vacuum by `1 - 1/C`. -/
theorem gap_of_poincare (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (C : ℝ) (hC : 1 ≤ C)
    (hP : NeutralPoincare n β η C) :
    ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 →
      ‖T f‖ ≤ (1 - 1 / C) * ‖T‖ * ‖f‖ := by
  have hCpos : 0 < C := by linarith only [hC]
  obtain ⟨hlam, -⟩ := top_eigenvector n β hβ
  set Ω := ContinuousMap.toLp 2 (μ') ℂ (complexify η) with hΩ
  have hTΩ : T Ω = ‖T‖ • Ω := by
    rw [hΩ, transfer_embed]
    have hs : sm n β η = ‖T‖ • η := by
      ext u
      rw [sm_apply, heig]
      rfl
    rw [hs, WilsonPositiveGroundState.complexify_smul, map_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  have hsym : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y) := (transfer_positive n β hβ).isSymmetric
  set M := neutralComplement n Ω with hM
  have hTM : ∀ f : Hilbert n, f ∈ M → T f ∈ M := by
    rintro f ⟨hf, hf'⟩
    refine ⟨fun i c => ?_, ?_⟩
    · rw [← transfer_flipOp, hf i c]
    · rw [← hsym, hTΩ, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, hf', mul_zero]
  have hB0 : 0 ≤ (1 - 1 / C) * ‖T‖ := by
    have : 0 ≤ 1 - 1 / C := by
      have := (div_le_one hCpos).mpr hC
      linarith only [this]
    positivity
  have hmain : ∀ f ∈ M, ‖T f‖ ≤ (1 - 1 / C) * ‖T‖ * ‖f‖ := by
    refine invariant_bound _ (transfer_positive n β hβ) (TwistedTransfer.transfer_compact n β) M
      (neutralComplement_closed n Ω) hTM _ hB0 ?_
    rintro w ⟨hneut, horth⟩ hwne lam' hlam' hTw
    obtain ⟨f, hfw, hfeig⟩ := continuous_eigenfunction n β lam' hlam'.ne' w hTw
    have hμC : ((lam' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam'.ne'
    -- Pointwise invariances of the eigenfunction
    have hfgauge (h : SliceGauge n Q) (u : Slice n) : f (gaugeSlice h u) = f u := by
      have h1 := hfeig (gaugeSlice h u)
      have h2 := hfeig u
      simp only [TwistedTreeGauge.twistedKernel_gauge_left] at h1
      rw [h2] at h1
      exact (mul_left_cancel₀ hμC h1).symm
    have hflipae (i : Fin 3) (c : ZMod n) : (f ∘ TwistedTransfer.flip n i c) =ᵐ[μ'] f := by
      have h1 : (flipOp n i c w : Slice n → ℂ) =ᵐ[μ'] ((w : Hilbert n) ∘ TwistedTransfer.flip n i c) :=
        Lp.coeFn_compMeasurePreserving _ (flip_measurePreserving n i c)
      have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ') f
      rw [hfw] at h2
      have h3 := (flip_measurePreserving n i c).quasiMeasurePreserving.ae_eq_comp h2
      rw [hneut i c] at h1
      exact h3.symm.trans (h1.symm.trans h2)
    have hfflip (i : Fin 3) (c : ZMod n) (u : Slice n) : f (TwistedTransfer.flip n i c u) = f u := by
      have hmp' : MeasurePreserving (flipEquiv n i c) (μ') (μ') := flip_measurePreserving n i c
      have h1 := hfeig (TwistedTransfer.flip n i c u)
      have h2 := hmp'.integral_comp'
        (fun v => (twistedKernel n β (TwistedTransfer.flip n i c u, v) : ℂ) * f v)
      have h3 : (∫ v, (twistedKernel n β (TwistedTransfer.flip n i c u, v) : ℂ) * f v ∂μ') =
          ∫ v, (twistedKernel n β (u, v) : ℂ) * f v ∂μ' := by
        rw [← h2]
        refine integral_congr_ae ((hflipae i c).mono fun v hv => ?_)
        change (twistedKernel n β (TwistedTransfer.flip n i c u, TwistedTransfer.flip n i c v) : ℂ) *
          f (TwistedTransfer.flip n i c v) = _
        rw [twistedKernel_flip]
        have : f (TwistedTransfer.flip n i c v) = f v := hv
        rw [this]
      rw [h3, hfeig u] at h1
      exact (mul_left_cancel₀ hμC h1).symm
    have hηgauge (h : SliceGauge n Q) (u : Slice n) : η (gaugeSlice h u) = η u := by
      have h1 := heig (gaugeSlice h u)
      have h2 := heig u
      simp only [TwistedTreeGauge.twistedKernel_gauge_left] at h1
      rw [h2] at h1
      exact (mul_left_cancel₀ hlam.ne' h1).symm
    have hηflip := top_flip n β η hη heig hlam
    -- The mean condition in complex form
    have hmeanC : ∫ u, (η u : ℂ) * f u ∂μ' = 0 := by
      have h := horth
      rw [hΩ, ← hfw, MeasureTheory.ContinuousMap.inner_toLp] at h
      rw [← h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [complexify, mul_comm]
    -- Pick a nonzero real or imaginary part
    have hfnz : ∃ u, f u ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hwne
      rw [← hfw]
      have : f = 0 := by
        ext u
        simp [hall u]
      rw [this, map_zero]
    obtain ⟨u₀, hu₀⟩ := hfnz
    have hcf (u : Slice n) : Integrable (fun v => (twistedKernel n β (u, v) : ℂ) * f v) μ' :=
      (Continuous.mul (Complex.continuous_ofReal.comp ((twistedKernel n β).continuous.comp
        (continuous_const.prodMk continuous_id))) f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hcη : Integrable (fun v => (η v : ℂ) * f v) μ' :=
      (Continuous.mul (Complex.continuous_ofReal.comp η.continuous)
        f.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    -- Every real functional of the eigenfunction is again an eigenfunction.
    have hmk (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ∀ (r : ℝ) (z : ℂ), ℓ ((r : ℂ) * z) = r * ℓ z)
        (hne : ℓ (f u₀) ≠ 0) : lam' ≤ (1 - 1 / C) * ‖T‖ := by
      let φ : C(Slice n, ℝ) := ⟨fun u => ℓ (f u), ℓ.continuous.comp f.continuous⟩
      have hφv (u : Slice n) : φ u = ℓ (f u) := rfl
      have hφeig (u : Slice n) : (∫ v, twistedKernel n β (u, v) * φ v ∂μ') = lam' * φ u := by
        have h1 := congrArg ℓ (hfeig u)
        rw [hℓ, ← ContinuousLinearMap.integral_comp_comm ℓ (hcf u)] at h1
        rw [hφv, ← h1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hφv, hℓ]
      have hφmean : ∫ u, η u * φ u ∂μ' = 0 := by
        have h1 := congrArg ℓ hmeanC
        rw [map_zero, ← ContinuousLinearMap.integral_comp_comm ℓ hcη] at h1
        rw [← h1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        rw [hφv, hℓ]
      let g : C(Slice n, ℝ) := ⟨fun u => φ u / η u,
        φ.continuous.div η.continuous fun u => (hη u).ne'⟩
      have hgv (u : Slice n) : g u = φ u / η u := rfl
      have hφg (u : Slice n) : φ u = g u * η u := by
        rw [hgv]
        field_simp [(hη u).ne']
      have hobs : NeutralObservable n η g :=
        { gauge := fun h u => by
            rw [hgv, hgv, hηgauge]
            change ℓ (f (gaugeSlice h u)) / _ = ℓ (f u) / _
            rw [hfgauge]
          flip := fun i c u => by
            rw [hgv, hgv, hηflip]
            change ℓ (f (TwistedTransfer.flip n i c u)) / _ = ℓ (f u) / _
            rw [hfflip]
          mean := by
            rw [← hφmean]
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            dsimp only
            rw [hφg u]
            ring }
      exact eigenvalue_of_poincare n β η φ g hη heig C hCpos hP hobs hφg ⟨u₀, hne⟩ lam' hφeig
    by_cases hre : (f u₀).re ≠ 0
    · exact hmk Complex.reCLM (fun r z => by simp) hre
    · have him : (f u₀).im ≠ 0 := by
        intro h
        apply hu₀
        push_neg at hre
        exact Complex.ext hre h
      exact hmk Complex.imCLM (fun r z => by simp) him
  exact fun f hf hf' => hmain f ⟨hf, hf'⟩

/-- **The target form.** A Poincaré constant `C = n / c` gives the contraction `exp (-c / n)` that the
gap half of `TargetAGap` asks for. -/
theorem exp_of_poincare (η : C(Slice n, ℝ)) (hη : ∀ u, 0 < η u)
    (heig : ∀ u, (∫ v, twistedKernel n β (u, v) * η v ∂μ') = ‖T‖ * η u) (c : ℝ) (hc : 0 < c)
    (hcn : c ≤ n) (hP : NeutralPoincare n β η (n / c)) :
    ∀ f, Neutral n f → inner ℂ (ContinuousMap.toLp 2 (μ') ℂ (complexify η)) f = 0 →
      ‖T f‖ ≤ Real.exp (-c / n) * ‖T‖ * ‖f‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hC : 1 ≤ (n : ℝ) / c := (one_le_div hc).mpr hcn
  intro f hf hf'
  have h := gap_of_poincare n β hβ η hη heig (n / c) hC hP f hf hf'
  have e : 1 - 1 / ((n : ℝ) / c) = -c / n + 1 := by
    field_simp
    ring
  have hexp : -c / n + 1 ≤ Real.exp (-c / n) := Real.add_one_le_exp _
  rw [e] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) (norm_nonneg _)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedPoincare
