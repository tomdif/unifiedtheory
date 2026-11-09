/- The transfer operator of the spatially twisted SU(2) law at spatial size `n`, and
its center-flip symmetries. It is compact, self-adjoint, positive and nonzero, with an
attained top eigenvector. The time extent does not enter, so this also serves `T ≠ L`.
`TargetAGap` states the open cutoff-uniform gap. Nothing here proves it. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedFlat
import UnifiedTheory.Clay.YangMills.PositiveKernelGroundState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator TwistedFlat
open WilsonSingleLinkStaples (character character_continuous)
open scoped InnerProductSpace

variable (n : ℕ) [NeZero n]

/-- Spatial form of the twist `n₁₂ = 1`: sign `-1` on one stack of (0,1) spatial plaquettes. -/
def spatialSign (x : SpatialVertex n) (p : SpatialPlane) : ℝ := by
  classical
  exact if p.1 = (0, 1) ∧ x 0 = 0 ∧ x 1 = 0 then -1 else 1

/-- The twisted spatial potential. -/
def twistedPotential (u : Slice n) : ℝ :=
  ∑ x : SpatialVertex n, ∑ p : SpatialPlane,
    (2 - spatialSign n x p * (character (spatialHolonomy u x p.1.1 p.1.2)).re)

/-- The part of the twisted potential beyond the untwisted one. -/
def defect (u : Slice n) : ℝ :=
  ∑ x : SpatialVertex n, ∑ p : SpatialPlane,
    (1 - spatialSign n x p) * (character (spatialHolonomy u x p.1.1 p.1.2)).re

theorem twistedPotential_eq (u : Slice n) :
    twistedPotential n u = potential character 2 u + defect n u := by
  unfold twistedPotential potential defect
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

theorem defect_continuous : Continuous (defect n) := by
  have hc := character_continuous
  unfold defect spatialHolonomy
  fun_prop

/-- The multiplier relating the twisted to the untwisted kernel. -/
def weightRatio (β : ℝ) (u : Slice n) : ℝ := Real.exp (-(β / 2) * defect n u)

theorem weightRatio_pos (β : ℝ) (u : Slice n) : 0 < weightRatio n β u := Real.exp_pos _

theorem weightRatio_continuous (β : ℝ) : Continuous (weightRatio n β) :=
  Real.continuous_exp.comp (continuous_const.mul (defect_continuous n))

/-- The twisted kernel, as a continuous kernel. -/
def twistedKernel (β : ℝ) : C(Slice n × Slice n, ℝ) :=
  ⟨fun uv => weightRatio n β uv.1 * kernelMap n β uv * weightRatio n β uv.2,
    (((weightRatio_continuous n β).comp continuous_fst).mul (kernelMap n β).continuous).mul
      ((weightRatio_continuous n β).comp continuous_snd)⟩

theorem twistedKernel_apply (β : ℝ) (u v : Slice n) :
    twistedKernel n β (u, v) = weightRatio n β u * kernelMap n β (u, v) * weightRatio n β v := rfl

/-- The twisted kernel carries the twisted potentials on both slices, and the original
temporal average. This is the literal half-slice form of the twisted slab. -/
theorem twistedKernel_eq (β : ℝ) (u v : Slice n) :
    twistedKernel n β (u, v) = Real.exp (-(β / 2) * twistedPotential n u) *
      (∫ h, Real.exp (-β * temporalAction character 2 u v h) ∂temporalHaar) *
      Real.exp (-(β / 2) * twistedPotential n v) := by
  rw [twistedKernel_apply]
  change _ * kernel character β 2 u v * _ = _
  unfold kernel slabAction weightRatio
  have hf (h : SliceGauge n Q) : Real.exp (-(β * (potential character 2 u / 2 +
      temporalAction character 2 u v h + potential character 2 v / 2))) =
      Real.exp (-(β / 2) * potential character 2 u) *
        (Real.exp (-β * temporalAction character 2 u v h) *
          Real.exp (-(β / 2) * potential character 2 v)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [hf]
  rw [integral_const_mul, integral_mul_const, twistedPotential_eq, twistedPotential_eq]
  have e1 : -(β / 2) * (potential character 2 u + defect n u) =
      -(β / 2) * defect n u + -(β / 2) * potential character 2 u := by ring
  have e2 : -(β / 2) * (potential character 2 v + defect n v) =
      -(β / 2) * defect n v + -(β / 2) * potential character 2 v := by ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

theorem twistedKernel_symm (β : ℝ) (u v : Slice n) :
    twistedKernel n β (u, v) = twistedKernel n β (v, u) := by
  simp only [twistedKernel_apply, kernelMap_symm n β u v]
  ring

theorem twistedKernel_pos (β : ℝ) (uv : Slice n × Slice n) : 0 < twistedKernel n β uv := by
  have hk : 0 < kernelMap n β uv :=
    kernel_positive _ character_continuous β 2 uv.1 uv.2
  exact mul_pos (mul_pos (weightRatio_pos n β _) hk) (weightRatio_pos n β _)

/-- The twisted transfer operator on `L²` of the slice. -/
def transfer (β : ℝ) : Hilbert n →L[ℂ] Hilbert n :=
  CompactKernelOperator.operator (WilsonSlabOperator.measure n) (twistedKernel n β)

theorem transfer_compact (β : ℝ) : IsCompactOperator (transfer n β) :=
  CompactKernelOperator.operator_compact (WilsonSlabOperator.measure n) (twistedKernel n β)

theorem transfer_selfAdjoint (β : ℝ) : IsSelfAdjoint (transfer n β) :=
  CompactKernelOperator.operator_selfAdjoint (WilsonSlabOperator.measure n) (twistedKernel n β)
    (twistedKernel_symm n β)

/-- Positivity is inherited from the actual Hilbert feature, not from pointwise signs. -/
theorem transfer_positive (β : ℝ) (hβ : 0 ≤ β) : (transfer n β).IsPositive := by
  refine CompactKernelOperatorPositivity.operator_positive (WilsonSlabOperator.measure n) (twistedKernel n β)
    (fun u => (weightRatio n β u : ℂ) • WilsonSlabPositiveOperator.feature n β hβ u) ?_ ?_
  · exact (Complex.continuous_ofReal.comp (weightRatio_continuous n β)).smul
      (WilsonSlabPositiveOperator.feature_continuous n β hβ)
  · intro u v
    dsimp only
    rw [inner_smul_left (𝕜 := ℂ) (WilsonSlabPositiveOperator.feature n β hβ u)
      ((weightRatio n β v : ℂ) • WilsonSlabPositiveOperator.feature n β hβ v)
      (weightRatio n β u : ℂ)]
    rw [inner_smul_right (𝕜 := ℂ) (WilsonSlabPositiveOperator.feature n β hβ u)
      (WilsonSlabPositiveOperator.feature n β hβ v) (weightRatio n β v : ℂ)]
    rw [WilsonSlabPositiveOperator.feature_inner, twistedKernel_apply]
    simp only [Complex.conj_ofReal, Complex.ofReal_mul]
    ring

theorem transfer_one_pairing (β : ℝ) :
    inner ℂ (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ)))
      (transfer n β (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ)))) =
      (∫ uv, twistedKernel n β uv ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) : ℝ) := by
  change inner ℂ (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ)))
    (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ
      (CompactKernelOperator.smoothing (WilsonSlabOperator.measure n) (twistedKernel n β)
        (ContinuousMap.toLp 2 (WilsonSlabOperator.measure n) ℂ (1 : C(Slice n, ℂ))))) = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  simp only [ContinuousMap.one_apply, map_one, mul_one]
  simp_rw [CompactKernelOperator.smoothing_continuous_input, ContinuousMap.one_apply, mul_one]
  rw [← integral_complex_ofReal]
  have hi : Integrable (fun uv => (twistedKernel n β uv : ℂ))
      ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) :=
    (Complex.continuous_ofReal.comp (twistedKernel n β).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (integral_prod _ hi).symm

theorem transfer_ne_zero (β : ℝ) : transfer n β ≠ 0 := by
  intro h0
  have hp := transfer_one_pairing n β
  rw [h0] at hp
  simp only [ContinuousLinearMap.zero_apply, inner_zero_right] at hp
  have hi : Integrable (twistedKernel n β) ((WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) :=
    (twistedKernel n β).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpos : 0 < ∫ uv, twistedKernel n β uv ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n) := by
    apply (integral_pos_iff_support_of_nonneg (fun uv => (twistedKernel_pos n β uv).le) hi).mpr
    have hs : Function.support (twistedKernel n β) = Set.univ := by
      ext uv
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (twistedKernel_pos n β uv)
    simp [hs]
  have : (∫ uv, twistedKernel n β uv ∂(WilsonSlabOperator.measure n).prod (WilsonSlabOperator.measure n)) = 0 := by
    exact_mod_cast hp.symm
  linarith

/-- The attained top eigenvector of the twisted operator at finite cutoff. -/
theorem top_eigenvector (β : ℝ) (hβ : 0 ≤ β) :
    0 < ‖transfer n β‖ ∧ ∃ v : Hilbert n, ‖v‖ = 1 ∧ transfer n β v = ‖transfer n β‖ • v :=
  PositiveKernelGroundState.positive_compact_top_eigenvector _ (transfer_positive n β hβ)
    (transfer_compact n β) (transfer_ne_zero n β)

/-! ### Center flips of spatial link slabs -/

/-- Multiply by `-1` all links in direction `i` on the slab `x i = c`. -/
def flip (i : Fin 3) (c : ZMod n) (u : Slice n) : Slice n :=
  fun e => if e.2 = i ∧ e.1 i = c then ω * u e else u e

theorem ω_mul_ω : (ω : Q) * ω = 1 := by
  apply Subtype.ext
  change ((-1 : Quaternion ℝ) * (-1)) = 1
  simp

theorem flip_flip (i : Fin 3) (c : ZMod n) (u : Slice n) : flip n i c (flip n i c u) = u := by
  funext e
  unfold flip
  by_cases h : e.2 = i ∧ e.1 i = c
  · simp only [if_pos h]
    rw [← mul_assoc, ω_mul_ω, one_mul]
  · simp only [if_neg h]

instance haar_left_invariant : (RegulatedGauge.compactHaar Q).IsMulLeftInvariant := by
  unfold RegulatedGauge.compactHaar
  infer_instance

theorem flip_measurePreserving (i : Fin 3) (c : ZMod n) :
    MeasurePreserving (flip n i c) (WilsonSlabOperator.measure n) (WilsonSlabOperator.measure n) := by
  refine measurePreserving_pi (μ := fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar Q)
    (fun _ => RegulatedGauge.compactHaar Q)
    (f := fun e q => if e.2 = i ∧ e.1 i = c then ω * q else q) (fun e => ?_)
  by_cases h : e.2 = i ∧ e.1 i = c
  · simp only [if_pos h]
    exact measurePreserving_mul_left _ (ω : Q)
  · simp only [if_neg h]
    exact MeasurePreserving.id _

theorem inv_ω_mul (a : Q) : (ω * a)⁻¹ = ω * a⁻¹ := by
  have hinv : (ω : Q)⁻¹ = ω := inv_eq_of_mul_eq_one_left ω_mul_ω
  rw [mul_inv_rev, hinv]
  exact ((ω_commute a⁻¹).eq).symm

theorem coe_ω_mul (a : Q) : ((ω * a : Q) : Quaternion ℝ) = -(a : Quaternion ℝ) := by
  change (-1 : Quaternion ℝ) * (a : Quaternion ℝ) = _
  simp

theorem coe_mul (a b : Q) : ((a * b : Q) : Quaternion ℝ) = (a : Quaternion ℝ) * (b : Quaternion ℝ) :=
  rfl

/-- Sign bookkeeping: `s` is the identity or `ω`, so it is central and self-inverse. -/
theorem sign_cancel (s t : Q) (hs : s = 1 ∨ s = ω) (ht : t = 1 ∨ t = ω) (a b c d : Q) :
    (s * a) * (t * b) * (s * c)⁻¹ * (t * d)⁻¹ = a * b * c⁻¹ * d⁻¹ := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp only [one_mul, inv_ω_mul] <;> apply Subtype.ext <;>
    simp only [coe_mul, ω_coe, neg_mul, mul_neg, neg_neg, one_mul]

theorem flip_coord (i : Fin 3) (c : ZMod n) (u : Slice n) (e : SpatialVertex n × Fin 3) :
    ∃ s : Q, (s = 1 ∨ s = ω) ∧ s = (if e.2 = i ∧ e.1 i = c then ω else 1) ∧
      flip n i c u e = s * u e := by
  refine ⟨_, ?_, rfl, ?_⟩
  · split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · unfold flip
    split_ifs <;> simp

theorem spatialStep_other (x : SpatialVertex n) (j k : Fin 3) (h : k ≠ j) :
    spatialStep n x j k = x k := by
  simp [spatialStep, h]

/-- Flips preserve every spatial holonomy with distinct directions. -/
theorem flip_holonomy (i : Fin 3) (c : ZMod n) (u : Slice n) (x : SpatialVertex n) (j k : Fin 3)
    (hjk : j ≠ k) :
    spatialHolonomy (flip n i c u) x j k = spatialHolonomy u x j k := by
  obtain ⟨s₁, hs₁, es₁, f₁⟩ := flip_coord n i c u (x, j)
  obtain ⟨s₂, hs₂, es₂, f₂⟩ := flip_coord n i c u (spatialStep n x j, k)
  obtain ⟨s₃, _, es₃, f₃⟩ := flip_coord n i c u (spatialStep n x k, j)
  obtain ⟨s₄, _, es₄, f₄⟩ := flip_coord n i c u (x, k)
  have h13 : s₃ = s₁ := by
    rw [es₃, es₁]
    by_cases hj : j = i
    · subst hj
      simp only [spatialStep_other n x k j hjk]
    · simp [hj]
  have h24 : s₄ = s₂ := by
    rw [es₄, es₂]
    by_cases hk : k = i
    · subst hk
      simp only [spatialStep_other n x j k hjk.symm]
    · simp [hk]
  unfold spatialHolonomy
  rw [f₁, f₂, f₃, f₄, h13, h24]
  exact sign_cancel _ _ hs₁ hs₂ _ _ _ _

theorem defect_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
    defect n (flip n i c u) = defect n u := by
  unfold defect
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  rw [flip_holonomy n i c u x p.1.1 p.1.2 (ne_of_lt p.2)]

theorem potential_flip (i : Fin 3) (c : ZMod n) (u : Slice n) :
    potential character 2 (flip n i c u) = potential character 2 u := by
  unfold potential
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  rw [flip_holonomy n i c u x p.1.1 p.1.2 (ne_of_lt p.2)]

/-- The temporal action is unchanged when both slices are flipped. -/
theorem temporalAction_flip (i : Fin 3) (c : ZMod n) (u v : Slice n) (h : SliceGauge n Q) :
    temporalAction character 2 (flip n i c u) (flip n i c v) h =
      temporalAction character 2 u v h := by
  unfold temporalAction temporalHolonomy
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨s, hs, es, fu⟩ := flip_coord n i c u (x, j)
  obtain ⟨t, _, et, fv⟩ := flip_coord n i c v (x, j)
  have hst : t = s := by rw [et, es]
  rw [fu, fv, hst]
  congr 3
  rcases hs with rfl | rfl
  · simp
  · rw [inv_ω_mul]
    apply Subtype.ext
    simp only [coe_mul, ω_coe, neg_mul, mul_neg, neg_neg, one_mul]

theorem kernelMap_flip (β : ℝ) (i : Fin 3) (c : ZMod n) (u v : Slice n) :
    kernelMap n β (flip n i c u, flip n i c v) = kernelMap n β (u, v) := by
  change kernel character β 2 _ _ = kernel character β 2 _ _
  unfold kernel slabAction
  simp only [potential_flip, temporalAction_flip]

theorem twistedKernel_flip (β : ℝ) (i : Fin 3) (c : ZMod n) (u v : Slice n) :
    twistedKernel n β (flip n i c u, flip n i c v) = twistedKernel n β (u, v) := by
  simp only [twistedKernel_apply, kernelMap_flip, weightRatio, defect_flip]

/-- The flip as a measurable equivalence. -/
def flipEquiv (i : Fin 3) (c : ZMod n) : Slice n ≃ᵐ Slice n where
  toFun := flip n i c
  invFun := flip n i c
  left_inv := flip_flip n i c
  right_inv := flip_flip n i c
  measurable_toFun := (flip_measurePreserving n i c).measurable
  measurable_invFun := (flip_measurePreserving n i c).measurable

/-- The isometry of `L²` induced by a flip. -/
def flipOp (i : Fin 3) (c : ZMod n) : Hilbert n →ₗᵢ[ℂ] Hilbert n :=
  Lp.compMeasurePreservingₗᵢ ℂ (flip n i c) (flip_measurePreserving n i c)

/-- Flips commute with the twisted transfer operator. -/
theorem transfer_flipOp (β : ℝ) (i : Fin 3) (c : ZMod n) (f : Hilbert n) :
    transfer n β (flipOp n i c f) = flipOp n i c (transfer n β f) := by
  have hmp := flip_measurePreserving n i c
  apply Lp.ext
  have hl := CompactKernelOperator.operator_integral (WilsonSlabOperator.measure n)
    (twistedKernel n β) (flipOp n i c f)
  have hf : (flipOp n i c f : Slice n → ℂ) =ᵐ[WilsonSlabOperator.measure n] (f ∘ flip n i c) :=
    Lp.coeFn_compMeasurePreserving f hmp
  have hr : (flipOp n i c (transfer n β f) : Slice n → ℂ) =ᵐ[WilsonSlabOperator.measure n]
      ((transfer n β f : Hilbert n) ∘ flip n i c) :=
    Lp.coeFn_compMeasurePreserving _ hmp
  have ht := hmp.quasiMeasurePreserving.ae_eq_comp
    (CompactKernelOperator.operator_integral (WilsonSlabOperator.measure n) (twistedKernel n β) f)
  refine hl.trans (Filter.EventuallyEq.trans ?_ (hr.trans ht).symm)
  refine Filter.Eventually.of_forall fun u => ?_
  simp only [Function.comp]
  have hc : (∫ v, (twistedKernel n β (u, v) : ℂ) * (flipOp n i c f) v ∂WilsonSlabOperator.measure n) =
      ∫ v, (twistedKernel n β (u, v) : ℂ) * f (flip n i c v) ∂WilsonSlabOperator.measure n :=
    integral_congr_ae (hf.mono fun v hv => by dsimp only; rw [hv]; rfl)
  rw [hc]
  have hmp' : MeasurePreserving (flipEquiv n i c) (WilsonSlabOperator.measure n)
      (WilsonSlabOperator.measure n) := hmp
  have hsub := hmp'.integral_comp'
    (fun v => (twistedKernel n β (flip n i c u, v) : ℂ) * f v)
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  change (twistedKernel n β (u, v) : ℂ) * f (flip n i c v) =
    (twistedKernel n β (flip n i c u, flip n i c v) : ℂ) * f (flip n i c v)
  rw [twistedKernel_flip]

/-! ### The open cutoff-uniform gap -/

/-- A vector invariant under every slab flip. -/
def Neutral (f : Hilbert n) : Prop := ∀ i c, flipOp n i c f = f

/-- The neutral spectral window at one cutoff: a neutral top eigenvector, a contraction by
`ρ₁` on its neutral complement, and a neutral complement vector shrinking by at most `ρ₂`. -/
def NeutralWindow (β ρ₁ ρ₂ : ℝ) : Prop :=
  ∃ Ω : Hilbert n, ‖Ω‖ = 1 ∧ transfer n β Ω = ‖transfer n β‖ • Ω ∧ Neutral n Ω ∧
    (∀ f, Neutral n f → inner ℂ Ω f = 0 → ‖transfer n β f‖ ≤ ρ₁ * ‖transfer n β‖ * ‖f‖) ∧
    ∃ f, Neutral n f ∧ inner ℂ Ω f = 0 ∧ f ≠ 0 ∧ ρ₂ * ‖transfer n β‖ * ‖f‖ ≤ ‖transfer n β f‖

/-- **Open.** The gap half of Target A: for every coupling above a logarithmic trajectory of
slope `b`, the neutral gap in units of `1/L` stays between positive constants. Here
`L = n a`, so a ratio `exp (-c / n)` is a physical energy `c / L`. The asymptotic-freedom
slope in this normalization is `11 / (6 π²)`; slopes above it reach only shrinking volume. -/
def TargetAGap (b : ℝ) : Prop :=
  ∃ β₀ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ (n : ℕ) [NeZero n], 2 ≤ n →
    ∀ β, b * Real.log n + β₀ ≤ β →
      NeutralWindow n β (Real.exp (-c / n)) (Real.exp (-C / n))

/-- The physical reading of the window: a ratio `exp (-c / n)` at spacing `L / n` is the
energy `c / L`, with no dependence on `n`. -/
theorem physical_energy (c L : ℝ) (hL : 0 < L) (m : ℕ) (hm : 0 < m) :
    -Real.log (Real.exp (-c / m)) / (L / m) = c / L := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Real.log_exp]
  field_simp

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer
