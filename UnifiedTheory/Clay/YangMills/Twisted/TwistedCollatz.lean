/- Collatz-Wielandt bounds for the actual twisted transfer operator: for any positive continuous
trial function, the top eigenvalue lies between the extremes of `Tψ / ψ`. Finite-cutoff, with no
statement about the gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedCollatz
noncomputable section
open MeasureTheory WilsonSlabOperator TwistedTransfer TwistedVacuum

variable (n : ℕ) [NeZero n]

local notation "μ'" => WilsonSlabOperator.measure n

/-- The kernel pairing is symmetric in the two test functions. -/
theorem pairing_symm (β : ℝ) (f g : C(Slice n, ℝ)) :
    ∫ u, (∫ v, twistedKernel n β (u, v) * f v ∂μ') * g u ∂μ' =
      ∫ u, f u * (∫ v, twistedKernel n β (u, v) * g v ∂μ') ∂μ' := by
  have hc : Continuous fun p : Slice n × Slice n => twistedKernel n β p * f p.2 * g p.1 :=
    ((twistedKernel n β).continuous.mul (f.continuous.comp continuous_snd)).mul
      (g.continuous.comp continuous_fst)
  have hi : Integrable (fun p : Slice n × Slice n => twistedKernel n β p * f p.2 * g p.1)
      ((μ').prod (μ')) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ u, (∫ v, twistedKernel n β (u, v) * f v ∂μ') * g u ∂μ'
      = ∫ u, ∫ v, twistedKernel n β (u, v) * f v * g u ∂μ' ∂μ' := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        exact (integral_mul_const _ _).symm
    _ = ∫ v, ∫ u, twistedKernel n β (u, v) * f v * g u ∂μ' ∂μ' :=
        integral_integral_swap (f := fun u v => twistedKernel n β (u, v) * f v * g u) hi
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
        dsimp only
        have : ∀ u, twistedKernel n β (u, v) * f v * g u =
            f v * (twistedKernel n β (v, u) * g u) := fun u => by
          rw [twistedKernel_symm]
          ring
        simp only [this]
        exact integral_const_mul _ _

/-- **Collatz-Wielandt.** If `m ψ ≤ Tψ ≤ M ψ` pointwise for a positive continuous `ψ`, then
`m ≤ ‖T‖ ≤ M`. -/
theorem collatz_wielandt (β : ℝ) (hβ : 0 ≤ β) (ψ : C(Slice n, ℝ)) (hψ : ∀ u, 0 < ψ u) (m M : ℝ)
    (hm : ∀ u, m * ψ u ≤ ∫ v, twistedKernel n β (u, v) * ψ v ∂μ')
    (hM : ∀ u, (∫ v, twistedKernel n β (u, v) * ψ v ∂μ') ≤ M * ψ u) :
    m ≤ ‖TwistedTransfer.transfer n β‖ ∧ ‖TwistedTransfer.transfer n β‖ ≤ M := by
  obtain ⟨η, hη, -, heig⟩ := exists_positive_top n β hβ
  set lam := ‖TwistedTransfer.transfer n β‖
  have hpair := pairing_symm n β η ψ
  simp only [heig] at hpair
  have hprodc : Continuous fun u => η u * ψ u := η.continuous.mul ψ.continuous
  have hprodi : Integrable (fun u => η u * ψ u) μ' :=
    hprodc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos : 0 < ∫ u, η u * ψ u ∂μ' := by
    apply (integral_pos_iff_support_of_nonneg (fun u => (mul_pos (hη u) (hψ u)).le) hprodi).mpr
    have hs : Function.support (fun u => η u * ψ u) = Set.univ := by
      ext u
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (mul_pos (hη u) (hψ u)).ne'
    simp [hs]
  have hlhs : ∫ u, lam * η u * ψ u ∂μ' = lam * ∫ u, η u * ψ u ∂μ' := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    ring
  have hTψc : Continuous fun u => ∫ v, twistedKernel n β (u, v) * ψ v ∂μ' := by
    have e : (fun u => ∫ v, twistedKernel n β (u, v) * ψ v ∂μ') =
        WilsonPositiveGroundState.realSmoothing (μ') (twistedKernel n β) ψ :=
      funext fun u => (WilsonPositiveGroundState.realSmoothing_integral (μ') _ ψ u).symm
    rw [e]
    exact (WilsonPositiveGroundState.realSmoothing (μ') (twistedKernel n β) ψ).continuous
  have hRi : Integrable (fun u => η u * ∫ v, twistedKernel n β (u, v) * ψ v ∂μ') μ' :=
    (η.continuous.mul hTψc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [hlhs] at hpair
  constructor
  · have h1 : ∫ u, m * (η u * ψ u) ∂μ' ≤ ∫ u, η u * ∫ v, twistedKernel n β (u, v) * ψ v ∂μ' ∂μ' := by
      refine integral_mono (hprodi.const_mul m) hRi fun u => ?_
      have := mul_le_mul_of_nonneg_left (hm u) (hη u).le
      dsimp only
      linarith only [this]
    rw [integral_const_mul, ← hpair] at h1
    exact le_of_mul_le_mul_right h1 hpos
  · have h1 : ∫ u, η u * ∫ v, twistedKernel n β (u, v) * ψ v ∂μ' ∂μ' ≤ ∫ u, M * (η u * ψ u) ∂μ' := by
      refine integral_mono hRi (hprodi.const_mul M) fun u => ?_
      have := mul_le_mul_of_nonneg_left (hM u) (hη u).le
      dsimp only
      linarith only [this]
    rw [integral_const_mul, ← hpair] at h1
    exact le_of_mul_le_mul_right h1 hpos

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedCollatz
