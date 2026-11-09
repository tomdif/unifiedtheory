/- Finite chains for an actual continuous kernel on a compact probability
space. Haar-specific or ground-state boundary assumptions are not inserted.
The literal product integral is connected to its boundary recursion. -/
import UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteKernelChain
noncomputable section
open MeasureTheory WilsonPositiveGroundState

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

abbrev Path (L : ℕ) := Fin L → X
local instance pathBorel (L : ℕ) : BorelSpace (Path (X := X) L) := Pi.borelSpace

def pathMeasure (L : ℕ) : Measure (Path (X := X) L) := Measure.pi (fun _ => μ)
instance pathMeasure_probability (L : ℕ) : IsProbabilityMeasure (pathMeasure μ L) := by
  unfold pathMeasure
  infer_instance

theorem path_integral_cons (L : ℕ) (F : Path (X := X) (L + 1) → ℝ) (hF : Continuous F) :
    (∫ u, F u ∂pathMeasure μ (L + 1)) =
      ∫ x, ∫ u, F (Fin.cons x u) ∂pathMeasure μ L ∂μ := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (L + 1) => μ) 0).symm
  have he := hp.integral_comp' F
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.zero_succAbove, cast_eq] at he
  unfold pathMeasure
  rw [← he]
  have hc : Continuous (fun z : X × Path (X := X) L => F (Fin.cons z.1 z.2)) := by
    apply hF.comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using
        (continuous_fst : Continuous (fun z : X × Path (X := X) L => z.1))
    · simpa only [Fin.cons_succ] using
        ((continuous_apply j).comp continuous_snd :
          Continuous (fun z : X × Path (X := X) L => z.2 j))
  exact integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

def chain (K : C(X × X, ℝ)) (L : ℕ) (u : Path (X := X) (L + 1)) : ℝ :=
  ∏ t : Fin L, K (u t.castSucc,u t.succ)

def endpoint (K : C(X × X, ℝ)) (L : ℕ) (F G : C(X, ℝ)) : ℝ :=
  ∫ u, F (u 0) * chain K L u * G (u (Fin.last L)) ∂pathMeasure μ (L + 1)

def message (K : C(X × X, ℝ)) (B : C(X, ℝ)) : ℕ → C(X, ℝ)
  | 0 => B
  | L + 1 => realSmoothing μ K (message K B L)

omit [SecondCountableTopology X] in
theorem message_succ (K : C(X × X, ℝ)) (B : C(X, ℝ)) (L : ℕ) (x : X) :
    message μ K B (L + 1) x = ∫ y, K (x, y) * message μ K B L y ∂μ :=
  realSmoothing_integral μ K (message μ K B L) x

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem chain_continuous (K : C(X × X, ℝ)) (L : ℕ) : Continuous (chain K L) := by
  unfold chain
  exact continuous_finset_prod Finset.univ (fun t _ =>
    K.continuous.comp ((continuous_apply t.castSucc).prodMk (continuous_apply t.succ)))

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem endpoint_continuous (K : C(X × X, ℝ)) (L : ℕ) (F G : C(X, ℝ)) :
    Continuous (fun u : Path (X := X) (L + 1) =>
      F (u 0) * chain K L u * G (u (Fin.last L))) :=
  ((F.continuous.comp (continuous_apply 0)).mul (chain_continuous K L)).mul
    (G.continuous.comp (continuous_apply (Fin.last L)))

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem chain_cons (K : C(X × X, ℝ)) (L : ℕ) (x : X) (u : Path (X := X) (L + 1)) :
    chain K (L + 1) (Fin.cons x u) = K (x,u 0) * chain K L u := by
  simp only [chain, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    Fin.castSucc_succ]

theorem endpoint_message (K : C(X × X, ℝ)) (L : ℕ) (F G : C(X, ℝ)) :
    endpoint μ K L F G = ∫ x, F x * message μ K G L x ∂μ := by
  induction L generalizing F with
  | zero =>
    unfold endpoint
    rw [path_integral_cons μ 0 _ (endpoint_continuous K 0 F G)]
    simp only [chain, Fin.prod_univ_zero, Fin.last_zero, Fin.cons_zero, mul_one]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl
  | succ L ih =>
    unfold endpoint
    rw [path_integral_cons μ (L + 1) _ (endpoint_continuous K (L + 1) F G)]
    apply integral_congr_ae
    filter_upwards [] with x
    have hlast : Fin.last (L + 1) = (Fin.last L).succ := rfl
    simp only [Fin.cons_zero, chain_cons, hlast, Fin.cons_succ]
    have he (u : Path (X := X) (L + 1)) :
        F x * (K (x,u 0) * chain K L u) * G (u (Fin.last L)) =
          F x * (K (x,u 0) * chain K L u * G (u (Fin.last L))) := by ring
    simp_rw [he]
    rw [integral_const_mul]
    let R : C(X, ℝ) := ⟨fun y => K (x, y),
      K.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hr := ih R
    change (∫ u, K (x,u 0) * chain K L u * G (u (Fin.last L)) ∂pathMeasure μ (L + 1)) =
      ∫ y, K (x, y) * message μ K G L y ∂μ at hr
    rw [hr, ← message_succ]

omit [SecondCountableTopology X] in
theorem message_nonneg (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (B : C(X, ℝ)) (hB : ∀ x, 0 ≤ B x) (L : ℕ) (x : X) : 0 ≤ message μ K B L x := by
  induction L generalizing x with
  | zero => exact hB x
  | succ L ih =>
    rw [message_succ]
    exact integral_nonneg (fun y => mul_nonneg (hK x y) (ih y))

omit [SecondCountableTopology X] in
theorem message_mono (K : C(X × X, ℝ)) (hK : ∀ x y, 0 ≤ K (x, y))
    (F G : C(X, ℝ)) (hFG : ∀ x, F x ≤ G x) (L : ℕ) (x : X) :
    message μ K F L x ≤ message μ K G L x := by
  induction L generalizing x with
  | zero => exact hFG x
  | succ L ih =>
    rw [message_succ, message_succ]
    apply integral_mono
    · exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        (message μ K F L).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · exact ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul
        (message μ K G L).continuous).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    · intro y
      exact mul_le_mul_of_nonneg_left (ih y) (hK x y)

omit [SecondCountableTopology X] in
theorem message_smul (K : C(X × X, ℝ)) (B : C(X, ℝ)) (c : ℝ) (L : ℕ) :
    message μ K (c • B) L = c • message μ K B L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    ext x
    simp only [message_succ, ih, ContinuousMap.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (K (x,_)) c]
    rw [integral_const_mul]

omit [SecondCountableTopology X] in
theorem message_eigen (K : C(X × X, ℝ)) (ψ : C(X, ℝ)) (lam : ℝ)
    (hψ : ∀ x, (∫ y, K (x, y) * ψ y ∂μ) = lam * ψ x) (L : ℕ) (x : X) :
    message μ K ψ L x = lam^L * ψ x := by
  induction L generalizing x with
  | zero => simp [message]
  | succ L ih =>
    rw [message_succ]
    simp_rw [ih, mul_left_comm (K (x,_)) (lam^L)]
    rw [integral_const_mul, hψ, pow_succ]
    ring

end
end UnifiedTheory.Clay.YangMills.FiniteKernelChain
