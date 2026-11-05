/- **Prékopa's theorem in many fine variables.** `TwistedPrekopa` proves Prékopa–Leindler on the
line for bounded real functions. This file removes the bound by truncation and monotone
convergence (`pl_ennreal`, for arbitrary measurable `ℝ≥0∞`-valued functions), then iterates
over coordinates. A measure space `(X, μ)` is a *Prékopa space* when integrating out `x ∈ X` from
any jointly log-concave kernel `F(x, y)` leaves a log-concave function of `y`. Then:

* `ℝ` with Lebesgue measure is a Prékopa space (`prekopaSpace_real`);
* products of Prékopa spaces are Prékopa spaces, by Tonelli (`PrekopaSpace.prod`);
* the property transports along measure-preserving linear equivalences (`PrekopaSpace.of_equiv`);
* so `ℝᵐ = Fin m → ℝ` with Lebesgue measure is a Prékopa space for every `m` (`prekopaSpace_pi`).

The RG consequence (`prekopa_rg_step_multi`) integrates out any number of fine variables in one
step. If `V(x, y) − c‖y‖²` is jointly convex, then `U(y) − c‖y‖²` is convex, where
`U = −log ∫ e^{−V(x,·)} dx`. The strong-convexity constant in the coarse field is preserved. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti

open MeasureTheory Set
open UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa

/-- **Prékopa–Leindler on the line, unbounded `ℝ≥0∞` version.** -/
theorem pl_ennreal (f g h : ℝ → ENNReal) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) :
    (∫⁻ x, f x) ^ lam * (∫⁻ x, g x) ^ (1 - lam) ≤ ∫⁻ x, h x := by
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  set T : ℕ → ENNReal := fun n => (n : ENNReal) + 1
  have Tne : ∀ n, T n ≠ ⊤ := fun n => by simp [T]
  have T0 : ∀ n, T n ≠ 0 := fun n => by simp [T]
  have Tmono : Monotone T := fun n k hnk => by
    simp only [T]; gcongr
  have mfin : ∀ (u : ENNReal) n, min u (T n) ≠ ⊤ := fun u n =>
    ((min_le_right _ _).trans_lt (lt_top_iff_ne_top.2 (Tne n))).ne
  have step : ∀ n, (∫⁻ x, min (f x) (T n)) ^ lam * (∫⁻ x, min (g x) (T n)) ^ (1 - lam)
      ≤ ∫⁻ x, h x := by
    intro n
    have bdd : ∀ u : ℝ → ENNReal, BddAbove (range fun x => (min (u x) (T n)).toReal) :=
      fun u => ⟨(T n).toReal, by
        rintro _ ⟨x, rfl⟩; exact ENNReal.toReal_mono (Tne n) (min_le_right _ _)⟩
    have key := prekopa_leindler (fun x => (min (f x) (T n)).toReal)
      (fun x => (min (g x) (T n)).toReal) (fun x => (min (h x) (T n)).toReal) lam hl0 hl1
      (hf.min measurable_const).ennreal_toReal (hg.min measurable_const).ennreal_toReal
      (hh.min measurable_const).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
      (fun _ => ENNReal.toReal_nonneg) (bdd f) (bdd g) (fun x y => by
        beta_reduce
        rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
        refine ENNReal.toReal_mono (mfin _ n) (le_min ?_ ?_)
        · exact (mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) hl0.le)
            (ENNReal.rpow_le_rpow (min_le_left _ _) hl1'.le)).trans (hyp x y)
        · calc min (f x) (T n) ^ lam * min (g y) (T n) ^ (1 - lam)
              ≤ T n ^ lam * T n ^ (1 - lam) :=
                mul_le_mul' (ENNReal.rpow_le_rpow (min_le_right _ _) hl0.le)
                  (ENNReal.rpow_le_rpow (min_le_right _ _) hl1'.le)
            _ = T n := by
                rw [← ENNReal.rpow_add _ _ (T0 n) (Tne n), add_sub_cancel, ENNReal.rpow_one])
    have hm : ∀ u : ENNReal, ENNReal.ofReal (min u (T n)).toReal = min u (T n) :=
      fun u => ENNReal.ofReal_toReal (mfin u n)
    simp only [hm] at key
    exact key.trans (lintegral_mono fun x => min_le_left _ _)
  have Tsup : ⨆ n, T n = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← ENNReal.iSup_natCast]
    exact iSup_mono fun n => le_self_add
  have lim : ∀ u : ℝ → ENNReal, Measurable u → ⨆ n, ∫⁻ x, min (u x) (T n) = ∫⁻ x, u x := by
    intro u hu
    rw [← lintegral_iSup (fun n => hu.min measurable_const)
      (fun n k hnk x => min_le_min_left _ (Tmono hnk))]
    congr 1; funext x
    rw [← inf_iSup_eq, Tsup]
    exact inf_top_eq _
  have amono : ∀ u : ℝ → ENNReal, Monotone fun n => ∫⁻ x, min (u x) (T n) :=
    fun u n k hnk => lintegral_mono fun x => min_le_min_left _ (Tmono hnk)
  have rp : ∀ (p : ℝ), 0 < p → ∀ a : ℕ → ENNReal, (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro p hp a
    exact Monotone.map_iSup_of_continuousAt (f := fun z : ENNReal => z ^ p)
      ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hp.le)
      (by simp [ENNReal.zero_rpow_of_pos hp])
  rw [← lim f hf, ← lim g hg, rp lam hl0, rp (1 - lam) hl1', ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  calc (∫⁻ x, min (f x) (T i)) ^ lam * (∫⁻ x, min (g x) (T j)) ^ (1 - lam)
      ≤ (∫⁻ x, min (f x) (T (max i j))) ^ lam * (∫⁻ x, min (g x) (T (max i j))) ^ (1 - lam) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (amono f (le_max_left i j)) hl0.le)
          (ENNReal.rpow_le_rpow (amono g (le_max_right i j)) hl1'.le)
    _ ≤ _ := step (max i j)

/-- Log-concavity of an `ℝ≥0∞`-valued function on a real vector space. -/
def LogConcave {X : Type*} [AddCommGroup X] [Module ℝ X] (F : X → ENNReal) : Prop :=
  ∀ (x x' : X) (lam : ℝ), 0 < lam → lam < 1 →
    F x ^ lam * F x' ^ (1 - lam) ≤ F (lam • x + (1 - lam) • x')

/-- `(X, μ)` is a **Prékopa space**: integrating out `x` preserves joint log-concavity. -/
def PrekopaSpace (X : Type) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] (μ : Measure X) :
    Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℝ E] (F : X × E → ENNReal), LogConcave F →
    (∀ y, Measurable fun x => F (x, y)) → LogConcave (fun y => ∫⁻ x, F (x, y) ∂μ)

/-- **The line is a Prékopa space.** -/
theorem prekopaSpace_real : PrekopaSpace ℝ volume := by
  intro E _ _ F hF hm y1 y2 lam hl0 hl1
  refine pl_ennreal _ _ _ lam hl0 hl1 (hm y1) (hm y2) (hm _) fun x x' => ?_
  have := hF (x, y1) (x', y2) lam hl0 hl1
  simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this

/-- **Products of Prékopa spaces are Prékopa spaces** (Tonelli). -/
theorem PrekopaSpace.prod {X₁ X₂ : Type} [AddCommGroup X₁] [Module ℝ X₁] [MeasurableSpace X₁]
    [AddCommGroup X₂] [Module ℝ X₂] [MeasurableSpace X₂] {μ₁ : Measure X₁} {μ₂ : Measure X₂}
    [SFinite μ₁] [SFinite μ₂] (h₁ : PrekopaSpace X₁ μ₁) (h₂ : PrekopaSpace X₂ μ₂) :
    PrekopaSpace (X₁ × X₂) (μ₁.prod μ₂) := by
  intro E _ _ F hF hm
  have hG : LogConcave (fun p : X₁ × E => ∫⁻ x₂, F ((p.1, x₂), p.2) ∂μ₂) := by
    refine h₂ (X₁ × E) (fun q : X₂ × (X₁ × E) => F ((q.2.1, q.1), q.2.2)) ?_ ?_
    · intro q q' lam hl0 hl1
      have := hF ((q.2.1, q.1), q.2.2) ((q'.2.1, q'.1), q'.2.2) lam hl0 hl1
      simpa only [Prod.smul_mk, Prod.mk_add_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
        Prod.snd_add] using this
    · intro p
      exact (hm p.2).comp (measurable_const.prodMk measurable_id :
        Measurable fun x : X₂ => (p.1, x))
  have eq : (fun y => ∫⁻ x, F (x, y) ∂(μ₁.prod μ₂)) =
      fun y => ∫⁻ x₁, ∫⁻ x₂, F ((x₁, x₂), y) ∂μ₂ ∂μ₁ :=
    funext fun y => lintegral_prod _ (hm y).aemeasurable
  rw [eq]
  exact h₁ E (fun p : X₁ × E => ∫⁻ x₂, F ((p.1, x₂), p.2) ∂μ₂) hG
    fun y => Measurable.lintegral_prod_right' (f := fun z => F (z, y)) (hm y)

/-- **Transport along a measure-preserving linear equivalence.** -/
theorem PrekopaSpace.of_equiv {X Y : Type} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : ∀ (a b : ℝ) (x x' : X), e (a • x + b • x') = a • e x + b • e x')
    (hμ : MeasurePreserving e μ ν) (hX : PrekopaSpace X μ) : PrekopaSpace Y ν := by
  intro E _ _ F hF hm
  have eq : (fun y => ∫⁻ x, F (x, y) ∂ν) = fun y => ∫⁻ x, F (e x, y) ∂μ :=
    funext fun y => (hμ.lintegral_comp_emb e.measurableEmbedding (fun x => F (x, y))).symm
  rw [eq]
  refine hX E (fun q => F (e q.1, q.2)) ?_ fun y => (hm y).comp e.measurable
  intro q q' lam hl0 hl1
  have := hF (e q.1, q.2) (e q'.1, q'.2) lam hl0 hl1
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, he]
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

/-- **`ℝᵐ` is a Prékopa space** for every `m`. -/
theorem prekopaSpace_pi : ∀ m : ℕ, PrekopaSpace (Fin m → ℝ) volume
  | 0 => by
    intro E _ _ F hF hm y1 y2 lam hl0 hl1
    have eq : ∀ y, ∫⁻ x, F (x, y) ∂(volume : Measure (Fin 0 → ℝ)) = F (0, y) := by
      intro y
      rw [volume_pi, Measure.pi_of_empty (x := 0), lintegral_dirac' _ (hm y)]
    simp only [eq]
    have := hF (0, y1) (0, y2) lam hl0 hl1
    simpa using this
  | m + 1 => by
    have hp := PrekopaSpace.prod (μ₁ := (volume : Measure ℝ))
      (μ₂ := (volume : Measure (Fin m → ℝ))) prekopaSpace_real (prekopaSpace_pi m)
    refine PrekopaSpace.of_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
      ?_ ?_ hp
    · intro a b p p'
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    · exact (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm _

/-- A finite, nonzero log-concave function has a convex negative logarithm. -/
theorem convex_neg_log {E : Type*} [AddCommGroup E] [Module ℝ E] (Z : E → ENNReal)
    (hZ : LogConcave Z) (hfin : ∀ y, Z y ≠ ⊤) (hpos : ∀ y, Z y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (Z y).toReal) := by
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : b = 1 - a := by linarith
  have key := ENNReal.toReal_mono (hfin _) (hZ y1 y2 a ha' (by linarith))
  have p1 : 0 < (Z y1).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  have p2 : 0 < (Z y2).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at key
  have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos p1 _) (Real.rpow_pos_of_pos p2 _)) key
  rw [Real.log_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
    Real.log_rpow p1, Real.log_rpow p2] at hl
  simp only [smul_eq_mul]
  linarith

/-- The Boltzmann weight of a convex action is log-concave. -/
theorem logConcave_exp_neg {X : Type*} [AddCommGroup X] [Module ℝ X] (W : X → ℝ)
    (hW : ConvexOn ℝ univ W) : LogConcave (fun x => ENNReal.ofReal (Real.exp (-W x))) := by
  intro x x' lam hl0 hl1
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl0.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hl1'.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  have := hW.2 (mem_univ x) (mem_univ x') hl0.le hl1'.le (by ring)
  simp only [smul_eq_mul] at this
  linarith

/-- The marginal weight `∫ e^{−V(x,y)} dμ(x)`. -/
noncomputable def ZM {X E : Type*} [MeasurableSpace X] (μ : Measure X) (V : X → E → ℝ) (y : E) :
    ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-V x y)) ∂μ

/-- **One RG step with many fine variables preserves strong convexity.** On any Prékopa space of
fine variables: if `V(x, y) − c‖y‖²` is jointly convex, the coarse action
`U(y) = −log ∫ e^{−V(x,y)} dμ(x)` has `U − c‖y‖²` convex. -/
theorem prekopa_rg_step_multi {X : Type} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PrekopaSpace X μ) {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V : X → E → ℝ) (c : ℝ)
    (hV : ConvexOn ℝ univ (fun p : X × E => V p.1 p.2 - c * ‖p.2‖ ^ 2))
    (hVm : ∀ y, Measurable fun x => V x y)
    (hfin : ∀ y, ZM μ V y ≠ ⊤) (hpos : ∀ y, ZM μ V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (ZM μ V y).toReal - c * ‖y‖ ^ 2) := by
  set W : X → E → ℝ := fun x y => V x y - c * ‖y‖ ^ 2
  have hZ : ∀ y, ZM μ W y = ENNReal.ofReal (Real.exp (c * ‖y‖ ^ 2)) * ZM μ V y := by
    intro y
    simp only [ZM, W]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hlc : LogConcave (ZM μ W) :=
    hX E (fun p : X × E => ENNReal.ofReal (Real.exp (-W p.1 p.2))) (logConcave_exp_neg _ hV)
      fun y => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        ((hVm y).sub_const (c * ‖y‖ ^ 2)).neg :)
  have hWfin : ∀ y, ZM μ W y ≠ ⊤ := fun y => by
    rw [hZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin y)
  have hWpos : ∀ y, ZM μ W y ≠ 0 := fun y => by
    rw [hZ]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hpos y)
  have key := convex_neg_log _ hlc hWfin hWpos
  convert key using 2 with y
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos (hpos y) (hfin y)).ne', Real.log_exp]
  ring

/-- **Prékopa's theorem on `ℝᵐ`.** For a jointly convex action `V(x, y)` with `x ∈ ℝᵐ`, the coarse
action `−log ∫ e^{−V(x,y)} dx` is convex in `y`. -/
theorem prekopa_pi (m : ℕ) {E : Type} [AddCommGroup E] [Module ℝ E] (V : (Fin m → ℝ) → E → ℝ)
    (hV : ConvexOn ℝ univ (fun p : (Fin m → ℝ) × E => V p.1 p.2))
    (hVm : ∀ y, Measurable fun x => V x y)
    (hfin : ∀ y, ZM volume V y ≠ ⊤) (hpos : ∀ y, ZM volume V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (ZM volume V y).toReal) :=
  convex_neg_log _ (prekopaSpace_pi m E (fun p => ENNReal.ofReal (Real.exp (-V p.1 p.2)))
    (logConcave_exp_neg _ hV)
    fun y => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hVm y).neg)) hfin hpos

/-- **The RG step on `ℝᵐ`.** Integrating out `m` fine variables keeps the coarse
strong-convexity constant `c`. -/
theorem prekopa_rg_step_pi (m : ℕ) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (V : (Fin m → ℝ) → E → ℝ) (c : ℝ)
    (hV : ConvexOn ℝ univ (fun p : (Fin m → ℝ) × E => V p.1 p.2 - c * ‖p.2‖ ^ 2))
    (hVm : ∀ y, Measurable fun x => V x y)
    (hfin : ∀ y, ZM volume V y ≠ ⊤) (hpos : ∀ y, ZM volume V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (ZM volume V y).toReal - c * ‖y‖ ^ 2) :=
  prekopa_rg_step_multi (prekopaSpace_pi m) V c hV hVm hfin hpos

end UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopaMulti
