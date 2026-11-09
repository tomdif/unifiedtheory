/- **Prékopa–Leindler on the line and the Prékopa marginal theorem.** This is the non-Gaussian
counterpart of `TwistedGaussianStep`. The chain is:

* 1D Brunn–Minkowski for compact sets, `|A + B| ≥ |A| + |B|` (`bm_compact`);
* the level-set inequality for measurable `f, g, h` (via inner regularity of Lebesgue measure);
* the layer-cake formula, giving the linear form `λ∫f + (1−λ)∫g ≤ ∫h` when `sup f = sup g = 1`;
* normalization plus weighted AM–GM in `ℝ≥0∞`, giving
  `(∫f)^λ (∫g)^{1−λ} ≤ ∫h` (`prekopa_leindler`).

Applied in the fine variable `x ∈ ℝ`, it gives Prékopa's theorem: if `V(x, y)` is jointly convex,
the marginal `Z(y) = ∫ e^{−V(x,y)} dx` is log-concave (`prekopa_marginal`). Hence
`U(y) = −log Z(y)` is convex (`prekopa_convex`), and a strong-convexity bound
`V − c(x² + ‖y‖²)` convex passes to `U − c‖y‖²` convex (`prekopa_rg_step`). This is the
Brascamp–Lieb/Prékopa step of one RG block with one fine variable integrated out, for any convex
action and not just a quadratic one. Not covered: several fine variables at once (iterate with
Tonelli), the compact gauge group, and large fields. -/
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa

open MeasureTheory Set Pointwise

/-- **Brunn–Minkowski on the line** for nonempty compact sets. -/
theorem bm_compact {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B) (hA0 : A.Nonempty)
    (hB0 : B.Nonempty) : volume A + volume B ≤ volume (A + B) := by
  set a := sInf A
  set b := sSup B
  have ha : a ∈ A := hA.sInf_mem hA0
  have hb : b ∈ B := hB.sSup_mem hB0
  have h1 : (· + b) '' A ⊆ A + B := by
    rintro _ ⟨x, hx, rfl⟩; exact Set.add_mem_add hx hb
  have h2 : (a + ·) '' B ⊆ A + B := by
    rintro _ ⟨y, hy, rfl⟩; exact Set.add_mem_add ha hy
  have hint : (· + b) '' A ∩ (a + ·) '' B ⊆ {a + b} := by
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have : a ≤ x := csInf_le hA.bddBelow hx
    have : y ≤ b := le_csSup hB.bddAbove hy
    simp only [mem_singleton_iff]; linarith
  have hmeas : MeasurableSet ((a + ·) '' B) :=
    (hB.image (continuous_const.add continuous_id)).measurableSet
  have e1 : volume ((· + b) '' A) = volume A := by
    simp only [image_add_right, measure_preimage_add_right]
  have e2 : volume ((a + ·) '' B) = volume B := by
    simp only [image_add_left, measure_preimage_add]
  calc volume A + volume B = volume ((· + b) '' A) + volume ((a + ·) '' B) := by rw [e1, e2]
    _ = volume ((· + b) '' A ∪ (a + ·) '' B) + volume ((· + b) '' A ∩ (a + ·) '' B) :=
        (measure_union_add_inter _ hmeas).symm
    _ ≤ volume (A + B) + 0 := by
        gcongr
        · exact union_subset h1 h2
        · exact le_of_le_of_eq (measure_mono hint) (by simp)
    _ = volume (A + B) := add_zero _

/-- Lebesgue measure of a measurable set as a supremum over compact subsets. -/
theorem vol_eq_iSup_sub {S : Set ℝ} (hS : MeasurableSet S) :
    volume S = ⨆ K : {K : Set ℝ // K ⊆ S ∧ IsCompact K}, volume K.1 := by
  rw [hS.measure_eq_iSup_isCompact]
  refine le_antisymm (iSup_le fun K => iSup_le fun hK => iSup_le fun hc =>
    le_iSup (fun K : {K : Set ℝ // K ⊆ S ∧ IsCompact K} => volume K.1) ⟨K, hK, hc⟩) ?_
  exact iSup_le fun K => le_iSup_of_le K.1 (le_iSup_of_le K.2.1 (le_iSup_of_le K.2.2 le_rfl))

/-- Inner approximation of two sets at once. -/
theorem sup_helper {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) (p q X : ENNReal)
    (H : ∀ K L, K ⊆ S → IsCompact K → L ⊆ T → IsCompact L → p * volume K + q * volume L ≤ X) :
    p * volume S + q * volume T ≤ X := by
  rw [vol_eq_iSup_sub hS, vol_eq_iSup_sub hT, ENNReal.mul_iSup, ENNReal.mul_iSup]
  haveI : Nonempty {K : Set ℝ // K ⊆ S ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  haveI : Nonempty {K : Set ℝ // K ⊆ T ∧ IsCompact K} := ⟨⟨∅, empty_subset _, isCompact_empty⟩⟩
  exact ENNReal.iSup_add_iSup_le fun K L => H K.1 L.1 K.2.1 K.2.2 L.2.1 L.2.2

theorem sum_subset_level (f g h : ℝ → ℝ) (lam t : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) (ht : 0 < t)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    {K L : Set ℝ} (hK : K ⊆ {x | t ≤ f x}) (hL : L ⊆ {x | t ≤ g x}) :
    lam • K + (1 - lam) • L ⊆ {x | t ≤ h x} := by
  intro z hz
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hz
  have hx' : t ≤ f x := hK hx
  have hy' : t ≤ g y := hL hy
  have e : t ^ lam * t ^ (1 - lam) = t := by
    rw [← Real.rpow_add ht, add_sub_cancel, Real.rpow_one]
  simp only [smul_eq_mul, mem_setOf_eq]
  calc t = t ^ lam * t ^ (1 - lam) := e.symm
    _ ≤ f x ^ lam * g y ^ (1 - lam) :=
        mul_le_mul (Real.rpow_le_rpow ht.le hx' hl0.le)
          (Real.rpow_le_rpow ht.le hy' (by linarith)) (Real.rpow_nonneg ht.le _)
          (Real.rpow_nonneg (ht.le.trans hx') _)
    _ ≤ _ := hyp x y

/-- **Level-set inequality.** For `0 < t` below both suprema,
`λ|{f ≥ t}| + (1−λ)|{g ≥ t}| ≤ |{h ≥ t}|`. -/
theorem level_ineq (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hf : Measurable f) (hg : Measurable g)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y))
    (t : ℝ) (ht : 0 < t) (hfn : ∃ x, t ≤ f x) (hgn : ∃ y, t ≤ g y) :
    ENNReal.ofReal lam * volume {x | t ≤ f x} + ENNReal.ofReal (1 - lam) * volume {x | t ≤ g x}
      ≤ volume {x | t ≤ h x} := by
  obtain ⟨x0, hx0⟩ := hfn
  obtain ⟨y0, hy0⟩ := hgn
  refine sup_helper (measurableSet_le measurable_const hf) (measurableSet_le measurable_const hg)
    _ _ _ fun K L hK hKc hL hLc => ?_
  have hK' : insert x0 K ⊆ {x | t ≤ f x} := insert_subset hx0 hK
  have hL' : insert y0 L ⊆ {x | t ≤ g x} := insert_subset hy0 hL
  have e1 : volume (lam • insert x0 K) = ENNReal.ofReal lam * volume (insert x0 K) := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos hl0]
  have e2 : volume ((1 - lam) • insert y0 L) = ENNReal.ofReal (1 - lam) * volume (insert y0 L) := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos (sub_pos.mpr hl1)]
  calc ENNReal.ofReal lam * volume K + ENNReal.ofReal (1 - lam) * volume L
      ≤ ENNReal.ofReal lam * volume (insert x0 K)
          + ENNReal.ofReal (1 - lam) * volume (insert y0 L) := by
        gcongr <;> exact subset_insert _ _
    _ = volume (lam • insert x0 K) + volume ((1 - lam) • insert y0 L) := by rw [e1, e2]
    _ ≤ volume (lam • insert x0 K + (1 - lam) • insert y0 L) :=
        bm_compact ((hKc.insert x0).smul lam) ((hLc.insert y0).smul (1 - lam))
          ((insert_nonempty _ _).smul_set) ((insert_nonempty _ _).smul_set)
    _ ≤ volume {x | t ≤ h x} := measure_mono (sum_subset_level f g h lam t hl0 hl1 ht hyp hK' hL')

theorem antitone_level (f : ℝ → ℝ) : Antitone (fun t : ℝ => volume {x | t ≤ f x}) :=
  fun _ _ hst => measure_mono fun _ hx => le_trans hst hx

theorem pl_linear (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ x, 0 ≤ g x) (h0 : ∀ x, 0 ≤ h x)
    (f1 : ∀ x, f x ≤ 1) (g1 : ∀ x, g x ≤ 1)
    (fs : ∀ t < 1, ∃ x, t ≤ f x) (gs : ∀ t < 1, ∃ x, t ≤ g x)
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) :
    ENNReal.ofReal lam * (∫⁻ x, ENNReal.ofReal (f x))
      + ENNReal.ofReal (1 - lam) * (∫⁻ x, ENNReal.ofReal (g x)) ≤ ∫⁻ x, ENNReal.ofReal (h x) := by
  have lc : ∀ u : ℝ → ℝ, (∀ x, 0 ≤ u x) → Measurable u →
      ∫⁻ x, ENNReal.ofReal (u x) = ∫⁻ t in Ioi 0, volume {x | t ≤ u x} :=
    fun u hu hum => lintegral_eq_lintegral_meas_le (f := u) volume (ae_of_all _ hu) hum.aemeasurable
  have ef := lc f f0 hf
  have eg := lc g g0 hg
  have eh := lc h h0 hh
  rw [ef, eg, eh,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left ((antitone_level f).measurable.const_mul _)]
  apply lintegral_mono_ae
  have hne : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ≠ 1 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]; simp
  filter_upwards [hne, ae_restrict_mem measurableSet_Ioi] with t ht1 ht0
  rcases lt_or_gt_of_ne ht1 with hlt | hgt
  · exact level_ineq f g h lam hl0 hl1 hf hg hyp t ht0 (fs t hlt) (gs t hlt)
  · have ef : {x | t ≤ f x} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact (f1 x).trans_lt hgt
    have eg : {x | t ≤ g x} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact (g1 x).trans_lt hgt
    simp [ef, eg]

theorem ennreal_amgm (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) (x y : ENNReal) :
    x ^ lam * y ^ (1 - lam) ≤ ENNReal.ofReal lam * x + ENNReal.ofReal (1 - lam) * y := by
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  rcases eq_or_ne x ⊤ with rfl | hx
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr hl0).ne', top_add]; exact le_top
  rcases eq_or_ne y ⊤ with rfl | hy
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr hl1').ne', add_top]; exact le_top
  lift x to NNReal using hx
  lift y to NNReal using hy
  have h := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal lam) (Real.toNNReal (1 - lam))
    x y (by rw [← Real.toNNReal_add hl0.le hl1'.le]; simp)
  rw [Real.coe_toNNReal _ hl0.le, Real.coe_toNNReal _ hl1'.le] at h
  rw [← ENNReal.coe_rpow_of_nonneg _ hl0.le, ← ENNReal.coe_rpow_of_nonneg _ hl1'.le, ENNReal.ofReal,
    ENNReal.ofReal]
  exact_mod_cast h

theorem lintegral_scale (u : ℝ → ℝ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (u x) = ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (u x / a) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1; funext x
  rw [← ENNReal.ofReal_mul ha.le, mul_div_cancel₀ _ ha.ne']

/-- **Prékopa–Leindler inequality on the line.** -/
theorem prekopa_leindler (f g h : ℝ → ℝ) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ x, 0 ≤ g x) (h0 : ∀ x, 0 ≤ h x)
    (fb : BddAbove (range f)) (gb : BddAbove (range g))
    (hyp : ∀ x y, f x ^ lam * g y ^ (1 - lam) ≤ h (lam * x + (1 - lam) * y)) :
    (∫⁻ x, ENNReal.ofReal (f x)) ^ lam * (∫⁻ x, ENNReal.ofReal (g x)) ^ (1 - lam)
      ≤ ∫⁻ x, ENNReal.ofReal (h x) := by
  have hl1' : 0 < 1 - lam := sub_pos.mpr hl1
  set a := ⨆ x, f x
  set b := ⨆ x, g x
  have fa : ∀ x, f x ≤ a := fun x => le_ciSup fb x
  have gb' : ∀ x, g x ≤ b := fun x => le_ciSup gb x
  have a0 : 0 ≤ a := (f0 0).trans (fa 0)
  have b0 : 0 ≤ b := (g0 0).trans (gb' 0)
  rcases a0.eq_or_lt with ha | ha
  · have : ∀ x, f x = 0 := fun x => le_antisymm (ha ▸ fa x) (f0 x)
    simp [this, ENNReal.zero_rpow_of_pos hl0]
  rcases b0.eq_or_lt with hb | hb
  · have : ∀ x, g x = 0 := fun x => le_antisymm (hb ▸ gb' x) (g0 x)
    simp [this, ENNReal.zero_rpow_of_pos hl1']
  set c := a ^ lam * b ^ (1 - lam)
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have lin := pl_linear (fun x => f x / a) (fun x => g x / b) (fun x => h x / c) lam hl0 hl1
    (hf.div_const a) (hg.div_const b) (hh.div_const c)
    (fun x => div_nonneg (f0 x) ha.le) (fun x => div_nonneg (g0 x) hb.le)
    (fun x => div_nonneg (h0 x) hc.le)
    (fun x => (div_le_one ha).mpr (fa x)) (fun x => (div_le_one hb).mpr (gb' x))
    (fun t ht => by
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (show t * a < a by nlinarith)
      exact ⟨x, (le_div_iff₀ ha).mpr hx.le⟩)
    (fun t ht => by
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (show t * b < b by nlinarith)
      exact ⟨x, (le_div_iff₀ hb).mpr hx.le⟩)
    (fun x y => by
      simp only
      rw [Real.div_rpow (f0 x) ha.le, Real.div_rpow (g0 y) hb.le, div_mul_div_comm]
      exact div_le_div_of_nonneg_right (hyp x y) hc.le)
  rw [lintegral_scale f a ha, lintegral_scale g b hb, lintegral_scale h c hc,
    ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl1'.le,
    ENNReal.ofReal_rpow_of_nonneg ha.le hl0.le, ENNReal.ofReal_rpow_of_nonneg hb.le hl1'.le]
  calc ENNReal.ofReal (a ^ lam) * (∫⁻ x, ENNReal.ofReal (f x / a)) ^ lam *
        (ENNReal.ofReal (b ^ (1 - lam)) * (∫⁻ x, ENNReal.ofReal (g x / b)) ^ (1 - lam))
      = ENNReal.ofReal c * ((∫⁻ x, ENNReal.ofReal (f x / a)) ^ lam *
          (∫⁻ x, ENNReal.ofReal (g x / b)) ^ (1 - lam)) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]; ring
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal lam * (∫⁻ x, ENNReal.ofReal (f x / a)) +
          ENNReal.ofReal (1 - lam) * (∫⁻ x, ENNReal.ofReal (g x / b))) := by
        gcongr; exact ennreal_amgm lam hl0 hl1 _ _
    _ ≤ ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (h x / c) := by gcongr

section Marginal

variable {E : Type*}

/-- The marginal weight `Z(y) = ∫ e^{−V(x,y)} dx` after integrating out one fine variable. -/
noncomputable def Z (V : ℝ → E → ℝ) (y : E) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-V x y))

/-- **Prékopa's theorem (one fine variable).** For a jointly convex action, the marginal is
log-concave: `Z(y₁)^λ Z(y₂)^{1−λ} ≤ Z(λy₁ + (1−λ)y₂)`. -/
theorem prekopa_marginal [AddCommGroup E] [Module ℝ E] (V : ℝ → E → ℝ)
    (hV : ConvexOn ℝ univ (fun p : ℝ × E => V p.1 p.2))
    (hVm : ∀ y, Measurable fun x => V x y) (hVb : ∀ y, BddBelow (range fun x => V x y))
    (y1 y2 : E) (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam < 1) :
    Z V y1 ^ lam * Z V y2 ^ (1 - lam) ≤ Z V (lam • y1 + (1 - lam) • y2) := by
  have bdd : ∀ y, BddAbove (range fun x => Real.exp (-V x y)) := by
    intro y
    obtain ⟨m, hm⟩ := hVb y
    exact ⟨Real.exp (-m), by
      rintro _ ⟨x, rfl⟩
      exact Real.exp_le_exp.2 (neg_le_neg (hm ⟨x, rfl⟩))⟩
  refine prekopa_leindler _ _ _ lam hl0 hl1 (Real.measurable_exp.comp (hVm y1).neg)
    (Real.measurable_exp.comp (hVm y2).neg) (Real.measurable_exp.comp (hVm _).neg)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (bdd y1) (bdd y2) fun x x' => ?_
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, Real.exp_le_exp]
  have := hV.2 (mem_univ (x, y1)) (mem_univ (x', y2)) hl0.le (sub_pos.2 hl1).le (by ring)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at this
  linarith

/-- **The coarse action is convex.** If the marginal is finite and nonzero everywhere,
`U(y) = −log Z(y)` is convex. -/
theorem prekopa_convex [AddCommGroup E] [Module ℝ E] (V : ℝ → E → ℝ)
    (hV : ConvexOn ℝ univ (fun p : ℝ × E => V p.1 p.2))
    (hVm : ∀ y, Measurable fun x => V x y) (hVb : ∀ y, BddBelow (range fun x => V x y))
    (hfin : ∀ y, Z V y ≠ ⊤) (hpos : ∀ y, Z V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (Z V y).toReal) := by
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  rcases ha.eq_or_lt with rfl | ha'
  · obtain rfl : b = 1 := by linarith
    simp
  rcases hb.eq_or_lt with rfl | hb'
  · obtain rfl : a = 1 := by linarith
    simp
  obtain rfl : b = 1 - a := by linarith
  have key := ENNReal.toReal_mono (hfin _) (prekopa_marginal V hV hVm hVb y1 y2 a ha' (by linarith))
  have p1 : 0 < (Z V y1).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  have p2 : 0 < (Z V y2).toReal := ENNReal.toReal_pos (hpos _) (hfin _)
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at key
  have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos p1 _) (Real.rpow_pos_of_pos p2 _)) key
  rw [Real.log_mul (Real.rpow_pos_of_pos p1 _).ne' (Real.rpow_pos_of_pos p2 _).ne',
    Real.log_rpow p1, Real.log_rpow p2] at hl
  simp only [smul_eq_mul]
  linarith

/-- **One non-Gaussian RG step preserves strong convexity.** If `V(x,y) − c(x² + ‖y‖²)` is jointly
convex, then `U(y) − c‖y‖²` is convex, where `U = −log ∫ e^{−V(x,·)} dx`. This is the same lower
bound in the coarse variable, for any convex action (compare `gaussian_rg_step`). -/
theorem prekopa_rg_step [NormedAddCommGroup E] [InnerProductSpace ℝ E] (V : ℝ → E → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hV : ConvexOn ℝ univ (fun p : ℝ × E => V p.1 p.2 - c * (p.1 ^ 2 + ‖p.2‖ ^ 2)))
    (hVm : ∀ y, Measurable fun x => V x y) (hVb : ∀ y, BddBelow (range fun x => V x y))
    (hfin : ∀ y, Z V y ≠ ⊤) (hpos : ∀ y, Z V y ≠ 0) :
    ConvexOn ℝ univ (fun y => -Real.log (Z V y).toReal - c * ‖y‖ ^ 2) := by
  set W : ℝ → E → ℝ := fun x y => V x y - c * ‖y‖ ^ 2
  have hsq : ConvexOn ℝ univ (fun p : ℝ × E => c * p.1 ^ 2) := by
    have h := ((Even.convexOn_pow (𝕜 := ℝ) (n := 2) even_two).comp_linearMap
      (LinearMap.fst ℝ ℝ E)).smul hc
    simpa using h
  have hW : ConvexOn ℝ univ (fun p : ℝ × E => W p.1 p.2) := by
    have := hV.add hsq
    convert this using 2 with p
    simp only [W, Pi.add_apply]; ring
  have hZ : ∀ y, Z W y = ENNReal.ofReal (Real.exp (c * ‖y‖ ^ 2)) * Z V y := by
    intro y
    simp only [Z, W]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1; funext x
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2; ring
  have hWfin : ∀ y, Z W y ≠ ⊤ := fun y => by
    rw [hZ]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin y)
  have hWpos : ∀ y, Z W y ≠ 0 := fun y => by
    rw [hZ]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' (hpos y)
  have hWm : ∀ y, Measurable fun x => W x y := fun y => (hVm y).sub_const _
  have hWb : ∀ y, BddBelow (range fun x => W x y) := by
    intro y
    obtain ⟨m, hm⟩ := hVb y
    exact ⟨m - c * ‖y‖ ^ 2, by
      rintro _ ⟨x, rfl⟩
      exact sub_le_sub_right (hm ⟨x, rfl⟩) _⟩
  have key := prekopa_convex W hW hWm hWb hWfin hWpos
  convert key using 2 with y
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos (hpos y) (hfin y)).ne', Real.log_exp]
  ring

end Marginal

end UnifiedTheory.Clay.YangMills.Twisted.TwistedPrekopa
