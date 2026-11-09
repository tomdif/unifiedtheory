/- Volume-independent comparison for the actual Wilson time-slab kernel.
A change of one spatial link touches at most four spatial plaquettes and one
temporal plaquette. The resulting factor is exp(6*|beta|*B). No eigenfunction,
continuum limit or physical-energy window is constructed here. -/
import UnifiedTheory.Clay.YangMills.WilsonTimeSlab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
noncomputable section
open MeasureTheory WilsonTimeSlab

variable (n : ℕ) [NeZero n]

def planes (μ : Fin 3) : Finset SpatialPlane := by
  classical
  exact Finset.univ.filter (fun p => p.1.1 = μ ∨ p.1.2 = μ)

theorem planes_card (μ : Fin 3) : (planes μ).card = 2 := by
  fin_cases μ <;> decide

def transverse (μ : Fin 3) (p : SpatialPlane) : Fin 3 :=
  if p.1.1 = μ then p.1.2 else p.1.1

def affected (x : SpatialVertex n) (μ : Fin 3) : Finset (SpatialVertex n × SpatialPlane) := by
  classical
  exact (planes μ).biUnion (fun p => {(x,p), (x-Pi.single (transverse μ p) 1,p)})

omit [NeZero n] in
theorem affected_card (x : SpatialVertex n) (μ : Fin 3) : (affected n x μ).card ≤ 4 := by
  classical
  calc
    (affected n x μ).card ≤ ∑ p ∈ planes μ,
        ({(x,p), (x-Pi.single (transverse μ p) 1,p)} : Finset _).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ planes μ, 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_insert_le _ _ |>.trans (by simp)
    _ = 4 := by simp [planes_card]

omit [NeZero n] in
theorem base_mem (x : SpatialVertex n) (μ : Fin 3) (p : SpatialPlane)
    (hp : p.1.1 = μ ∨ p.1.2 = μ) : (x,p) ∈ affected n x μ := by
  classical
  simp only [affected, Finset.mem_biUnion]
  exact ⟨p, by simpa [planes] using hp, by simp⟩

omit [NeZero n] in
theorem shifted_mem (x : SpatialVertex n) (μ : Fin 3) (p : SpatialPlane)
    (hp : p.1.1 = μ ∨ p.1.2 = μ) :
    (x-Pi.single (transverse μ p) 1,p) ∈ affected n x μ := by
  classical
  simp only [affected, Finset.mem_biUnion]
  exact ⟨p, by simpa [planes] using hp, by simp⟩

variable (G : Type*) [Group G]

omit [NeZero n] in
theorem holonomy_unchanged (x : SpatialVertex n) (μ : Fin 3)
    (p : SpatialVertex n × SpatialPlane) (hp : p ∉ affected n x μ)
    (u u' : SpatialLinks n G) (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    spatialHolonomy u p.1 p.2.1.1 p.2.1.2 = spatialHolonomy u' p.1 p.2.1.1 p.2.1.2 := by
  have h1 : (p.1,p.2.1.1) ≠ (x,μ) := by
    intro he
    have hd := congrArg Prod.snd he
    have hs : p.1 = x := congrArg Prod.fst he
    apply hp
    change (p.1,p.2) ∈ affected n x μ
    rw [hs]
    exact base_mem n x μ p.2 (Or.inl hd)
  have h2 : (spatialStep n p.1 p.2.1.1,p.2.1.2) ≠ (x,μ) := by
    intro he
    have hd : p.2.1.2 = μ := congrArg Prod.snd he
    have hs : p.1 = x-Pi.single p.2.1.1 1 := eq_sub_iff_add_eq.mpr (congrArg Prod.fst he)
    have hn : p.2.1.1 ≠ μ := by rw [← hd]; exact ne_of_lt p.2.2
    have ht : transverse μ p.2 = p.2.1.1 := by simp [transverse, hn]
    have hm := shifted_mem n x μ p.2 (Or.inr hd)
    rw [ht, ← hs] at hm
    exact hp hm
  have h3 : (spatialStep n p.1 p.2.1.2,p.2.1.1) ≠ (x,μ) := by
    intro he
    have hd : p.2.1.1 = μ := congrArg Prod.snd he
    have hs : p.1 = x-Pi.single p.2.1.2 1 := eq_sub_iff_add_eq.mpr (congrArg Prod.fst he)
    have ht : transverse μ p.2 = p.2.1.2 := by simp [transverse, hd]
    have hm := shifted_mem n x μ p.2 (Or.inl hd)
    rw [ht, ← hs] at hm
    exact hp hm
  have h4 : (p.1,p.2.1.2) ≠ (x,μ) := by
    intro he
    have hd := congrArg Prod.snd he
    have hs : p.1 = x := congrArg Prod.fst he
    apply hp
    change (p.1,p.2) ∈ affected n x μ
    rw [hs]
    exact base_mem n x μ p.2 (Or.inr hd)
  unfold spatialHolonomy
  rw [hu _ h1, hu _ h2, hu _ h3, hu _ h4]

theorem potential_oscillation (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x,μ) → u e = u' e) : |potential χ c u-potential χ c u'| ≤ 8*B := by
  classical
  let diff : SpatialVertex n × SpatialPlane → ℝ := fun p =>
    (χ (spatialHolonomy u' p.1 p.2.1.1 p.2.1.2)).re-
      (χ (spatialHolonomy u p.1 p.2.1.1 p.2.1.2)).re
  have he : potential χ c u-potential χ c u' = ∑ p, diff p := by
    unfold potential
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [diff]
    ring
  have hd0 (p : SpatialVertex n × SpatialPlane) (hp : p ∉ affected n x μ) : diff p = 0 := by
    have hh := holonomy_unchanged n G x μ p hp u u' hu
    dsimp [diff]
    rw [hh, sub_self]
  have hs : (∑ p, diff p) = ∑ p ∈ affected n x μ, diff p := by
    symm
    exact Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => hd0 p hp)
  have hd (p : SpatialVertex n × SpatialPlane) : |diff p| ≤ 2*B := by
    have h1 := (Complex.abs_re_le_norm (χ (spatialHolonomy u' p.1 p.2.1.1 p.2.1.2))).trans (hχ _)
    have h2 := (Complex.abs_re_le_norm (χ (spatialHolonomy u p.1 p.2.1.1 p.2.1.2))).trans (hχ _)
    exact (abs_sub _ _).trans (by linarith)
  rw [he,hs]
  calc
    _ ≤ ∑ p ∈ affected n x μ, |diff p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ affected n x μ, 2*B := Finset.sum_le_sum (fun p _ => hd p)
    _ = ((affected n x μ).card : ℝ)*(2*B) := by simp
    _ ≤ 8*B := by
      have hc : ((affected n x μ).card : ℝ) ≤ 4 := by exact_mod_cast affected_card n x μ
      nlinarith

/-- The half spatial action contributes four, rather than eight, units of
|beta|*B to a single-link ratio. -/
theorem spatialWeight_comparison (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    spatialWeight χ β c u ≤ Real.exp (4 * |β| * B) * spatialWeight χ β c u' := by
  have hp := potential_oscillation n G χ B hB hχ c x μ u u' hu
  have hd : |-(β/2)*(potential χ c u-potential χ c u')| ≤ 4 * |β| * B := by
    rw [abs_mul, abs_neg, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ |β|/2)).trans_eq (by ring)
  unfold spatialWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := (le_abs_self (-(β/2)*(potential χ c u-potential χ c u'))).trans hd
  nlinarith

theorem temporalAction_oscillation (χ : G → ℂ) (B : ℝ) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' v : SpatialLinks n G)
    (h : SliceGauge n G) (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    |temporalAction χ c u v h-temporalAction χ c u' v h| ≤ 2*B := by
  classical
  let diff : SpatialVertex n × Fin 3 → ℝ := fun e =>
    (χ (temporalHolonomy u' v h e.1 e.2)).re-(χ (temporalHolonomy u v h e.1 e.2)).re
  have he : temporalAction χ c u v h-temporalAction χ c u' v h = ∑ e, diff e := by
    unfold temporalAction
    rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [diff]
    ring
  have hs : (∑ e, diff e) = diff (x,μ) := by
    apply Finset.sum_eq_single (x,μ)
    · intro e _ he
      dsimp [diff, temporalHolonomy]
      rw [hu e he, sub_self]
    · simp
  rw [he,hs]
  have h1 := (Complex.abs_re_le_norm (χ (temporalHolonomy u' v h x μ))).trans (hχ _)
  have h2 := (Complex.abs_re_le_norm (χ (temporalHolonomy u v h x μ))).trans (hχ _)
  exact (abs_sub _ _).trans (by linarith)

theorem slabAction_oscillation (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' v : SpatialLinks n G)
    (h : SliceGauge n G) (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    |slabAction χ β c u v h-slabAction χ β c u' v h| ≤ 6 * |β| * B := by
  have hp := potential_oscillation n G χ B hB hχ c x μ u u' hu
  have ht := temporalAction_oscillation n G χ B hχ c x μ u u' v h hu
  have he : slabAction χ β c u v h-slabAction χ β c u' v h =
      β*((potential χ c u-potential χ c u')/2+
        (temporalAction χ c u v h-temporalAction χ c u' v h)) := by unfold slabAction; ring
  rw [he, abs_mul]
  have hb : |(potential χ c u-potential χ c u')/2+
      (temporalAction χ c u v h-temporalAction χ c u' v h)| ≤ 6*B := by
    apply (abs_add_le _ _).trans
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg β)).trans_eq (by ring)

theorem boltzmann_comparison (χ : G → ℂ) (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' v : SpatialLinks n G)
    (h : SliceGauge n G) (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    Real.exp (-slabAction χ β c u v h) ≤
      Real.exp (6 * |β| * B) * Real.exp (-slabAction χ β c u' v h) := by
  have hh := slabAction_oscillation n G χ B hB hχ β c x μ u u' v h hu
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := neg_le_abs (slabAction χ β c u v h-slabAction χ β c u' v h)
  linarith

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- A pointwise ratio bound independent of spatial volume, the other slice,
temporal links and the additive plaquette offset. -/
theorem kernel_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (x : SpatialVertex n) (μ : Fin 3) (u u' v : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    kernel χ β c u v ≤ Real.exp (6 * |β| * B) * kernel χ β c u' v := by
  have hi (w : SpatialLinks n G) :
      Integrable (fun h : SliceGauge n G => Real.exp (-slabAction χ β c w v h)) temporalHaar := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold slabAction temporalAction temporalHolonomy
    fun_prop
  have hh := integral_mono (hi u) ((hi u').const_mul (Real.exp (6 * |β| * B)))
    (fun h => boltzmann_comparison n G χ B hB hχ β c x μ u u' v h hu)
  rw [integral_const_mul] at hh
  exact hh

/-- Any supplied continuous nonnegative positive-eigenvalue eigenfunction
inherits the actual kernel comparison. This theorem does not construct one. -/
theorem eigenfunction_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (σ : Measure (SpatialLinks n G)) [IsFiniteMeasure σ]
    (ψ : SpatialLinks n G → ℝ) (hcψ : Continuous ψ) (hψ : ∀ v, 0 ≤ ψ v)
    (ell : ℝ) (hell : 0 < ell)
    (heig : ∀ u, (∫ v, kernel χ β c u v * ψ v ∂σ) = ell*ψ u)
    (x : SpatialVertex n) (μ : Fin 3) (u u' : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    ψ u ≤ Real.exp (6 * |β| * B) * ψ u' := by
  have hi (w : SpatialLinks n G) : Integrable (fun v => kernel χ β c w v * ψ v) σ := by
    have hc : Continuous (fun v => kernel χ β c w v * ψ v) :=
      ((kernel_continuous χ hcχ β c).comp (continuous_const.prodMk continuous_id)).mul hcψ
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono (hi u) ((hi u').const_mul (Real.exp (6 * |β| * B))) (fun v => by
    have hk := mul_le_mul_of_nonneg_right
      (kernel_comparison n G χ hcχ B hB hχ β c x μ u u' v hu) (hψ v)
    simpa only [mul_assoc] using hk)
  rw [integral_const_mul, heig u, heig u'] at hh
  apply (mul_le_mul_iff_right₀ hell).mp
  convert hh using 1
  ring

/-- The kinetic-weighted eigenfunction eta=w*psi has single-link ratio
at most exp(10*|beta|*B), still independent of spatial volume. -/
theorem weighted_eigenfunction_comparison (χ : G → ℂ) (hcχ : Continuous χ)
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ g, ‖χ g‖ ≤ B)
    (β c : ℝ) (σ : Measure (SpatialLinks n G)) [IsFiniteMeasure σ]
    (ψ : SpatialLinks n G → ℝ) (hcψ : Continuous ψ) (hψ : ∀ v, 0 ≤ ψ v)
    (ell : ℝ) (hell : 0 < ell)
    (heig : ∀ u, (∫ v, kernel χ β c u v * ψ v ∂σ) = ell*ψ u)
    (x : SpatialVertex n) (μ : Fin 3) (u u' : SpatialLinks n G)
    (hu : ∀ e, e ≠ (x,μ) → u e = u' e) :
    spatialWeight χ β c u * ψ u ≤
      Real.exp (10 * |β| * B) * (spatialWeight χ β c u' * ψ u') := by
  have hw := spatialWeight_comparison n G χ B hB hχ β c x μ u u' hu
  have hp := eigenfunction_comparison n G χ hcχ B hB hχ β c σ ψ hcψ hψ ell hell heig x μ u u' hu
  have hh := mul_le_mul hw hp (hψ u)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  apply hh.trans_eq
  rw [show 10 * |β| * B = 4 * |β| * B + 6 * |β| * B by ring, Real.exp_add]
  ring

end
end UnifiedTheory.Clay.YangMills.WilsonSlabLocalComparison
