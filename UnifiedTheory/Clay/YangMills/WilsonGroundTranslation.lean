/- Spatial homogeneity of the actual positive Wilson vacuum and ground slab.
The local temporal-energy estimate has no spatial-volume factor. It is an
absolute energy bound, not a relative continuum survival or mass-gap bound. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundSlabEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonGroundTranslation
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonGroundLocalComparison
open WilsonSingleLinkStaples WilsonGroundSlabEnergy
open scoped NNReal

variable (n : ℕ) [NeZero n]

local instance slabBorel : BorelSpace (Slab n) := Prod.borelSpace

def shiftSlice (s : SpatialVertex n) (u : Slice n) : Slice n :=
  fun e => u (e.1 + s, e.2)

def shiftGauge (s : SpatialVertex n) (h : SliceGauge n WilsonSlabOperator.Q) :
    SliceGauge n WilsonSlabOperator.Q := fun x => h (x + s)

def sliceEquiv (s : SpatialVertex n) : Slice n ≃ᵐ Slice n :=
  MeasurableEquiv.piCongrLeft (fun _ : SpatialVertex n × Fin 3 => WilsonSlabOperator.Q)
    (Equiv.prodCongr (Equiv.addRight s) (Equiv.refl (Fin 3))).symm

def gaugeEquiv (s : SpatialVertex n) :
    SliceGauge n WilsonSlabOperator.Q ≃ᵐ SliceGauge n WilsonSlabOperator.Q :=
  MeasurableEquiv.piCongrLeft (fun _ : SpatialVertex n => WilsonSlabOperator.Q)
    (Equiv.addRight s).symm

omit [NeZero n] in
theorem sliceEquiv_apply (s : SpatialVertex n) (u : Slice n) :
    sliceEquiv n s u = shiftSlice n s u := by
  funext e
  simp [sliceEquiv, shiftSlice, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rfl

omit [NeZero n] in
theorem gaugeEquiv_apply (s : SpatialVertex n) (h : SliceGauge n WilsonSlabOperator.Q) :
    gaugeEquiv n s h = shiftGauge n s h := by
  funext x
  simp [gaugeEquiv, shiftGauge, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem slice_preserving (s : SpatialVertex n) :
    MeasurePreserving (sliceEquiv n s) (measure n) (measure n) :=
  measurePreserving_piCongrLeft
    (fun _ : SpatialVertex n × Fin 3 => RegulatedGauge.compactHaar WilsonSlabOperator.Q)
    (Equiv.prodCongr (Equiv.addRight s) (Equiv.refl (Fin 3))).symm

theorem gauge_preserving (s : SpatialVertex n) :
    MeasurePreserving (gaugeEquiv n s) temporalHaar temporalHaar :=
  measurePreserving_piCongrLeft
    (fun _ : SpatialVertex n => RegulatedGauge.compactHaar WilsonSlabOperator.Q)
    (Equiv.addRight s).symm

theorem slice_integral (s : SpatialVertex n) (F : Slice n → ℝ) :
    (∫ u, F (shiftSlice n s u) ∂measure n) = ∫ u, F u ∂measure n := by
  simpa only [sliceEquiv_apply] using (slice_preserving n s).integral_comp' F

theorem gauge_integral (s : SpatialVertex n) (F : SliceGauge n WilsonSlabOperator.Q → ℝ) :
    (∫ h, F (shiftGauge n s h) ∂temporalHaar) = ∫ h, F h ∂temporalHaar := by
  simpa only [gaugeEquiv_apply] using (gauge_preserving n s).integral_comp' F

omit [NeZero n] in
theorem shiftSlice_continuous (s : SpatialVertex n) : Continuous (shiftSlice n s) :=
  continuous_pi (fun _ => continuous_apply _)

omit [NeZero n] in
theorem shiftGauge_continuous (s : SpatialVertex n) : Continuous (shiftGauge n s) :=
  continuous_pi (fun _ => continuous_apply _)

omit [NeZero n] in
theorem step_add (x s : SpatialVertex n) (i : Fin 3) :
    spatialStep n x i + s = spatialStep n (x + s) i := by
  unfold spatialStep
  abel

omit [NeZero n] in
theorem spatialHolonomy_shift (s : SpatialVertex n) (u : Slice n)
    (x : SpatialVertex n) (i j : Fin 3) :
    spatialHolonomy (shiftSlice n s u) x i j = spatialHolonomy u (x+s) i j := by
  simp only [spatialHolonomy, shiftSlice, step_add]

omit [NeZero n] in
theorem temporalHolonomy_shift (s : SpatialVertex n) (u v : Slice n)
    (h : SliceGauge n WilsonSlabOperator.Q) (x : SpatialVertex n) (i : Fin 3) :
    temporalHolonomy (shiftSlice n s u) (shiftSlice n s v) (shiftGauge n s h) x i =
      temporalHolonomy u v h (x+s) i := by
  simp only [temporalHolonomy, shiftSlice, shiftGauge, step_add]

theorem potential_shift (s : SpatialVertex n) (u : Slice n) :
    potential character 2 (shiftSlice n s u) = potential character 2 u := by
  simp only [potential, spatialHolonomy_shift]
  exact Equiv.sum_comp (Equiv.addRight s) (fun x : SpatialVertex n =>
    ∑ p : SpatialPlane, (2 - (character (spatialHolonomy u x p.1.1 p.1.2)).re))

theorem temporalAction_shift (s : SpatialVertex n) (u v : Slice n)
    (h : SliceGauge n WilsonSlabOperator.Q) :
    temporalAction character 2 (shiftSlice n s u) (shiftSlice n s v) (shiftGauge n s h) =
      temporalAction character 2 u v h := by
  simp only [temporalAction, temporalHolonomy_shift]
  exact Equiv.sum_comp (Equiv.addRight s) (fun x : SpatialVertex n =>
    ∑ i : Fin 3, (2 - (character (temporalHolonomy u v h x i)).re))

theorem slabAction_shift (β : ℝ) (s : SpatialVertex n) (u v : Slice n)
    (h : SliceGauge n WilsonSlabOperator.Q) :
    slabAction character β 2 (shiftSlice n s u) (shiftSlice n s v) (shiftGauge n s h) =
      slabAction character β 2 u v h := by
  simp only [slabAction, potential_shift, temporalAction_shift]

theorem kernel_shift (β : ℝ) (s : SpatialVertex n) (u v : Slice n) :
    kernelMap n β (shiftSlice n s u, shiftSlice n s v) = kernelMap n β (u,v) := by
  change (∫ h, Real.exp (-slabAction character β 2 (shiftSlice n s u) (shiftSlice n s v) h)
    ∂temporalHaar) = _
  rw [← gauge_integral n s (fun h =>
    Real.exp (-slabAction character β 2 (shiftSlice n s u) (shiftSlice n s v) h))]
  simp only [slabAction_shift]
  rfl

/-- The chosen normalized positive vacuum inherits actual spatial translation symmetry. -/
theorem ground_shift (β : ℝ) (hβ : 0 ≤ β) (s : SpatialVertex n) (u : Slice n) :
    ground n β hβ (shiftSlice n s u) = ground n β hβ u := by
  let f : C(Slice n,ℝ) := ⟨fun v => ground n β hβ (shiftSlice n s v),
    (ground n β hβ).continuous.comp (shiftSlice_continuous n s)⟩
  have hf (v : Slice n) : (∫ w, kernelMap n β (v,w) * f w ∂measure n) =
      ‖transfer n β‖ * f v := by
    have he := slice_integral n s (fun w =>
      kernelMap n β (shiftSlice n s v,w) * ground n β hβ w)
    simp only [kernel_shift] at he
    exact he.trans (ground_equation n β hβ (shiftSlice n s v))
  obtain ⟨c,hc⟩ := PositiveKernelRatio.real_top_proportional (measure n)
    (kernelMap n β) (ground n β hβ) (ground_pos n β hβ) ‖transfer n β‖
    (Real.exp (-(24 * β * (Fintype.card (SpatialVertex n) : ℝ)))) 1
    (PositiveKernelGroundState.transfer_top_eigenvector n β hβ).1 (Real.exp_pos _)
    (by norm_num) (fun v w => (WilsonSlabBounds.kernel_bounds n β hβ v w).1)
    (fun v w => (WilsonSlabBounds.kernel_bounds n β hβ v w).2)
    (ground_equation n β hβ) f hf
  have hi : (∫ v, ground n β hβ v ∂measure n) =
      c * (∫ v, ground n β hβ v ∂measure n) := by
    calc
      _ = ∫ v, ground n β hβ (shiftSlice n s v) ∂measure n :=
        (slice_integral n s (ground n β hβ)).symm
      _ = ∫ v, c * ground n β hβ v ∂measure n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hc
      _ = _ := integral_const_mul _ _
  have hpos : 0 < ∫ v, ground n β hβ v ∂measure n :=
    WilsonVacuumConvergence.overlap_pos n β hβ
  have hc1 : c = 1 := mul_right_cancel₀ hpos.ne' (by simpa using hi.symm)
  have h := hc u
  simpa only [f, ContinuousMap.coe_mk, hc1, one_mul] using h

def slabShift (s : SpatialVertex n) (z : Slab n) : Slab n :=
  ((shiftSlice n s z.1.1,shiftSlice n s z.1.2),shiftGauge n s z.2)

def slabEquiv (s : SpatialVertex n) : Slab n ≃ᵐ Slab n :=
  ((sliceEquiv n s).prodCongr (sliceEquiv n s)).prodCongr (gaugeEquiv n s)

omit [NeZero n] in
theorem slabEquiv_apply (s : SpatialVertex n) (z : Slab n) :
    slabEquiv n s z = slabShift n s z := by
  change (((sliceEquiv n s) z.1.1, (sliceEquiv n s) z.1.2),
    (gaugeEquiv n s) z.2) = _
  rw [sliceEquiv_apply, sliceEquiv_apply, gaugeEquiv_apply]
  rfl

theorem reference_preserving (s : SpatialVertex n) :
    MeasurePreserving (slabEquiv n s) (reference n) (reference n) :=
  ((slice_preserving n s).prod (slice_preserving n s)).prod (gauge_preserving n s)

theorem energy_shift (s : SpatialVertex n) (z : Slab n) :
    energy n (slabShift n s z) = energy n z :=
  slabAction_shift n 1 s z.1.1 z.1.2 z.2

theorem weight_shift (β : ℝ) (hβ : 0 ≤ β) (s : SpatialVertex n) (z : Slab n) :
    weight n β hβ (slabShift n s z) = weight n β hβ z := by
  change ground n β hβ (shiftSlice n s z.1.1) *
    ground n β hβ (shiftSlice n s z.1.2) * Real.exp (-(β * energy n (slabShift n s z))) = _
  rw [ground_shift, ground_shift, energy_shift]
  rfl

/-- Translation invariance holds for the original ground-weighted slab law. -/
theorem law_integral_shift (β : ℝ) (hβ : 0 ≤ β) (s : SpatialVertex n) (F : Slab n → ℝ) :
    (∫ z, F (slabShift n s z) ∂law n β hβ) = ∫ z, F z ∂law n β hβ := by
  rw [law_integral, law_integral]
  congr 1
  have he := (reference_preserving n s).integral_comp' (fun z => weight n β hβ z * F z)
  simpa only [slabEquiv_apply, weight_shift] using he

def temporalDefect (x : SpatialVertex n) (i : Fin 3) (z : Slab n) : ℝ :=
  2 - (character (temporalHolonomy z.1.1 z.1.2 z.2 x i)).re

omit [NeZero n] in
theorem temporalDefect_continuous (x : SpatialVertex n) (i : Fin 3) :
    Continuous (temporalDefect n x i) := by
  unfold temporalDefect temporalHolonomy
  have hc : Continuous character := character_continuous
  fun_prop

omit [NeZero n] in
theorem temporalDefect_nonneg (x : SpatialVertex n) (i : Fin 3) (z : Slab n) :
    0 ≤ temporalDefect n x i z := by
  have h := Complex.re_le_norm (character (temporalHolonomy z.1.1 z.1.2 z.2 x i))
  have hb := character_bound (temporalHolonomy z.1.1 z.1.2 z.2 x i)
  unfold temporalDefect
  linarith

omit [NeZero n] in
theorem temporalDefect_shift (s x : SpatialVertex n) (i : Fin 3) (z : Slab n) :
    temporalDefect n x i (slabShift n s z) = temporalDefect n (x+s) i z := by
  simp only [temporalDefect, slabShift, temporalHolonomy_shift]

theorem temporal_mean_eq (β : ℝ) (hβ : 0 ≤ β) (x y : SpatialVertex n) (i : Fin 3) :
    (∫ z, temporalDefect n x i z ∂law n β hβ) =
      ∫ z, temporalDefect n y i z ∂law n β hβ := by
  have h := law_integral_shift n β hβ (y-x) (temporalDefect n x i)
  simp only [temporalDefect_shift, show x + (y-x) = y by abel] at h
  exact h.symm

/-- All translates of one temporal orientation are paid for by the actual slab energy. -/
theorem temporal_sum_le_energy (i : Fin 3) (z : Slab n) :
    (∑ x : SpatialVertex n, temporalDefect n x i z) ≤ energy n z := by
  have hs : (∑ x : SpatialVertex n, temporalDefect n x i z) ≤
      temporalAction character 2 z.1.1 z.1.2 z.2 := by
    apply Finset.sum_le_sum
    intro x _
    exact Finset.single_le_sum
      (fun j _ => temporalDefect_nonneg n x j z) (Finset.mem_univ i)
  have hu := (WilsonSlabBounds.potential_bounds n z.1.1).1
  have hv := (WilsonSlabBounds.potential_bounds n z.1.2).1
  unfold energy slabAction
  simp only [one_mul]
  linarith

/-- A local temporal plaquette costs at most six times the mean slab energy density.
The spatial-volume factor cancels through proved vacuum translation symmetry. -/
theorem temporal_mean_le_density (β : ℝ) (hβ : 0 ≤ β)
    (x : SpatialVertex n) (i : Fin 3) :
    (∫ z, temporalDefect n x i z ∂law n β hβ) ≤
      (∫ z, energy n z ∂law n β hβ) / (Fintype.card (SpatialVertex n) : ℝ) := by
  have hi (y : SpatialVertex n) : Integrable (temporalDefect n y i) (law n β hβ) :=
    (temporalDefect_continuous n y i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs := integral_mono (integrable_finset_sum _ (fun y _ => hi y))
    ((energy_continuous n).integrable_of_hasCompactSupport
      (μ := law n β hβ) (HasCompactSupport.of_compactSpace _))
    (temporal_sum_le_energy n i)
  rw [integral_finset_sum _ (fun y _ => hi y)] at hs
  have he : (∑ y : SpatialVertex n, ∫ z, temporalDefect n y i z ∂law n β hβ) =
      (Fintype.card (SpatialVertex n) : ℝ) *
        (∫ z, temporalDefect n x i z ∂law n β hβ) := by
    simp_rw [temporal_mean_eq n β hβ _ x i]
    simp
  rw [he] at hs
  apply (le_div_iff₀ (by positivity : 0 < (Fintype.card (SpatialVertex n) : ℝ))).mpr
  simpa only [mul_comm] using hs

/-- An actual local weak-coupling bound independent of spatial volume. -/
theorem temporal_mean_bound (β : ℝ) (hβ : 0 < β)
    (x : SpatialVertex n) (i : Fin 3) :
    (∫ z, temporalDefect n x i z ∂law n β hβ.le) ≤ 6 * envelope β := by
  have hm := temporal_mean_le_density n β hβ.le x i
  have he := energy_density_bound n β hβ
  have hv : 0 < (Fintype.card (SpatialVertex n) : ℝ) := by positivity
  have he' := (div_le_iff₀ (by positivity : 0 < 6 * (Fintype.card (SpatialVertex n) : ℝ))).mp he
  apply hm.trans
  apply (div_le_iff₀ hv).mpr
  nlinarith

omit n [NeZero n] in
/-- Local temporal defects vanish uniformly along changing spatial regulators. -/
theorem temporal_mean_tendsto {ι : Type*} {l : Filter ι}
    (N : ι → ℕ) [∀ k, NeZero (N k)] (β : ι → ℝ≥0)
    (hβ : Filter.Tendsto (fun k => (β k : ℝ)) l Filter.atTop)
    (x : ∀ k, SpatialVertex (N k)) (i : ι → Fin 3) :
    Filter.Tendsto (fun k => ∫ z, temporalDefect (N k) (x k) (i k) z
      ∂law (N k) (β k) (β k).coe_nonneg) l (nhds 0) := by
  have he := (envelope_tendsto.comp hβ).const_mul 6
  simp only [mul_zero] at he
  apply squeeze_zero' _ _ he
  · exact Filter.Eventually.of_forall (fun k =>
      integral_nonneg (temporalDefect_nonneg (N k) (x k) (i k)))
  · filter_upwards [hβ.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with k hk
    exact temporal_mean_bound (N k) (β k) hk (x k) (i k)

end
end UnifiedTheory.Clay.YangMills.WilsonGroundTranslation
