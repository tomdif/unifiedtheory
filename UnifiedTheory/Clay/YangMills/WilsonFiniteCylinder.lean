/- A genuine open Wilson time cylinder of arbitrary temporal length, with
fixed spatial period. All temporal links are independently Haar integrated.
Full spatial endpoint actions produce explicit spatialWeight boundary factors;
the sum-of-slabs convention instead has constant boundary one. -/
import UnifiedTheory.Clay.YangMills.WilsonSlabGauge
import UnifiedTheory.Clay.YangMills.GibbsMarginalTower
import Mathlib.MeasureTheory.Integral.Pi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonFiniteCylinder
noncomputable section
open MeasureTheory WilsonTimeSlab

abbrev Slices (n : ℕ) (G : Type*) (L : ℕ) := Fin (L + 1) → SpatialLinks n G
abbrev TemporalLinks (n : ℕ) (G : Type*) (L : ℕ) := Fin L → SliceGauge n G

variable {n : ℕ} [NeZero n] {G : Type*} [Group G]

/-- Every spatial slice has its full potential, including both endpoints. -/
def fullAction (χ : G → ℂ) (β c : ℝ) (L : ℕ)
    (U : Slices n G L) (h : TemporalLinks n G L) : ℝ :=
  β * ((∑ t, potential χ c (U t)) +
    ∑ t : Fin L, temporalAction χ c (U t.castSucc) (U t.succ) (h t))

/-- The transfer convention gives half of the spatial action to each adjacent slab. -/
def halfAction (χ : G → ℂ) (β c : ℝ) (L : ℕ)
    (U : Slices n G L) (h : TemporalLinks n G L) : ℝ :=
  ∑ t : Fin L, slabAction χ β c (U t.castSucc) (U t.succ) (h t)

/-- The spatial endpoint correction is exact, including the zero-length case. -/
theorem fullAction_eq (χ : G → ℂ) (β c : ℝ) (L : ℕ)
    (U : Slices n G L) (h : TemporalLinks n G L) :
    fullAction χ β c L U h = halfAction χ β c L U h +
      (β / 2) * (potential χ c (U 0) + potential χ c (U (Fin.last L))) := by
  have hzero := Fin.sum_univ_succ (fun t : Fin (L + 1) => potential χ c (U t))
  have hlast := Fin.sum_univ_castSucc (fun t : Fin (L + 1) => potential χ c (U t))
  have hs : (∑ t : Fin (L + 1), potential χ c (U t)) =
      (potential χ c (U 0) + potential χ c (U (Fin.last L))) / 2 +
        ((∑ t : Fin L, potential χ c (U t.castSucc)) +
          ∑ t : Fin L, potential χ c (U t.succ)) / 2 := by linarith
  unfold fullAction halfAction
  simp only [slabAction, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hs]
  ring

theorem half_boltzmann_product (χ : G → ℂ) (β c : ℝ) (L : ℕ)
    (U : Slices n G L) (h : TemporalLinks n G L) :
    Real.exp (-halfAction χ β c L U h) =
      ∏ t : Fin L, Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) (h t)) := by
  rw [halfAction, ← Finset.sum_neg_distrib, Real.exp_sum]

/-- Actual Wilson weight with full endpoint potentials, not substituted ground-state boundaries. -/
theorem full_boltzmann_product (χ : G → ℂ) (β c : ℝ) (L : ℕ)
    (U : Slices n G L) (h : TemporalLinks n G L) :
    Real.exp (-fullAction χ β c L U h) =
      spatialWeight χ β c (U 0) *
        (∏ t : Fin L, Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) (h t))) *
          spatialWeight χ β c (U (Fin.last L)) := by
  rw [fullAction_eq, neg_add, Real.exp_add, half_boltzmann_product]
  have he : Real.exp (-(β / 2 *
      (potential χ c (U 0) + potential χ c (U (Fin.last L))))) =
      spatialWeight χ β c (U 0) * spatialWeight χ β c (U (Fin.last L)) := by
    unfold spatialWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance slicesBorel (L : ℕ) : BorelSpace (Slices n G L) := Pi.borelSpace
local instance temporalLinksBorel (L : ℕ) : BorelSpace (TemporalLinks n G L) := Pi.borelSpace
local instance cylinderBorel (L : ℕ) : BorelSpace (Slices n G L × TemporalLinks n G L) :=
  Prod.borelSpace

/-- Independent normalized spatial Haar measures, one for each time slice. -/
abbrev slicesHaar (L : ℕ) : Measure (Slices n G L) :=
  Measure.pi (fun _ : Fin (L + 1) => WilsonSlabGauge.spatialHaar)

/-- Independent temporal gauge variables on each of the L temporal bonds. -/
abbrev temporalLinksHaar (L : ℕ) : Measure (TemporalLinks n G L) :=
  Measure.pi (fun _ : Fin L => (temporalHaar (n := n) (G := G)))

def transferProduct (χ : G → ℂ) (β c : ℝ) (L : ℕ) (U : Slices n G L) : ℝ :=
  ∏ t : Fin L, kernel χ β c (U t.castSucc) (U t.succ)

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem spatialWeight_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    Continuous (spatialWeight (n := n) χ β c) := by
  unfold spatialWeight potential spatialHolonomy
  fun_prop

theorem transferProduct_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) (L : ℕ) :
    Continuous (transferProduct (n := n) χ β c L) := by
  have hK : Continuous (fun uv : SpatialLinks n G × SpatialLinks n G =>
      kernel χ β c uv.1 uv.2) := kernel_continuous χ hχ β c
  have ht (t : Fin L) : Continuous (fun U : Slices n G L =>
      kernel χ β c (U t.castSucc) (U t.succ)) :=
    hK.comp (f := fun U : Slices n G L => (U t.castSucc, U t.succ))
      ((continuous_apply t.castSucc).prodMk (continuous_apply t.succ))
  exact continuous_finset_prod Finset.univ (fun t _ => ht t)

/-- The half-endpoint convention integrates to the product of genuine full slab kernels. -/
theorem temporal_integral_half (χ : G → ℂ) (β c : ℝ) (L : ℕ) (U : Slices n G L) :
    (∫ h, Real.exp (-halfAction χ β c L U h) ∂temporalLinksHaar L) =
      transferProduct χ β c L U := by
  have hp := integral_fintype_prod_eq_prod (ι := Fin L)
    (E := fun _ => SliceGauge n G) (𝕜 := ℝ)
    (μ := fun _ : Fin L => (temporalHaar (n := n) (G := G)))
    (fun t h => Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) h))
  change (∫ h, ∏ t : Fin L,
    Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) (h t))
      ∂temporalLinksHaar L) = transferProduct χ β c L U at hp
  simpa only [half_boltzmann_product] using hp

/-- Integrating all temporal links leaves the exact full-endpoint boundary factors. -/
theorem temporal_integral_full (χ : G → ℂ) (β c : ℝ) (L : ℕ) (U : Slices n G L) :
    (∫ h, Real.exp (-fullAction χ β c L U h) ∂temporalLinksHaar L) =
      spatialWeight χ β c (U 0) * transferProduct χ β c L U *
        spatialWeight χ β c (U (Fin.last L)) := by
  simp_rw [full_boltzmann_product]
  rw [integral_mul_const, integral_const_mul]
  have hp := integral_fintype_prod_eq_prod (ι := Fin L) (E := fun _ => SliceGauge n G) (𝕜 := ℝ)
    (μ := fun _ : Fin L => (temporalHaar (n := n) (G := G)))
    (fun t h => Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) h))
  change (∫ h, ∏ t : Fin L,
    Real.exp (-slabAction χ β c (U t.castSucc) (U t.succ) (h t))
      ∂temporalLinksHaar L) = transferProduct χ β c L U at hp
  rw [hp]

/-- Joint Haar measure on the actual spatial and temporal links of the cylinder. -/
abbrev cylinderHaar (L : ℕ) : Measure (Slices n G L × TemporalLinks n G L) :=
  (slicesHaar L).prod (temporalLinksHaar L)

omit [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] in
theorem fullAction_continuous (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) (L : ℕ) :
    Continuous (fun z : Slices n G L × TemporalLinks n G L => fullAction χ β c L z.1 z.2) := by
  unfold fullAction potential spatialHolonomy temporalAction temporalHolonomy
  fun_prop

/-- The genuine cylinder observable integral reduces to the transfer-product integral. -/
theorem full_integral (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) (L : ℕ)
    (F : C(Slices n G L, ℝ)) :
    (∫ z, Real.exp (-fullAction χ β c L z.1 z.2) * F z.1 ∂cylinderHaar (n := n) (G := G) L) =
      ∫ U, (spatialWeight χ β c (U 0) * transferProduct χ β c L U *
        spatialWeight χ β c (U (Fin.last L))) * F U ∂slicesHaar (n := n) (G := G) L := by
  have hc : Continuous (fun z : Slices n G L × TemporalLinks n G L =>
      Real.exp (-fullAction χ β c L z.1 z.2) * F z.1) :=
    (Real.continuous_exp.comp (fullAction_continuous χ hχ β c L).neg).mul
      (F.continuous.comp continuous_fst)
  rw [integral_prod _ (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [integral_mul_const, temporal_integral_full]

/-- The normalized actual open-cylinder Wilson law, before temporal variables are integrated. -/
def law (χ : G → ℂ) (β c : ℝ) (L : ℕ) :
    Measure (Slices n G L × TemporalLinks n G L) :=
  CompactGibbsContinuity.law (cylinderHaar L) (fun z => fullAction χ β c L z.1 z.2)

theorem law_probability (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) (L : ℕ) :
    IsProbabilityMeasure (law (n := n) χ β c L) :=
  CompactGibbsContinuity.law_probability _ _ (fullAction_continuous χ hχ β c L)

/-- Normalized cylinder expectations have the proved transfer-product numerator and partition. -/
theorem law_integral (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) (L : ℕ)
    (F : C(Slices n G L, ℝ)) :
    (∫ z, F z.1 ∂law χ β c L) =
      (∫ U, (spatialWeight χ β c (U 0) * transferProduct χ β c L U *
        spatialWeight χ β c (U (Fin.last L))) * F U ∂slicesHaar (n := n) (G := G) L) /
      (∫ U, spatialWeight χ β c (U 0) * transferProduct χ β c L U *
        spatialWeight χ β c (U (Fin.last L)) ∂slicesHaar (n := n) (G := G) L) := by
  have hc : Continuous (fun z : Slices n G L × TemporalLinks n G L =>
      Real.exp (-fullAction χ β c L z.1 z.2)) :=
    Real.continuous_exp.comp (fullAction_continuous (n := n) χ hχ β c L).neg
  have hpos := CompactGibbsContinuity.partition_positive (cylinderHaar (n := n) (G := G) L)
    (fun z => fullAction χ β c L z.1 z.2) (fullAction_continuous χ hχ β c L)
  have hden := full_integral χ hχ β c L (1 : C(Slices n G L, ℝ))
  simp only [ContinuousMap.one_apply, mul_one] at hden
  change (∫ z, F z.1 ∂LocalGibbsComparison.weightedLaw (cylinderHaar L)
    (fun z => Real.exp (-fullAction χ β c L z.1 z.2))) = _
  rw [LocalGibbsComparison.weighted_integral _ _ hc.measurable
    (fun _ => (Real.exp_pos _).le) hpos, full_integral χ hχ β c L F, hden]

end
end UnifiedTheory.Clay.YangMills.WilsonFiniteCylinder
