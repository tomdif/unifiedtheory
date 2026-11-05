/- Exact separation of center-even and center-odd physical directions.
The odd sector has coercivity with constant 1/4 for the global twist
response. The even sector and comparison with transfer loss remain. -/
import UnifiedTheory.Clay.YangMills.WilsonCenterTwist

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonCenterCoercivity
noncomputable section
open MeasureTheory WilsonTimeSlab WilsonSlabOperator WilsonCenterTwist
open WilsonGroundHeatBath WilsonPhysicalVariance WilsonHighFieldDecay
open CompactDensityEntropy

variable (n : ℕ) [NeZero n]

def pull (i : Fin 3) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  WilsonRawSymmetry.pull n (symmetry n i) f

theorem pull_apply (i : Fin 3) (f : C(Slice n, ℝ)) (u : Slice n) :
    pull n i f u = f (twist n i u) := rfl

def evenPart (i : Fin 3) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  (1 / 2 : ℝ) • (f + pull n i f)

def oddPart (i : Fin 3) (f : C(Slice n, ℝ)) : C(Slice n, ℝ) :=
  (1 / 2 : ℝ) • (f - pull n i f)

theorem parts_sum (i : Fin 3) (f : C(Slice n, ℝ)) : evenPart n i f + oddPart n i f = f := by
  ext u
  simp only [evenPart, oddPart, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem even_parity (i : Fin 3) (f : C(Slice n, ℝ)) (u : Slice n) :
    evenPart n i f (twist n i u) = evenPart n i f u := by
  simp only [evenPart, ContinuousMap.smul_apply, ContinuousMap.add_apply, pull_apply,
    twist_involution, smul_eq_mul, add_comm]

theorem odd_parity (i : Fin 3) (f : C(Slice n, ℝ)) (u : Slice n) :
    oddPart n i f (twist n i u) = -oddPart n i f u := by
  simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.sub_apply, pull_apply,
    twist_involution, smul_eq_mul]
  ring

theorem parts_gauge (i : Fin 3) (f : C(Slice n, ℝ))
    (hf : ∀ h u, f (gaugeSlice h u) = f u) (h : SliceGauge n Q) (u : Slice n) :
    evenPart n i f (gaugeSlice h u) = evenPart n i f u ∧
      oddPart n i f (gaugeSlice h u) = oddPart n i f u := by
  simp only [evenPart, oddPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
    ContinuousMap.sub_apply, pull_apply, twist_gauge, hf, and_self]

/-- Conditioning by any twist-invariant weight retains exact odd cancellation. -/
theorem weighted_odd_mean (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (W F : Slice n → ℝ) (hW : ∀ u, W (twist n i u) = W u)
    (hF : ∀ u, F (twist n i u) = -F u) :
    (∫ u, W u * F u ∂groundLaw n β hβ) = 0 := by
  have hh := ground_integral n i β hβ (fun u => W u * F u)
  simp only [hW, hF, mul_neg, integral_neg] at hh
  linarith

theorem odd_mean (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) :
    (∫ u, f u ∂groundLaw n β hβ) = 0 := by
  simpa only [one_mul] using weighted_odd_mean n i β hβ (fun _ => 1) f (fun _ => rfl) hf

theorem even_mean (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, evenPart n i f u ∂groundLaw n β hβ) = ∫ u, f u ∂groundLaw n β hβ := by
  letI := groundLaw_probability n β hβ
  have hh := integral_add (continuous_integrable (groundLaw n β hβ) _
    (evenPart n i f).continuous) (continuous_integrable (groundLaw n β hβ) _
      (oddPart n i f).continuous)
  change (∫ u, (evenPart n i f + oddPart n i f) u ∂groundLaw n β hβ) = _ at hh
  rw [parts_sum, odd_mean n i β hβ _ (odd_parity n i f), add_zero] at hh
  exact hh.symm

theorem parts_orthogonal (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    (∫ u, evenPart n i f u * oddPart n i f u ∂groundLaw n β hβ) = 0 :=
  weighted_odd_mean n i β hβ _ _ (even_parity n i f) (odd_parity n i f)

theorem mass_split (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    mass n β hβ f = mass n β hβ (evenPart n i f) + mass n β hβ (oddPart n i f) := by
  letI := groundLaw_probability n β hβ
  have he := continuous_integrable (groundLaw n β hβ) _ ((evenPart n i f).continuous.pow 2)
  have ho := continuous_integrable (groundLaw n β hβ) _ ((oddPart n i f).continuous.pow 2)
  have hc := continuous_integrable (groundLaw n β hβ) _
    ((evenPart n i f).continuous.mul (oddPart n i f).continuous)
  have hh (u : Slice n) : (f u)^2 = (evenPart n i f u)^2 + (oddPart n i f u)^2 +
      2 * (evenPart n i f u * oddPart n i f u) := by
    have hs := congrArg (fun F : C(Slice n, ℝ) => F u) (parts_sum n i f)
    change evenPart n i f u + oddPart n i f u = f u at hs
    rw [← hs]
    ring
  unfold mass
  simp_rw [hh]
  have ha := integral_add (he.add ho) (hc.const_mul 2)
  simp only [Pi.add_apply, Pi.mul_apply] at ha
  rw [ha, integral_add he ho, integral_const_mul, parts_orthogonal, mul_zero, add_zero]

theorem variance_split (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    variance n β hβ f = variance n β hβ (evenPart n i f) +
      variance n β hβ (oddPart n i f) := by
  rw [variance_formula, variance_formula, variance_formula,
    odd_mean n i β hβ _ (odd_parity n i f), even_mean]
  change mass n β hβ f - _ = (mass n β hβ (evenPart n i f) - _) +
    (mass n β hβ (oddPart n i f) - _)
  rw [mass_split n i β hβ f]
  ring

theorem step_combination (β : ℝ) (hβ : 0 ≤ β) (a b : ℝ) (f g : C(Slice n, ℝ)) :
    step n β hβ (a • f + b • g) = a • step n β hβ f + b • step n β hβ g := by
  ext u
  letI := WilsonTemporalInfluence.rowLaw_probability n β hβ u
  change (∫ v, a * f v + b * g v ∂WilsonTemporalInfluence.rowLaw n β hβ u) = _
  rw [integral_add ((continuous_integrable _ _ f.continuous).const_mul a)
    ((continuous_integrable _ _ g.continuous).const_mul b), integral_const_mul,
    integral_const_mul]
  rfl

theorem step_parts (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    step n β hβ (evenPart n i f) = evenPart n i (step n β hβ f) ∧
      step n β hβ (oddPart n i f) = oddPart n i (step n β hβ f) := by
  have hp : step n β hβ (pull n i f) = pull n i (step n β hβ f) :=
    WilsonRawSymmetry.step_pull n (symmetry n i) β hβ f
  have he : evenPart n i f = (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • pull n i f := by
    rw [evenPart, smul_add]
  have ho : oddPart n i f = (1 / 2 : ℝ) • f + (-1 / 2 : ℝ) • pull n i f := by
    ext u
    simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      ContinuousMap.sub_apply, smul_eq_mul]
    ring
  constructor
  · rw [he, step_combination, hp, evenPart, smul_add]
  · rw [ho, step_combination, hp]
    ext u
    simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.add_apply,
      ContinuousMap.sub_apply, smul_eq_mul]
    ring

/-- The actual variance loss splits along the same two invariant sectors. -/
theorem loss_split (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    loss n β hβ f = loss n β hβ (evenPart n i f) + loss n β hβ (oddPart n i f) := by
  simp only [loss, (step_parts n i β hβ f).1, (step_parts n i β hβ f).2]
  rw [variance_split n i β hβ f, variance_split n i β hβ (step n β hβ f)]
  ring

def energy (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) : ℝ :=
  ∫ u, (f (twist n i u) - f u)^2 ∂groundLaw n β hβ

theorem energy_odd_mass (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    energy n i β hβ f = 4 * mass n β hβ (oddPart n i f) := by
  rw [energy, mass, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [oddPart, ContinuousMap.smul_apply, ContinuousMap.sub_apply, pull_apply, smul_eq_mul]
  ring

/-- An exact lower bound for the missing global odd direction, with its even remainder kept. -/
theorem variance_energy_split (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ)) :
    variance n β hβ f = variance n β hβ (evenPart n i f) + energy n i β hβ f / 4 := by
  rw [variance_split n i β hβ f, variance_formula n β hβ (oddPart n i f),
    odd_mean n i β hβ _ (odd_parity n i f), energy_odd_mass]
  change _ + (mass n β hβ (oddPart n i f) - 0^2) = _
  ring

/-- Constant 1/4 is uniform, but the response rotates a whole periodic seam. -/
theorem odd_coercivity (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = -f u) :
    variance n β hβ f = energy n i β hβ f / 4 := by
  rw [variance_formula, odd_mean n i β hβ f hf]
  have he : energy n i β hβ f = 4 * mass n β hβ f := by
    rw [energy, mass, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [hf]
    ring
  rw [he]
  change mass n β hβ f - 0^2 = _
  ring

/-- The concrete winding loop is nonzero, centered, physical, and has exact twist coercivity. -/
theorem winding_coercivity (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) :
    0 < variance n β hβ (WilsonWindingLoop.loop n i) ∧
      variance n β hβ (WilsonWindingLoop.loop n i) =
        energy n i β hβ (WilsonWindingLoop.loop n i) / 4 :=
  ⟨WilsonWindingLoop.loop_variance_positive n β hβ i,
    odd_coercivity n i β hβ _ (loop_odd n i)⟩

/-- Every weighting constructed only from the spatial plaquettes keeps the winding loop centered. -/
theorem plaquette_weighted_loop (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (W : (SpatialVertex n → Fin 3 → Fin 3 → Q) → ℝ) :
    (∫ u, W (spatialHolonomy u) * WilsonWindingLoop.loop n i u ∂groundLaw n β hβ) = 0 := by
  apply weighted_odd_mean n i β hβ _ _ _ (loop_odd n i)
  intro u
  congr 1
  funext x j k
  exact twist_holonomy n i u x j k

/-- The entire even sector is invisible to this one global response. -/
theorem even_energy_zero (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β) (f : C(Slice n, ℝ))
    (hf : ∀ u, f (twist n i u) = f u) : energy n i β hβ f = 0 := by
  simp only [energy, hf, sub_self, zero_pow (by decide : 2 ≠ 0), integral_zero]

/-- The new global direction complements local control; it cannot replace it. -/
theorem no_full_twist_coercivity [Fact (1 < n)] (i : Fin 3) (β : ℝ) (hβ : 0 ≤ β)
    (C : ℝ) :
    ¬∀ f : C(Slice n, ℝ), (∀ h u, f (gaugeSlice h u) = f u) →
      variance n β hβ f ≤ C * energy n i β hβ f := by
  intro hh
  let f := WilsonPlaquetteTransport.plaquette n 0 0 1
  have hv := WilsonGroundVarianceBudget.plaquette_variance_positive n β hβ 0 0 1 (by decide)
  have hp := hh f (WilsonPlaquetteTransport.plaquette_gauge n 0 0 1)
  have he : energy n i β hβ f = 0 := by
    apply even_energy_zero n i β hβ f
    intro u
    change (WilsonSingleLinkStaples.character (spatialHolonomy (twist n i u) 0 0 1)).re = _
    rw [twist_holonomy]
    rfl
  rw [he, mul_zero] at hp
  exact (not_le_of_gt hv) hp

end
end UnifiedTheory.Clay.YangMills.WilsonCenterCoercivity
