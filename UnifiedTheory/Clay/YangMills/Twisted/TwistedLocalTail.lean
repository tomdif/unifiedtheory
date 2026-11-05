/- A local bound for the twisted law, with no volume factor and no assumption on cross terms. It is a free-energy estimate:
`Z` is bounded from below by Jensen against a product trial weight, with `Z(β) ≥ mass(6β)^(links - |tSet|)` (`Zr_lower_trial`), and
from above by integrating links in a triangular order, where a link carrying `k` plaquettes costs `mass(k t)` (`Elim.Zon_le`). The
powers of `β` cancel in the bulk.

Proved, for all `n ≥ 1`, with `N = 2n`:
* one plaquette, any orientation, `β > 0`: `E[d²] ≤ ((3/2) log 54 + (3/(2n)) log 4 + (2/n)(-log mass(6β))) / β` (`defect_sq_le`), which is
  about `5.98/β` at large `n`, from lowering the coupling of that one plane to zero (`off_jensen`);
* the mixed planes: about `3.51/β` at large `n` (`mixed_le`);
* the energy per vertex: about `15.42/β` at large `n`, at `l ≈ 0.29` (`energy_le`), and from below about `0.57/β` (`energy_ge`), which is the
  same power of `β` with a gap of about `27` in the constant;
* `E[d²] ≤ (7/2)(-log mass(6β))/β` (`defect_sq_le_log`), whose numerator is below `4 log cap(24β)` for all `β ≥ 1/32` (`log_form_le`). So it
  implies the flow-time-zero case of the existing `TwistedFlow.law_term_mean`, at every coupling where that one applies. It says nothing at
  positive flow time;
* the orbit identity `energy = N⁴ (m₁₂ + m₀₃ + 4 m₀₁)` from the axis swaps `(0 3)` and `(1 2)` (`energy_orbits`), and the joint law form of
  translation invariance (`defectField_law`), with explicit link signs (`Cov`).

Already in the repo, restated here because this module does not import `TwistedFlow`: translation up to a center flip
(`TwistedFlow.law_Rκ`, `law_term_step`, also `TwistedLimit`). Only `defectField_law` and the explicit signs are added.

What this is not. The tail is Chebyshev on the second moment, not exponential, so a union over all plaquettes costs the volume. The
constants are about `8` times the value near `0.75/β` from the repo's Monte Carlo at large `n`, and more at small `n`, where the term `(2/n)` matters.
The second moment bound drops below the Haar value `2` only above `β_std = 2β` about `6` at large `n` and about `11` at `n = 3`. It says
nothing about the sign of different-plane cross terms, about correlations at separated points, about blocked fields, or about any gap. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice
import UnifiedTheory.Clay.YangMills.PeriodicSpacetimeTranslation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalTail
noncomputable section
open MeasureTheory
open PeriodicLattice4 TwistedFlat TwistedStability TwistedLandau TwistedLocalization TwistedReflection
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge PeriodicSpacetimeTranslation
open WilsonSingleLinkStaples (Q character)
open scoped Quaternion RealInnerProductSpace
open scoped Classical

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-! ### The center flip that moves the twist sheet back -/

/-- The sign on a link. A translation by `e₁` flips the direction-2 links over `x₁ = x₂ = 0`, and a translation by
`e₂` flips the direction-1 links there. Translations by `e₀` and `e₃` need no flip. -/
def sgn (i : Fin 4) (x : V') (μ : Fin 4) : Q :=
  if ((i = 1 ∧ μ = 2) ∨ (i = 2 ∧ μ = 1)) ∧ x 1 = 0 ∧ x 2 = 0 then ω else 1

theorem ω_mul_ω : ω * ω = 1 := by
  apply Subtype.ext
  change ((-1 : ℍ[ℝ]) * (-1)) = 1
  simp

theorem ω_inv : ω⁻¹ = ω := inv_eq_of_mul_eq_one_left ω_mul_ω

/-- The defining property: the flip's coboundary is the difference of the twist and its translate. -/
theorem sgn_cobound (i : Fin 4) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    sgn n i x μ * sgn n i (step (2 * n) x μ) ν * sgn n i (step (2 * n) x ν) μ * sgn n i x ν *
        ω ^ twistExp μ ν x = ω ^ twistExp μ ν (step (2 * n) x i) := by
  have s (y : V') (a b : Fin 4) (hab : b ≠ a) : step (2 * n) y a b = y b := step_other y a b hab
  have ss (y : V') (a : Fin 4) : step (2 * n) y a a = y a + 1 := by simp [step]
  fin_cases i <;> fin_cases μ <;> fin_cases ν <;> first
    | exact absurd h (by decide)
    | (simp only [sgn, twistExp]
       simp [s, ss]
       done)
    | (simp only [sgn, twistExp]
       simp [s, ss]
       by_cases h1 : x 1 = 0 <;> by_cases h2 : x 2 = 0 <;> by_cases h3 : x 1 + 1 = 0 <;>
         by_cases h4 : x 2 + 1 = 0 <;> simp [h1, h2, h3, h4, ω_mul_ω])


theorem sgn_cases (i : Fin 4) (x : V') (μ : Fin 4) : sgn n i x μ = 1 ∨ sgn n i x μ = ω := by
  unfold sgn
  split_ifs <;> simp

/-- The translation by `e_i` followed by the center flip. -/
def symMap (i : Fin 4) (U : Configuration V' Q) : Configuration V' Q :=
  fun e => sgn n i (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2 *
    shiftConfiguration (2 * n) Q (Pi.single i 1) U e

theorem symMap_link (i : Fin 4) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q (symMap n i U) x μ =
      sgn n i x μ * linkValue (2 * n) Q U (step (2 * n) x i) μ := rfl

theorem center_commute (a : Q) (ha : a = 1 ∨ a = ω) (g : Q) : Commute a g := by
  rcases ha with rfl | rfl
  · exact Commute.one_left g
  · exact ω_commute g

theorem center_inv (a : Q) (ha : a = 1 ∨ a = ω) : a⁻¹ = a := by
  rcases ha with rfl | rfl
  · simp
  · exact ω_inv

theorem center_mul (a b : Q) (ha : a = 1 ∨ a = ω) (hb : b = 1 ∨ b = ω) : a * b = 1 ∨ a * b = ω := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [ω_mul_ω]

theorem prod4 (a b c f A B C D : Q) (hb : b = 1 ∨ b = ω) (hc : c = 1 ∨ c = ω) (hf : f = 1 ∨ f = ω) :
    a * A * (b * B) * (c * C)⁻¹ * (f * D)⁻¹ = (a * b * c * f) * (A * B * C⁻¹ * D⁻¹) := by
  have cb := center_commute b hb A
  have cc := center_commute c hc D⁻¹
  have hW : Commute (c * f) (A * B * C⁻¹ * D⁻¹) :=
    (center_commute c hc _).mul_left (center_commute f hf _)
  rw [mul_inv_rev, mul_inv_rev, center_inv c hc, center_inv f hf]
  calc a * A * (b * B) * (C⁻¹ * c) * (D⁻¹ * f)
      = a * (A * b) * B * C⁻¹ * (c * D⁻¹) * f := by simp only [mul_assoc]
    _ = a * (b * A) * B * C⁻¹ * (D⁻¹ * c) * f := by rw [← cb.eq, cc.eq]
    _ = (a * b) * ((A * B * C⁻¹ * D⁻¹) * (c * f)) := by simp only [mul_assoc]
    _ = (a * b) * ((c * f) * (A * B * C⁻¹ * D⁻¹)) := by rw [hW.eq]
    _ = _ := by simp only [mul_assoc]

/-- **The flip restores the twist.** The defect of the flipped translate at `x` is the defect at `x + e_i`. -/
theorem defect_symMap (i : Fin 4) (U : Configuration V' Q) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    defect (linkValue (2 * n) Q (symMap n i U)) μ ν x =
      defect (linkValue (2 * n) Q U) μ ν (step (2 * n) x i) := by
  unfold defect
  simp only [symMap_link]
  rw [prod4 _ _ _ _ _ _ _ _ (sgn_cases n i _ _) (sgn_cases n i _ _) (sgn_cases n i _ _),
    step_comm (2 * n) x μ i, step_comm (2 * n) x ν i]
  have hZ := center_mul _ _ (center_mul _ _ (center_mul _ _ (sgn_cases n i x μ)
    (sgn_cases n i (step (2 * n) x μ) ν)) (sgn_cases n i (step (2 * n) x ν) μ)) (sgn_cases n i x ν)
  rw [← sgn_cobound n i x μ ν h]
  set Z := sgn n i x μ * sgn n i (step (2 * n) x μ) ν * sgn n i (step (2 * n) x ν) μ * sgn n i x ν
  have hZZ : Z * Z = 1 := by
    rcases hZ with e | e <;> rw [e]
    · simp
    · exact ω_mul_ω
  have e : ω ^ twistExp μ ν x = Z * (Z * ω ^ twistExp μ ν x) := by
    rw [← mul_assoc, hZZ, one_mul]
  conv_lhs => rw [e]
  rw [d_mul_left]

theorem symMap_ref (i : Fin 4) :
    MeasurePreserving (symMap n i) (referenceMeasure Q V') (referenceMeasure Q V') :=
  (measurePreserving_pi (fun _ : Edge V' => compactHaar Q) (fun _ : Edge V' => compactHaar Q)
    (fun e => measurePreserving_mul_left (compactHaar Q)
      (sgn n i (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2))).comp
    (reference_preserves_shift (2 * n) Q (Pi.single i 1))

theorem actionOne_symMap (i : Fin 4) (U : Configuration V' Q) :
    actionOne n (symMap n i U) = actionOne n U := by
  rw [TwistedNearFlat.actionOne_eq, TwistedNearFlat.actionOne_eq]
  unfold actionL
  have h (p : PlaquetteIndex (2 * n)) :
      defect (linkValue (2 * n) Q (symMap n i U)) p.2.1.1 p.2.1.2 p.1 ^ 2 =
        (fun q : PlaquetteIndex (2 * n) => defect (linkValue (2 * n) Q U) q.2.1.1 q.2.1.2 q.1 ^ 2)
          (plaquetteShiftEquiv (2 * n) (Pi.single i 1) p) := by
    rw [defect_symMap n i U _ _ p.2.2]
    rfl
  simp only [h]
  exact Equiv.sum_comp (plaquetteShiftEquiv (2 * n) (Pi.single i 1))
    (fun q : PlaquetteIndex (2 * n) => defect (linkValue (2 * n) Q U) q.2.1.1 q.2.1.2 q.1 ^ 2)

/-- A Haar-preserving map that fixes the action preserves the twisted law. -/
theorem law_pres (β : ℝ) (T : Configuration V' Q → Configuration V' Q)
    (hT : MeasurePreserving T (referenceMeasure Q V') (referenceMeasure Q V'))
    (hinv : ∀ U, actionOne n (T U) = actionOne n U) :
    MeasurePreserving T (twistedLaw n β) (twistedLaw n β) := by
  have hSc : Continuous (action n Q (spatialTwist n) character β 2) :=
    continuous_action n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  apply MeasurePreserving.smul_measure
  refine preserves_withDensity hT _ (Real.continuous_exp.comp hSc.neg).measurable.ennreal_ofReal ?_
  intro U
  simp only [gibbsDensity, action_eq_mul, hinv]

/-! ### All translations -/

/-- A symmetry of the twisted law that translates the defect field by `v` and changes each link by a center sign. -/
def Cov (β : ℝ) (v : V') : Prop :=
  ∃ T : Configuration V' Q → Configuration V' Q, MeasurePreserving T (twistedLaw n β) (twistedLaw n β) ∧
    ∃ s : V' → Fin 4 → Q, (∀ x μ, s x μ = 1 ∨ s x μ = ω) ∧
      (∀ U x μ, linkValue (2 * n) Q (T U) x μ = s x μ * linkValue (2 * n) Q U (x + v) μ) ∧
      ∀ U (μ ν : Fin 4), μ < ν → ∀ x,
        defect (linkValue (2 * n) Q (T U)) μ ν x = defect (linkValue (2 * n) Q U) μ ν (x + v)

theorem cov_zero (β : ℝ) : Cov n β 0 :=
  ⟨id, MeasurePreserving.id _, fun _ _ => 1, fun _ _ => Or.inl rfl, by simp, by simp⟩

theorem cov_add (β : ℝ) (v w : V') (hv : Cov n β v) (hw : Cov n β w) : Cov n β (v + w) := by
  obtain ⟨T, hT, s, hs, hl, hd⟩ := hv
  obtain ⟨T', hT', s', hs', hl', hd'⟩ := hw
  refine ⟨T ∘ T', hT.comp hT', fun x μ => s x μ * s' (x + v) μ, fun x μ => center_mul _ _ (hs x μ) (hs' _ μ),
    ?_, ?_⟩
  · intro U x μ
    simp only [Function.comp_apply]
    rw [hl, hl', mul_assoc, add_assoc]
  · intro U μ ν h x
    simp only [Function.comp_apply]
    rw [hd _ μ ν h, hd' _ μ ν h, add_assoc]

theorem cov_single (β : ℝ) (i : Fin 4) : Cov n β (Pi.single i 1) :=
  ⟨symMap n i, law_pres n β _ (symMap_ref n i) (actionOne_symMap n i), sgn n i, sgn_cases n i,
    fun _ _ _ => rfl, fun U μ ν h x => defect_symMap n i U μ ν h x⟩

theorem cov_nsmul (β : ℝ) (v : V') (hv : Cov n β v) (k : ℕ) : Cov n β (k • v) := by
  induction k with
  | zero => simpa using cov_zero n β
  | succ k ih =>
    rw [succ_nsmul]
    exact cov_add n β _ _ ih hv

/-- **Translation symmetry of the twisted law**, with explicit link signs. Every translation lifts to a symmetry of the law, in all
four directions. This is the symmetry of `TwistedFlow.law_Rκ`, packaged for arbitrary translations. -/
theorem cov_all (β : ℝ) (v : V') : Cov n β v := by
  have hv : v = (v 0).val • (Pi.single 0 1 : V') + (v 1).val • (Pi.single 1 1 : V') +
      (v 2).val • (Pi.single 2 1 : V') + (v 3).val • (Pi.single 3 1 : V') := by
    funext i
    fin_cases i <;> simp [Pi.single_apply, -ZMod.natCast_val, ZMod.natCast_zmod_val]
  rw [hv]
  exact cov_add n β _ _ (cov_add n β _ _ (cov_add n β _ _ (cov_nsmul n β _ (cov_single n β 0) _)
    (cov_nsmul n β _ (cov_single n β 1) _)) (cov_nsmul n β _ (cov_single n β 2) _))
    (cov_nsmul n β _ (cov_single n β 3) _)

theorem defect_continuous (x : V') (μ ν : Fin 4) :
    Continuous fun U : Configuration V' Q => defect (linkValue (2 * n) Q U) μ ν x := by
  have ha := TwistedSlice.continuous_linkValue n x μ
  have hb := TwistedSlice.continuous_linkValue n (step (2 * n) x μ) ν
  have hc := TwistedSlice.continuous_linkValue n (step (2 * n) x ν) μ
  have he := TwistedSlice.continuous_linkValue n x ν
  have hco : Continuous fun g : Q => (g : ℍ[ℝ]) := continuous_subtype_val
  unfold defect d
  exact (hco.comp (((ha.mul hb).mul hc.inv).mul he.inv)).sub continuous_const |>.norm

/-- The defect field of a configuration. -/
def defectField (U : Configuration V' Q) : PlaquetteIndex (2 * n) → ℝ :=
  fun p => defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1

theorem defectField_continuous : Continuous (defectField n) :=
  continuous_pi fun p => defect_continuous n p.1 p.2.1.1 p.2.1.2

/-- **The joint law of all plaquette defects is translation invariant.** -/
theorem defectField_law (β : ℝ) (v : V') :
    (twistedLaw n β).map (fun U p => defectField n U (p.1 + v, p.2)) =
      (twistedLaw n β).map (defectField n) := by
  obtain ⟨T, hT, -, -, -, hd⟩ := cov_all n β v
  have e : (fun U (p : PlaquetteIndex (2 * n)) => defectField n U (p.1 + v, p.2)) = defectField n ∘ T := by
    funext U p
    exact (hd U p.2.1.1 p.2.1.2 p.2.2 p.1).symm
  rw [e, ← Measure.map_map (defectField_continuous n).measurable hT.measurable, hT.map_eq]

/-- **The law of one plaquette's defect does not depend on its position**, within a plane orientation. -/
theorem defect_law (β : ℝ) (μ ν : Fin 4) (h : μ < ν) (x y : V') :
    (twistedLaw n β).map (fun U => defect (linkValue (2 * n) Q U) μ ν x) =
      (twistedLaw n β).map (fun U => defect (linkValue (2 * n) Q U) μ ν y) := by
  obtain ⟨T, hT, -, -, -, hd⟩ := cov_all n β (y - x)
  have e : (fun U => defect (linkValue (2 * n) Q U) μ ν y) =
      (fun U => defect (linkValue (2 * n) Q U) μ ν x) ∘ T := by
    funext U
    simp only [Function.comp_apply]
    rw [hd U μ ν h x, add_sub_cancel]
  rw [e, ← Measure.map_map (defect_continuous n x μ ν).measurable hT.measurable, hT.map_eq]

theorem integral_defect_eq (β : ℝ) (μ ν : Fin 4) (h : μ < ν) (x y : V') (G : ℝ → ℝ) (hG : Measurable G) :
    ∫ U, G (defect (linkValue (2 * n) Q U) μ ν x) ∂twistedLaw n β =
      ∫ U, G (defect (linkValue (2 * n) Q U) μ ν y) ∂twistedLaw n β := by
  have hx := integral_map (defect_continuous n x μ ν).measurable.aemeasurable (μ := twistedLaw n β)
    (f := G) hG.aestronglyMeasurable
  have hy := integral_map (defect_continuous n y μ ν).measurable.aemeasurable (μ := twistedLaw n β)
    (f := G) hG.aestronglyMeasurable
  rw [← hx, ← hy, defect_law n β μ ν h x y]

/-- The mean square defect of an orientation, at the base point. -/
def planeMean (β : ℝ) (μ ν : Fin 4) : ℝ :=
  ∫ U, defect (linkValue (2 * n) Q U) μ ν 0 ^ 2 ∂twistedLaw n β

theorem planeMean_eq (β : ℝ) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂twistedLaw n β = planeMean n β μ ν :=
  integral_defect_eq n β μ ν h x 0 (fun r => r ^ 2) (measurable_id.pow_const 2)

/-! ### From the energy to one plaquette -/

/-- The expected energy at coupling `β`. -/
def energy (β : ℝ) : ℝ := ∫ U, actionOne n U ∂twistedLaw n β

instance law_prob (β : ℝ) : IsProbabilityMeasure (twistedLaw n β) :=
  law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2

theorem defect_sq_integrable (β : ℝ) (x : V') (μ ν : Fin 4) :
    Integrable (fun U => defect (linkValue (2 * n) Q U) μ ν x ^ 2) (twistedLaw n β) :=
  ((defect_continuous n x μ ν).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **The orbit count.** The energy is the volume times the sum over the six plane orientations of one mean square
defect each. -/
theorem energy_eq (β : ℝ) (x₀ : V') :
    energy n β = ((2 * n : ℕ) : ℝ) ^ 4 *
      ∑ d : Plane, ∫ U, defect (linkValue (2 * n) Q U) d.1.1 d.1.2 x₀ ^ 2 ∂twistedLaw n β := by
  have e0 : energy n β = ∫ U, ∑ p : PlaquetteIndex (2 * n),
      defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2 ∂twistedLaw n β := by
    unfold energy
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    exact TwistedNearFlat.actionOne_eq n U
  rw [e0, integral_finset_sum _ fun p _ => defect_sq_integrable n β p.1 p.2.1.1 p.2.1.2, Fintype.sum_prod_type]
  have hx (x : V') : ∑ d : Plane, ∫ U, defect (linkValue (2 * n) Q U) d.1.1 d.1.2 x ^ 2 ∂twistedLaw n β =
      ∑ d : Plane, ∫ U, defect (linkValue (2 * n) Q U) d.1.1 d.1.2 x₀ ^ 2 ∂twistedLaw n β :=
    Finset.sum_congr rfl fun d _ => integral_defect_eq n β d.1.1 d.1.2 d.2 x x₀ (fun r => r ^ 2)
      (measurable_id.pow_const 2)
  simp only [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_vertex]

/-- One plaquette, in any orientation, has at most the energy per vertex. The six orbits are not assumed equal. -/
theorem defect_sq_le_energy (β : ℝ) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂twistedLaw n β ≤ energy n β / ((2 * n : ℕ) : ℝ) ^ 4 := by
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    have := NeZero.pos n
    positivity
  rw [le_div_iff₀ hN, energy_eq n β x, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hN.le
  have hs := Finset.single_le_sum (s := (Finset.univ : Finset Plane)) (f := fun d : Plane =>
    ∫ U, defect (linkValue (2 * n) Q U) d.1.1 d.1.2 x ^ 2 ∂twistedLaw n β)
    (fun d _ => integral_nonneg fun U => sq_nonneg _) (Finset.mem_univ (⟨(μ, ν), h⟩ : Plane))
  exact hs

/-! ### The energy through a ratio of partition functions -/

/-- The partition function, as a real number. -/
def Zr (β : ℝ) : ℝ := ∫ U, Real.exp (-(β * actionOne n U)) ∂referenceMeasure Q V'

theorem weight_continuous (β : ℝ) : Continuous fun U : Configuration V' Q => Real.exp (-(β * actionOne n U)) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_actionOne n)).neg)

theorem weight_integrable (β : ℝ) :
    Integrable (fun U : Configuration V' Q => Real.exp (-(β * actionOne n U))) (referenceMeasure Q V') :=
  (weight_continuous n β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem Zr_pos (β : ℝ) : 0 < Zr n β := integral_exp_pos (weight_integrable n β)

theorem Zr_zero : Zr n 0 = 1 := by
  simp [Zr]

theorem partition_toReal (β : ℝ) :
    (gibbsPartition V' Q (action n Q (spatialTwist n) character β 2)).toReal = Zr n β := by
  unfold gibbsPartition gibbsDensity Zr
  have hi : Integrable (fun U => Real.exp (-action n Q (spatialTwist n) character β 2 U))
      (referenceMeasure Q V') := by
    simpa only [action_eq_mul] using weight_integrable n β
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le),
    ENNReal.toReal_ofReal (integral_nonneg fun U => (Real.exp_pos _).le)]
  simp only [action_eq_mul]

theorem law_expect (β : ℝ) (f : Configuration V' Q → ℝ) :
    ∫ U, f U ∂twistedLaw n β =
      (Zr n β)⁻¹ * ∫ U, Real.exp (-(β * actionOne n U)) * f U ∂referenceMeasure Q V' := by
  rw [TwistedIBP.law_integral, ENNReal.toReal_inv, partition_toReal]
  simp only [action_eq_mul]

/-- The exponential moment of the energy is a ratio of partition functions. -/
theorem exp_moment (β θ : ℝ) :
    ∫ U, Real.exp (θ * actionOne n U) ∂twistedLaw n β = Zr n (β - θ) / Zr n β := by
  rw [law_expect, div_eq_inv_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change Real.exp _ * Real.exp _ = Real.exp _
  rw [← Real.exp_add]
  congr 1
  ring

theorem actionOne_integrable (β : ℝ) : Integrable (actionOne n) (twistedLaw n β) :=
  (continuous_actionOne n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **Jensen.** `θ E_β[f] ≤ log ∫ exp(-β S + θ f) - log Z(β)`, for a continuous `f`. -/
theorem gen_jensen (β θ : ℝ) (f : Configuration V' Q → ℝ) (hf : Continuous f) :
    θ * ∫ U, f U ∂twistedLaw n β ≤
      Real.log (∫ U, Real.exp (-(β * actionOne n U) + θ * f U) ∂referenceMeasure Q V') - Real.log (Zr n β) := by
  set a := ∫ U, f U ∂twistedLaw n β with ha
  set I := ∫ U, Real.exp (-(β * actionOne n U) + θ * f U) ∂referenceMeasure Q V' with hI
  have hIc : Continuous fun U : Configuration V' Q => Real.exp (-(β * actionOne n U) + θ * f U) :=
    Real.continuous_exp.comp (((continuous_const.mul (continuous_actionOne n)).neg).add (continuous_const.mul hf))
  have hIp : 0 < I := integral_exp_pos (hIc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hc : Continuous fun U : Configuration V' Q => Real.exp (θ * f U) :=
    Real.continuous_exp.comp (continuous_const.mul hf)
  have hi : Integrable (fun U : Configuration V' Q => Real.exp (θ * f U)) (twistedLaw n β) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS : Integrable f (twistedLaw n β) := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmom : ∫ U, Real.exp (θ * f U) ∂twistedLaw n β = I / Zr n β := by
    rw [law_expect, div_eq_inv_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    change Real.exp _ * Real.exp _ = Real.exp _
    rw [← Real.exp_add]
  have hl : ∫ U, (1 + θ * (f U - a)) ∂twistedLaw n β = 1 := by
    have e : (fun U => 1 + θ * (f U - a)) = fun U => (1 - θ * a) + θ * f U := by
      funext U
      ring
    rw [e, integral_add (integrable_const _) (hS.const_mul _), integral_const_mul]
    simp [ha]
  have hmono : ∫ U, (1 + θ * (f U - a)) ∂twistedLaw n β ≤
      ∫ U, Real.exp (-(θ * a)) * Real.exp (θ * f U) ∂twistedLaw n β := by
    refine integral_mono ((integrable_const _).add ((hS.sub (integrable_const _)).const_mul _))
      (hi.const_mul _) fun U => ?_
    change _ ≤ Real.exp _ * Real.exp _
    rw [← Real.exp_add]
    have := Real.add_one_le_exp (-(θ * a) + θ * f U)
    linarith only [this]
  rw [hl, integral_const_mul, hmom] at hmono
  have hZ := Zr_pos n β
  have h2 : Real.exp (θ * a) ≤ I / Zr n β := by
    have hp : Real.exp (θ * a) * Real.exp (-(θ * a)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc Real.exp (θ * a) = Real.exp (θ * a) * 1 := (mul_one _).symm
      _ ≤ Real.exp (θ * a) * (Real.exp (-(θ * a)) * (I / Zr n β)) :=
        mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
      _ = I / Zr n β := by rw [← mul_assoc, hp, one_mul]
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rwa [Real.log_exp, Real.log_div hIp.ne' hZ.ne'] at h3

/-- `(β - β') E_β[S] ≤ log Z(β') - log Z(β)`, for all real `β, β'`. -/
theorem energy_jensen (β β' : ℝ) :
    (β - β') * energy n β ≤ Real.log (Zr n β') - Real.log (Zr n β) := by
  have h := gen_jensen n β (β - β') (actionOne n) (continuous_actionOne n)
  refine h.trans_eq ?_
  congr 2
  unfold Zr
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change Real.exp _ = Real.exp _
  congr 1
  ring

/-! ### Resampling one link -/

theorem resample (H : Configuration V' Q → ℝ) (hH : Continuous H) (e : Edge V') :
    ∫ U, H U ∂referenceMeasure Q V' =
      ∫ U, ∫ w, H (Function.update U e w) ∂compactHaar Q ∂referenceMeasure Q V' := by
  let τ : Q → Configuration V' Q → Configuration V' Q := fun w U => fun e' => if e' = e then U e' * w else U e'
  have hτ (w : Q) : MeasurePreserving (τ w) (referenceMeasure Q V') (referenceMeasure Q V') := by
    refine measurePreserving_pi (fun _ : Edge V' => compactHaar Q) (fun _ : Edge V' => compactHaar Q)
      (f := fun e' q => if e' = e then q * w else q) fun e' => ?_
    by_cases he : e' = e
    · simp only [he, if_true]
      exact measurePreserving_mul_right _ _
    · simp only [he, if_false]
      exact MeasurePreserving.id _
  have hτe (w : Q) (U : Configuration V' Q) : τ w U = Function.update U e (U e * w) := by
    funext e'
    by_cases he : e' = e
    · subst he
      simp [τ]
    · simp [τ, he]
  have h1 (w : Q) : ∫ U, H (τ w U) ∂referenceMeasure Q V' = ∫ U, H U ∂referenceMeasure Q V' := by
    have := integral_map (μ := referenceMeasure Q V') (hτ w).measurable.aemeasurable (f := H)
      hH.aestronglyMeasurable
    rw [(hτ w).map_eq] at this
    exact this.symm
  have hcont : Continuous fun p : Q × Configuration V' Q => H (τ p.1 p.2) := by
    refine hH.comp (continuous_pi fun e' => ?_)
    by_cases he : e' = e
    · simp only [τ, he, if_true]
      exact (continuous_apply e |>.comp continuous_snd).mul continuous_fst
    · simp only [τ, he, if_false]
      exact continuous_apply e' |>.comp continuous_snd
  have hint : Integrable (Function.uncurry fun (w : Q) (U : Configuration V' Q) => H (τ w U))
      ((compactHaar Q).prod (referenceMeasure Q V')) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ U, H U ∂referenceMeasure Q V'
      = ∫ _ : Q, ∫ U, H U ∂referenceMeasure Q V' ∂compactHaar Q := by simp
    _ = ∫ w, ∫ U, H (τ w U) ∂referenceMeasure Q V' ∂compactHaar Q := by simp only [h1]
    _ = ∫ U, ∫ w, H (τ w U) ∂compactHaar Q ∂referenceMeasure Q V' := integral_integral_swap hint
    _ = _ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      simp only [hτe]
      exact integral_mul_left_eq_self (fun w => H (Function.update U e w)) (U e)

/-! ### Gauge fixing one link at a time -/

/-- The gauge transformation concentrated at one vertex. -/
def gv (v : V') (h : Q) : V' → Q := fun y => if y = v then h else 1

theorem gv_continuous (v y : V') : Continuous fun h : Q => gv n v h y := by
  unfold gv
  by_cases hy : y = v
  · simpa only [hy, if_true] using continuous_id
  · simpa only [hy, if_false] using continuous_const

theorem gauge_joint (v : V') :
    Continuous fun p : Q × Configuration V' Q => RegulatedGauge.gauge V' Q (gv n v p.1) p.2 := by
  refine continuous_pi fun e => ?_
  unfold RegulatedGauge.gauge
  exact (((gv_continuous n v e.1).comp continuous_fst).mul ((continuous_apply e).comp continuous_snd)).mul
    ((gv_continuous n v e.2.1).comp continuous_fst).inv

/-- One link can be set to `1` inside the integral of a function invariant under the gauge at its head. -/
theorem gauge_fix_step (F : Configuration V' Q → ℝ) (hF : Continuous F) (e : Edge V') (hne : e.1 ≠ e.2.1)
    (hinv : ∀ h U, F (RegulatedGauge.gauge V' Q (gv n e.2.1 h) U) = F U) :
    ∫ U, F U ∂referenceMeasure Q V' = ∫ U, F (Function.update U e 1) ∂referenceMeasure Q V' := by
  let Φ : Configuration V' Q → ℝ := fun U => F (Function.update U e 1)
  have hΦ : Continuous Φ := hF.comp (continuous_id.update e continuous_const)
  have key (U : Configuration V' Q) (w : Q) :
      F (Function.update U e w) = Φ (RegulatedGauge.gauge V' Q (gv n e.2.1 w) U) := by
    rw [← hinv w]
    congr 1
    funext e'
    by_cases he : e' = e
    · subst he
      simp [RegulatedGauge.gauge, gv, hne]
    · simp [RegulatedGauge.gauge, he]
  have hcont : Continuous fun p : Q × Configuration V' Q => Φ (RegulatedGauge.gauge V' Q (gv n e.2.1 p.1) p.2) :=
    hΦ.comp (gauge_joint n e.2.1)
  have hint : Integrable (Function.uncurry fun (w : Q) (U : Configuration V' Q) =>
      Φ (RegulatedGauge.gauge V' Q (gv n e.2.1 w) U)) ((compactHaar Q).prod (referenceMeasure Q V')) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 (w : Q) : ∫ U, Φ (RegulatedGauge.gauge V' Q (gv n e.2.1 w) U) ∂referenceMeasure Q V' =
      ∫ U, Φ U ∂referenceMeasure Q V' := by
    have hp := gauge_preserves_reference Q V' (gv n e.2.1 w)
    have := integral_map (μ := referenceMeasure Q V') hp.measurable.aemeasurable (f := Φ)
      hΦ.aestronglyMeasurable
    rw [hp.map_eq] at this
    exact this.symm
  rw [resample n F hF e]
  simp only [key]
  rw [← integral_integral_swap hint]
  simp only [h1]
  simp [Φ]

/-- The temporal link at `x`. -/
def tE (x : V') : Edge V' := ⟨x, step (2 * n) x 0, forward (2 * n) x 0⟩

theorem tE_injective : Function.Injective (tE n) := by
  intro x y h
  exact congrArg Sigma.fst h

/-- The temporal links that a gauge can remove: all those not closing the time circle. -/
def tSet : Finset V' := Finset.univ.filter fun x => (x 0).val + 1 < 2 * n

theorem next_val (x : V') (hx : (x 0).val + 1 < 2 * n) :
    (step (2 * n) x 0 0).val = (x 0).val + 1 := by
  have h1 : (1 : ZMod (2 * n)).val = 1 := ZMod.val_one'' (by have := NeZero.pos n; omega)
  change (x 0 + (Pi.single 0 (1 : ZMod (2 * n)) : V') 0).val = _
  rw [Pi.single_eq_same, ZMod.val_add_of_lt (by rw [h1]; omega), h1]

/-- Set the temporal links over `s` to `1`. -/
def fixOn (s : Finset V') (U : Configuration V' Q) : Configuration V' Q :=
  fun e => if e ∈ s.image (tE n) then 1 else U e

theorem fixOn_continuous (s : Finset V') : Continuous (fixOn n s) := by
  refine continuous_pi fun e => ?_
  unfold fixOn
  by_cases he : e ∈ s.image (tE n)
  · simpa only [he, if_true] using continuous_const
  · simpa only [he, if_false] using continuous_apply e

theorem fixOn_empty (U : Configuration V' Q) : fixOn n ∅ U = U := by
  funext e
  simp [fixOn]

theorem fixOn_insert (a : V') (s : Finset V') (U : Configuration V' Q) :
    fixOn n s (Function.update U (tE n a) 1) = fixOn n (insert a s) U := by
  funext e
  by_cases he : e = tE n a
  · subst he
    simp [fixOn]
  · by_cases hs : e ∈ s.image (tE n)
    · have hs' : e ∈ (insert a s).image (tE n) := by
        rw [Finset.image_insert]
        exact Finset.mem_insert_of_mem hs
      simp [fixOn, hs]
    · have hs' : e ∉ (insert a s).image (tE n) := by
        rw [Finset.image_insert, Finset.mem_insert]
        tauto
      simp [fixOn, hs, he]

/-- **The temporal gauge, inside the integral.** A gauge-invariant integrand may be evaluated with all temporal links
over `s ⊆ tSet` replaced by `1`. There is no Jacobian. -/
theorem gauge_fix_temporal (F : Configuration V' Q → ℝ) (hF : Continuous F)
    (hinv : ∀ g U, F (RegulatedGauge.gauge V' Q g U) = F U) (s : Finset V') :
    s ⊆ tSet n → ∫ U, F U ∂referenceMeasure Q V' = ∫ U, F (fixOn n s U) ∂referenceMeasure Q V' := by
  refine Finset.induction_on_max_value (fun x : V' => (x 0).val) s ?_ ?_
  · intro _
    simp only [fixOn_empty]
  · intro a s ha hmax ih hsub
    rw [ih fun x hx => hsub (Finset.mem_insert_of_mem hx)]
    have hat : (a 0).val + 1 < 2 * n := (Finset.mem_filter.1 (hsub (Finset.mem_insert_self a s))).2
    have hnext := next_val n a hat
    have hne : (tE n a).1 ≠ (tE n a).2.1 := by
      intro h
      have : a = step (2 * n) a 0 := h
      rw [← this] at hnext
      omega
    have hstep := gauge_fix_step n (fun U => F (fixOn n s U)) (hF.comp (fixOn_continuous n s)) (tE n a) hne ?_
    · rw [hstep]
      simp only [fixOn_insert]
    · intro h U
      change F (fixOn n s (RegulatedGauge.gauge V' Q (gv n (step (2 * n) a 0) h) U)) = F (fixOn n s U)
      rw [← hinv (gv n (step (2 * n) a 0) h) (fixOn n s U)]
      congr 1
      funext e
      by_cases he : e ∈ s.image (tE n)
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 he
        have hle := hmax y hy
        have hy1 : y ≠ step (2 * n) a 0 := by
          intro h
          have : (y 0).val ≤ (a 0).val := hle
          rw [h, hnext] at this
          omega
        have hy2 : step (2 * n) y 0 ≠ step (2 * n) a 0 := by
          intro h
          apply ha
          have : y = a := by
            have h' : y + Pi.single 0 1 = a + Pi.single 0 1 := h
            exact add_right_cancel h'
          rwa [← this]
        simp only [fixOn, Finset.mem_image_of_mem _ hy, if_true, RegulatedGauge.gauge]
        change _ = gv n (step (2 * n) a 0) h y * 1 * (gv n (step (2 * n) a 0) h (step (2 * n) y 0))⁻¹
        simp [gv, hy1, hy2]
      · simp only [fixOn, he, if_false, RegulatedGauge.gauge]

/-! ### A lower bound on the partition function with the gauge removed -/

theorem actionOne_gauge (g : V' → Q) (U : Configuration V' Q) :
    actionOne n (RegulatedGauge.gauge V' Q g U) = actionOne n U := by
  rw [TwistedNearFlat.actionOne_eq, TwistedNearFlat.actionOne_eq]
  exact actionL_act g (linkValue (2 * n) Q U)


/-- The link at `x` in direction `μ`, as an edge. -/
def eOf (x : V') (μ : Fin 4) : Edge V' := ⟨x, step (2 * n) x μ, forward (2 * n) x μ⟩

theorem eOf_inj {x y : V'} {μ ν : Fin 4} (h : eOf n x μ = eOf n y ν) : x = y ∧ μ = ν := by
  have : (x, μ) = (y, ν) := congrArg (edgeCoordinates (2 * n)) h
  exact Prod.mk.inj this

theorem link_update (U : Configuration V' Q) (e : Edge V') (w : Q) (y : V') (ν : Fin 4) (h : eOf n y ν ≠ e) :
    linkValue (2 * n) Q (Function.update U e w) y ν = linkValue (2 * n) Q U y ν :=
  Function.update_of_ne h _ _

/-! ### Gaussian masses -/

theorem mass_le_one (s : ℝ) (hs : 0 ≤ s) : SU2GaussianMass.mass s ≤ 1 := by
  have h0 : SU2GaussianMass.mass 0 = 1 := by
    simp [SU2GaussianMass.mass, SU2GaussianMass.weight]
  rw [← h0]
  exact SU2GaussianMass.mass_antitone hs

theorem cap_pos (s : ℝ) (hs : 0 < s) : 0 < SU2GaussianMass.cap s := by
  unfold SU2GaussianMass.cap
  have h1 := SU2ScalarTilt.partition_pos 0
  have h2 := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have h3 := Real.sqrt_pos.2 hs
  positivity

/-- The growth of `cap` is exactly `s^(3/2)`. -/
theorem log_cap_ratio (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    Real.log (SU2GaussianMass.cap (r * s)) =
      Real.log (SU2GaussianMass.cap s) + 3 / 2 * Real.log r := by
  have hP := SU2ScalarTilt.partition_pos 0
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  set c := 4 * SU2ScalarTilt.partition 0 / Real.Gamma (3 / 2) with hc
  have hc0 : 0 < c := by positivity
  have e (u : ℝ) : SU2GaussianMass.cap u = c * (u * Real.sqrt u) := by
    unfold SU2GaussianMass.cap
    rw [hc]
    ring
  have lg (u : ℝ) (hu : 0 < u) : Real.log (SU2GaussianMass.cap u) = Real.log c + 3 / 2 * Real.log u := by
    have hq := Real.sqrt_pos.2 hu
    rw [e, Real.log_mul hc0.ne' (by positivity), Real.log_mul hu.ne' hq.ne', Real.log_sqrt hu.le]
    ring
  rw [lg _ (mul_pos hr hs), lg _ hs, Real.log_mul hr.ne' hs.ne']
  ring

theorem log_mass_lower (s : ℝ) (hs : 3 / 4 ≤ s) :
    -Real.log (SU2GaussianMass.cap s) ≤ Real.log (SU2GaussianMass.mass s) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hm := SU2GaussianMass.mass_pos s
  have hc := cap_pos s hs0
  rw [← Real.log_inv]
  apply Real.log_le_log (inv_pos.2 hc)
  rw [inv_le_iff_one_le_mul₀ hc]
  exact SU2GaussianMass.mass_cap_lower s hs

theorem log_cap_nonneg (s : ℝ) (hs : 3 / 4 ≤ s) : 0 ≤ Real.log (SU2GaussianMass.cap s) := by
  have hs0 : 0 < s := by linarith only [hs]
  have h1 := SU2GaussianMass.mass_cap_lower s hs
  have h2 := mass_le_one s hs0.le
  have hc := cap_pos s hs0
  apply Real.log_nonneg
  have hm := SU2GaussianMass.mass_pos s
  nlinarith only [h1, h2, hc, hm]

/-- All but one time slice of temporal links are removed. -/
theorem tSet_card_lower : ((2 * n : ℕ) : ℝ) ^ 4 ≤ (tSet n).card + ((2 * n : ℕ) : ℝ) ^ 3 := by
  have hcompl : ((Finset.univ : Finset V') \ tSet n).card ≤ (2 * n) ^ 3 := by
    have hinj : Set.InjOn (fun x : V' => (Fin.tail x : Fin 3 → ZMod (2 * n)))
        (((Finset.univ : Finset V') \ tSet n : Finset V') : Set V') := by
      intro x hx y hy hxy
      have hval (z : V') (hz : z ∈ (Finset.univ : Finset V') \ tSet n) : (z 0).val + 1 = 2 * n := by
        have h1 : ¬ (z 0).val + 1 < 2 * n := by
          intro h
          exact (Finset.mem_sdiff.1 hz).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
        have h2 := ZMod.val_lt (z 0)
        omega
      have h0 : x 0 = y 0 := ZMod.val_injective _ (by
        have a := hval x (Finset.mem_coe.1 hx)
        have b := hval y (Finset.mem_coe.1 hy)
        omega)
      funext i
      refine Fin.cases h0 (fun j => ?_) i
      exact congrFun hxy j
    have hle := Finset.card_le_card_of_injOn _ (fun x _ => Finset.mem_univ _) hinj
    refine hle.trans_eq ?_
    simp [ZMod.card]
  have hc : ((Finset.univ : Finset V') \ tSet n).card + (tSet n).card = (2 * n) ^ 4 := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
    simp [ZMod.card]
  have : (2 * n) ^ 4 ≤ (tSet n).card + (2 * n) ^ 3 := by omega
  exact_mod_cast this

/-! ### A product trial weight -/

/-- The links the gauge removes. -/
def gSet : Finset (Edge V') := (tSet n).image (tE n)

/-- The exponent of the trial weight on one link: zero on a removed link, the squared distance to the flat field on the
others. -/
def gE (e : Edge V') (q : Q) : ℝ := if e ∈ gSet n then 0 else d q (flatConfiguration n e) ^ 2

/-- The trial weight, a product over links. -/
def trial (s : ℝ) (U : Configuration V' Q) : ℝ := ∏ e, Real.exp (-s * gE n e (U e))

theorem gE_continuous (e : Edge V') : Continuous (gE n e) := by
  unfold gE d
  by_cases he : e ∈ gSet n
  · simpa only [he, if_true] using continuous_const
  · simp only [he, if_false]
    fun_prop

theorem trial_continuous (s : ℝ) : Continuous (trial n s) :=
  continuous_finset_prod _ fun e _ =>
    Real.continuous_exp.comp (continuous_const.mul ((gE_continuous n e).comp (continuous_apply e)))

theorem trial_pos (s : ℝ) (U : Configuration V' Q) : 0 < trial n s U :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

theorem trial_eq_exp (s : ℝ) (U : Configuration V' Q) : trial n s U = Real.exp (-(s * ∑ e, gE n e (U e))) := by
  unfold trial
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem flat_of_mem (e : Edge V') (he : e ∈ gSet n) : flatConfiguration n e = 1 := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
  change flatLink x 0 = 1
  simp [flatLink]

/-- The mass of the trial weight. -/
theorem trial_mass (s : ℝ) :
    ∫ U, trial n s U ∂referenceMeasure Q V' = SU2GaussianMass.mass s ^ (linkCount n - (tSet n).card) := by
  unfold referenceMeasure trial
  have h := integral_fintype_prod_eq_prod (ι := Edge V') (E := fun _ => Q)
    (fun e q => Real.exp (-s * gE n e q)) (μ := fun _ => compactHaar Q)
  refine h.trans ?_
  have hf (e : Edge V') : ∫ q : Q, Real.exp (-s * gE n e q) ∂compactHaar Q =
      if e ∈ gSet n then 1 else SU2GaussianMass.mass s := by
    by_cases he : e ∈ gSet n
    · simp [gE, he]
    · simp only [gE, he, if_false]
      exact gaussian_translate _ _
  simp only [hf]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have hc : (Finset.univ.filter fun e => e ∉ gSet n).card = Fintype.card (Edge V') - (gSet n).card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rw [hc]
  unfold gSet
  rw [Finset.card_image_of_injective _ (tE_injective n)]
  rfl

theorem trial_mass_pos (s : ℝ) : 0 < ∫ U, trial n s U ∂referenceMeasure Q V' := by
  rw [trial_mass]
  exact pow_pos (SU2GaussianMass.mass_pos s) _

/-! ### The mean of one link under the trial weight -/

/-- The mean real part of a link under the Gaussian weight of parameter `s`. -/
def linkMean (s : ℝ) : ℝ := SU2HaarTilt.axisMean (2 * s)

theorem linkMean_mul_mass (s : ℝ) :
    linkMean s * SU2GaussianMass.mass s = Real.exp (-2 * s) * SU2HaarTilt.axisNumerator (2 * s) := by
  unfold linkMean SU2HaarTilt.axisMean
  rw [SU2GaussianMass.mass_eq_axis]
  have := SU2HaarTilt.axisPartition_pos (2 * s)
  field_simp

theorem d_sq_eq (g h : Q) : d g h ^ 2 = 2 - 2 * ((g : ℍ[ℝ]) * star (h : ℍ[ℝ])).re := by
  unfold d
  rw [norm_sub_sq_real, norm_coe, norm_coe, Quaternion.inner_def]
  ring

theorem re_star_comm (a b : ℍ[ℝ]) : (a * b).re = (b * a).re := SU2HaarTilt.real_mul_comm a b

/-- **One link, integrated.** Haar inversion kills the transverse part, so a Gaussian link enters a real part only through
its mean. -/
theorem link_mean (f : Q) (A B : ℍ[ℝ]) (s : ℝ) :
    ∫ w : Q, (A * (w : ℍ[ℝ]) * B).re * Real.exp (-s * d w f ^ 2) ∂compactHaar Q =
      linkMean s * SU2GaussianMass.mass s * (A * (f : ℍ[ℝ]) * B).re := by
  have e1 := integral_mul_right_eq_self (μ := compactHaar Q)
    (fun w : Q => (A * (w : ℍ[ℝ]) * B).re * Real.exp (-s * d w f ^ 2)) f
  rw [← e1, linkMean_mul_mass]
  have hd (k : Q) : d (k * f) f = ‖(k : ℍ[ℝ]) - 1‖ := by
    have e := d_mul_right f k 1
    rw [one_mul] at e
    rw [e]
    rfl
  have hint : (fun k : Q => (A * ((k * f : Q) : ℍ[ℝ]) * B).re * Real.exp (-s * d (k * f) f ^ 2)) =
      fun k : Q => Real.exp (-2 * s) * (SU2HaarTilt.axisWeight (2 * s) k * ⟪(k : ℍ[ℝ]), star ((f : ℍ[ℝ]) * B * A)⟫) := by
    funext k
    rw [hd, SU2GaussianMass.chord_square, Quaternion.inner_def, star_star]
    have ec : (A * ((k * f : Q) : ℍ[ℝ]) * B).re = ((k : ℍ[ℝ]) * ((f : ℍ[ℝ]) * B * A)).re := by
      have : ((k * f : Q) : ℍ[ℝ]) = (k : ℍ[ℝ]) * (f : ℍ[ℝ]) := rfl
      rw [this, mul_assoc, re_star_comm]
      simp only [mul_assoc]
    rw [ec]
    unfold SU2HaarTilt.axisWeight
    have : Real.exp (-s * (2 * (1 - (k : ℍ[ℝ]).re))) =
        Real.exp (-2 * s) * Real.exp (2 * s * (k : ℍ[ℝ]).re) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [this]
    ring
  rw [hint, integral_const_mul]
  have hax := SU2HaarTilt.axis_inner_integral (2 * s) (star ((f : ℍ[ℝ]) * B * A))
  rw [show (∫ k : Q, SU2HaarTilt.axisWeight (2 * s) k * ⟪(k : ℍ[ℝ]), star ((f : ℍ[ℝ]) * B * A)⟫ ∂compactHaar Q) =
    _ from hax]
  rw [Quaternion.re_star]
  have ef : (A * (f : ℍ[ℝ]) * B).re = ((f : ℍ[ℝ]) * B * A).re := by
    rw [mul_assoc, re_star_comm]
  rw [ef]
  ring

/-- The trial weight, split at one link. -/
theorem trial_update (s : ℝ) (U : Configuration V' Q) (e : Edge V') (w : Q) :
    trial n s (Function.update U e w) =
      Real.exp (-s * gE n e w) * ∏ e' ∈ Finset.univ.erase e, Real.exp (-s * gE n e' (U e')) := by
  unfold trial
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun e' he' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]

/-- The gauge-fixed field. -/
abbrev fx (U : Configuration V' Q) : Configuration V' Q := fixOn n (tSet n) U

theorem fx_mem (U : Configuration V' Q) (e : Edge V') (he : e ∈ gSet n) : fx n U e = 1 := by
  have : e ∈ (tSet n).image (tE n) := he
  simp only [fx, fixOn, this, if_true]

theorem fx_notMem (U : Configuration V' Q) (e : Edge V') (he : e ∉ gSet n) : fx n U e = U e := by
  have : e ∉ (tSet n).image (tE n) := he
  simp only [fx, fixOn, this, if_false]

theorem fx_update (U : Configuration V' Q) (e e' : Edge V') (w : Q) (h : e' ≠ e) :
    fx n (Function.update U e w) e' = fx n U e' := by
  by_cases he : e' ∈ gSet n
  · rw [fx_mem n _ _ he, fx_mem n _ _ he]
  · rw [fx_notMem n _ _ he, fx_notMem n _ _ he, Function.update_of_ne h]

theorem fx_coe_continuous (e : Edge V') : Continuous fun U : Configuration V' Q => ((fx n U e : Q) : ℍ[ℝ]) :=
  continuous_subtype_val.comp ((continuous_apply e).comp (fixOn_continuous n (tSet n)))

/-- The mean of a link under the trial weight: `1` on a removed link. -/
def meanE (s : ℝ) (e : Edge V') : ℝ := if e ∈ gSet n then 1 else linkMean s

theorem re_integrable (F : Configuration V' Q → ℝ) (hF : Continuous F) : Integrable F (referenceMeasure Q V') :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- **One link at a time.** Under the trial weight, a link entering a real part once can be replaced by its mean times the
flat link. -/
theorem trial_step (s : ℝ) (e : Edge V') (X Y : Configuration V' Q → ℍ[ℝ]) (hX : Continuous X) (hY : Continuous Y)
    (hXi : ∀ U w, X (Function.update U e w) = X U) (hYi : ∀ U w, Y (Function.update U e w) = Y U) :
    ∫ U, (X U * ((fx n U e : Q) : ℍ[ℝ]) * Y U).re * trial n s U ∂referenceMeasure Q V' =
      meanE n s e * ∫ U, (X U * ((flatConfiguration n e : Q) : ℍ[ℝ]) * Y U).re * trial n s U ∂referenceMeasure Q V' := by
  by_cases he : e ∈ gSet n
  · simp only [meanE, he, if_true, one_mul, fx_mem n _ e he, flat_of_mem n e he]
  · have hre : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
    have hH1 : Continuous fun U : Configuration V' Q => (X U * ((U e : Q) : ℍ[ℝ]) * Y U).re * trial n s U :=
      (hre.comp ((hX.mul (continuous_subtype_val.comp (continuous_apply e))).mul hY)).mul (trial_continuous n s)
    have hH2 : Continuous fun U : Configuration V' Q =>
        (X U * ((flatConfiguration n e : Q) : ℍ[ℝ]) * Y U).re * trial n s U :=
      (hre.comp ((hX.mul continuous_const).mul hY)).mul (trial_continuous n s)
    simp only [meanE, he, if_false, fx_notMem n _ e he]
    rw [resample n _ hH1 e, resample n _ hH2 e, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [Function.update_self, hXi, hYi, trial_update]
    set R := ∏ e' ∈ Finset.univ.erase e, Real.exp (-s * gE n e' (U e'))
    have hg (w : Q) : gE n e w = d w (flatConfiguration n e) ^ 2 := by simp only [gE, he, if_false]
    simp only [hg]
    have h1 : ∫ w : Q, (X U * (w : ℍ[ℝ]) * Y U).re *
          (Real.exp (-s * d w (flatConfiguration n e) ^ 2) * R) ∂compactHaar Q =
        (∫ w : Q, (X U * (w : ℍ[ℝ]) * Y U).re * Real.exp (-s * d w (flatConfiguration n e) ^ 2) ∂compactHaar Q) * R := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      change _ = _
      ring
    have h2 : ∫ w : Q, (X U * ((flatConfiguration n e : Q) : ℍ[ℝ]) * Y U).re *
          (Real.exp (-s * d w (flatConfiguration n e) ^ 2) * R) ∂compactHaar Q =
        (X U * ((flatConfiguration n e : Q) : ℍ[ℝ]) * Y U).re * SU2GaussianMass.mass s * R := by
      rw [← gaussian_translate (flatConfiguration n e) s, ← integral_const_mul, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      change _ = _
      ring
    rw [h1, h2, link_mean]
    ring

/-- The same for a link entering through its inverse. -/
theorem trial_step_star (s : ℝ) (e : Edge V') (X Y : Configuration V' Q → ℍ[ℝ]) (hX : Continuous X) (hY : Continuous Y)
    (hXi : ∀ U w, X (Function.update U e w) = X U) (hYi : ∀ U w, Y (Function.update U e w) = Y U) :
    ∫ U, (X U * star ((fx n U e : Q) : ℍ[ℝ]) * Y U).re * trial n s U ∂referenceMeasure Q V' =
      meanE n s e *
        ∫ U, (X U * star ((flatConfiguration n e : Q) : ℍ[ℝ]) * Y U).re * trial n s U ∂referenceMeasure Q V' := by
  have hs (z : ℍ[ℝ]) (U : Configuration V' Q) : (X U * star z * Y U).re = (star (Y U) * z * star (X U)).re := by
    rw [← Quaternion.re_star]
    simp only [star_mul, star_star, mul_assoc]
  simp only [hs]
  have hstar : Continuous fun q : ℍ[ℝ] => star q := continuous_star
  exact trial_step n s e (fun U => star (Y U)) (fun U => star (X U)) (hstar.comp hY) (hstar.comp hX)
    (fun U w => by simp only [hYi]) (fun U w => by simp only [hXi])

/-! ### The energy under the trial weight -/

theorem linkMean_le (s : ℝ) : linkMean s ≤ 1 ∧ -1 ≤ linkMean s := by
  have hP := SU2HaarTilt.axisPartition_pos (2 * s)
  have hw : Continuous (SU2HaarTilt.axisWeight (2 * s)) := SU2HaarTilt.axisWeight_continuous _
  have hre : Continuous fun q : Q => (q : ℍ[ℝ]).re := Quaternion.continuous_re.comp continuous_subtype_val
  have hi1 := (hw.mul hre).integrable_of_hasCompactSupport (μ := SU2HaarTilt.haar) (HasCompactSupport.of_compactSpace _)
  have hi2 := hw.integrable_of_hasCompactSupport (μ := SU2HaarTilt.haar) (HasCompactSupport.of_compactSpace _)
  have hb (q : Q) : |(q : ℍ[ℝ]).re| ≤ 1 := by
    have h := TwistedHessianField.re_abs_le (q : ℍ[ℝ])
    rwa [norm_coe] at h
  have hwp (q : Q) : 0 ≤ SU2HaarTilt.axisWeight (2 * s) q := (Real.exp_pos _).le
  have hN1 : SU2HaarTilt.axisNumerator (2 * s) ≤ SU2HaarTilt.axisPartition (2 * s) := by
    refine integral_mono hi1 hi2 fun q => ?_
    have := (abs_le.1 (hb q)).2
    exact mul_le_of_le_one_right (hwp q) this
  have hN2 : -SU2HaarTilt.axisPartition (2 * s) ≤ SU2HaarTilt.axisNumerator (2 * s) := by
    unfold SU2HaarTilt.axisPartition SU2HaarTilt.axisNumerator
    rw [← integral_neg]
    refine integral_mono hi2.neg hi1 fun q => ?_
    have := (abs_le.1 (hb q)).1
    change -_ ≤ _ * _
    nlinarith only [this, hwp q]
  unfold linkMean SU2HaarTilt.axisMean
  constructor
  · rw [div_le_one hP]
    exact hN1
  · rw [le_div_iff₀ hP]
    linarith only [hN2]

theorem meanE_le (s : ℝ) (e : Edge V') : meanE n s e ≤ 1 ∧ -1 ≤ meanE n s e := by
  unfold meanE
  split_ifs
  · norm_num
  · exact linkMean_le s

theorem bernoulli2 (a b : ℝ) (ha : a ≤ 1 ∧ -1 ≤ a) (hb : b ≤ 1 ∧ -1 ≤ b) :
    (a * b ≤ 1 ∧ -1 ≤ a * b) ∧ 1 - a * b ≤ (1 - a) + (1 - b) := by
  obtain ⟨a1, a2⟩ := ha
  obtain ⟨b1, b2⟩ := hb
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.2 a1) (by linarith only [b2] : 0 ≤ b + 1),
      mul_nonneg (by linarith only [a2] : 0 ≤ a + 1) (sub_nonneg.2 b1)]
  · nlinarith only [mul_nonneg (by linarith only [a2] : 0 ≤ a + 1) (by linarith only [b2] : 0 ≤ b + 1),
      mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1)]
  · nlinarith only [mul_nonneg (sub_nonneg.2 a1) (sub_nonneg.2 b1)]

theorem step_ne (x : V') (ν : Fin 4) : step (2 * n) x ν ≠ x := by
  intro h
  have h1 := congrFun h ν
  have h2 : step (2 * n) x ν ν = x ν + 1 := by simp [step]
  rw [h2] at h1
  have h3 : (1 : ZMod (2 * n)) = 0 := by simpa using h1
  have hpos := NeZero.pos n
  haveI : Fact (1 < 2 * n) := ⟨by omega⟩
  exact one_ne_zero h3

theorem coe_plaq (A B C D : Q) :
    ((A * B * C⁻¹ * D⁻¹ : Q) : ℍ[ℝ]) = (A : ℍ[ℝ]) * (B : ℍ[ℝ]) * star (C : ℍ[ℝ]) * star (D : ℍ[ℝ]) := rfl

theorem link_eOf (U : Configuration V' Q) (x : V') (μ : Fin 4) : linkValue (2 * n) Q U x μ = U (eOf n x μ) := rfl

/-- A sum over links, in coordinates. -/
theorem edge_sum (F : Edge V' → ℝ) : ∑ e, F e = ∑ μ, ∑ x, F (eOf n x μ) := by
  rw [← Equiv.sum_comp (edgeCoordinates (2 * n)).symm, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem re_self (Ω : Q) : ((Ω : ℍ[ℝ]) * star (Ω : ℍ[ℝ])).re = 1 := by
  have h := d_sq_eq Ω Ω
  have h0 : d Ω Ω = 0 := by simp [d]
  rw [h0] at h
  linarith only [h]

theorem defect_sq_re (L : V' → Fin 4 → Q) (μ ν : Fin 4) (x : V') :
    defect L μ ν x ^ 2 = 2 - 2 * ((L x μ : ℍ[ℝ]) * (L (step (2 * n) x μ) ν : ℍ[ℝ]) * star (L (step (2 * n) x ν) μ : ℍ[ℝ]) *
      star (L x ν : ℍ[ℝ]) * star ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ])).re := by
  unfold defect
  rw [d_sq_eq, coe_plaq]

/-- Four distinct links of a real part, replaced one at a time. -/
theorem four_step (s : ℝ) (A B C E : Edge V') (nAB : B ≠ A) (nAC : C ≠ A) (nAE : E ≠ A) (nBC : C ≠ B) (nBE : E ≠ B)
    (nCE : E ≠ C) (W : ℍ[ℝ]) :
    ∫ U, (((fx n U A : Q) : ℍ[ℝ]) * ((fx n U B : Q) : ℍ[ℝ]) * star ((fx n U C : Q) : ℍ[ℝ]) * star ((fx n U E : Q) : ℍ[ℝ]) *
        W).re * trial n s U ∂referenceMeasure Q V' =
      meanE n s A * meanE n s B * meanE n s C * meanE n s E *
        ∫ U, (((flatConfiguration n A : Q) : ℍ[ℝ]) * ((flatConfiguration n B : Q) : ℍ[ℝ]) *
          star ((flatConfiguration n C : Q) : ℍ[ℝ]) * star ((flatConfiguration n E : Q) : ℍ[ℝ]) * W).re *
            trial n s U ∂referenceMeasure Q V' := by
  have hind (e₀ e₁ : Edge V') (hn : e₁ ≠ e₀) (U : Configuration V' Q) (w : Q) :
      ((fx n (Function.update U e₀ w) e₁ : Q) : ℍ[ℝ]) = ((fx n U e₁ : Q) : ℍ[ℝ]) := by
    rw [fx_update n U e₀ e₁ w hn]
  have ca := fx_coe_continuous n A
  have cb := fx_coe_continuous n B
  have cc := fx_coe_continuous n C
  have ce := fx_coe_continuous n E
  have hstar : Continuous fun q : ℍ[ℝ] => star q := continuous_star
  generalize hfA : ((flatConfiguration n A : Q) : ℍ[ℝ]) = fA at *
  have s1 := trial_step n s A (fun _ => 1)
    (fun U => ((fx n U B : Q) : ℍ[ℝ]) * star ((fx n U C : Q) : ℍ[ℝ]) * star ((fx n U E : Q) : ℍ[ℝ]) * W) continuous_const
    (((cb.mul (hstar.comp cc)).mul (hstar.comp ce)).mul continuous_const) (fun _ _ => rfl)
    (fun U w => by simp only [hind A B nAB, hind A C nAC, hind A E nAE])
  have s2 := trial_step n s B (fun _ => fA) (fun U => star ((fx n U C : Q) : ℍ[ℝ]) * star ((fx n U E : Q) : ℍ[ℝ]) * W)
    continuous_const (((hstar.comp cc).mul (hstar.comp ce)).mul continuous_const) (fun _ _ => rfl)
    (fun U w => by simp only [hind B C nBC, hind B E nBE])
  generalize hfB : ((flatConfiguration n B : Q) : ℍ[ℝ]) = fB at *
  have s3 := trial_step_star n s C (fun _ => fA * fB) (fun U => star ((fx n U E : Q) : ℍ[ℝ]) * W) continuous_const
    ((hstar.comp ce).mul continuous_const) (fun _ _ => rfl) (fun U w => by simp only [hind C E nCE])
  generalize hfC : ((flatConfiguration n C : Q) : ℍ[ℝ]) = fC at *
  have s4 := trial_step_star n s E (fun _ => fA * fB * star fC) (fun _ => W) continuous_const
    continuous_const (fun _ _ => rfl) (fun _ _ => rfl)
  generalize hfE : ((flatConfiguration n E : Q) : ℍ[ℝ]) = fE at *
  simp only [one_mul, hfA] at s1
  simp only [mul_assoc] at s1 s2 s3 s4 ⊢
  rw [s1, s2, s3, s4]

/-- **The mean square defect of one plaquette under the trial weight** is exactly `2 - 2 m_a m_b m_c m_e`. Cross terms between
links of a plaquette vanish here, which is what the triangle inequality in `actionOne_le` loses. -/
theorem plaquette_trial (s : ℝ) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    ∫ U, defect (linkValue (2 * n) Q (fx n U)) μ ν x ^ 2 * trial n s U ∂referenceMeasure Q V' =
      (2 - 2 * (meanE n s (eOf n x μ) * meanE n s (eOf n (step (2 * n) x μ) ν) *
          meanE n s (eOf n (step (2 * n) x ν) μ) * meanE n s (eOf n x ν))) *
        ∫ U, trial n s U ∂referenceMeasure Q V' := by
  have hne : μ ≠ ν := h.ne
  have nAB : eOf n (step (2 * n) x μ) ν ≠ eOf n x μ := fun e => hne (eOf_inj n e).2.symm
  have nAC : eOf n (step (2 * n) x ν) μ ≠ eOf n x μ := fun e => step_ne n x ν (eOf_inj n e).1
  have nAE : eOf n x ν ≠ eOf n x μ := fun e => hne (eOf_inj n e).2.symm
  have nBC : eOf n (step (2 * n) x ν) μ ≠ eOf n (step (2 * n) x μ) ν := fun e => hne (eOf_inj n e).2
  have nBE : eOf n x ν ≠ eOf n (step (2 * n) x μ) ν := fun e => step_ne n x μ (eOf_inj n e).1.symm
  have nCE : eOf n x ν ≠ eOf n (step (2 * n) x ν) μ := fun e => hne (eOf_inj n e).2.symm
  have hflat : (((flatConfiguration n (eOf n x μ) : Q) : ℍ[ℝ]) * ((flatConfiguration n (eOf n (step (2 * n) x μ) ν) : Q) : ℍ[ℝ]) *
      star ((flatConfiguration n (eOf n (step (2 * n) x ν) μ) : Q) : ℍ[ℝ]) * star ((flatConfiguration n (eOf n x ν) : Q) : ℍ[ℝ]) *
      star ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ])).re = 1 := by
    have hf := flatLink_flat (N := 2 * n) x μ ν h
    have e' : ((flatLink x μ * flatLink (step (2 * n) x μ) ν * (flatLink (step (2 * n) x ν) μ)⁻¹ *
        (flatLink x ν)⁻¹ : Q) : ℍ[ℝ]) = ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ]) := by rw [hf]
    rw [coe_plaq] at e'
    have : ∀ y a, flatConfiguration n (eOf n y a) = flatLink y a := fun _ _ => rfl
    simp only [this]
    rw [e']
    exact re_self _
  have hF := four_step n s _ _ _ _ nAB nAC nAE nBC nBE nCE (star ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ]))
  simp only [hflat, one_mul] at hF
  have hpt (U : Configuration V' Q) : defect (linkValue (2 * n) Q (fx n U)) μ ν x ^ 2 * trial n s U =
      2 * trial n s U - 2 * ((((fx n U (eOf n x μ) : Q) : ℍ[ℝ]) * ((fx n U (eOf n (step (2 * n) x μ) ν) : Q) : ℍ[ℝ]) *
        star ((fx n U (eOf n (step (2 * n) x ν) μ) : Q) : ℍ[ℝ]) * star ((fx n U (eOf n x ν) : Q) : ℍ[ℝ]) *
        star ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ])).re * trial n s U) := by
    rw [defect_sq_re, link_eOf, link_eOf, link_eOf, link_eOf]
    ring
  simp only [hpt]
  have hre : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
  have hstar : Continuous fun q : ℍ[ℝ] => star q := continuous_star
  have hc1 : Continuous fun U => (((fx n U (eOf n x μ) : Q) : ℍ[ℝ]) * ((fx n U (eOf n (step (2 * n) x μ) ν) : Q) : ℍ[ℝ]) *
        star ((fx n U (eOf n (step (2 * n) x ν) μ) : Q) : ℍ[ℝ]) * star ((fx n U (eOf n x ν) : Q) : ℍ[ℝ]) *
        star ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ])).re * trial n s U :=
    (hre.comp ((((((fx_coe_continuous n _).mul (fx_coe_continuous n _)).mul (hstar.comp (fx_coe_continuous n _))).mul
      (hstar.comp (fx_coe_continuous n _)))).mul continuous_const)).mul (trial_continuous n s)
  rw [integral_sub ((re_integrable n _ (trial_continuous n s)).const_mul 2) ((re_integrable n _ hc1).const_mul 2),
    integral_const_mul, integral_const_mul, hF]
  ring

/-- The mean squared distance of one link to the flat field under the trial weight. -/
theorem link_trial (s : ℝ) (e : Edge V') :
    ∫ U, gE n e (U e) * trial n s U ∂referenceMeasure Q V' =
      (2 - 2 * meanE n s e) * ∫ U, trial n s U ∂referenceMeasure Q V' := by
  set f := flatConfiguration n e with hf
  have hpt (U : Configuration V' Q) : gE n e (U e) * trial n s U =
      2 * trial n s U - 2 * ((1 * ((fx n U e : Q) : ℍ[ℝ]) * star (f : ℍ[ℝ])).re * trial n s U) := by
    have hg : gE n e (U e) = d (fx n U e) f ^ 2 := by
      by_cases he : e ∈ gSet n
      · rw [fx_mem n U e he, hf, flat_of_mem n e he]
        simp [gE, he, d]
      · rw [fx_notMem n U e he]
        simp only [gE, he, if_false, hf]
    rw [hg, d_sq_eq, one_mul]
    ring
  simp only [hpt]
  have hre : Continuous fun q : ℍ[ℝ] => q.re := Quaternion.continuous_re
  have hc1 : Continuous fun U => (1 * ((fx n U e : Q) : ℍ[ℝ]) * star (f : ℍ[ℝ])).re * trial n s U :=
    (hre.comp ((continuous_const.mul (fx_coe_continuous n e)).mul continuous_const)).mul (trial_continuous n s)
  rw [integral_sub ((re_integrable n _ (trial_continuous n s)).const_mul 2) ((re_integrable n _ hc1).const_mul 2),
    integral_const_mul, integral_const_mul,
    trial_step n s e (fun _ => 1) (fun _ => star (f : ℍ[ℝ])) continuous_const continuous_const
      (fun _ _ => rfl) (fun _ _ => rfl)]
  simp only [one_mul, ← hf, re_self]
  ring

/-- The Bernoulli inequality over the four links of a plaquette: the mean square defect is at most the sum of the four mean
squared distances. -/
theorem plaquette_trial_le (s : ℝ) (p : PlaquetteIndex (2 * n)) :
    ∫ U, defect (linkValue (2 * n) Q (fx n U)) p.2.1.1 p.2.1.2 p.1 ^ 2 * trial n s U ∂referenceMeasure Q V' ≤
      ((2 - 2 * meanE n s (eOf n p.1 p.2.1.1)) + (2 - 2 * meanE n s (eOf n (step (2 * n) p.1 p.2.1.1) p.2.1.2)) +
        (2 - 2 * meanE n s (eOf n (step (2 * n) p.1 p.2.1.2) p.2.1.1)) + (2 - 2 * meanE n s (eOf n p.1 p.2.1.2))) *
        ∫ U, trial n s U ∂referenceMeasure Q V' := by
  rw [plaquette_trial n s p.1 p.2.1.1 p.2.1.2 p.2.2]
  refine mul_le_mul_of_nonneg_right ?_ (trial_mass_pos n s).le
  have m1 := meanE_le n s (eOf n p.1 p.2.1.1)
  have m2 := meanE_le n s (eOf n (step (2 * n) p.1 p.2.1.1) p.2.1.2)
  have m3 := meanE_le n s (eOf n (step (2 * n) p.1 p.2.1.2) p.2.1.1)
  have m4 := meanE_le n s (eOf n p.1 p.2.1.2)
  obtain ⟨b1, h1⟩ := bernoulli2 _ _ m1 m2
  obtain ⟨b2, h2⟩ := bernoulli2 _ _ b1 m3
  obtain ⟨-, h3⟩ := bernoulli2 _ _ b2 m4
  linarith only [h1, h2, h3]

theorem defect_fx_continuous (x : V') (μ ν : Fin 4) :
    Continuous fun U : Configuration V' Q => defect (linkValue (2 * n) Q (fx n U)) μ ν x := by
  have h := defect_continuous n x μ ν
  exact h.comp (fixOn_continuous n (tSet n))

theorem trial_action_eq (s : ℝ) :
    ∫ U, actionOne n (fx n U) * trial n s U ∂referenceMeasure Q V' =
      ∑ p : PlaquetteIndex (2 * n), ∫ U, defect (linkValue (2 * n) Q (fx n U)) p.2.1.1 p.2.1.2 p.1 ^ 2 * trial n s U
        ∂referenceMeasure Q V' := by
  have hdc (p : PlaquetteIndex (2 * n)) : Continuous fun U : Configuration V' Q =>
      defect (linkValue (2 * n) Q (fx n U)) p.2.1.1 p.2.1.2 p.1 ^ 2 * trial n s U :=
    ((defect_fx_continuous n p.1 p.2.1.1 p.2.1.2).pow 2).mul (trial_continuous n s)
  have hpt (U : Configuration V' Q) : actionOne n (fx n U) * trial n s U =
      ∑ p : PlaquetteIndex (2 * n), defect (linkValue (2 * n) Q (fx n U)) p.2.1.1 p.2.1.2 p.1 ^ 2 * trial n s U := by
    rw [TwistedNearFlat.actionOne_eq, actionL, Finset.sum_mul]
  simp only [hpt]
  exact integral_finset_sum _ fun p _ => re_integrable n _ (hdc p)

theorem trial_dist_eq (s : ℝ) :
    ∫ U, (∑ e, gE n e (U e)) * trial n s U ∂referenceMeasure Q V' =
      (∑ μ, ∑ x, (2 - 2 * meanE n s (eOf n x μ))) * ∫ U, trial n s U ∂referenceMeasure Q V' := by
  have hgc (e : Edge V') : Continuous fun U : Configuration V' Q => gE n e (U e) * trial n s U :=
    ((gE_continuous n e).comp (continuous_apply e)).mul (trial_continuous n s)
  have e1 : ∫ U, (∑ e, gE n e (U e)) * trial n s U ∂referenceMeasure Q V' =
      ∑ e, ∫ U, gE n e (U e) * trial n s U ∂referenceMeasure Q V' := by
    simp only [Finset.sum_mul]
    exact integral_finset_sum _ fun e _ => re_integrable n _ (hgc e)
  rw [e1]
  simp only [link_trial]
  rw [← Finset.sum_mul, edge_sum n]

/-- **The action against the trial weight.** Six plaquettes meet each link and each sees the link only through its squared
distance, with coefficient one, so the action costs `6`, not the `24` of `actionOne_le`. -/
theorem trial_action (s : ℝ) :
    ∫ U, actionOne n (fx n U) * trial n s U ∂referenceMeasure Q V' ≤
      6 * ∫ U, (∑ e, gE n e (U e)) * trial n s U ∂referenceMeasure Q V' := by
  rw [trial_action_eq, trial_dist_eq]
  refine (Finset.sum_le_sum fun p _ => plaquette_trial_le n s p).trans_eq ?_
  rw [← Finset.sum_mul, six_count n (fun x μ => 2 - 2 * meanE n s (eOf n x μ))]
  ring

/-- **Lower bound by a product trial.** For `β ≥ 0`, `Z(β) ≥ mass(6β)^(links - |tSet|)`. Jensen against the trial weight
replaces the `24` of the pointwise estimate `TwistedLocalization.actionOne_le` by `6`. The Gaussian mode count, by hand and not proved,
gives about `3 log mass(β) - 6.0` per vertex for `log Z` at weak coupling, against `3 log mass(β) - 8.06` here and `3 log mass(β) - 2.69` from `Elim.Zon_le`. -/
theorem Zr_lower_trial (β : ℝ) (hβ : 0 ≤ β) :
    SU2GaussianMass.mass (6 * β) ^ (linkCount n - (tSet n).card) ≤ Zr n β := by
  set s := 6 * β with hs
  have hfix : Zr n β = ∫ U, Real.exp (-(β * actionOne n (fx n U))) ∂referenceMeasure Q V' := by
    refine gauge_fix_temporal n (fun U => Real.exp (-(β * actionOne n U))) (weight_continuous n β) ?_
      (tSet n) subset_rfl
    intro h U
    simp only [actionOne_gauge]
  have hSc : Continuous fun U : Configuration V' Q => actionOne n (fx n U) :=
    (continuous_actionOne n).comp (fixOn_continuous n (tSet n))
  have hVc : Continuous fun U : Configuration V' Q => ∑ e, gE n e (U e) :=
    continuous_finset_sum _ fun e _ => (gE_continuous n e).comp (continuous_apply e)
  have hA := trial_action n s
  have hSt := re_integrable n _ (hSc.mul (trial_continuous n s))
  have hVt := re_integrable n _ (hVc.mul (trial_continuous n s))
  have htr := re_integrable n _ (trial_continuous n s)
  let W : Configuration V' Q → ℝ := fun U => -(β * actionOne n (fx n U)) + s * ∑ e, gE n e (U e)
  have hpt (U : Configuration V' Q) :
      trial n s U + (-(β * (actionOne n (fx n U) * trial n s U)) +
        s * ((∑ e, gE n e (U e)) * trial n s U)) ≤ Real.exp (-(β * actionOne n (fx n U))) := by
    have ht := trial_pos n s U
    have h1 := Real.add_one_le_exp (W U)
    have h2 : Real.exp (W U) * trial n s U = Real.exp (-(β * actionOne n (fx n U))) := by
      rw [trial_eq_exp, ← Real.exp_add]
      congr 1
      simp only [W]
      ring
    rw [← h2]
    have h3 := mul_le_mul_of_nonneg_right h1 ht.le
    simp only [W] at h3 ⊢
    linarith only [h3]
  rw [hfix, ← trial_mass n s]
  have hi1 : Integrable (fun U => β * (actionOne n (fx n U) * trial n s U)) (referenceMeasure Q V') :=
    hSt.const_mul β
  have hi2 : Integrable (fun U => s * ((∑ e, gE n e (U e)) * trial n s U)) (referenceMeasure Q V') :=
    hVt.const_mul s
  have hint : ∫ U, (trial n s U + (-(β * (actionOne n (fx n U) * trial n s U)) +
        s * ((∑ e, gE n e (U e)) * trial n s U))) ∂referenceMeasure Q V' ≤
      ∫ U, Real.exp (-(β * actionOne n (fx n U))) ∂referenceMeasure Q V' :=
    integral_mono (htr.add (hi1.neg.add hi2))
      (((weight_continuous n β).comp (fixOn_continuous n _)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (fun U => hpt U)
  refine le_trans ?_ hint
  have e1 : ∫ U, (trial n s U + (-(β * (actionOne n (fx n U) * trial n s U)) +
        s * ((∑ e, gE n e (U e)) * trial n s U))) ∂referenceMeasure Q V' =
      ∫ U, trial n s U ∂referenceMeasure Q V' + (-(β * ∫ U, actionOne n (fx n U) * trial n s U ∂referenceMeasure Q V') +
        s * ∫ U, (∑ e, gE n e (U e)) * trial n s U ∂referenceMeasure Q V') := by
    have hi0 : Integrable (fun U => -(β * (actionOne n (fx n U) * trial n s U))) (referenceMeasure Q V') := hi1.neg
    have hi3 : Integrable (fun U => -(β * (actionOne n (fx n U) * trial n s U)) +
        s * ((∑ e, gE n e (U e)) * trial n s U)) (referenceMeasure Q V') := hi0.add hi2
    rw [integral_add htr hi3, integral_add hi0 hi2, integral_neg, integral_const_mul, integral_const_mul]
  rw [e1]
  have : β * ∫ U, actionOne n (fx n U) * trial n s U ∂referenceMeasure Q V' ≤
      s * ∫ U, (∑ e, gE n e (U e)) * trial n s U ∂referenceMeasure Q V' := by
    have := mul_le_mul_of_nonneg_left hA hβ
    rw [hs]
    linarith only [this]
  linarith only [this]

/-! ### Several plaquettes on one link -/

theorem axisPartition_cosh (κ : ℝ) :
    SU2HaarTilt.axisPartition κ = ∫ q : Q, Real.cosh (κ * (q : ℍ[ℝ]).re) ∂compactHaar Q := by
  have hw : Continuous (SU2HaarTilt.axisWeight κ) := SU2HaarTilt.axisWeight_continuous _
  have hi := hw.integrable_of_hasCompactSupport (μ := compactHaar Q) (HasCompactSupport.of_compactSpace _)
  have hneg : ∫ q : Q, SU2HaarTilt.axisWeight κ ((-1 : Q) * q) ∂compactHaar Q = SU2HaarTilt.axisPartition κ :=
    integral_mul_left_eq_self (SU2HaarTilt.axisWeight κ) (-1 : Q)
  have hi2 : Integrable (fun q : Q => SU2HaarTilt.axisWeight κ ((-1 : Q) * q)) (compactHaar Q) :=
    (hw.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e (q : Q) : Real.cosh (κ * (q : ℍ[ℝ]).re) =
      (SU2HaarTilt.axisWeight κ q + SU2HaarTilt.axisWeight κ ((-1 : Q) * q)) / 2 := by
    rw [Real.cosh_eq]
    unfold SU2HaarTilt.axisWeight
    have : (((-1 : Q) * q : Q) : ℍ[ℝ]).re = -(q : ℍ[ℝ]).re := by
      simp [Unitary.coe_neg]
    rw [this]
    congr 2
    ring_nf
  simp only [e]
  rw [integral_div, integral_add hi hi2, hneg]
  change _ = (SU2HaarTilt.axisPartition κ + _) / 2
  ring

theorem axisPartition_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    SU2HaarTilt.axisPartition a ≤ SU2HaarTilt.axisPartition b := by
  rw [axisPartition_cosh, axisPartition_cosh]
  have hre : Continuous fun q : Q => (q : ℍ[ℝ]).re := Quaternion.continuous_re.comp continuous_subtype_val
  have hc (κ : ℝ) : Continuous fun q : Q => Real.cosh (κ * (q : ℍ[ℝ]).re) :=
    Real.continuous_cosh.comp (continuous_const.mul hre)
  refine integral_mono ((hc a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hc b).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun q => ?_
  refine Real.cosh_le_cosh.2 ?_
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg (ha.trans hab)]
  exact mul_le_mul_of_nonneg_right hab (abs_nonneg _)

/-- **Several plaquettes on one link.** If a link enters `k` plaquettes, its Gaussian integral is at most `mass (k t)`, with
equality when the `k` centres coincide. -/
theorem gauss_bundle {ι : Type*} (s : Finset ι) (g : ι → Q) (t : ℝ) (ht : 0 ≤ t) :
    ∫ w : Q, Real.exp (-t * ∑ i ∈ s, d w (g i) ^ 2) ∂compactHaar Q ≤ SU2GaussianMass.mass ((s.card : ℝ) * t) := by
  set A : ℍ[ℝ] := ∑ i ∈ s, (g i : ℍ[ℝ]) with hA
  set k : ℝ := (s.card : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hAn : ‖A‖ ≤ k := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_coe, Finset.sum_const, nsmul_eq_mul, mul_one, hk, le_refl]
  have hpt (w : Q) : Real.exp (-t * ∑ i ∈ s, d w (g i) ^ 2) =
      Real.exp (-2 * (k * t)) * SU2HaarTilt.tiltWeight t A w := by
    unfold SU2HaarTilt.tiltWeight
    rw [← Real.exp_add]
    congr 1
    have h1 : ∑ i ∈ s, d w (g i) ^ 2 = 2 * k - 2 * ⟪(w : ℍ[ℝ]), A⟫ := by
      rw [hA, inner_sum, Finset.mul_sum]
      simp only [d_sq_eq, Quaternion.inner_def]
      rw [Finset.sum_sub_distrib]
      simp [hk]
      ring
    rw [h1]
    ring
  simp only [hpt]
  rw [integral_const_mul]
  have hT : ∫ w : Q, SU2HaarTilt.tiltWeight t A w ∂compactHaar Q = SU2HaarTilt.axisPartition (2 * t * ‖A‖) := by
    by_cases hA0 : A = 0
    · have h0 : SU2HaarTilt.axisPartition 0 = 1 := by
        simp [SU2HaarTilt.axisPartition, SU2HaarTilt.axisWeight]
      rw [hA0]
      simp [SU2HaarTilt.tiltWeight, h0]
    · exact SU2HaarTilt.tiltPartition_eq_axis t A hA0
  rw [hT, SU2GaussianMass.mass_eq_axis]
  refine mul_le_mul_of_nonneg_left (axisPartition_mono (by positivity) ?_) (Real.exp_pos _).le
  have := mul_le_mul_of_nonneg_left hAn (by positivity : 0 ≤ 2 * t)
  linarith only [this]

section Elim

/-! ### Triangular integration, with several plaquettes on a link -/

variable (π : Equiv.Perm (Fin 4))

/-- The lexicographic rank of a vertex, reading its coordinates in the order `π`. -/
def rk (y : V') : Lex (Fin 4 → ℕ) := toLex fun k => (y (π k)).val

/-- The base of the plaquette whose later link along `τ` starts at `y`. -/
def dn (y : V') (τ : Fin 4) : V' := y - Pi.single τ 1

theorem step_dn (y : V') (τ : Fin 4) : step (2 * n) (dn n y τ) τ = y := by
  change y - Pi.single τ 1 + Pi.single τ 1 = y
  abel

theorem val_sub_one_lt (a : ZMod (2 * n)) (ha : a ≠ 0) : (a - 1).val < a.val := by
  have hpos := NeZero.pos n
  have h1 : (1 : ZMod (2 * n)).val = 1 := ZMod.val_one'' (by omega)
  have h2 : a.val ≠ 0 := by
    rwa [Ne, ZMod.val_eq_zero]
  rw [ZMod.val_sub (by omega), h1]
  omega

theorem rk_dn (y : V') (k : Fin 4) (hy : y (π k) ≠ 0) : rk n π (dn n y (π k)) < rk n π y := by
  refine ⟨k, fun j hj => ?_, ?_⟩
  · have : π j ≠ π k := fun h => hj.ne (π.injective h)
    change ((y - Pi.single (π k) 1 : V') (π j)).val = (y (π j)).val
    simp [this]
  · change ((y - Pi.single (π k) 1 : V') (π k)).val < (y (π k)).val
    simpa using val_sub_one_lt n _ hy

theorem rk_dn_up (y : V') (k m : Fin 4) (hkm : k < m) (hy : y (π k) ≠ 0) :
    rk n π (step (2 * n) (dn n y (π k)) (π m)) < rk n π y := by
  have hne : π k ≠ π m := fun h => hkm.ne (π.injective h)
  refine ⟨k, fun j hj => ?_, ?_⟩
  · have h1 : π j ≠ π k := fun h => hj.ne (π.injective h)
    have h2 : π j ≠ π m := fun h => (hj.trans hkm).ne (π.injective h)
    change ((y - Pi.single (π k) 1 + Pi.single (π m) 1 : V') (π j)).val = (y (π j)).val
    simp [h1, h2]
  · change ((y - Pi.single (π k) 1 + Pi.single (π m) 1 : V') (π k)).val < (y (π k)).val
    simpa [hne] using val_sub_one_lt n _ hy

theorem d_pos2 (A w C E Ω : Q) : d (A * w * C⁻¹ * E⁻¹) Ω = d w (A⁻¹ * Ω * (E * C)) := by
  have e1 : A * w * C⁻¹ * E⁻¹ = A * (w * (C⁻¹ * E⁻¹)) := by group
  have e2 : Ω = A * ((A⁻¹ * Ω * (E * C)) * (C⁻¹ * E⁻¹)) := by group
  rw [e1]
  conv_lhs => rw [e2]
  rw [d_mul_left, d_mul_right]

theorem d_pos3 (A B w E Ω : Q) : d (A * B * w⁻¹ * E⁻¹) Ω = d w (E⁻¹ * Ω⁻¹ * (A * B)) := by
  have e1 : A * B * w⁻¹ * E⁻¹ = (A * B) * (w⁻¹ * E⁻¹) := by group
  have e2 : Ω = (A * B) * ((E⁻¹ * Ω⁻¹ * (A * B))⁻¹ * E⁻¹) := by group
  rw [e1]
  conv_lhs => rw [e2]
  rw [d_mul_left, d_mul_right, TwistedLocalization.d_inv]

/-- A plaquette, as a function of its later link along `τ`, is a distance to a fixed centre. -/
theorem pd_center (U : Configuration V' Q) (y : V') (τ κ : Fin 4) (h : τ ≠ κ) :
    ∃ c : Q, ∀ w : Q, TwistedBadSet.pd n (linkValue (2 * n) Q (Function.update U (eOf n y κ) w)) τ κ (dn n y τ) = d w c := by
  set z := dn n y τ with hz
  have hstep : step (2 * n) z τ = y := step_dn n y τ
  have hne : z ≠ y := by
    intro h'
    have := step_ne n z τ
    rw [hstep] at this
    exact this h'.symm
  have l1 : eOf n z τ ≠ eOf n y κ := fun e => h (eOf_inj n e).2
  have l3 : eOf n (step (2 * n) z κ) τ ≠ eOf n y κ := fun e => h (eOf_inj n e).2
  have l4 : eOf n z κ ≠ eOf n y κ := fun e => hne (eOf_inj n e).1
  have l2 (w : Q) : linkValue (2 * n) Q (Function.update U (eOf n y κ) w) y κ = w := Function.update_self _ _ _
  rcases lt_or_gt_of_ne h with hlt | hgt
  · refine ⟨(linkValue (2 * n) Q U z τ)⁻¹ * ω ^ twistExp τ κ z *
      (linkValue (2 * n) Q U z κ * linkValue (2 * n) Q U (step (2 * n) z κ) τ), fun w => ?_⟩
    simp only [TwistedBadSet.pd, hlt, if_true]
    unfold defect
    rw [hstep, l2, link_update n U _ w _ _ l1, link_update n U _ w _ _ l3, link_update n U _ w _ _ l4, d_pos2]
  · have hngt : ¬ τ < κ := not_lt.2 hgt.le
    refine ⟨(linkValue (2 * n) Q U z τ)⁻¹ * (ω ^ twistExp κ τ z)⁻¹ *
      (linkValue (2 * n) Q U z κ * linkValue (2 * n) Q U (step (2 * n) z κ) τ), fun w => ?_⟩
    simp only [TwistedBadSet.pd, hngt, hgt, if_true, if_false]
    unfold defect
    rw [hstep, l2, link_update n U _ w _ _ l1, link_update n U _ w _ _ l3, link_update n U _ w _ _ l4, d_pos3]

/-- A plaquette does not see a link outside its four. -/
theorem pd_indep (U : Configuration V' Q) (e : Edge V') (w : Q) (τ κ : Fin 4) (z : V')
    (l1 : eOf n z τ ≠ e) (l2 : eOf n (step (2 * n) z τ) κ ≠ e) (l3 : eOf n (step (2 * n) z κ) τ ≠ e)
    (l4 : eOf n z κ ≠ e) :
    TwistedBadSet.pd n (linkValue (2 * n) Q (Function.update U e w)) τ κ z = TwistedBadSet.pd n (linkValue (2 * n) Q U) τ κ z := by
  unfold TwistedBadSet.pd
  split_ifs
  · unfold defect
    rw [link_update n U _ w _ _ l1, link_update n U _ w _ _ l2, link_update n U _ w _ _ l3, link_update n U _ w _ _ l4]
  · unfold defect
    rw [link_update n U _ w _ _ l1, link_update n U _ w _ _ l2, link_update n U _ w _ _ l3, link_update n U _ w _ _ l4]
  · rfl

/-- The data of a triangular integration. `Elim.T` is the set of base vertices, `π 0` the time axis, and a pair `(y, i)` owns
the link at `y` in direction `π (i+1)`. On `g` that link carries the plaquettes below it along the axes `ax i`, elsewhere only
the one along the time axis. The links along `π 0`, and those over `y (π 0) = 0`, own nothing and integrate to `1`. -/
structure Elim where
  ax : Fin 3 → Finset (Fin 4)
  g : Finset V'
  ax_lt : ∀ i, ∀ k ∈ ax i, k < i.succ
  ax_zero : ∀ i, (0 : Fin 4) ∈ ax i
  g_ne : ∀ y ∈ g, ∀ i, ∀ k ∈ ax i, y (π k) ≠ 0

variable {n π}
variable (D : Elim n π)

/-- The base vertices. -/
def Elim.T (_D : Elim n π) : Finset V' := Finset.univ.filter fun y => y (π 0) ≠ 0

/-- The axes of the plaquettes carried by a link. -/
def Elim.bundle (a : V' × Fin 3) : Finset (Fin 4) := if a.1 ∈ D.g then D.ax a.2 else {0}

theorem Elim.bundle_lt (a : V' × Fin 3) : ∀ k ∈ D.bundle a, k < a.2.succ := by
  intro k hk
  unfold Elim.bundle at hk
  split_ifs at hk
  · exact D.ax_lt _ _ hk
  · rw [Finset.mem_singleton.1 hk]
    exact Fin.succ_pos _

theorem Elim.bundle_ne (a : V' × Fin 3) (ha : a.1 ∈ D.T) : ∀ k ∈ D.bundle a, a.1 (π k) ≠ 0 := by
  intro k hk
  unfold Elim.bundle at hk
  split_ifs at hk with hg
  · exact D.g_ne _ hg _ _ hk
  · rw [Finset.mem_singleton.1 hk]
    exact (Finset.mem_filter.1 ha).2

/-- The factor of one owned link. -/
def Elim.F (t : ℝ) (a : V' × Fin 3) (U : Configuration V' Q) : ℝ :=
  Real.exp (-t * ∑ k ∈ D.bundle a,
    TwistedBadSet.pd n (linkValue (2 * n) Q U) (π k) (π a.2.succ) (dn n a.1 (π k)) ^ 2)

theorem pd_continuous (τ κ : Fin 4) (z : V') :
    Continuous fun U : Configuration V' Q => TwistedBadSet.pd n (linkValue (2 * n) Q U) τ κ z := by
  unfold TwistedBadSet.pd
  split_ifs
  · exact defect_continuous n z τ κ
  · exact defect_continuous n z κ τ
  · exact continuous_const

theorem Elim.F_continuous (t : ℝ) (a : V' × Fin 3) : Continuous (D.F t a) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun k _ => (pd_continuous _ _ _).pow 2))

theorem Elim.F_nonneg (t : ℝ) (a : V' × Fin 3) (U : Configuration V' Q) : 0 ≤ D.F t a U := (Real.exp_pos _).le

/-- The owned link. -/
def Elim.own (_D : Elim n π) (a : V' × Fin 3) : Edge V' := eOf n a.1 (π a.2.succ)

theorem Elim.F_integral (t : ℝ) (ht : 0 ≤ t) (a : V' × Fin 3) (U : Configuration V' Q) :
    ∫ w, D.F t a (Function.update U (D.own a) w) ∂compactHaar Q ≤
      SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t) := by
  have hne (k : Fin 4) (hk : k ∈ D.bundle a) : π k ≠ π a.2.succ := fun h =>
    (D.bundle_lt a k hk).ne (π.injective h)
  have hc (k : Fin 4) : ∃ c : Q, k ∈ D.bundle a → ∀ w : Q,
      TwistedBadSet.pd n (linkValue (2 * n) Q (Function.update U (D.own a) w)) (π k) (π a.2.succ) (dn n a.1 (π k)) = d w c := by
    by_cases hk : k ∈ D.bundle a
    · obtain ⟨c, hc⟩ := pd_center n U a.1 (π k) (π a.2.succ) (hne k hk)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h => absurd h hk⟩
  choose c hc using hc
  have e (w : Q) : D.F t a (Function.update U (D.own a) w) =
      Real.exp (-t * ∑ k ∈ D.bundle a, d w (c k) ^ 2) := by
    unfold Elim.F
    congr 2
    exact Finset.sum_congr rfl fun k hk => by rw [hc k hk w]
  simp only [e]
  exact gauss_bundle _ _ t ht

/-- A plaquette of a lower link does not see a higher owned link. -/
theorem Elim.F_indep (t : ℝ) (a b : V' × Fin 3) (U : Configuration V' Q) (w : Q) (hb : b.1 ∈ D.T)
    (hab : rk n π b.1 ≤ rk n π a.1) (hne : b ≠ a) :
    D.F t b (Function.update U (D.own a) w) = D.F t b U := by
  unfold Elim.F
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  have hy := D.bundle_ne b hb k hk
  have hlt := D.bundle_lt b k hk
  have r1 := rk_dn n π b.1 k hy
  have r2 := rk_dn_up n π b.1 k b.2.succ hlt hy
  rw [pd_indep n U (D.own a) w (π k) (π b.2.succ) (dn n b.1 (π k))]
  · intro h
    have h1 := (eOf_inj n h).1
    rw [← h1] at hab
    exact absurd r1 (not_lt.2 hab)
  · intro h
    rw [step_dn] at h
    obtain ⟨h1, h2⟩ := eOf_inj n h
    exact hne (Prod.ext h1 (Fin.succ_injective _ (π.injective h2)))
  · intro h
    have h1 := (eOf_inj n h).1
    rw [← h1] at hab
    exact absurd r2 (not_lt.2 hab)
  · intro h
    have h1 := (eOf_inj n h).1
    rw [← h1] at hab
    exact absurd r1 (not_lt.2 hab)

/-- **Triangular integration.** Integrating the owned links in order of decreasing rank gives one mass per owned link. -/
theorem Elim.prod_le (t : ℝ) (ht : 0 ≤ t) (s : Finset (V' × Fin 3)) :
    (∀ a ∈ s, a.1 ∈ D.T) →
    ∫ U, ∏ a ∈ s, D.F t a U ∂referenceMeasure Q V' ≤
      ∏ a ∈ s, SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t) := by
  refine Finset.induction_on_max_value (fun a : V' × Fin 3 => rk n π a.1) s ?_ ?_
  · intro _
    simp
  · intro a s ha hmax ih hsub
    have hsub' : ∀ b ∈ s, b.1 ∈ D.T := fun b hb => hsub b (Finset.mem_insert_of_mem hb)
    have hR : Continuous fun U => ∏ b ∈ s, D.F t b U :=
      continuous_finset_prod _ fun b _ => D.F_continuous t b
    have hH : Continuous fun U => D.F t a U * ∏ b ∈ s, D.F t b U := (D.F_continuous t a).mul hR
    have hRnn (U : Configuration V' Q) : 0 ≤ ∏ b ∈ s, D.F t b U := Finset.prod_nonneg fun b _ => D.F_nonneg t b U
    have hin (U : Configuration V' Q) :
        ∫ w, (D.F t a (Function.update U (D.own a) w) *
          ∏ b ∈ s, D.F t b (Function.update U (D.own a) w)) ∂compactHaar Q ≤
        SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t) * ∏ b ∈ s, D.F t b U := by
      have hind : ∀ w, ∏ b ∈ s, D.F t b (Function.update U (D.own a) w) = ∏ b ∈ s, D.F t b U := by
        intro w
        refine Finset.prod_congr rfl fun b hb => ?_
        exact D.F_indep t a b U w (hsub' b hb) (hmax b hb) (fun h => ha (h ▸ hb))
      simp only [hind]
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right (D.F_integral t ht a U) (hRnn U)
    simp only [Finset.prod_insert ha]
    rw [resample n _ hH (D.own a)]
    have hcontin : Continuous fun U : Configuration V' Q => ∫ w, (D.F t a (Function.update U (D.own a) w) *
          ∏ b ∈ s, D.F t b (Function.update U (D.own a) w)) ∂compactHaar Q := by
      have hu : Continuous (Function.uncurry fun (U : Configuration V' Q) (w : Q) =>
          D.F t a (Function.update U (D.own a) w) * ∏ b ∈ s, D.F t b (Function.update U (D.own a) w)) :=
        hH.comp (continuous_fst.update _ continuous_snd)
      have := continuous_parametric_integral_of_continuous (μ := compactHaar Q) hu isCompact_univ
      simpa only [Measure.restrict_univ] using this
    have hI : Integrable (fun U => SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t) * ∏ b ∈ s, D.F t b U)
        (referenceMeasure Q V') :=
      (continuous_const.mul hR).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    refine (integral_mono (hcontin.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) hI hin).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (ih hsub') (SU2GaussianMass.mass_pos _).le

/-! ### The action against the plaquettes used -/

/-- The plane of two distinct axes, sorted. -/
def planeOf (τ κ : Fin 4) : Plane := if h : τ ≠ κ then ⟨(min τ κ, max τ κ), min_lt_max.2 h⟩ else ⟨(0, 1), by decide⟩

theorem planeOf_cases : ∀ τ κ τ' κ' : Fin 4, τ ≠ κ → τ' ≠ κ' → planeOf τ κ = planeOf τ' κ' →
    (τ = τ' ∧ κ = κ') ∨ (τ = κ' ∧ κ = τ') := by
  decide

theorem pd_eq (L : V' → Fin 4 → Q) (τ κ : Fin 4) (h : τ ≠ κ) (z : V') :
    TwistedBadSet.pd n L τ κ z = defect L (planeOf τ κ).1.1 (planeOf τ κ).1.2 z := by
  simp only [planeOf, h, ne_eq, not_false_eq_true, dif_pos, TwistedBadSet.pd]
  rcases lt_or_gt_of_ne h with hlt | hgt
  · simp [hlt, hlt.le]
  · simp [hgt, hgt.le, not_lt.2 hgt.le]

/-- The action of the planes outside `Off`. -/
def onPart (Off : Finset Plane) (U : Configuration V' Q) : ℝ :=
  ∑ p : PlaquetteIndex (2 * n), if p.2 ∈ Off then 0 else defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2

/-- The action of the planes in `Off`. -/
def offPart (Off : Finset Plane) (U : Configuration V' Q) : ℝ :=
  ∑ p : PlaquetteIndex (2 * n), if p.2 ∈ Off then defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2 else 0

theorem on_add_off (Off : Finset Plane) (U : Configuration V' Q) :
    onPart (n := n) Off U + offPart (n := n) Off U = actionOne n U := by
  rw [TwistedNearFlat.actionOne_eq, actionL, onPart, offPart, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem onPart_continuous (Off : Finset Plane) : Continuous (onPart (n := n) Off) := by
  refine continuous_finset_sum _ fun p _ => ?_
  split_ifs
  · exact continuous_const
  · exact (defect_continuous n _ _ _).pow 2

theorem offPart_continuous (Off : Finset Plane) : Continuous (offPart (n := n) Off) := by
  refine continuous_finset_sum _ fun p _ => ?_
  split_ifs
  · exact (defect_continuous n _ _ _).pow 2
  · exact continuous_const

/-- The partition function without the planes in `Off`. -/
def Zon (Off : Finset Plane) (t : ℝ) : ℝ := ∫ U, Real.exp (-(t * onPart (n := n) Off U)) ∂referenceMeasure Q V'

/-- The action of the planes not in `Off` is at least the sum of the plaquettes used. -/
theorem Elim.sum_le (Off : Finset Plane) (hOff : ∀ i, ∀ k ∈ D.ax i, planeOf (π k) (π i.succ) ∉ Off)
    (U : Configuration V' Q) :
    ∑ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)), ∑ k ∈ D.bundle a,
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (π k) (π a.2.succ) (dn n a.1 (π k)) ^ 2 ≤ onPart (n := n) Off U := by
  let c : PlaquetteIndex (2 * n) → ℝ := fun p =>
    if p.2 ∈ Off then 0 else defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2
  have hc0 (p : PlaquetteIndex (2 * n)) : 0 ≤ c p := by
    simp only [c]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  let φ : (Σ _ : V' × Fin 3, Fin 4) → PlaquetteIndex (2 * n) := fun x =>
    (dn n x.1.1 (π x.2), planeOf (π x.2) (π x.1.2.succ))
  let S := (D.T ×ˢ (Finset.univ : Finset (Fin 3))).sigma fun a => D.bundle a
  have hne (a : V' × Fin 3) (k : Fin 4) (hk : k ∈ D.bundle a) : π k ≠ π a.2.succ := fun h =>
    (D.bundle_lt a k hk).ne (π.injective h)
  have hax (a : V' × Fin 3) (k : Fin 4) (hk : k ∈ D.bundle a) : k ∈ D.ax a.2 := by
    unfold Elim.bundle at hk
    split_ifs at hk
    · exact hk
    · rw [Finset.mem_singleton.1 hk]
      exact D.ax_zero _
  have hval (x : Σ _ : V' × Fin 3, Fin 4) (hx : x ∈ S) :
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (π x.2) (π x.1.2.succ) (dn n x.1.1 (π x.2)) ^ 2 = c (φ x) := by
    have hk := (Finset.mem_sigma.1 hx).2
    simp only [c, φ, hOff _ _ (hax _ _ hk), if_false]
    rw [pd_eq _ _ _ (hne _ _ hk)]
  have hinj : Set.InjOn φ (S : Set (Σ _ : V' × Fin 3, Fin 4)) := by
    rintro ⟨⟨y, i⟩, k⟩ hx ⟨⟨y', i'⟩, k'⟩ hx' he
    have hk := (Finset.mem_sigma.1 (Finset.mem_coe.1 hx)).2
    have hk' := (Finset.mem_sigma.1 (Finset.mem_coe.1 hx')).2
    have h1 : dn n y (π k) = dn n y' (π k') := congrArg Prod.fst he
    have h2 : planeOf (π k) (π i.succ) = planeOf (π k') (π i'.succ) := congrArg Prod.snd he
    have l1 := D.bundle_lt (y, i) k hk
    have l2 := D.bundle_lt (y', i') k' hk'
    rcases planeOf_cases _ _ _ _ (hne _ _ hk) (hne _ _ hk') h2 with ⟨a, b⟩ | ⟨a, b⟩
    · have ek : k = k' := π.injective a
      have ei : i = i' := Fin.succ_injective _ (π.injective b)
      subst ek
      subst ei
      have ey : y = y' := by
        have := congrArg (fun z => step (2 * n) z (π k)) h1
        simpa only [step_dn] using this
      subst ey
      rfl
    · exfalso
      have e1 : k = i'.succ := π.injective a
      have e2 : i.succ = k' := π.injective b
      simp only at l1 l2
      rw [e2] at l1
      rw [e1] at l1
      exact absurd (l1.trans l2) (lt_irrefl _)
  have hsum : ∑ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)), ∑ k ∈ D.bundle a,
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (π k) (π a.2.succ) (dn n a.1 (π k)) ^ 2 = ∑ x ∈ S, c (φ x) := by
    rw [← Finset.sum_congr rfl hval]
    exact (Finset.sum_sigma _ _ (fun x : (Σ _ : V' × Fin 3, Fin 4) =>
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (π x.2) (π x.1.2.succ) (dn n x.1.1 (π x.2)) ^ 2)).symm
  rw [hsum, ← Finset.sum_image hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun p _ _ => hc0 p

/-- **The partition function without some planes, from above.** One mass per owned link, with `k` plaquettes on the link costing
`mass (k t)`. By a hand count, not formalized, owners of this kind cannot beat the sizes `1, 2, 3` per vertex: spatial plaquettes owned
by distinct links of a slice are independent, so at most `2/3` of the links of a slice can own one. -/
theorem Elim.Zon_le (Off : Finset Plane) (hOff : ∀ i, ∀ k ∈ D.ax i, planeOf (π k) (π i.succ) ∉ Off) (t : ℝ) (ht : 0 ≤ t) :
    Zon (n := n) Off t ≤ ∏ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)), SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t) := by
  refine le_trans ?_ (D.prod_le t ht _ fun a ha => (Finset.mem_product.1 ha).1)
  refine integral_mono (((Real.continuous_exp.comp ((continuous_const.mul (onPart_continuous Off)).neg))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))
    ((continuous_finset_prod _ fun b _ => D.F_continuous t b).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) fun U => ?_
  change Real.exp _ ≤ ∏ a ∈ _, Real.exp _
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (D.sum_le Off hOff U) ht
  simp only [neg_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
  linarith only [h]

/-! ### Comparing Gaussian masses -/

theorem denominator_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    SU2QuotientRemainder.denominator a ≤ SU2QuotientRemainder.denominator b := by
  unfold SU2QuotientRemainder.denominator SqrtSourceRemainder.gammaAverage
  refine div_le_div_of_nonneg_right ?_ (Real.Gamma_pos_of_pos (by norm_num)).le
  unfold SqrtSourceRemainder.gammaIntegral
  refine integral_mono_ae (SqrtSourceRemainder.gamma_cutoff_integrable (by norm_num) ha)
    (SqrtSourceRemainder.gamma_cutoff_integrable (by norm_num) (ha.trans_le hab)) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  refine mul_le_mul_of_nonneg_left ?_ (SqrtSourceRemainder.gammaWeight_nonneg _ (le_of_lt hu))
  unfold SqrtSourceRemainder.cutoffSqrt
  refine Real.sqrt_le_sqrt (max_le_max ?_ le_rfl)
  have hu0 : 0 ≤ u := le_of_lt hu
  have : u / (2 * b) ≤ u / (2 * a) := div_le_div_of_nonneg_left hu0 (by positivity) (by linarith only [hab])
  linarith only [this]

theorem denominator_le_one {κ : ℝ} (hκ : 0 < κ) : SU2QuotientRemainder.denominator κ ≤ 1 := by
  unfold SU2QuotientRemainder.denominator SqrtSourceRemainder.gammaAverage
  have hG := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  rw [div_le_one hG]
  unfold SqrtSourceRemainder.gammaIntegral
  have hG2 : Real.Gamma (3 / 2) = ∫ u in Set.Ioi 0, SqrtSourceRemainder.gammaWeight (3 / 2) u := by
    rw [Real.Gamma_eq_integral (by norm_num)]
    rfl
  rw [hG2]
  refine integral_mono_ae (SqrtSourceRemainder.gamma_cutoff_integrable (by norm_num) hκ) ?_ ?_
  · have := Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 3 / 2)
    exact this
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    exact mul_le_of_le_one_right (SqrtSourceRemainder.gammaWeight_nonneg _ (le_of_lt hu))
      (SqrtSourceRemainder.cutoffSqrt_le_one hκ (le_of_lt hu))

/-- `mass s * s^(3/2)` increases, so `mass a / mass b ≤ (b/a)^(3/2)` for `a ≤ b`, with no constant lost. -/
theorem log_mass_sub_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Real.log (SU2GaussianMass.mass a) - Real.log (SU2GaussianMass.mass b) ≤ 3 / 2 * Real.log (b / a) := by
  have hb := ha.trans_le hab
  have hm := denominator_mono (a := 2 * a) (b := 2 * b) (by positivity) (by linarith only [hab])
  have h1 := SU2GaussianMass.mass_cap_identity a ha
  have h2 := SU2GaussianMass.mass_cap_identity b hb
  have hle : SU2GaussianMass.mass a * SU2GaussianMass.cap a ≤ SU2GaussianMass.mass b * SU2GaussianMass.cap b := by
    rw [h1, h2]
    linarith only [hm]
  have hma := SU2GaussianMass.mass_pos a
  have hmb := SU2GaussianMass.mass_pos b
  have hca := cap_pos a ha
  have hcb := cap_pos b hb
  have hl := Real.log_le_log (mul_pos hma hca) hle
  rw [Real.log_mul hma.ne' hca.ne', Real.log_mul hmb.ne' hcb.ne'] at hl
  have hr := log_cap_ratio a (b / a) ha (div_pos hb ha)
  rw [div_mul_cancel₀ _ ha.ne'] at hr
  linarith only [hl, hr]

/-- The opposite comparison, with the loss made explicit. -/
theorem log_mass_sub_ge (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (h : 3 / 8 < a) :
    3 / 2 * Real.log (b / a) + Real.log (1 - 3 / (8 * a)) ≤
      Real.log (SU2GaussianMass.mass a) - Real.log (SU2GaussianMass.mass b) := by
  have hb := ha.trans_le hab
  have h1 := SU2GaussianMass.mass_cap_identity a ha
  have h2 := SU2GaussianMass.mass_cap_identity b hb
  have hD1 := SqrtSourceRemainder.su2_denominator_lower (κ := 2 * a) (by positivity)
  have hD2 := denominator_le_one (κ := 2 * b) (by positivity)
  have hma := SU2GaussianMass.mass_pos a
  have hmb := SU2GaussianMass.mass_pos b
  have hca := cap_pos a ha
  have hcb := cap_pos b hb
  have hx : 0 < 1 - 3 / (8 * a) := by
    rw [sub_pos, div_lt_one (by positivity)]
    linarith only [h]
  have e : 3 / (4 * (2 * a)) = 3 / (8 * a) := by
    congr 1
    ring
  rw [e] at hD1
  have hle : (1 - 3 / (8 * a)) * (SU2GaussianMass.mass b * SU2GaussianMass.cap b) ≤
      SU2GaussianMass.mass a * SU2GaussianMass.cap a := by
    rw [h1, h2]
    change _ ≤ 2 * SqrtSourceRemainder.gammaAverage (3 / 2) (SqrtSourceRemainder.cutoffSqrt (2 * a))
    have : SU2QuotientRemainder.denominator (2 * b) ≤ 1 := hD2
    nlinarith only [hD1, this, hx]
  have hl := Real.log_le_log (mul_pos hx (mul_pos hmb hcb)) hle
  rw [Real.log_mul hx.ne' (mul_pos hmb hcb).ne', Real.log_mul hmb.ne' hcb.ne', Real.log_mul hma.ne' hca.ne'] at hl
  have hr := log_cap_ratio a (b / a) ha (div_pos hb ha)
  rw [div_mul_cancel₀ _ ha.ne'] at hr
  linarith only [hl, hr]

theorem neg_log_mass_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ -Real.log (SU2GaussianMass.mass s) := by
  have h := Real.log_le_log (SU2GaussianMass.mass_pos s) (mass_le_one s hs)
  rw [Real.log_one] at h
  linarith only [h]

/-! ### Counting vertices -/

theorem zero_slice (τ : Fin 4) :
    ((Finset.univ.filter fun y : V' => y τ = 0).card : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3 := by
  have hinj : Set.InjOn (fun y : V' => fun j : Fin 3 => y (τ.succAbove j))
      ((Finset.univ.filter fun y : V' => y τ = 0 : Finset V') : Set V') := by
    intro x hx y hy hxy
    funext i
    rcases Fin.eq_self_or_eq_succAbove τ i with rfl | ⟨j, rfl⟩
    · rw [(Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2, (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2]
    · exact congrFun hxy j
  have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset (Fin 3 → ZMod (2 * n)))) _
    (fun x _ => Finset.mem_univ _) hinj
  have e : (Finset.univ : Finset (Fin 3 → ZMod (2 * n))).card = (2 * n) ^ 3 := by
    simp [ZMod.card]
  rw [e] at hle
  exact_mod_cast hle

/-- The vertices where the coordinates in `A`, read through `π`, are not zero. -/
def gOf (A : Finset (Fin 4)) : Finset V' := Finset.univ.filter fun y => ∀ k ∈ A, y (π k) ≠ 0

theorem gOf_card (A : Finset (Fin 4)) :
    ((2 * n : ℕ) : ℝ) ^ 4 - A.card * ((2 * n : ℕ) : ℝ) ^ 3 ≤ ((gOf (n := n) (π := π) A).card : ℝ) := by
  have hsub : (Finset.univ : Finset V') ⊆ gOf (n := n) (π := π) A ∪
      A.biUnion fun k => Finset.univ.filter fun y : V' => y (π k) = 0 := by
    intro y _
    by_cases hy : ∀ k ∈ A, y (π k) ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩)
    · push_neg at hy
      obtain ⟨k, hk, h0⟩ := hy
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨k, hk, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (gOf (n := n) (π := π) A) (A.biUnion fun k => Finset.univ.filter fun y : V' => y (π k) = 0)
  have h3 : (((A.biUnion fun k => Finset.univ.filter fun y : V' => y (π k) = 0).card : ℕ) : ℝ) ≤
      A.card * ((2 * n : ℕ) : ℝ) ^ 3 := by
    have h4 := Finset.card_biUnion_le (s := A) (t := fun k => Finset.univ.filter fun y : V' => y (π k) = 0)
    have h5 : ((∑ k ∈ A, (Finset.univ.filter fun y : V' => y (π k) = 0).card : ℕ) : ℝ) ≤
        A.card * ((2 * n : ℕ) : ℝ) ^ 3 := by
      rw [Nat.cast_sum]
      have h7 : ∑ k ∈ A, (((Finset.univ.filter fun y : V' => y (π k) = 0).card : ℕ) : ℝ) ≤
          ∑ _k ∈ A, ((2 * n : ℕ) : ℝ) ^ 3 := Finset.sum_le_sum fun k _ => zero_slice (n := n) (π k)
      rwa [Finset.sum_const, nsmul_eq_mul] at h7
    refine le_trans ?_ h5
    exact_mod_cast h4
  have e : (Finset.univ : Finset V').card = (2 * n) ^ 4 := by
    simp [ZMod.card]
  rw [e] at h1
  have h6 : ((2 * n : ℕ) : ℝ) ^ 4 ≤ ((gOf (n := n) (π := π) A).card : ℝ) +
      ((A.biUnion fun k => Finset.univ.filter fun y : V' => y (π k) = 0).card : ℝ) := by
    exact_mod_cast h1.trans h2
  linarith only [h3, h6]

theorem card_le_vol (s : Finset V') : (s.card : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 4 := by
  have h := Finset.card_le_univ s
  have e : Fintype.card V' = (2 * n) ^ 4 := by simp [ZMod.card]
  rw [e] at h
  exact_mod_cast h

/-! ### The ratio of partition functions -/

theorem Elim.card_bundle (a : V' × Fin 3) :
    1 ≤ (D.bundle a).card ∧ (D.bundle a).card ≤ 3 := by
  constructor
  · refine Finset.card_pos.2 ⟨0, ?_⟩
    unfold Elim.bundle
    split_ifs
    · exact D.ax_zero _
    · exact Finset.mem_singleton_self _
  · have hsub : D.bundle a ⊆ ({0, 1, 2} : Finset (Fin 4)) := by
      intro k hk
      have h1 := D.bundle_lt a k hk
      have h2 : k < 3 := lt_of_lt_of_le h1 (Fin.le_last _)
      revert h2
      clear h1 hk
      revert k
      decide
    exact (Finset.card_le_card hsub).trans (by decide)

theorem Elim.g_sub : D.g ⊆ D.T := fun y hy =>
  Finset.mem_filter.2 ⟨Finset.mem_univ _, D.g_ne y hy 0 0 (D.ax_zero 0)⟩

/-- The sum over owned links of the logarithm of the bundle size. -/
theorem Elim.sum_log_card :
    ∑ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)), Real.log ((D.bundle a).card : ℝ) =
      (D.g.card : ℝ) * ∑ i, Real.log ((D.ax i).card : ℝ) := by
  rw [Finset.sum_product]
  have hy (y : V') : ∑ i, Real.log ((D.bundle (y, i)).card : ℝ) =
      if y ∈ D.g then ∑ i, Real.log ((D.ax i).card : ℝ) else 0 := by
    by_cases hg : y ∈ D.g
    · simp [Elim.bundle, hg]
    · simp [Elim.bundle, hg]
  simp only [hy]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 D.g_sub, Finset.sum_const, nsmul_eq_mul]

/-- The upper bound, in logarithms. -/
theorem Elim.log_Zon_le (Off : Finset Plane) (hOff : ∀ i, ∀ k ∈ D.ax i, planeOf (π k) (π i.succ) ∉ Off) (t : ℝ) (ht : 0 < t) :
    Real.log (Zon (n := n) Off t) ≤ ∑ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)),
      Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t)) := by
  have hZpos : 0 < Zon (n := n) Off t := integral_exp_pos
    ((Real.continuous_exp.comp ((continuous_const.mul (onPart_continuous Off)).neg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have h := Real.log_le_log hZpos (D.Zon_le Off hOff t ht.le)
  rwa [Real.log_prod (fun a _ => (SU2GaussianMass.mass_pos _).ne')] at h

/-- **The ratio of partition functions, in general.** With `L = log mass` and `N = 2n`,
`log Z_on(t) - log Z(β) ≤ N⁴ (9/2) log(6β/t) - |g| (3/2) Σ_i log |ax i| + 4 N³ (-L(6β))`. -/
theorem Elim.log_ratio (Off : Finset Plane) (hOff : ∀ i, ∀ k ∈ D.ax i, planeOf (π k) (π i.succ) ∉ Off)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 < t) (ht2 : t ≤ 2 * β) :
    Real.log (Zon (n := n) Off t) - Real.log (Zr n β) ≤
      ((2 * n : ℕ) : ℝ) ^ 4 * (9 / 2 * Real.log (6 * β / t)) -
        (D.g.card : ℝ) * (3 / 2 * ∑ i, Real.log ((D.ax i).card : ℝ)) +
        4 * ((2 * n : ℕ) : ℝ) ^ 3 * -Real.log (SU2GaussianMass.mass (6 * β)) := by
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  set L6 := Real.log (SU2GaussianMass.mass (6 * β)) with hL6
  set Kc := D.T ×ˢ (Finset.univ : Finset (Fin 3)) with hKc
  have hL6n : 0 ≤ -L6 := neg_log_mass_nonneg _ (by positivity)
  -- The upper bound, link by link.
  have hup : Real.log (Zon (n := n) Off t) ≤ ∑ a ∈ Kc, Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t)) :=
    D.log_Zon_le Off hOff t ht
  have hlink (a : V' × Fin 3) : Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t)) ≤
      L6 + 3 / 2 * (Real.log (6 * β / t) - Real.log ((D.bundle a).card : ℝ)) := by
    obtain ⟨c1, c3⟩ := D.card_bundle a
    have hc1 : (1 : ℝ) ≤ ((D.bundle a).card : ℝ) := by exact_mod_cast c1
    have hc3 : ((D.bundle a).card : ℝ) ≤ 3 := by exact_mod_cast c3
    have hc0 : (0 : ℝ) < ((D.bundle a).card : ℝ) := by linarith only [hc1]
    have hle : ((D.bundle a).card : ℝ) * t ≤ 6 * β := by nlinarith only [hc3, ht, ht2, hβ]
    have h := log_mass_sub_le _ _ (mul_pos hc0 ht) hle
    have e : Real.log (6 * β / (((D.bundle a).card : ℝ) * t)) =
        Real.log (6 * β / t) - Real.log ((D.bundle a).card : ℝ) := by
      rw [show 6 * β / (((D.bundle a).card : ℝ) * t) = (6 * β / t) / ((D.bundle a).card : ℝ) by field_simp,
        Real.log_div (by positivity) hc0.ne']
    rw [e] at h
    linarith only [h]
  have hKcard : (Kc.card : ℝ) = 3 * (D.T.card : ℝ) := by
    rw [hKc, Finset.card_product]
    simp
    ring
  have hsum : ∑ a ∈ Kc, Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * t)) ≤
      3 * (D.T.card : ℝ) * L6 + 3 * (D.T.card : ℝ) * (3 / 2 * Real.log (6 * β / t)) -
        (D.g.card : ℝ) * (3 / 2 * ∑ i, Real.log ((D.ax i).card : ℝ)) := by
    refine (Finset.sum_le_sum fun a _ => hlink a).trans_eq ?_
    simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hKcard]
    rw [← Finset.mul_sum, hKc, D.sum_log_card]
    ring
  -- The lower bound.
  have hlow : -Real.log (Zr n β) ≤ (4 * N ^ 4 - (tSet n).card) * -L6 := by
    have hm := SU2GaussianMass.mass_pos (6 * β)
    have h1 := Real.log_le_log (pow_pos hm _) (Zr_lower_trial n β hβ.le)
    rw [Real.log_pow] at h1
    have hle : (tSet n).card ≤ linkCount n := by
      rw [linkCount_eq]
      have := Finset.card_le_univ (tSet n)
      have e : Fintype.card V' = (2 * n) ^ 4 := by simp [ZMod.card]
      rw [e] at this
      omega
    have hcast : ((linkCount n - (tSet n).card : ℕ) : ℝ) = 4 * N ^ 4 - (tSet n).card := by
      rw [Nat.cast_sub hle, linkCount_eq, hN]
      push_cast
      ring
    rw [hcast] at h1
    linarith only [h1]
  have hTl : N ^ 4 - N ^ 3 ≤ (D.T.card : ℝ) := by
    have h := gOf_card (n := n) (π := π) {0}
    simp only [gOf, Finset.mem_singleton, forall_eq, Finset.card_singleton, Nat.cast_one, one_mul] at h
    exact h
  have hTu : (D.T.card : ℝ) ≤ N ^ 4 := card_le_vol (n := n) _
  have htl : N ^ 4 - N ^ 3 ≤ ((tSet n).card : ℝ) := by
    have := tSet_card_lower n
    linarith only [this]
  have hLog : 0 ≤ Real.log (6 * β / t) := Real.log_nonneg (by
    rw [le_div_iff₀ ht]
    linarith only [ht2, hβ])
  have hrem : (4 * N ^ 4 - (tSet n).card - 3 * (D.T.card : ℝ)) * -L6 ≤ 4 * N ^ 3 * -L6 :=
    mul_le_mul_of_nonneg_right (by linarith only [hTl, htl]) hL6n
  have hbulk : 3 * (D.T.card : ℝ) * (3 / 2 * Real.log (6 * β / t)) ≤ N ^ 4 * (9 / 2 * Real.log (6 * β / t)) := by
    have := mul_le_mul_of_nonneg_right hTu (by positivity : 0 ≤ 9 / 2 * Real.log (6 * β / t))
    linarith only [this]
  nlinarith only [hup, hsum, hlow, hrem, hbulk]

end Elim

/-! ### Concrete choices of plaquettes -/

/-- Build the data from a set of required nonzero coordinates. -/
def mkElim (π : Equiv.Perm (Fin 4)) (ax : Fin 3 → Finset (Fin 4)) (A : Finset (Fin 4))
    (h1 : ∀ i, ∀ k ∈ ax i, k < i.succ) (h0 : ∀ i, (0 : Fin 4) ∈ ax i) (hA : ∀ i, ax i ⊆ A) : Elim n π :=
  ⟨ax, gOf A, h1, h0, fun _ hy i k hk => (Finset.mem_filter.1 hy).2 k (hA i hk)⟩

/-- `Elim.log_ratio` with the count of `g` made explicit. -/
theorem ratio_of (π : Equiv.Perm (Fin 4)) (ax : Fin 3 → Finset (Fin 4)) (A : Finset (Fin 4))
    (h1 : ∀ i, ∀ k ∈ ax i, k < i.succ) (h0 : ∀ i, (0 : Fin 4) ∈ ax i) (hA : ∀ i, ax i ⊆ A)
    (Off : Finset Plane) (hOff : ∀ i, ∀ k ∈ ax i, planeOf (π k) (π i.succ) ∉ Off)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 < t) (ht2 : t ≤ 2 * β) :
    Real.log (Zon (n := n) Off t) - Real.log (Zr n β) ≤
      ((2 * n : ℕ) : ℝ) ^ 4 * (9 / 2 * Real.log (6 * β / t)) -
        (((2 * n : ℕ) : ℝ) ^ 4 - A.card * ((2 * n : ℕ) : ℝ) ^ 3) * (3 / 2 * ∑ i, Real.log ((ax i).card : ℝ)) +
        4 * ((2 * n : ℕ) : ℝ) ^ 3 * -Real.log (SU2GaussianMass.mass (6 * β)) := by
  have h := (mkElim (n := n) π ax A h1 h0 hA).log_ratio Off hOff β t hβ ht ht2
  have hg := gOf_card (n := n) (π := π) A
  have hs : 0 ≤ 3 / 2 * ∑ i, Real.log ((ax i).card : ℝ) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Real.log_natCast_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hg hs
  refine h.trans ?_
  change _ - ((gOf (n := n) (π := π) A).card : ℝ) * (3 / 2 * ∑ i, Real.log ((ax i).card : ℝ)) + _ ≤ _
  linarith only [hm]

theorem Zon_empty (t : ℝ) : Zon (n := n) ∅ t = Zr n t := by
  unfold Zon Zr
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  have h := on_add_off (n := n) ∅ U
  have h0 : offPart (n := n) ∅ U = 0 := by simp [offPart]
  change Real.exp _ = Real.exp _
  rw [h0, add_zero] at h
  rw [h]

/-- Every link direction carries all the plaquettes below it in the order of the axes. -/
def allAx : Fin 3 → Finset (Fin 4) := ![{0}, {0, 1}, {0, 1, 2}]

/-- The link directions carry the plaquettes along the first two axes only. -/
def twoAx : Fin 3 → Finset (Fin 4) := ![{0}, {0, 1}, {0, 1}]

/-- As `twoAx`, with the last direction carrying only the time plaquette. -/
def mixAx : Fin 3 → Finset (Fin 4) := ![{0}, {0, 1}, {0}]

theorem log_six : Real.log 2 + Real.log 3 = Real.log 6 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem sum_allAx : ∑ i, Real.log ((allAx i).card : ℝ) = Real.log 6 := by
  have a0 : (allAx 0).card = 1 := by decide
  have a1 : (allAx 1).card = 2 := by decide
  have a2 : (allAx 2).card = 3 := by decide
  rw [Fin.sum_univ_three, a0, a1, a2, ← log_six]
  norm_num

theorem sum_twoAx : ∑ i, Real.log ((twoAx i).card : ℝ) = Real.log 4 := by
  have a0 : (twoAx 0).card = 1 := by decide
  have a1 : (twoAx 1).card = 2 := by decide
  have a2 : (twoAx 2).card = 2 := by decide
  rw [Fin.sum_univ_three, a0, a1, a2, show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem sum_mixAx : ∑ i, Real.log ((mixAx i).card : ℝ) = Real.log 2 := by
  have a0 : (mixAx 0).card = 1 := by decide
  have a1 : (mixAx 1).card = 2 := by decide
  have a2 : (mixAx 2).card = 1 := by decide
  rw [Fin.sum_univ_three, a0, a1, a2]
  norm_num

/-! ### The energy per vertex, with no logarithm at leading order -/

/-- The constant of the energy bound. -/
def energyConst (β l : ℝ) : ℝ :=
  (9 / 2 * Real.log (6 / l) - 3 / 2 * Real.log 6) + 9 / (4 * (n : ℝ)) * Real.log 6 +
    2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β))

theorem vol_div (a : ℝ) : ((2 * n : ℕ) : ℝ) ^ 4 * (a / (n : ℝ)) = 2 * a * ((2 * n : ℕ) : ℝ) ^ 3 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  push_cast
  field_simp

/-- **The ratio of partition functions.** For `β > 0` and `0 < l < 1`, `log Z(lβ) - log Z(β) ≤ N⁴ · energyConst`. -/
theorem log_ratio_le (β l : ℝ) (hβ : 0 < β) (hl0 : 0 < l) (hl1 : l < 1) :
    Real.log (Zr n (l * β)) - Real.log (Zr n β) ≤ ((2 * n : ℕ) : ℝ) ^ 4 * energyConst n β l := by
  have h := ratio_of (n := n) 1 allAx {0, 1, 2} (by decide) (by decide) (by decide) ∅ (by simp)
    β (l * β) hβ (mul_pos hl0 hβ) (by nlinarith only [hl1, hβ])
  rw [Zon_empty, sum_allAx, show 6 * β / (l * β) = 6 / l by field_simp] at h
  have hc : (({0, 1, 2} : Finset (Fin 4)).card : ℝ) = 3 := by
    have : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [this]
    norm_num
  rw [hc] at h
  refine h.trans_eq ?_
  unfold energyConst
  have e1 := vol_div (n := n) (9 / 4 * Real.log 6)
  have e2 := vol_div (n := n) (2 * -Real.log (SU2GaussianMass.mass (6 * β)))
  have e3 : ((2 * n : ℕ) : ℝ) ^ 4 * (9 / (4 * (n : ℝ)) * Real.log 6) =
      ((2 * n : ℕ) : ℝ) ^ 4 * (9 / 4 * Real.log 6 / (n : ℝ)) := by
    congr 1
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp
  have e4 : ((2 * n : ℕ) : ℝ) ^ 4 * (2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β))) =
      ((2 * n : ℕ) : ℝ) ^ 4 * (2 * -Real.log (SU2GaussianMass.mass (6 * β)) / (n : ℝ)) := by
    congr 1
    ring
  rw [mul_add, mul_add, e3, e4, e1, e2]
  ring

/-- **The energy per vertex.** `(1 - l) β E[S] ≤ N⁴ · energyConst`. The best `l` is about `0.29`, which gives about `15.42/β` per vertex at
large `n`. Nothing about any one plane follows beyond `planeMean_le`. -/
theorem energy_le (β l : ℝ) (hβ : 0 < β) (hl0 : 0 < l) (hl1 : l < 1) :
    (1 - l) * β * energy n β ≤ ((2 * n : ℕ) : ℝ) ^ 4 * energyConst n β l := by
  have hJ := energy_jensen n β (l * β)
  have hrw : (β - l * β) = (1 - l) * β := by ring
  rw [hrw] at hJ
  exact hJ.trans (log_ratio_le n β l hβ hl0 hl1)

/-- The energy per vertex, the logarithmic form. It needs only the lower bound on `Z`. The existing `TwistedFlow.law_action_le` has
`4 N⁴ log cap(24β)` here. -/
theorem energy_le_log (β : ℝ) (hβ : 0 < β) :
    β * energy n β ≤ (3 * ((2 * n : ℕ) : ℝ) ^ 4 + ((2 * n : ℕ) : ℝ) ^ 3) * -Real.log (SU2GaussianMass.mass (6 * β)) := by
  have hJ := energy_jensen n β 0
  rw [Zr_zero, Real.log_one, sub_zero, zero_sub] at hJ
  have hL := neg_log_mass_nonneg (6 * β) (by positivity)
  have hm := SU2GaussianMass.mass_pos (6 * β)
  have h1 := Real.log_le_log (pow_pos hm _) (Zr_lower_trial n β hβ.le)
  rw [Real.log_pow] at h1
  have hle : (tSet n).card ≤ linkCount n := by
    rw [linkCount_eq]
    have := Finset.card_le_univ (tSet n)
    have e : Fintype.card V' = (2 * n) ^ 4 := by simp [ZMod.card]
    rw [e] at this
    omega
  have hcast : ((linkCount n - (tSet n).card : ℕ) : ℝ) = 4 * ((2 * n : ℕ) : ℝ) ^ 4 - (tSet n).card := by
    rw [Nat.cast_sub hle, linkCount_eq]
    push_cast
    ring
  rw [hcast] at h1
  have htl := tSet_card_lower n
  have h2 := mul_le_mul_of_nonneg_right
    (by linarith only [htl] : 4 * ((2 * n : ℕ) : ℝ) ^ 4 - (tSet n).card ≤ 3 * ((2 * n : ℕ) : ℝ) ^ 4 + ((2 * n : ℕ) : ℝ) ^ 3) hL
  nlinarith only [hJ, h1, h2]

/-- **A lower bound on the energy, of the same power of `β`.** For `β ≥ 1/4`, with `x = (3/2) log(4/3) + log(1 - 1/(16 β)) ≥ 0`,
`7 β E[S] ≥ 3 (N⁴ - N³) x + (N⁴ - 3 N³) (3/2) log 6 - 4 N³ (-log mass(6β))`.
Per vertex at large `n` and `β` this is about `0.57/β`, against the upper `15.42/β`, a factor of about `27`. The right side
is negative unless `n` is large against `log cap(6β)`, and it bounds only the orientation sum, not any one plaquette. -/
theorem energy_ge (β : ℝ) (hβ : 1 / 4 ≤ β) :
    3 * (((2 * n : ℕ) : ℝ) ^ 4 - ((2 * n : ℕ) : ℝ) ^ 3) * (3 / 2 * Real.log (4 / 3) + Real.log (1 - 1 / (16 * β))) +
        (((2 * n : ℕ) : ℝ) ^ 4 - 3 * ((2 * n : ℕ) : ℝ) ^ 3) * (3 / 2 * Real.log 6) -
        4 * ((2 * n : ℕ) : ℝ) ^ 3 * -Real.log (SU2GaussianMass.mass (6 * β)) ≤ 7 * β * energy n β := by
  have hβ0 : 0 < β := by linarith only [hβ]
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  set L6 := Real.log (SU2GaussianMass.mass (6 * β)) with hL6
  set x := 3 / 2 * Real.log (4 / 3) + Real.log (1 - 1 / (16 * β)) with hx
  let D : Elim n 1 := mkElim n 1 allAx {0, 1, 2} (by decide) (by decide) (by decide)
  have hL6n : 0 ≤ -L6 := neg_log_mass_nonneg _ (by positivity)
  have hJ := energy_jensen n β (8 * β)
  have hlin : (β - 8 * β) * energy n β = -(7 * β * energy n β) := by ring
  rw [hlin] at hJ
  -- The upper bound at `8 β`.
  have hup := D.log_Zon_le ∅ (by simp) (8 * β) (by positivity)
  rw [Zon_empty] at hup
  have hlink (a : V' × Fin 3) :
      x + 3 / 2 * Real.log ((D.bundle a).card : ℝ) ≤ L6 - Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * (8 * β))) := by
    obtain ⟨c1, -⟩ := D.card_bundle a
    have hc1 : (1 : ℝ) ≤ ((D.bundle a).card : ℝ) := by exact_mod_cast c1
    have hc0 : (0 : ℝ) < ((D.bundle a).card : ℝ) := by linarith only [hc1]
    have h6 : 6 * β ≤ ((D.bundle a).card : ℝ) * (8 * β) := by nlinarith only [hc1, hβ0]
    have h := log_mass_sub_ge (6 * β) _ (by positivity) h6 (by linarith only [hβ])
    have e : ((D.bundle a).card : ℝ) * (8 * β) / (6 * β) = ((D.bundle a).card : ℝ) * (4 / 3) := by
      field_simp
      ring
    rw [e, Real.log_mul hc0.ne' (by norm_num), show 3 / (8 * (6 * β)) = 1 / (16 * β) by field_simp; ring] at h
    rw [hx, ← hL6] at *
    linarith only [h]
  have hTl : N ^ 4 - N ^ 3 ≤ (D.T.card : ℝ) := by
    have h := gOf_card (n := n) (π := 1) {0}
    simp only [gOf, Finset.mem_singleton, forall_eq, Finset.card_singleton, Nat.cast_one, one_mul] at h
    exact h
  have hTu : (D.T.card : ℝ) ≤ N ^ 4 := card_le_vol (n := n) _
  have hg : N ^ 4 - 3 * N ^ 3 ≤ (D.g.card : ℝ) := by
    have h := gOf_card (n := n) (π := 1) {0, 1, 2}
    have hc : (({0, 1, 2} : Finset (Fin 4)).card : ℝ) = 3 := by
      have : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
      rw [this]
      norm_num
    rw [hc] at h
    exact h
  have hKcard : ((D.T ×ˢ (Finset.univ : Finset (Fin 3))).card : ℝ) = 3 * (D.T.card : ℝ) := by
    rw [Finset.card_product]
    simp
    ring
  have hsum : 3 * (D.T.card : ℝ) * x + (D.g.card : ℝ) * (3 / 2 * Real.log 6) ≤
      3 * (D.T.card : ℝ) * L6 - ∑ a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3)),
        Real.log (SU2GaussianMass.mass (((D.bundle a).card : ℝ) * (8 * β))) := by
    have h := Finset.sum_le_sum fun a (_ : a ∈ D.T ×ˢ (Finset.univ : Finset (Fin 3))) => hlink a
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hKcard, ← Finset.mul_sum] at h
    rw [D.sum_log_card, show (∑ i, Real.log ((D.ax i).card : ℝ)) = Real.log 6 from sum_allAx] at h
    linarith only [h]
  -- The lower bound at `β`.
  have hlow : (4 * N ^ 4 - (tSet n).card) * L6 ≤ Real.log (Zr n β) := by
    have hm := SU2GaussianMass.mass_pos (6 * β)
    have h1 := Real.log_le_log (pow_pos hm _) (Zr_lower_trial n β hβ0.le)
    rw [Real.log_pow] at h1
    have hle : (tSet n).card ≤ linkCount n := by
      rw [linkCount_eq]
      have := Finset.card_le_univ (tSet n)
      have e : Fintype.card V' = (2 * n) ^ 4 := by simp [ZMod.card]
      rw [e] at this
      omega
    have hcast : ((linkCount n - (tSet n).card : ℕ) : ℝ) = 4 * N ^ 4 - (tSet n).card := by
      rw [Nat.cast_sub hle, linkCount_eq, hN]
      push_cast
      ring
    rwa [hcast] at h1
  have htl : N ^ 4 - N ^ 3 ≤ ((tSet n).card : ℝ) := by
    have := tSet_card_lower n
    linarith only [this]
  have htu : ((tSet n).card : ℝ) ≤ N ^ 4 := card_le_vol (n := n) _
  have hrem : (4 * N ^ 4 - (tSet n).card - 3 * (D.T.card : ℝ)) * -L6 ≤ 4 * N ^ 3 * -L6 :=
    mul_le_mul_of_nonneg_right (by linarith only [hTl, htl]) hL6n
  have hx0 : 0 ≤ x := by
    have h34 : (3 : ℝ) / 4 ≤ 1 - 1 / (16 * β) := by
      have : 1 / (16 * β) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith only [hβ]
      linarith only [this]
    have h1 := Real.log_le_log (by norm_num) h34
    have h2 : Real.log (3 / 4) = -Real.log (4 / 3) := by
      rw [← Real.log_inv]
      norm_num
    have h3 : 0 ≤ Real.log (4 / 3) := Real.log_nonneg (by norm_num)
    rw [hx]
    linarith only [h1, h2, h3]
  have hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hA := mul_le_mul_of_nonneg_right hTl hx0
  have hB := mul_le_mul_of_nonneg_right hg (by positivity : 0 ≤ 3 / 2 * Real.log 6)
  nlinarith only [hJ, hup, hsum, hlow, hrem, hA, hB]

/-! ### One plane, with no assumption on the others -/

/-- Any plane can be placed last in the order of the axes. -/
theorem exists_perm : ∀ μ ν : Fin 4, μ < ν → ∃ π : Equiv.Perm (Fin 4), π 2 = μ ∧ π 3 = ν := by
  decide

/-- The mean action of a set of planes is a sum of the mean square defects of its orientations. -/
theorem offPart_mean (Off : Finset Plane) (β : ℝ) :
    ∫ U, offPart (n := n) Off U ∂twistedLaw n β =
      ((2 * n : ℕ) : ℝ) ^ 4 * ∑ d ∈ Off, planeMean n β d.1.1 d.1.2 := by
  have hc (p : PlaquetteIndex (2 * n)) : Continuous fun U : Configuration V' Q =>
      if p.2 ∈ Off then defect (linkValue (2 * n) Q U) p.2.1.1 p.2.1.2 p.1 ^ 2 else 0 := by
    split_ifs
    · exact (defect_continuous n _ _ _).pow 2
    · exact continuous_const
  have e1 : ∫ U, offPart (n := n) Off U ∂twistedLaw n β = ∑ p : PlaquetteIndex (2 * n),
      if p.2 ∈ Off then planeMean n β p.2.1.1 p.2.1.2 else 0 := by
    unfold offPart
    rw [integral_finset_sum _ fun p _ => (hc p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.2 ∈ Off
    · simp only [hp, if_true]
      exact planeMean_eq n β _ _ p.2.2 p.1
    · simp [hp]
  rw [e1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_vertex]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Jensen for a set of planes.** `β N⁴ Σ_{d ∈ Off} m_d ≤ log Z_on(β) - log Z(β)`: the coupling of the planes in `Off` is
lowered to zero. -/
theorem off_jensen (Off : Finset Plane) (β : ℝ) :
    β * (((2 * n : ℕ) : ℝ) ^ 4 * ∑ d ∈ Off, planeMean n β d.1.1 d.1.2) ≤
      Real.log (Zon (n := n) Off β) - Real.log (Zr n β) := by
  have h := gen_jensen n β β (offPart (n := n) Off) (offPart_continuous Off)
  rw [offPart_mean] at h
  refine h.trans_eq ?_
  congr 2
  unfold Zon
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change Real.exp _ = Real.exp _
  congr 1
  have := on_add_off (n := n) Off U
  rw [← this]
  ring

/-- The bound for one plane. -/
def planeBound (β : ℝ) : ℝ :=
  (3 / 2 * Real.log 54 + 3 / (2 * (n : ℝ)) * Real.log 4 + 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β))) / β

theorem twoAx_mem : ∀ (i : Fin 3) (k : Fin 4), k ∈ twoAx i → (k = 0 ∨ k = 1) ∧ k < i.succ := by
  decide

/-- **One plane.** The mean square defect of any orientation is at most `planeBound`. At large `n` this is
`(3/2) log 54 / β ≈ 5.98/β`, and nothing is assumed about any other plane or any cross term. -/
theorem planeMean_le (β : ℝ) (hβ : 0 < β) (μ ν : Fin 4) (h : μ < ν) : planeMean n β μ ν ≤ planeBound n β := by
  obtain ⟨π, h2, h3⟩ := exists_perm μ ν h
  have hne : μ ≠ ν := h.ne
  have hP : planeOf μ ν = ⟨(μ, ν), h⟩ := by
    simp [planeOf, hne, min_eq_left h.le, max_eq_right h.le]
  have hOff : ∀ i, ∀ k ∈ twoAx i, planeOf (π k) (π i.succ) ∉ ({⟨(μ, ν), h⟩} : Finset Plane) := by
    intro i k hk hmem
    obtain ⟨hk01, hki⟩ := twoAx_mem i k hk
    have e := Finset.mem_singleton.1 hmem
    rw [← hP] at e
    have hne' : π k ≠ π i.succ := fun h' => hki.ne (π.injective h')
    rw [← h2, ← h3] at e
    have hne23 : π 2 ≠ π 3 := fun h' => absurd (π.injective h') (by decide)
    rcases planeOf_cases _ _ _ _ hne' hne23 e with ⟨a, -⟩ | ⟨a, -⟩
    · have := π.injective a
      rcases hk01 with rfl | rfl <;> exact absurd this (by decide)
    · have := π.injective a
      rcases hk01 with rfl | rfl <;> exact absurd this (by decide)
  have hR := ratio_of (n := n) π twoAx {0, 1} (by decide) (by decide) (by decide) _ hOff β β hβ hβ (by linarith only [hβ])
  have hJ := off_jensen (n := n) {⟨(μ, ν), h⟩} β
  rw [Finset.sum_singleton] at hJ
  rw [sum_twoAx, show 6 * β / β = 6 by field_simp] at hR
  have hc : (({0, 1} : Finset (Fin 4)).card : ℝ) = 2 := by
    have : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
    rw [this]
    norm_num
  rw [hc] at hR
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    have := NeZero.pos n
    positivity
  have h54 : Real.log 54 = 3 * Real.log 6 - Real.log 4 := by
    rw [show (54 : ℝ) = 6 ^ 3 / 4 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  unfold planeBound
  rw [le_div_iff₀ hβ]
  have hm : ((2 * n : ℕ) : ℝ) ^ 4 * (planeMean n β μ ν * β) ≤ ((2 * n : ℕ) : ℝ) ^ 4 *
      (3 / 2 * Real.log 54 + 3 / (2 * (n : ℝ)) * Real.log 4 + 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β))) := by
    have e1 := vol_div (n := n) (3 / 2 * Real.log 4)
    have e2 := vol_div (n := n) (2 * -Real.log (SU2GaussianMass.mass (6 * β)))
    have e3 : 3 / (2 * (n : ℝ)) * Real.log 4 = 3 / 2 * Real.log 4 / (n : ℝ) := by
      have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
      field_simp
    have e4 : 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) =
        2 * -Real.log (SU2GaussianMass.mass (6 * β)) / (n : ℝ) := by ring
    rw [mul_add, mul_add, e3, e4, e1, e2, h54]
    calc _ = β * (((2 * n : ℕ) : ℝ) ^ 4 * planeMean n β μ ν) := by ring
      _ ≤ _ := hJ.trans hR
      _ = _ := by ring
  exact le_of_mul_le_mul_left hm hN

/-- **The volume-free local bound.** For every `β > 0`, every orientation and every position, `E[d²] ≤ planeBound`. -/
theorem defect_sq_le (β : ℝ) (hβ : 0 < β) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂twistedLaw n β ≤ planeBound n β := by
  rw [planeMean_eq n β μ ν h x]
  exact planeMean_le n β hβ μ ν h

/-- The logarithmic form, from the energy. It is `(3 + 1/(2n)) ≤ 7/2` times `-log mass(6β)/β`. -/
theorem defect_sq_le_log (β : ℝ) (hβ : 0 < β) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂twistedLaw n β ≤
      7 / 2 * -Real.log (SU2GaussianMass.mass (6 * β)) / β := by
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    have := NeZero.pos n
    positivity
  have hN1 : ((2 * n : ℕ) : ℝ) ^ 3 ≤ 1 / 2 * ((2 * n : ℕ) : ℝ) ^ 4 := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
    have h2 : (2 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      push_cast
      linarith only [hn]
    have h3 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 3 := by positivity
    have e : ((2 * n : ℕ) : ℝ) ^ 4 = ((2 * n : ℕ) : ℝ) * ((2 * n : ℕ) : ℝ) ^ 3 := by ring
    rw [e]
    nlinarith only [h2, h3]
  have hL := neg_log_mass_nonneg (6 * β) (by positivity)
  have hE := energy_le_log n β hβ
  refine (defect_sq_le_energy n β μ ν h x).trans ?_
  rw [div_le_div_iff₀ hN hβ]
  have h3 := mul_le_mul_of_nonneg_right
    (by linarith only [hN1] : 3 * ((2 * n : ℕ) : ℝ) ^ 4 + ((2 * n : ℕ) : ℝ) ^ 3 ≤ 7 / 2 * ((2 * n : ℕ) : ℝ) ^ 4) hL
  nlinarith only [hE, h3]

/-- The numerator of the logarithmic form is below the numerator of `TwistedFlow.law_term_mean` at every `β ≥ 1/32`, and the
denominators are the same `β`. So `defect_sq_le_log` implies the flow-time-zero case of that theorem. -/
theorem log_form_le (β : ℝ) (hβ : 1 / 32 ≤ β) :
    7 / 2 * -Real.log (SU2GaussianMass.mass (6 * β)) ≤ 4 * Real.log (SU2GaussianMass.cap (24 * β)) := by
  have hβ0 : 0 < β := by linarith only [hβ]
  set s0 := max (6 * β) (3 / 4) with hs0
  have h34 : 3 / 4 ≤ s0 := le_max_right _ _
  have h6 : 6 * β ≤ s0 := le_max_left _ _
  have hs24 : s0 ≤ 24 * β := max_le (by linarith only [hβ0]) (by linarith only [hβ])
  have hs0p : 0 < s0 := by linarith only [h34]
  have h1 : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ -Real.log (SU2GaussianMass.mass s0) := by
    have := Real.log_le_log (SU2GaussianMass.mass_pos _) (SU2GaussianMass.mass_antitone h6)
    linarith only [this]
  have h2 := log_mass_lower s0 h34
  have h3 : Real.log (SU2GaussianMass.cap s0) ≤ Real.log (SU2GaussianMass.cap (24 * β)) := by
    have hr : 0 < 24 * β / s0 := by positivity
    have := log_cap_ratio s0 (24 * β / s0) hs0p hr
    rw [div_mul_cancel₀ _ hs0p.ne'] at this
    have h4 : 0 ≤ Real.log (24 * β / s0) := Real.log_nonneg (by
      rw [le_div_iff₀ hs0p]
      linarith only [hs24])
    linarith only [this, h4]
  have hc := log_cap_nonneg (24 * β) (by linarith only [hβ])
  linarith only [h1, h2, h3, hc]

/-- **The tail of one plaquette, with no volume factor.** This is Chebyshev on the second moment, not an exponential
tail, so a union over all plaquettes costs the full volume. -/
theorem defect_tail (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    twistedLaw n β {U | δ < defect (linkValue (2 * n) Q U) μ ν x} ≤
      ENNReal.ofReal (planeBound n β / δ ^ 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := twistedLaw n β)
    (f := fun U => defect (linkValue (2 * n) Q U) μ ν x ^ 2)
    (Filter.Eventually.of_forall fun U => sq_nonneg _) (defect_sq_integrable n β x μ ν) (δ ^ 2)
  have hb := defect_sq_le n β hβ μ ν h x
  have hd2 : 0 < δ ^ 2 := by positivity
  have hsub : {U | δ < defect (linkValue (2 * n) Q U) μ ν x} ⊆
      {U | δ ^ 2 ≤ defect (linkValue (2 * n) Q U) μ ν x ^ 2} := by
    intro U hU
    exact pow_le_pow_left₀ hδ.le (le_of_lt hU) 2
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (μ := twistedLaw n β)]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hd2, mul_comm]
  exact hm.trans hb

/-- The energy tail through the ratio of partition functions. -/
theorem energy_tail (β l s : ℝ) (hβ : 0 < β) (hl1 : l < 1) :
    twistedLaw n β {U | s ≤ actionOne n U} ≤
      ENNReal.ofReal (Real.exp (-((1 - l) * β * s)) * (Zr n (l * β) / Zr n β)) := by
  set θ := (1 - l) * β with hθ
  have hθ0 : 0 < θ := mul_pos (by linarith only [hl1]) hβ
  have hc : Continuous fun U : Configuration V' Q => Real.exp (θ * actionOne n U) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_actionOne n))
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := twistedLaw n β)
    (f := fun U => Real.exp (θ * actionOne n U)) (Filter.Eventually.of_forall fun U => (Real.exp_pos _).le)
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (Real.exp (θ * s))
  rw [exp_moment, show β - θ = l * β by rw [hθ]; ring] at hm
  have hsub : {U | s ≤ actionOne n U} ⊆ {U | Real.exp (θ * s) ≤ Real.exp (θ * actionOne n U)} := by
    intro U hU
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hU hθ0.le)
  refine (measure_mono hsub).trans ?_
  rw [← ofReal_measureReal (μ := twistedLaw n β)]
  apply ENNReal.ofReal_le_ofReal
  have hp : Real.exp (-(θ * s)) * Real.exp (θ * s) = 1 := by
    rw [← Real.exp_add]
    simp
  calc _ = Real.exp (-(θ * s)) * (Real.exp (θ * s) * _) := by rw [← mul_assoc, hp, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le

/-- **The density of bad plaquettes.** Except with probability `exp(-t N⁴)`, the number of plaquettes with defect above `δ`
times `δ²` is below `N⁴ (energyConst + t) / ((1 - l) β)`. The probability here is `exp(-t N⁴)`; `TwistedBadSet.measure_bad_density`
writes `exp(-t' links) = exp(-4 t' N⁴)`, so the two compare at `t = 4 t'`. It concerns the density, not any one plaquette. -/
theorem measure_bad_density_free (β l δ t : ℝ) (hβ : 0 < β) (hl0 : 0 < l) (hl1 : l < 1) (hδ0 : 0 ≤ δ) :
    twistedLaw n β {U | ((2 * n : ℕ) : ℝ) ^ 4 * (energyConst n β l + t) / ((1 - l) * β) ≤
        ((TwistedBadSet.badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(t * ((2 * n : ℕ) : ℝ) ^ 4))) := by
  have hp : 0 < (1 - l) * β := mul_pos (by linarith only [hl1]) hβ
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hN
  set C := energyConst n β l with hC
  set s := N ^ 4 * (C + t) / ((1 - l) * β) with hs
  have hsub : {U : Configuration V' Q | s ≤ ((TwistedBadSet.badPlaq n (linkValue (2 * n) Q U) δ).card : ℝ) * δ ^ 2} ⊆
      {U | s ≤ actionOne n U} := by
    intro U hU
    change s ≤ actionOne n U
    rw [TwistedNearFlat.actionOne_eq]
    exact le_trans hU (TwistedBadSet.card_badPlaq_le n _ δ hδ0)
  refine (measure_mono hsub).trans ((energy_tail n β l s hβ hl1).trans (ENNReal.ofReal_le_ofReal ?_))
  have hR := log_ratio_le n β l hβ hl0 hl1
  have hZ : Zr n (l * β) / Zr n β ≤ Real.exp (N ^ 4 * C) := by
    have hdiv : 0 < Zr n (l * β) / Zr n β := div_pos (Zr_pos n _) (Zr_pos n _)
    rw [← Real.log_le_iff_le_exp hdiv, Real.log_div (Zr_pos n _).ne' (Zr_pos n _).ne']
    exact hR
  have hexp : Real.exp (-((1 - l) * β * s)) * Real.exp (N ^ 4 * C) = Real.exp (-(t * N ^ 4)) := by
    have hcancel : (1 - l) * β * s = N ^ 4 * (C + t) := by
      rw [hs]
      exact mul_div_cancel₀ _ hp.ne'
    rw [← Real.exp_add, hcancel]
    congr 1
    ring
  rw [← hexp]
  exact mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le

/-! ### The plaquette rates -/

open TwistedIBP TwistedHessianField TwistedActionJet in
theorem conj_re (u : Q) (y : ℍ[ℝ]) (hy : star y = -y) : ((u : ℍ[ℝ]) * y * ((u⁻¹ : Q) : ℍ[ℝ])).re = 0 := by
  have hs : star ((u : ℍ[ℝ]) * y * ((u⁻¹ : Q) : ℍ[ℝ])) = -((u : ℍ[ℝ]) * y * ((u⁻¹ : Q) : ℍ[ℝ])) := by
    have hi : ((u⁻¹ : Q) : ℍ[ℝ]) = star (u : ℍ[ℝ]) := rfl
    rw [hi, star_mul, star_mul, star_star, hy]
    noncomm_ring
  have h := congrArg (fun q : ℍ[ℝ] => q.re) hs
  simp only [Quaternion.re_star, Quaternion.re_neg] at h
  linarith only [h]

open TwistedIBP TwistedHessianField TwistedActionJet in
/-- The rate of a plaquette vanishes where its defect does: `|A_p| ≤ (Σ_{e∈p} ‖X_e‖) · d_p`. -/
theorem Ap_abs_le_defect (X : Fin 3 → Fin 4 → TwistedHessian.Section (2 * n)) (q : PlaquetteIndex (2 * n))
    (U : Configuration V' Q) :
    |Ap n X q U| ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 * defect (linkValue (2 * n) Q U) q.2.1.1 q.2.1.2 q.1 := by
  set L := linkValue (2 * n) Q U with hL
  set Z := Zp n L X q with hZ
  set c := plaqC n L X q.1 q.2.1.1 q.2.1.2 with hc
  have hZre : Z.re = 0 := by
    have h1 : (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₁.re = 0 := by
      have h := congrArg (fun r : ℍ[ℝ] => r.re) (imag_star X q.2.1.1 q.1)
      simp only [Quaternion.re_star, Quaternion.re_neg] at h
      change (imag X q.2.1.1 q.1).re = 0
      linarith only [h]
    have h2 : (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₂.re = 0 := conj_re _ _ (imag_star _ _ _)
    have key (u : Q) (y : ℍ[ℝ]) (hy : star y = -y) : (-((u : ℍ[ℝ]) * y * ((u⁻¹ : Q) : ℍ[ℝ]))).re = 0 := by
      rw [Quaternion.re_neg, conj_re u y hy, neg_zero]
    have h3 : (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₃.re = 0 := key _ _ (imag_star _ _ _)
    have h4 : (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₄.re = 0 := key _ _ (imag_star _ _ _)
    simp only [hZ, Zp, Quaternion.re_add, h1, h2, h3, h4, add_zero]
  have hZn : ‖Z‖ ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 := by
    rw [← plaq_norms n L]
    refine (norm_add_le _ _).trans ?_
    have a := norm_add_le ((plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₁ + (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₂)
      (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₃
    have b := norm_add_le (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₁ (plaqOf n L X q.1 q.2.1.1 q.2.1.2).Y₂
    linarith only [a, b]
  have hcn : ‖c - 1‖ = defect L q.2.1.1 q.2.1.2 q.1 := by
    rw [hc]
    unfold plaqC defect d
    rcases (by unfold twistExp; split_ifs <;> simp :
      twistExp q.2.1.1 q.2.1.2 q.1 = 0 ∨ twistExp q.2.1.1 q.2.1.2 q.1 = 1) with ht | ht
    · rw [ht]
      simp only [zero_ne_one, if_false, one_smul, pow_zero]
      rfl
    · rw [ht]
      simp only [if_true, pow_one, ω_coe, neg_smul, one_smul]
      rw [show ∀ x : ℍ[ℝ], -x - 1 = -(x - -1) from fun x => by abel, norm_neg]
      rfl
  have hsplit : (Z * c).re = (Z * (c - 1)).re := by
    have : Z * c = Z * (c - 1) + Z := by noncomm_ring
    rw [this, Quaternion.re_add, hZre, add_zero]
  change |(Z * c).re| ≤ _
  rw [hsplit, ← hcn]
  refine (re_abs_le _).trans ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hZn (norm_nonneg _)

open TwistedIBP TwistedHessianField in
/-- **The rate of one plaquette, with no hypothesis on cross terms.** `E[A_p²]` is at most `(Σ_{e∈p} ‖X_e‖)²` times
`planeBound`. Compared with `TwistedIBP.own_le_of_cross`, whose hypothesis is open and whose conclusion has `1/(2β)`, this conclusion
is about `12` times weaker at large `n` and larger at small `n`. It adds nothing to `TwistedIBP.Ap_abs` until `planeBound < 1`. -/
theorem rate_sq_le (β : ℝ) (hβ : 0 < β)
    (X : Fin 3 → Fin 4 → TwistedHessian.Section (2 * n)) (q : PlaquetteIndex (2 * n)) :
    ∫ U, Ap n X q U ^ 2 ∂twistedLaw n β ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 ^ 2 * planeBound n β := by
  have hm := ((TwistedSlice.Ap_continuous n X q).pow 2).integrable_of_hasCompactSupport
    (μ := twistedLaw n β) (HasCompactSupport.of_compactSpace _)
  have hd := defect_sq_integrable n β q.1 q.2.1.1 q.2.1.2
  have hb := defect_sq_le n β hβ q.2.1.1 q.2.1.2 q.2.2 q.1
  have hS : 0 ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 ^ 2 := sq_nonneg _
  calc _ ≤ ∫ U, linkSum n X q.1 q.2.1.1 q.2.1.2 ^ 2 *
        defect (linkValue (2 * n) Q U) q.2.1.1 q.2.1.2 q.1 ^ 2 ∂twistedLaw n β := by
        refine integral_mono hm (hd.const_mul _) fun U => ?_
        have h := Ap_abs_le_defect n X q U
        have h0 := abs_nonneg (Ap n X q U)
        change Ap n X q U ^ 2 ≤ _
        rw [← sq_abs, ← mul_pow]
        exact pow_le_pow_left₀ h0 h 2
    _ = _ * ∫ U, defect (linkValue (2 * n) Q U) q.2.1.1 q.2.1.2 q.1 ^ 2 ∂twistedLaw n β := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hS

/-! ### An explicit constant in a stated range of couplings -/

theorem log_two_bound : Real.log 2 ≤ 0.6932 := by
  have h := Real.log_two_lt_d9
  linarith only [h]

/-- In the range `-log mass(6β) ≤ n`, `planeBound ≤ 11/β`. The range is a hypothesis on `n` against `β`, not a trajectory. -/
theorem planeBound_le (β : ℝ) (hβ : 0 < β) (hc : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ n) :
    planeBound n β ≤ 11 / β := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hn0 : (0 : ℝ) < n := by linarith only [hn]
  have hL2 := log_two_bound
  have h20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h54 : Real.log 54 ≤ 6 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) (by norm_num : (54 : ℝ) ≤ 2 ^ 6)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h3 : 3 / (2 * (n : ℝ)) * Real.log 4 ≤ 3 * Real.log 2 := by
    rw [h4]
    have : 3 / (2 * (n : ℝ)) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hn]
    nlinarith only [this, h20]
  have h5 : 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) ≤ 2 := by
    calc _ ≤ 2 / (n : ℝ) * n := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 := by field_simp
  unfold planeBound
  rw [div_le_div_iff₀ hβ hβ]
  exact mul_le_mul_of_nonneg_right (by linarith only [h54, h3, h5, hL2]) hβ.le

/-- **The explicit local bound.** While `-log mass(6β) ≤ n`, every plaquette has `E[d²] ≤ 11/β`. It beats the pointwise
`d² ≤ 4` only for `β > 11/4`, where the range needs `n ≥ 6`, and the Haar value `2` only for `β > 11/2`, where it needs `n ≥ 7`. -/
theorem defect_sq_le_explicit (β : ℝ) (hβ : 0 < β) (hc : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ n)
    (μ ν : Fin 4) (h : μ < ν) (x : V') :
    ∫ U, defect (linkValue (2 * n) Q U) μ ν x ^ 2 ∂twistedLaw n β ≤ 11 / β :=
  (defect_sq_le n β hβ μ ν h x).trans (planeBound_le n β hβ hc)

/-- The tail in the same range: `P(d > δ) ≤ 11/(β δ²)`. -/
theorem defect_tail_explicit (β δ : ℝ) (hβ : 0 < β) (hc : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ n)
    (hδ : 0 < δ) (μ ν : Fin 4) (h : μ < ν) (x : V') :
    twistedLaw n β {U | δ < defect (linkValue (2 * n) Q U) μ ν x} ≤ ENNReal.ofReal (11 / (β * δ ^ 2)) := by
  refine (defect_tail n β δ hβ hδ μ ν h x).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← div_div]
  exact div_le_div_of_nonneg_right (planeBound_le n β hβ hc) (by positivity)

/-! ### Axis swaps: four of the six orbits coincide -/

/-- Permute the coordinates of a vertex. -/
def axis (σ : Equiv.Perm (Fin 4)) (x : V') : V' := fun i => x (σ.symm i)

theorem axis_step (σ : Equiv.Perm (Fin 4)) (x : V') (μ : Fin 4) :
    axis n σ (step (2 * n) x μ) = step (2 * n) (axis n σ x) (σ μ) := by
  funext i
  simp only [axis, step, Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq]

/-- The action of `σ` on vertices, as an equivalence. -/
def axisEquiv (σ : Equiv.Perm (Fin 4)) : V' ≃ V' where
  toFun := axis n σ
  invFun := axis n σ.symm
  left_inv x := by
    funext i
    simp [axis]
  right_inv x := by
    funext i
    simp [axis]

/-- The action of `σ` on edges. -/
def axisEdge (σ : Equiv.Perm (Fin 4)) : Edge V' ≃ Edge V' :=
  (edgeCoordinates (2 * n)).trans ((Equiv.prodCongr (axisEquiv n σ) σ).trans (edgeCoordinates (2 * n)).symm)

/-- Relabel the axes of a configuration. -/
def axisMap (σ : Equiv.Perm (Fin 4)) (U : Configuration V' Q) : Configuration V' Q := U ∘ axisEdge n σ

theorem axisMap_link (σ : Equiv.Perm (Fin 4)) (U : Configuration V' Q) (x : V') (μ : Fin 4) :
    linkValue (2 * n) Q (axisMap n σ U) x μ = linkValue (2 * n) Q U (axis n σ x) (σ μ) := rfl

theorem axisMap_ref (σ : Equiv.Perm (Fin 4)) :
    MeasurePreserving (axisMap n σ) (referenceMeasure Q V') (referenceMeasure Q V') := by
  have h := measurePreserving_piCongrLeft (fun _ : Edge V' => compactHaar Q) (axisEdge n σ).symm
  convert h using 1
  funext U e
  simp [axisMap, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

/-- The two generators that fix the twist. -/
def TwistFixing (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∀ (x : V') (μ ν : Fin 4), μ < ν →
    (if σ μ < σ ν then twistExp (σ μ) (σ ν) (axis n σ x) else twistExp (σ ν) (σ μ) (axis n σ x)) = twistExp μ ν x

theorem twistFixing_03 : TwistFixing n (Equiv.swap 0 3) := by
  intro x μ ν h
  fin_cases μ <;> fin_cases ν <;> first
    | exact absurd h (by decide)
    | simp (decide := true) [twistExp, axis, Equiv.swap_apply_def]

theorem twistFixing_12 : TwistFixing n (Equiv.swap 1 2) := by
  intro x μ ν h
  fin_cases μ <;> fin_cases ν <;> first
    | exact absurd h (by decide)
    | (simp (decide := true) [twistExp, axis, Equiv.swap_apply_def]; try (split_ifs <;> first | rfl | tauto))

/-- The defect of a plane, in either order of its directions, from `TwistedBadSet`. -/
theorem defect_axis (σ : Equiv.Perm (Fin 4)) (hσ : TwistFixing n σ) (U : Configuration V' Q) (μ ν : Fin 4) (h : μ < ν)
    (x : V') :
    defect (linkValue (2 * n) Q (axisMap n σ U)) μ ν x =
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (σ μ) (σ ν) (axis n σ x) := by
  have hne : σ μ ≠ σ ν := fun e => h.ne (σ.injective e)
  set L := linkValue (2 * n) Q U with hL
  have hP : linkValue (2 * n) Q (axisMap n σ U) x μ * linkValue (2 * n) Q (axisMap n σ U) (step (2 * n) x μ) ν *
      (linkValue (2 * n) Q (axisMap n σ U) (step (2 * n) x ν) μ)⁻¹ * (linkValue (2 * n) Q (axisMap n σ U) x ν)⁻¹ =
      L (axis n σ x) (σ μ) * L (step (2 * n) (axis n σ x) (σ μ)) (σ ν) *
      (L (step (2 * n) (axis n σ x) (σ ν)) (σ μ))⁻¹ * (L (axis n σ x) (σ ν))⁻¹ := by
    simp only [axisMap_link, axis_step]
    rfl
  have ht := hσ x μ ν h
  unfold defect TwistedBadSet.pd
  rw [hP]
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · simp only [hlt, if_true] at ht ⊢
    rw [← ht]
    unfold defect
    rfl
  · have hnl : ¬ σ μ < σ ν := not_lt.2 hlt.le
    simp only [hnl, if_false, hlt, if_true] at ht ⊢
    rw [← ht]
    unfold defect
    set y := axis n σ x
    have hinv : L y (σ μ) * L (step (2 * n) y (σ μ)) (σ ν) * (L (step (2 * n) y (σ ν)) (σ μ))⁻¹ * (L y (σ ν))⁻¹ =
        (L y (σ ν) * L (step (2 * n) y (σ ν)) (σ μ) * (L (step (2 * n) y (σ μ)) (σ ν))⁻¹ * (L y (σ μ))⁻¹)⁻¹ := by
      group
    rw [hinv]
    have hw : ω ^ twistExp (σ ν) (σ μ) y = (ω ^ twistExp (σ ν) (σ μ) y)⁻¹ := by
      rw [← inv_pow, ω_inv]
    conv_lhs => rw [hw]
    exact d_inv _ _

theorem actionOne_axis (σ : Equiv.Perm (Fin 4)) (hσ : TwistFixing n σ) (hswap : σ 0 = 3 ∧ σ 3 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∨
    σ 0 = 0 ∧ σ 3 = 3 ∧ σ 1 = 2 ∧ σ 2 = 1) (U : Configuration V' Q) :
    actionOne n (axisMap n σ U) = actionOne n U := by
  rw [TwistedNearFlat.actionOne_eq, TwistedNearFlat.actionOne_eq]
  unfold actionL
  set L := linkValue (2 * n) Q U with hL
  let M : Fin 4 → Fin 4 → ℝ := fun a b => ∑ y : V', TwistedBadSet.pd n L a b y ^ 2
  have hM (a b : Fin 4) : M a b = M b a := by
    simp only [M]
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold TwistedBadSet.pd
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [h]
    · simp [h, not_lt.2 h.le]
  have hax (a b : Fin 4) : ∑ x : V', TwistedBadSet.pd n L a b (axis n σ x) ^ 2 = M a b :=
    Equiv.sum_comp (axisEquiv n σ) fun y => TwistedBadSet.pd n L a b y ^ 2
  have hl : ∑ p : PlaquetteIndex (2 * n), defect (linkValue (2 * n) Q (axisMap n σ U)) p.2.1.1 p.2.1.2 p.1 ^ 2 =
      ∑ d : Plane, M (σ d.1.1) (σ d.1.2) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← hax]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [defect_axis n σ hσ U d.1.1 d.1.2 d.2 x]
  have hr : ∑ p : PlaquetteIndex (2 * n), defect L p.2.1.1 p.2.1.2 p.1 ^ 2 = ∑ d : Plane, M d.1.1 d.1.2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    have : TwistedBadSet.pd n L d.1.1 d.1.2 x = defect L d.1.1 d.1.2 x := by
      unfold TwistedBadSet.pd
      simp [d.2]
    rw [this]
  rw [hl, hr, TwistedActionJet.plane_sum (fun a b => M (σ a) (σ b)), TwistedActionJet.plane_sum (fun a b => M a b)]
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  rcases hswap with ⟨h0, h3, h1, h2⟩ | ⟨h0, h3, h1, h2⟩ <;> rw [h0, h1, h2, h3]
  · linarith only [hM 3 1, hM 3 2, hM 3 0, hM 1 0, hM 2 0]
  · linarith only [hM 2 1, hM 0 2, hM 2 3, hM 1 3]

theorem axis_law (β : ℝ) (σ : Equiv.Perm (Fin 4)) (hσ : TwistFixing n σ) (hswap : σ 0 = 3 ∧ σ 3 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∨
    σ 0 = 0 ∧ σ 3 = 3 ∧ σ 1 = 2 ∧ σ 2 = 1) :
    MeasurePreserving (axisMap n σ) (twistedLaw n β) (twistedLaw n β) :=
  law_pres n β _ (axisMap_ref n σ) (actionOne_axis n σ hσ hswap)

/-- The swap of a plane's mean square defect under a twist-fixing relabelling. -/
theorem planeMean_swap (β : ℝ) (σ : Equiv.Perm (Fin 4)) (hσ : TwistFixing n σ) (hswap : σ 0 = 3 ∧ σ 3 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∨
    σ 0 = 0 ∧ σ 3 = 3 ∧ σ 1 = 2 ∧ σ 2 = 1) (μ ν μ' ν' : Fin 4) (h : μ < ν) (h' : μ' < ν')
    (hpd : (σ μ = μ' ∧ σ ν = ν') ∨ (σ μ = ν' ∧ σ ν = μ')) :
    planeMean n β μ ν = planeMean n β μ' ν' := by
  have hp := axis_law n β σ hσ hswap
  have hpd2 (U : Configuration V' Q) :
      TwistedBadSet.pd n (linkValue (2 * n) Q U) (σ μ) (σ ν) (axis n σ 0) =
        defect (linkValue (2 * n) Q U) μ' ν' (axis n σ 0) := by
    unfold TwistedBadSet.pd
    rcases hpd with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]
    · simp [h']
    · simp [h', not_lt.2 h'.le]
  have hc : Continuous fun U : Configuration V' Q => defect (linkValue (2 * n) Q U) μ ν 0 ^ 2 :=
    (defect_continuous n _ μ ν).pow 2
  have hm := integral_map (μ := twistedLaw n β) hp.measurable.aemeasurable hc.aestronglyMeasurable
  rw [hp.map_eq] at hm
  unfold planeMean
  have e1 : ∫ U, defect (linkValue (2 * n) Q U) μ ν 0 ^ 2 ∂twistedLaw n β =
      ∫ U, defect (linkValue (2 * n) Q U) μ' ν' (axis n σ 0) ^ 2 ∂twistedLaw n β := by
    rw [hm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only
    rw [defect_axis n σ hσ U μ ν h 0, hpd2]
  rw [e1]
  exact planeMean_eq n β μ' ν' h' _

/-- **Four of the six orbits coincide.** The planes `01, 02, 13, 23` have the same mean square defect. The planes `12` and
`03` are not related to them, or to each other, by any symmetry used here. -/
theorem planeMean_mixed (β : ℝ) :
    planeMean n β 0 2 = planeMean n β 0 1 ∧ planeMean n β 1 3 = planeMean n β 0 1 ∧
      planeMean n β 2 3 = planeMean n β 0 1 := by
  have h12 : (Equiv.swap (1 : Fin 4) 2) 0 = 3 ∧ (Equiv.swap (1 : Fin 4) 2) 3 = 0 ∧ (Equiv.swap (1 : Fin 4) 2) 1 = 1 ∧
      (Equiv.swap (1 : Fin 4) 2) 2 = 2 ∨ (Equiv.swap (1 : Fin 4) 2) 0 = 0 ∧ (Equiv.swap (1 : Fin 4) 2) 3 = 3 ∧
      (Equiv.swap (1 : Fin 4) 2) 1 = 2 ∧ (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by decide
  have h03 : (Equiv.swap (0 : Fin 4) 3) 0 = 3 ∧ (Equiv.swap (0 : Fin 4) 3) 3 = 0 ∧ (Equiv.swap (0 : Fin 4) 3) 1 = 1 ∧
      (Equiv.swap (0 : Fin 4) 3) 2 = 2 ∨ (Equiv.swap (0 : Fin 4) 3) 0 = 0 ∧ (Equiv.swap (0 : Fin 4) 3) 3 = 3 ∧
      (Equiv.swap (0 : Fin 4) 3) 1 = 2 ∧ (Equiv.swap (0 : Fin 4) 3) 2 = 1 := by decide
  have a : planeMean n β 0 1 = planeMean n β 0 2 :=
    planeMean_swap n β _ (twistFixing_12 n) h12 0 1 0 2 (by decide) (by decide) (by decide)
  have b : planeMean n β 0 1 = planeMean n β 1 3 :=
    planeMean_swap n β _ (twistFixing_03 n) h03 0 1 1 3 (by decide) (by decide) (by decide)
  have c : planeMean n β 0 2 = planeMean n β 2 3 :=
    planeMean_swap n β _ (twistFixing_03 n) h03 0 2 2 3 (by decide) (by decide) (by decide)
  exact ⟨a.symm, b.symm, (a.trans c).symm⟩

/-- The six orbits, accounted for: the energy per vertex is `m₁₂ + m₀₃ + 4 m₀₁`. -/
theorem energy_orbits (β : ℝ) :
    energy n β = ((2 * n : ℕ) : ℝ) ^ 4 * (planeMean n β 1 2 + planeMean n β 0 3 + 4 * planeMean n β 0 1) := by
  obtain ⟨h2, h3, h4⟩ := planeMean_mixed n β
  rw [energy_eq n β 0]
  congr 1
  have := TwistedActionJet.plane_sum (fun a b => planeMean n β a b)
  change ∑ d : Plane, planeMean n β d.1.1 d.1.2 = _
  rw [this]
  simp (decide := true) only [Fin.sum_univ_four, if_true, if_false]
  linarith only [h2, h3, h4]

/-- **The mixed planes.** Lowering planes `13` and `23` together, which the axis swaps identify, gives
`2 β m₀₁ ≤ (3/2) log 108 + (3/(2n)) log 2 + (2/n) (-log mass(6β))`, about `3.51/β` for `m₀₁` at large `n`. -/
theorem mixed_le (β : ℝ) (hβ : 0 < β) :
    2 * β * planeMean n β 0 1 ≤
      3 / 2 * Real.log 108 + 3 / (2 * (n : ℝ)) * Real.log 2 + 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) := by
  obtain ⟨-, h13, h23⟩ := planeMean_mixed n β
  let Off : Finset Plane := {⟨(1, 3), by decide⟩, ⟨(2, 3), by decide⟩}
  have hOff : ∀ i, ∀ k ∈ mixAx i, planeOf ((1 : Equiv.Perm (Fin 4)) k) ((1 : Equiv.Perm (Fin 4)) i.succ) ∉ Off := by
    decide
  have hR := ratio_of (n := n) 1 mixAx {0, 1} (by decide) (by decide) (by decide) Off hOff β β hβ hβ (by linarith only [hβ])
  have hJ := off_jensen (n := n) Off β
  have hs : ∑ d ∈ Off, planeMean n β d.1.1 d.1.2 = 2 * planeMean n β 0 1 := by
    have : ∑ d ∈ Off, planeMean n β d.1.1 d.1.2 = planeMean n β 1 3 + planeMean n β 2 3 :=
      Finset.sum_pair (by decide)
    rw [this, h13, h23]
    ring
  rw [hs] at hJ
  rw [sum_mixAx, show 6 * β / β = 6 by field_simp] at hR
  have hc : (({0, 1} : Finset (Fin 4)).card : ℝ) = 2 := by
    have : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
    rw [this]
    norm_num
  rw [hc] at hR
  have hN : (0 : ℝ) < ((2 * n : ℕ) : ℝ) ^ 4 := by
    have := NeZero.pos n
    positivity
  have h108 : Real.log 108 = 3 * Real.log 6 - Real.log 2 := by
    rw [show (108 : ℝ) = 6 ^ 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have e1 := vol_div (n := n) (3 / 2 * Real.log 2)
  have e2 := vol_div (n := n) (2 * -Real.log (SU2GaussianMass.mass (6 * β)))
  have e3 : 3 / (2 * (n : ℝ)) * Real.log 2 = 3 / 2 * Real.log 2 / (n : ℝ) := by
    have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp
  have e4 : 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) =
      2 * -Real.log (SU2GaussianMass.mass (6 * β)) / (n : ℝ) := by ring
  refine le_of_mul_le_mul_left ?_ hN
  rw [mul_add, mul_add, e3, e4, e1, e2, h108]
  calc _ = β * (((2 * n : ℕ) : ℝ) ^ 4 * (2 * planeMean n β 0 1)) := by ring
    _ ≤ _ := hJ.trans hR
    _ = _ := by ring

/-- In the range of `defect_sq_le_explicit`, `m₀₁ ≤ 6/β`. -/
theorem mixed_le_explicit (β : ℝ) (hβ : 0 < β) (hc : -Real.log (SU2GaussianMass.mass (6 * β)) ≤ n) :
    planeMean n β 0 1 ≤ 6 / β := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.pos n
  have hn0 : (0 : ℝ) < n := by linarith only [hn]
  have hL2 := log_two_bound
  have h20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h108 : Real.log 108 ≤ 7 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num) (by norm_num : (108 : ℝ) ≤ 2 ^ 7)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have h3 : 3 / (2 * (n : ℝ)) * Real.log 2 ≤ 3 / 2 * Real.log 2 := by
    have : 3 / (2 * (n : ℝ)) ≤ 3 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith only [hn]
    exact mul_le_mul_of_nonneg_right this h20
  have h5 : 2 / (n : ℝ) * -Real.log (SU2GaussianMass.mass (6 * β)) ≤ 2 := by
    calc _ ≤ 2 / (n : ℝ) * n := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 := by field_simp
  have hm := mixed_le n β hβ
  rw [le_div_iff₀ hβ]
  linarith only [hm, h108, h3, h5, hL2]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedLocalTail
