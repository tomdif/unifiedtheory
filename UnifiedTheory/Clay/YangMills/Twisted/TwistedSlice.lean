/- Reflection positivity applied to the plaquette rates. For a direction `X` carried by the two fixed time slices,
the rate `T₊` of the plaquettes in the open upper half and its mirror image `T₊ ∘ θ` satisfy
`E[(T₊ - T₊ ∘ θ)²] ≤ E[T²]`, where `T` is the rate of the whole action. So the difference of the up and down
plaquette rates at a slice link is controlled by the force, with no volume factor, and `E[T₊ · T₊ ∘ θ] ≥ 0`.
Only reflections in time are available: a reflection in a direction of the twist plane does not preserve the twist. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP
import UnifiedTheory.Clay.YangMills.ReflectedDefectBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice
noncomputable section
open MeasureTheory
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField TwistedIBP
open PeriodicPlaquetteReflection PeriodicTimeReflection PeriodicHalfSplit PeriodicHalfAction PeriodicHalfGeometry
open PeriodicSiteReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)
local notation "θ" => reflectConfiguration (2 * n) Q

/-! ### Reflection positivity for real observables of the closed upper half -/

/-- An observable that does not depend on the links of the open lower half. -/
def UpperLocal (F : Configuration V' Q → ℝ) : Prop :=
  ∀ b x y, F (assemble n Q (b, (x, y))) = F (assemble n Q (b, (x, 1)))

theorem reflected_nonneg (β : ℝ) (F : Configuration V' Q → ℝ) (hF : Continuous F)
    (hloc : UpperLocal n F) : 0 ≤ ∫ U, F (θ U) * F U ∂twistedLaw n β := by
  let f : BoundaryConfiguration n Q × HalfConfiguration n Q → ℂ :=
    fun z => ((F (assemble n Q (z.1, (z.2, 1))) : ℝ) : ℂ)
  have hf : Continuous f := Complex.continuous_ofReal.comp (hF.comp ((continuous_assemble n Q).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))))
  have h := (TwistedReflection.reflection_positive n Q (spatialTwist n) (spatialTwist_invariant n) character
    WilsonSingleLinkStaples.character_continuous WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re β 2 f hf).1
  have hobs (U : Configuration V' Q) : observable n Q f U = ((F (θ U) : ℝ) : ℂ) := by
    obtain ⟨z, rfl⟩ : ∃ z, U = assemble n Q z := ⟨_, (assemble_split n Q U).symm⟩
    rw [reflect_assemble, hloc]
    change f ((splitConfiguration n Q (assemble n Q z)).1, (splitConfiguration n Q (assemble n Q z)).2.2) = _
    have hs : splitConfiguration n Q (assemble n Q z) = z := split_assemble n Q z
    rw [hs]
  have hobsθ (U : Configuration V' Q) : observable n Q f (θ U) = ((F U : ℝ) : ℂ) := by
    rw [hobs, reflectConfiguration_involutive (2 * n) Q U]
  have he : (fun U => star (observable n Q f (θ U)) * observable n Q f U) =
      fun U => ((F (θ U) * F U : ℝ) : ℂ) := by
    funext U
    rw [hobsθ, hobs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
  have hlaw : twistedLaw n β = law n Q (spatialTwist n) character β 2 := rfl
  rw [hlaw] at *
  rw [he, integral_complex_ofReal, Complex.ofReal_re] at h
  exact h

/-! ### The plaquette rates -/

theorem Ap_congr (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (U W : Configuration V' Q)
    (h₁ : linkValue (2 * n) Q U q.1 q.2.1.1 = linkValue (2 * n) Q W q.1 q.2.1.1)
    (h₂ : linkValue (2 * n) Q U (step (2 * n) q.1 q.2.1.1) q.2.1.2 =
      linkValue (2 * n) Q W (step (2 * n) q.1 q.2.1.1) q.2.1.2)
    (h₃ : linkValue (2 * n) Q U (step (2 * n) q.1 q.2.1.2) q.2.1.1 =
      linkValue (2 * n) Q W (step (2 * n) q.1 q.2.1.2) q.2.1.1)
    (h₄ : linkValue (2 * n) Q U q.1 q.2.1.2 = linkValue (2 * n) Q W q.1 q.2.1.2) :
    Ap n X q U = Ap n X q W := by
  simp only [Ap, Zp, plaqC, plaqOf, h₁, h₂, h₃, h₄]

theorem continuous_linkValue (x : V') (μ : Fin 4) :
    Continuous fun U : Configuration V' Q => linkValue (2 * n) Q U x μ :=
  continuous_apply _

theorem Ap_continuous (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) :
    Continuous (Ap n X q) := by
  have ha := continuous_linkValue n q.1 q.2.1.1
  have hb := continuous_linkValue n (step (2 * n) q.1 q.2.1.1) q.2.1.2
  have hc := continuous_linkValue n (step (2 * n) q.1 q.2.1.2) q.2.1.1
  have he := continuous_linkValue n q.1 q.2.1.2
  have hco : Continuous fun g : Q => (g : ℍ[ℝ]) := continuous_subtype_val
  have hre : Continuous fun w : ℍ[ℝ] => w.re := Quaternion.continuous_re
  unfold Ap Zp plaqC plaqOf
  dsimp only
  apply hre.comp
  have h3 := ((ha.mul hb).mul hc.inv)
  have h4 := h3.mul he.inv
  have c1 := hco.comp ha
  have c1i := hco.comp ha.inv
  have c3 := hco.comp h3
  have c3i := hco.comp h3.inv
  have c4 := hco.comp h4
  have c4i := hco.comp h4.inv
  simp only [Function.comp_def] at c1 c1i c3 c3i c4 c4i
  refine Continuous.mul ?_ (continuous_const.smul c4)
  exact ((continuous_const.add ((c1.mul continuous_const).mul c1i)).add
    ((c3.mul continuous_const).mul c3i).neg).add ((c4.mul continuous_const).mul c4i).neg

theorem Ap_positive_local (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (hq : PositiveP n q) :
    UpperLocal n (Ap n X q) := by
  intro b x y
  obtain ⟨h₁, h₂, h₃, h₄⟩ := positive_plaquette_support n q hq
  exact Ap_congr n X q _ _ (assemble_closed_link n Q _ h₁ b x y 1) (assemble_closed_link n Q _ h₂ b x y 1)
    (assemble_closed_link n Q _ h₃ b x y 1) (assemble_closed_link n Q _ h₄ b x y 1)

theorem Ap_boundary_local (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (hq : BoundaryP n q) :
    UpperLocal n (Ap n X q) := by
  intro b x y
  obtain ⟨h₁, h₂, h₃, h₄⟩ := boundary_plaquette_support n q hq
  exact Ap_congr n X q _ _ (assemble_boundary_link n Q _ h₁ b x y x 1) (assemble_boundary_link n Q _ h₂ b x y x 1)
    (assemble_boundary_link n Q _ h₃ b x y x 1) (assemble_boundary_link n Q _ h₄ b x y x 1)

/-! ### Directions carried by the fixed slices -/

/-- `X` vanishes off the two fixed time slices, so the flow commutes with the reflection. -/
def SliceSupported (X : Fin 3 → Fin 4 → Section (2 * n)) : Prop :=
  ∀ a μ x, ¬ Boundary n (x, μ) → X a μ x = 0

theorem edgeRot_zero (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) (e : Edge V')
    (he : ¬ Boundary n (edgeCoordinates (2 * n) e)) : edgeRot n X e = 0 := by
  unfold edgeRot imag
  refine Finset.sum_eq_zero fun a _ => ?_
  have h0 : X a (edgeCoordinates (2 * n) e).2 (edgeCoordinates (2 * n) e).1 = 0 :=
    congrArg (fun r : ℝ => r) (hX a (edgeCoordinates (2 * n) e).2 (edgeCoordinates (2 * n) e).1 he)
  rw [h0, zero_smul]

theorem expQ_edge_zero (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (e : Edge V') (h : edgeRot n X e = 0) :
    expQ (t • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) t) = 1 := by
  apply Subtype.ext
  change NormedSpace.exp (t • edgeRot n X e) = 1
  rw [h, smul_zero, NormedSpace.exp_zero]

theorem edgeEquiv_coords (e : Edge V') :
    edgeCoordinates (2 * n) (edgeEquiv (2 * n) e) = reflectIndex (2 * n) (edgeCoordinates (2 * n) e) :=
  Equiv.apply_symm_apply _ _

theorem flow_reflect (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) (t : ℝ)
    (U : Configuration V' Q) : θ (flow n X t U) = flow n X t (θ U) := by
  funext e
  rw [flow_apply]
  by_cases hb : Boundary n (edgeCoordinates (2 * n) e)
  · have hfix : edgeEquiv (2 * n) e = e := by
      apply (edgeCoordinates (2 * n)).injective
      rw [edgeEquiv_coords]
      exact boundary_fixed n _ hb
    have hd : e.2.2.val ≠ 0 := hb.1
    simp only [reflectConfiguration, if_neg hd, hfix, flow_apply]
  · have hb' : ¬ Boundary n (edgeCoordinates (2 * n) (edgeEquiv (2 * n) e)) := by
      intro h
      apply hb
      rw [edgeEquiv_coords] at h
      have hf := boundary_fixed n _ h
      rw [reflectIndex_involutive] at hf
      rw [hf]
      exact h
    rw [expQ_edge_zero n X t e (edgeRot_zero n X hX e hb), one_mul]
    have hm : flow n X t U (edgeEquiv (2 * n) e) = U (edgeEquiv (2 * n) e) := by
      rw [flow_apply, expQ_edge_zero n X t _ (edgeRot_zero n X hX _ hb'), one_mul]
    simp only [reflectConfiguration, hm]

theorem term_reflect (U : Configuration V' Q) (p : PlaquetteIndex (2 * n)) :
    term n Q (spatialTwist n) character 2 U (reflectPlaquette (2 * n) p) =
      term n Q (spatialTwist n) character 2 (θ U) p := by
  unfold term
  rw [reflected_plaquette_character (2 * n) Q character WilsonSingleLinkStaples.character_classFunction
    WilsonSingleLinkStaples.character_inverse_re U p, spatialTwist_invariant n p]
  rfl

/-- The rate of a reflected plaquette is the rate of the plaquette in the reflected configuration. -/
theorem Ap_reflect (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) (q : PlaquetteIndex (2 * n))
    (U : Configuration V' Q) : Ap n X (reflectPlaquette (2 * n) q) U = Ap n X q (θ U) := by
  obtain ⟨f₁, -, h₁, -, h₀, -⟩ := term_jet n (linkValue (2 * n) Q U) X (reflectPlaquette (2 * n) q)
  obtain ⟨g₁, -, k₁, -, k₀, -⟩ := term_jet n (linkValue (2 * n) Q (θ U)) X q
  have hfun : (fun t => term n Q (spatialTwist n) character 2 (cfg n (linkValue (2 * n) Q U) X t)
      (reflectPlaquette (2 * n) q)) =
      fun t => term n Q (spatialTwist n) character 2 (cfg n (linkValue (2 * n) Q (θ U)) X t) q := by
    funext t
    rw [term_reflect]
    exact congrArg (fun W => term n Q (spatialTwist n) character 2 W q) (flow_reflect n X hX t U)
  have hd := (h₁ 0).unique (hfun ▸ k₁ 0)
  rw [h₀, k₀] at hd
  simp only [Ap]
  linarith only [hd]

/-! ### The slice estimate -/

open scoped Classical in
/-- The rate of the plaquettes in the open upper half. -/
def Tup (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) : ℝ :=
  ∑ q, if PositiveP n q then Ap n X q U else 0

open scoped Classical in
/-- The rate of the plaquettes lying in the fixed slices. -/
def Tbd (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) : ℝ :=
  ∑ q, if BoundaryP n q then Ap n X q U else 0

/-- The rate of the whole action, up to the factor `-2 β`. -/
def Ttot (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) : ℝ := ∑ q, Ap n X q U

theorem Tup_continuous (X : Fin 3 → Fin 4 → Section (2 * n)) : Continuous (Tup n X) := by
  classical
  refine continuous_finset_sum _ fun q _ => ?_
  by_cases h : PositiveP n q
  · simpa only [h, if_true] using Ap_continuous n X q
  · simpa only [h, if_false] using continuous_const

theorem Tbd_continuous (X : Fin 3 → Fin 4 → Section (2 * n)) : Continuous (Tbd n X) := by
  classical
  refine continuous_finset_sum _ fun q _ => ?_
  by_cases h : BoundaryP n q
  · simpa only [h, if_true] using Ap_continuous n X q
  · simpa only [h, if_false] using continuous_const

theorem Ttot_continuous (X : Fin 3 → Fin 4 → Section (2 * n)) : Continuous (Ttot n X) :=
  continuous_finset_sum _ fun q _ => Ap_continuous n X q

theorem Tup_local (X : Fin 3 → Fin 4 → Section (2 * n)) : UpperLocal n (Tup n X) := by
  classical
  intro b x y
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : PositiveP n q
  · simp only [h, if_true]
    exact Ap_positive_local n X q h b x y
  · simp only [h, if_false]

theorem Tbd_local (X : Fin 3 → Fin 4 → Section (2 * n)) : UpperLocal n (Tbd n X) := by
  classical
  intro b x y
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : BoundaryP n q
  · simp only [h, if_true]
    exact Ap_boundary_local n X q h b x y
  · simp only [h, if_false]

theorem Tbd_reflect (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) (U : Configuration V' Q) :
    Tbd n X (θ U) = Tbd n X U := by
  classical
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : BoundaryP n q
  · simp only [h, if_true]
    rw [← Ap_reflect n X hX, boundaryP_fixed n q h]
  · simp only [h, if_false]

theorem Ttot_split (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) (U : Configuration V' Q) :
    Ttot n X U = Tbd n X U + Tup n X U + Tup n X (θ U) := by
  classical
  unfold Ttot Tbd Tup
  rw [sum_half_partition n (fun q => Ap n X q U)]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Ap_reflect n X hX]

/-- **Reflection positivity of the upper rate.** -/
theorem Tup_reflected_nonneg (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    0 ≤ ∫ U, Tup n X (θ U) * Tup n X U ∂twistedLaw n β :=
  reflected_nonneg n β _ (Tup_continuous n X) (Tup_local n X)

/-- **The slice estimate.** The difference between the upper rate and its mirror image is bounded in `L²` by the
rate of the whole action, with no dependence on the volume. -/
theorem slice_le_force (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) :
    ∫ U, (Tup n X U - Tup n X (θ U)) ^ 2 ∂twistedLaw n β ≤ ∫ U, Ttot n X U ^ 2 ∂twistedLaw n β := by
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hθ : Continuous θ := ReflectedDefectBound.continuous_reflection Q (2 * n)
  let F : Configuration V' Q → ℝ := fun U => 2 * Tup n X U + Tbd n X U
  have hFc : Continuous F := (continuous_const.mul (Tup_continuous n X)).add (Tbd_continuous n X)
  have hFl : UpperLocal n F := by
    intro b x y
    simp only [F, Tup_local n X b x y, Tbd_local n X b x y]
  have hpos := reflected_nonneg n β F hFc hFl
  have hc₁ : Continuous fun U => F (θ U) * F U := (hFc.comp hθ).mul hFc
  have hc₂ : Continuous fun U => (Tup n X U - Tup n X (θ U)) ^ 2 :=
    ((Tup_continuous n X).sub ((Tup_continuous n X).comp hθ)).pow 2
  have hid : (fun U => Ttot n X U ^ 2) =
      fun U => F (θ U) * F U + (Tup n X U - Tup n X (θ U)) ^ 2 := by
    funext U
    simp only [F]
    rw [Ttot_split n X hX, Tbd_reflect n X hX]
    ring
  rw [hid, integral_add (hc₁.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc₂.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  linarith only [hpos]

/-- The total rate from the plaquette equation: `2 β E[T²] = -Σ_p E[B_p]`. -/
theorem force_sq (β : ℝ) (hβ : 0 ≤ β) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    2 * β * ∫ U, Ttot n X U ^ 2 ∂twistedLaw n β = -∑ p, ∫ U, Bp n X p U ∂twistedLaw n β := by
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hint (q p : PlaquetteIndex (2 * n)) : Integrable (fun U => Ap n X q U * Ap n X p U) (twistedLaw n β) :=
    ((Ap_continuous n X q).mul (Ap_continuous n X p)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : ∫ U, Ttot n X U ^ 2 ∂twistedLaw n β =
      ∑ p, ∑ q, ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β := by
    have : (fun U => Ttot n X U ^ 2) = fun U => ∑ p, ∑ q, Ap n X q U * Ap n X p U := by
      funext U
      simp only [Ttot, sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
    rw [this, integral_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hint q p]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact integral_finset_sum _ fun q _ => hint q p
  rw [hs, Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p _ => plaquette_ibp n β hβ X p

/-- `E[T²]` is at most `Σ_p (Σ_{e ∈ p} ‖X_e‖)² / (2 β)`. -/
theorem force_sq_le (β : ℝ) (hβ : 0 < β) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∫ U, Ttot n X U ^ 2 ∂twistedLaw n β ≤ (∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2) / (2 * β) := by
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have h := force_sq n β hβ.le X
  have hB : -∑ p, ∫ U, Bp n X p U ∂twistedLaw n β ≤ ∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    have := norm_integral_le_of_norm_le_const (μ := twistedLaw n β) (f := Bp n X p)
      (C := linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2) (Filter.Eventually.of_forall fun U => by
        simpa [Real.norm_eq_abs] using Bp_abs n X p U)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
    linarith only [neg_abs_le (∫ U, Bp n X p U ∂twistedLaw n β), this]
  rw [le_div_iff₀ (by positivity)]
  linarith only [h, hB]

/-- **Volume-free control of the second time difference of the field.** -/
theorem slice_bound (β : ℝ) (hβ : 0 < β) (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X) :
    ∫ U, (Tup n X U - Tup n X (θ U)) ^ 2 ∂twistedLaw n β ≤
      (∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2) / (2 * β) :=
  (slice_le_force n β X hX).trans (force_sq_le n β hβ X)

theorem linkSum_total_le (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∑ p : PlaquetteIndex (2 * n), linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 ≤ 24 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := by
  have h := link_count n X
  calc _ ≤ ∑ p : PlaquetteIndex (2 * n), 4 * linkSq n X p.1 p.2.1.1 p.2.1.2 :=
        Finset.sum_le_sum fun p _ => linkSum_sq n X _ _ _
    _ = 4 * ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 := by rw [Finset.mul_sum]
    _ = 24 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := by
        simp only [linkSq]
        rw [h]
        ring

/-! ### One link of the slice `t = 0` -/

/-- **The opposite plaquette.** A positive plaquette and its mirror image have nonnegative correlated rates along
any direction carried by the fixed slices. -/
theorem opposite_nonneg (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SliceSupported n X)
    (q : PlaquetteIndex (2 * n)) (hq : PositiveP n q) :
    0 ≤ ∫ U, Ap n X (reflectPlaquette (2 * n) q) U * Ap n X q U ∂twistedLaw n β := by
  have h := reflected_nonneg n β _ (Ap_continuous n X q) (Ap_positive_local n X q hq)
  simpa only [Ap_reflect n X hX] using h

/-- `X` is carried by the single link `(x, m)`. -/
def SingleLink (x : V') (m : Fin 4) (X : Fin 3 → Fin 4 → Section (2 * n)) : Prop :=
  ∀ a μ y, (y, μ) ≠ (x, m) → X a μ y = 0

theorem SingleLink.imag_zero {x : V'} {m : Fin 4} {X : Fin 3 → Fin 4 → Section (2 * n)} (hX : SingleLink n x m X)
    (y : V') (μ : Fin 4) (h : (y, μ) ≠ (x, m)) : imag X μ y = 0 := by
  unfold imag
  refine Finset.sum_eq_zero fun a _ => ?_
  have h0 : X a μ y = 0 := congrArg (fun r : ℝ => r) (hX a μ y h)
  rw [h0, zero_smul]

theorem SingleLink.slice {x : V'} {m : Fin 4} {X : Fin 3 → Fin 4 → Section (2 * n)} (hX : SingleLink n x m X)
    (hm : m ≠ 0) (hx : (x 0).val = 0) : SliceSupported n X := by
  intro a μ y hb
  apply hX a μ y
  intro he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact hb ⟨hm, Or.inl hx⟩

/-- Among the plaquettes of the open upper half, only one contains a link of the slice `t = 0`. -/
theorem Tup_single (x : V') (m : Fin 4) (hm : (0 : Fin 4) < m) (hx : (x 0).val = 0)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SingleLink n x m X) (U : Configuration V' Q) :
    Tup n X U = Ap n X (x, ⟨(0, m), hm⟩) U := by
  classical
  have hm0 : m ≠ 0 := hm.ne'
  have hnpos := NeZero.pos n
  have hqpos : PositiveP n (x, ⟨(0, m), hm⟩) := by
    change Positive n (x, 0)
    simp only [Positive, if_true]
    omega
  unfold Tup
  rw [Finset.sum_eq_single (x, ⟨(0, m), hm⟩)]
  · simp only [hqpos, if_true]
  · rintro ⟨y, ⟨⟨μ, ν⟩, hμν⟩⟩ - hne
    by_cases hpos : PositiveP n (y, ⟨(μ, ν), hμν⟩)
    · simp only [hpos, if_true]
      have hν : ν ≠ 0 := by
        intro h
        subst h
        exact (not_lt_of_ge (Fin.zero_le μ)) hμν
      change Positive n (y, μ) at hpos
      have hspatial (hμ0 : μ ≠ 0) : 0 < (y 0).val := by
        exact (show 0 < (y 0).val ∧ (y 0).val < n from by
          simpa only [Positive, if_neg hμ0] using hpos).1
      have l₁ : imag X μ y = 0 := by
        apply hX.imag_zero
        intro he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        have := hspatial hm0
        omega
      have l₄ : imag X ν y = 0 := by
        apply hX.imag_zero
        intro he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        by_cases hμ0 : μ = 0
        · subst hμ0
          exact hne rfl
        · have := hspatial hμ0
          omega
      have l₂ : imag X ν (step (2 * n) y μ) = 0 := by
        apply hX.imag_zero
        intro he
        obtain ⟨h1, -⟩ := Prod.mk.inj he
        by_cases hμ0 : μ = 0
        · subst hμ0
          have ht : (y 0).val < n := by simpa only [Positive, if_true] using hpos
          have := next_time_val n y ht
          rw [h1] at this
          omega
        · have h2 := spatial_time n y μ hμ0
          rw [h1] at h2
          have := hspatial hμ0
          rw [← h2] at this
          omega
      have l₃ : imag X μ (step (2 * n) y ν) = 0 := by
        apply hX.imag_zero
        intro he
        obtain ⟨h1, h3⟩ := Prod.mk.inj he
        subst h3
        have h2 := spatial_time n y ν hν
        rw [h1] at h2
        have := hspatial hm0
        rw [← h2] at this
        omega
      have hab := Ap_abs n X (y, ⟨(μ, ν), hμν⟩) U
      simp only [linkSum, l₁, l₂, l₃, l₄, norm_zero, add_zero] at hab
      exact abs_nonpos_iff.mp hab
    · simp only [hpos, if_false]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **One link of the slice.** With `p` the plaquette above a slice link and `p'` its mirror image below,
`E[(A_p - A_p')²] ≤ 12 ‖X‖² / β`, with no dependence on the volume. -/
theorem single_link_bound (β : ℝ) (hβ : 0 < β) (x : V') (m : Fin 4) (hm : (0 : Fin 4) < m) (hx : (x 0).val = 0)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (hX : SingleLink n x m X) :
    ∫ U, (Ap n X (x, ⟨(0, m), hm⟩) U -
        Ap n X (reflectPlaquette (2 * n) (x, ⟨(0, m), hm⟩)) U) ^ 2 ∂twistedLaw n β ≤
      12 * (∑ a, ∑ μ, ‖X a μ‖ ^ 2) / β := by
  have hS := hX.slice n hm.ne' hx
  have h := slice_bound n β hβ X hS
  simp only [Tup_single n x m hm hx X hX] at h
  simp only [Ap_reflect n X hS]
  refine h.trans ?_
  have hl := linkSum_total_le n X
  rw [div_le_div_iff₀ (by positivity) hβ]
  nlinarith only [mul_le_mul_of_nonneg_right hl hβ.le, hβ]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedSlice
