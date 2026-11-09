/- Local finite spacetime forces and convergence on every C₀ spacetime
test. Zero extension is proved on the compact square boundary. -/
import UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
import UnifiedTheory.Audit.KFCausalVanishingForceTests

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction Classical
open scoped Topology ZeroAtInfty
open UnifiedTheory.Audit.KFCausalCompactSpacetimeForce
open UnifiedTheory.Audit.KFCausalSpacetimeForcePair (Pair)

def interior : Set Square := {z | z.1 ∈ KFCausalLocalForceMeasure.interior ∧
  z.2 ∈ KFCausalLocalForceMeasure.interior}

def inverse (z : Square) : ℝ × ℝ := (Real.tan (z.1:ℝ),Real.tan (z.2:ℝ))

theorem interior_open : IsOpen interior :=
  ((isOpen_Ioo.preimage continuous_subtype_val).preimage continuous_fst).inter
    ((isOpen_Ioo.preimage continuous_subtype_val).preimage continuous_snd)

theorem inverse_measurable : Measurable inverse :=
  (KFCausalLocalForceMeasure.tangent_measurable.comp measurable_fst).prodMk
    (KFCausalLocalForceMeasure.tangent_measurable.comp measurable_snd)

theorem embed_interior (z : ℝ × ℝ) : embed z ∈ interior :=
  ⟨KFCausalVanishingForceTests.embed_interior z.1,KFCausalVanishingForceTests.embed_interior z.2⟩

theorem embed_inverse (z : Square) (hz : z ∈ interior) : embed (inverse z) = z :=
  Prod.ext (KFCausalVanishingForceTests.embed_tangent z.1 hz.1)
    (KFCausalVanishingForceTests.embed_tangent z.2 hz.2)

theorem inverse_embed (z : ℝ × ℝ) : inverse (embed z) = z :=
  Prod.ext (Real.tan_arctan z.1) (Real.tan_arctan z.2)

theorem inverse_continuousAt (z : Square) (hz : z ∈ interior) : ContinuousAt inverse z := by
  have ht (x : KFCausalCompactifiedForceMeasure.Spectrum) (hx : x ∈ KFCausalLocalForceMeasure.interior) :
      ContinuousAt (fun y : KFCausalCompactifiedForceMeasure.Spectrum => Real.tan (y:ℝ)) x := by
    simpa only [Real.tan_eq_sin_div_cos] using
      (Real.continuous_sin.continuousAt.comp continuous_subtype_val.continuousAt).div
        (Real.continuous_cos.continuousAt.comp continuous_subtype_val.continuousAt)
        (ne_of_gt (Real.cos_pos_of_mem_Ioo hx))
  exact ((ht z.1 hz.1).comp continuous_fst.continuousAt).prodMk
    ((ht z.2 hz.2).comp continuous_snd.continuousAt)

def finitePart (μ : FiniteMeasure Square) : FiniteMeasure (ℝ × ℝ) :=
  (μ.restrict interior).map inverse

theorem finitePart_mass (μ : FiniteMeasure Square) : (finitePart μ).mass ≤ μ.mass :=
  (FiniteMeasure.mass_map_le _ _).trans
    (by rw [FiniteMeasure.restrict_mass]; exact μ.apply_mono (Set.subset_univ interior))

theorem finitePart_test (μ : FiniteMeasure Square) (q : Square →ᵇ ℂ)
    (hq : ∀ z, z ∉ interior → q z = 0) :
    (∫ z, pullback q z ∂(finitePart μ : Measure (ℝ × ℝ))) = ∫ z, q z ∂(μ : Measure Square) := by
  change (∫ z, pullback q z ∂(((μ:Measure Square).restrict interior).map inverse)) = _
  rw [integral_map inverse_measurable.aemeasurable (pullback q).continuous.aestronglyMeasurable]
  calc
    _ = ∫ z in interior, q z ∂(μ:Measure Square) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem interior_open.measurableSet] with z hz
      exact congrArg q (embed_inverse z hz)
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hq

def finitePair (P N : FiniteMeasure Square) : Pair where
  positive := finitePart P
  negative := finitePart N
  positive_finite := inferInstance
  negative_finite := inferInstance

theorem finitePair_test (P N : FiniteMeasure Square) (q : Square →ᵇ ℂ)
    (hq : ∀ z, z ∉ interior → q z = 0) :
    (finitePair P N).evaluate (pullback q) =
      ((∫ z, q z ∂(P:Measure Square))-(∫ z, q z ∂(N:Measure Square)))/2 :=
  congrArg₂ (fun a b : ℂ => (a-b)/2) (finitePart_test P q hq) (finitePart_test N q hq)

theorem boundary_test_of_compact_limits (F : ℕ → Pair) (P N : FiniteMeasure Square)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (q : Square →ᵇ ℂ) (hq : ∀ z, z ∉ interior → q z = 0) :
    Tendsto (fun n => (F n).evaluate (pullback q)) atTop
      (𝓝 ((finitePair P N).evaluate (pullback q))) := by
  have hp := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hP q
  have hn := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hN q
  rw [finitePair_test P N q hq]
  simpa only [compactify_test,Pair.evaluate] using (hp.sub hn).div_const 2

theorem local_limit_mass_bound (F : ℕ → Pair) (P N : FiniteMeasure Square)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (C : ℝ) (hb : ∀ᶠ n in atTop, (F n).mass ≤ C) :
    (finitePair P N).mass ≤ C := by
  have hp := (NNReal.continuous_coe.tendsto P.mass).comp hP.mass
  have hn := (NNReal.continuous_coe.tendsto N.mass).comp hN.mass
  have hm : (P.mass:ℝ)+(N.mass:ℝ) ≤ C := by
    apply le_of_tendsto (hp.add hn)
    simpa only [Function.comp_apply,compactify_mass,Pair.mass] using hb
  apply le_trans _ hm
  change ((finitePart P).mass:ℝ)+((finitePart N).mass:ℝ) ≤ _
  exact add_le_add (by exact_mod_cast finitePart_mass P) (by exact_mod_cast finitePart_mass N)

def extensionValue (f : C₀(ℝ × ℝ,ℂ)) (z : Square) : ℂ :=
  if z ∈ interior then f (inverse z) else 0

theorem extension_continuous (f : C₀(ℝ × ℝ,ℂ)) : Continuous (extensionValue f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ interior
  · apply (f.continuous.continuousAt.comp (inverse_continuousAt z hz)).congr_of_eventuallyEq
    filter_upwards [interior_open.mem_nhds hz] with x hx
    simp [extensionValue,hx]
  · change Tendsto (extensionValue f) (𝓝 z) (𝓝 (extensionValue f z))
    rw [extensionValue,if_neg hz]
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    obtain ⟨K,hK,hsmall⟩ := mem_cocompact.mp
      ((zero_at_infty f) (Metric.ball_mem_nhds (0:ℂ) hδ))
    have hS : IsClosed (embed '' K) := (hK.image embed_continuous).isClosed
    have hzS : z ∈ (embed '' K)ᶜ := by
      rintro ⟨x,_,rfl⟩
      exact hz (embed_interior x)
    filter_upwards [hS.isOpen_compl.mem_nhds hzS] with x hx
    by_cases hxI : x ∈ interior
    · have hxK : inverse x ∉ K := fun h => hx ⟨inverse x,h,embed_inverse x hxI⟩
      simpa [extensionValue,hxI] using hsmall hxK
    · simpa [extensionValue,hxI] using hδ

def extension (f : C₀(ℝ × ℝ,ℂ)) : Square →ᵇ ℂ :=
  mkOfCompact ⟨extensionValue f,extension_continuous f⟩

theorem extension_boundary (f : C₀(ℝ × ℝ,ℂ)) (z : Square) (hz : z ∉ interior) :
    extension f z = 0 := by
  change extensionValue f z = 0
  simp [extensionValue,hz]

theorem extension_pullback (f : C₀(ℝ × ℝ,ℂ)) : pullback (extension f) = f.toBCF := by
  ext z
  change extensionValue f (embed z) = f z
  rw [extensionValue,if_pos (embed_interior z),inverse_embed]

theorem finitePair_test_zero (P N : FiniteMeasure Square) (f : C₀(ℝ × ℝ,ℂ)) :
    (finitePair P N).evaluate f.toBCF =
      ((∫ z, extension f z ∂(P:Measure Square))-(∫ z, extension f z ∂(N:Measure Square)))/2 := by
  rw [← extension_pullback f]
  exact congrArg₂ (fun a b : ℂ => (a-b)/2)
    (finitePart_test P (extension f) (extension_boundary f))
    (finitePart_test N (extension f) (extension_boundary f))

theorem zero_test_of_compact_limits (F : ℕ → Pair) (P N : FiniteMeasure Square)
    (hP : Tendsto (fun n => compactify (F n).positive) atTop (𝓝 P))
    (hN : Tendsto (fun n => compactify (F n).negative) atTop (𝓝 N))
    (f : C₀(ℝ × ℝ,ℂ)) :
    Tendsto (fun n => (F n).evaluate f.toBCF) atTop
      (𝓝 ((finitePair P N).evaluate f.toBCF)) := by
  have hp := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hP (extension f)
  have hn := (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hN (extension f)
  rw [finitePair_test_zero]
  simpa only [compactify_test,extension_pullback,Pair.evaluate] using (hp.sub hn).div_const 2

#print axioms interior_open
#print axioms inverse_measurable
#print axioms inverse_continuousAt
#print axioms finitePart_mass
#print axioms finitePart_test
#print axioms finitePair_test
#print axioms boundary_test_of_compact_limits
#print axioms local_limit_mass_bound
#print axioms extension_continuous
#print axioms extension_boundary
#print axioms extension_pullback
#print axioms finitePair_test_zero
#print axioms zero_test_of_compact_limits
end
end UnifiedTheory.Audit.KFCausalLocalSpacetimeTests
