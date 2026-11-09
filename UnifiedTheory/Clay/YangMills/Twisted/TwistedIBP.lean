/- An exact integration-by-parts identity for the twisted Wilson measure. Haar measure is invariant under
`U ↦ exp(t X)·U`, so for every direction `X`, every `β ≥ 0` and every lattice size,
`E[(∂_X S)²] = E[∂²_X S]`, with no Gaussian approximation and no small-field restriction. Consequently
`E[(∂_X S)²] ≤ 48 β ‖X‖²`. This controls the force along `X`, a sum over the six plaquettes of a link in the
single-link case, and does not by itself control each plaquette's defect. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedBadSet
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP
noncomputable section
open MeasureTheory Filter Topology
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection TwistedHessianField
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-! ### The abstract identity -/

section Abstract
variable {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν] (Φ : ℝ → α → α)

/-- The integral of the derivative along a measure-preserving family vanishes. -/
theorem ibp_first (hpres : ∀ t, MeasurePreserving (Φ t) ν ν) (h0 : ∀ ω, Φ 0 ω = ω) (G : α → ℝ)
    (hG : Measurable G) (M : ℝ) (hM : ∀ ω, |G ω| ≤ M) (g : α → ℝ → ℝ)
    (hg : ∀ ω t, HasDerivAt (fun t => G (Φ t ω)) (g ω t) t) (K : ℝ) (hK : ∀ ω t, |g ω t| ≤ K) :
    Measurable (fun ω => g ω 0) ∧ ∫ ω, g ω 0 ∂ν = 0 := by
  let τ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hτ0 (k : ℕ) : τ k ≠ 0 := by
    have : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    exact (one_div_pos.2 this).ne'
  have hτlim : Tendsto τ atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hτ0⟩
  let q : ℕ → α → ℝ := fun k ω => (τ k)⁻¹ • (G (Φ (0 + τ k) ω) - G (Φ 0 ω))
  have hqm (k : ℕ) : Measurable (q k) :=
    ((hG.comp (hpres (0 + τ k)).measurable).sub (hG.comp (hpres 0).measurable)).const_smul (τ k)⁻¹
  have hlim (ω : α) : Tendsto (fun k => q k ω) atTop (𝓝 (g ω 0)) :=
    (hg ω 0).tendsto_slope_zero.comp hτlim
  have hmeas : Measurable (fun ω => g ω 0) :=
    measurable_of_tendsto_metrizable hqm (tendsto_pi_nhds.2 hlim)
  refine ⟨hmeas, ?_⟩
  have hbd (k : ℕ) (ω : α) : ‖q k ω‖ ≤ K := by
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
      (f := fun t => G (Φ t ω)) (f' := g ω) (C := K) (x := 0) (y := 0 + τ k)
      (fun t _ => (hg ω t).hasDerivWithinAt) (fun t _ => by simpa using hK ω t) convex_univ
      (Set.mem_univ _) (Set.mem_univ _)
    simp only [q, norm_smul, norm_inv]
    have hpos : 0 < ‖τ k‖ := norm_pos_iff.2 (hτ0 k)
    rw [zero_add, sub_zero] at hmv
    rw [zero_add, inv_mul_le_iff₀ hpos, mul_comm]
    simpa using hmv
  have hint (k : ℕ) : ∫ ω, q k ω ∂ν = 0 := by
    have hb (t : ℝ) : Integrable (fun ω => G (Φ t ω)) ν :=
      Integrable.of_bound (hG.comp (hpres t).measurable).aestronglyMeasurable M
        (Eventually.of_forall fun ω => by simpa using hM _)
    have hinv (t : ℝ) : ∫ ω, G (Φ t ω) ∂ν = ∫ ω, G ω ∂ν := by
      have := integral_map (hpres t).measurable.aemeasurable (f := G) (μ := ν)
        hG.aestronglyMeasurable
      rw [(hpres t).map_eq] at this
      exact this.symm
    simp only [q]
    rw [integral_smul, integral_sub (hb _) (hb _), hinv, hinv, sub_self, smul_zero]
  have hconv := tendsto_integral_of_dominated_convergence (fun _ => K) (μ := ν)
    (fun k => (hqm k).aestronglyMeasurable) (integrable_const K)
    (fun k => Eventually.of_forall (hbd k)) (Eventually.of_forall hlim)
  simp only [hint] at hconv
  exact (tendsto_nhds_unique hconv tendsto_const_nhds)

/-- The integral of the second derivative along a measure-preserving flow vanishes, given bounds on the
derivatives at time zero only. -/
theorem ibp_second (hpres : ∀ t, MeasurePreserving (Φ t) ν ν) (h0 : ∀ ω, Φ 0 ω = ω)
    (hflow : ∀ s t ω, Φ t (Φ s ω) = Φ (t + s) ω) (G : α → ℝ) (hG : Measurable G) (M : ℝ)
    (hM : ∀ ω, |G ω| ≤ M) (g₁ g₂ : α → ℝ → ℝ)
    (h₁ : ∀ ω t, HasDerivAt (fun t => G (Φ t ω)) (g₁ ω t) t)
    (h₂ : ∀ ω t, HasDerivAt (g₁ ω) (g₂ ω t) t) (K₁ K₂ : ℝ) (hK₁ : ∀ ω, |g₁ ω 0| ≤ K₁)
    (hK₂ : ∀ ω, |g₂ ω 0| ≤ K₂) :
    Measurable (fun ω => g₁ ω 0) ∧ Measurable (fun ω => g₂ ω 0) ∧ ∫ ω, g₂ ω 0 ∂ν = 0 := by
  have e₁ (s t : ℝ) (ω : α) : g₁ (Φ s ω) t = g₁ ω (t + s) := by
    have a := h₁ (Φ s ω) t
    have b := (h₁ ω (t + s)).comp_add_const t s
    simp only [hflow] at a
    exact a.unique b
  have e₂ (s t : ℝ) (ω : α) : g₂ (Φ s ω) t = g₂ ω (t + s) := by
    have a := h₂ (Φ s ω) t
    have hf : g₁ (Φ s ω) = fun t => g₁ ω (t + s) := funext fun t => e₁ s t ω
    rw [hf] at a
    exact a.unique ((h₂ ω (t + s)).comp_add_const t s)
  have b₁ (ω : α) (t : ℝ) : |g₁ ω t| ≤ K₁ := by
    have := hK₁ (Φ t ω)
    rwa [e₁, zero_add] at this
  have b₂ (ω : α) (t : ℝ) : |g₂ ω t| ≤ K₂ := by
    have := hK₂ (Φ t ω)
    rwa [e₂, zero_add] at this
  obtain ⟨m₁, -⟩ := ibp_first ν Φ hpres h0 G hG M hM g₁ h₁ K₁ b₁
  have hd (ω : α) (t : ℝ) : HasDerivAt (fun t => g₁ (Φ t ω) 0) (g₂ ω t) t := by
    have : (fun t => g₁ (Φ t ω) 0) = g₁ ω := by
      funext t
      rw [e₁, zero_add]
    rw [this]
    exact h₂ ω t
  obtain ⟨m₂, hz⟩ := ibp_first ν Φ hpres h0 (fun ω => g₁ ω 0) m₁ K₁ (fun ω => hK₁ ω) g₂ hd K₂ b₂
  exact ⟨m₁, m₂, hz⟩

/-- Integration by parts with an observable and an exponential weight. Bounds are needed at time zero only. -/
theorem ibp_mixed (hpres : ∀ t, MeasurePreserving (Φ t) ν ν) (h0 : ∀ ω, Φ 0 ω = ω)
    (hflow : ∀ s t ω, Φ t (Φ s ω) = Φ (t + s) ω) (f : α → ℝ) (hf : Measurable f) (Mf : ℝ)
    (hMf : ∀ ω, |f ω| ≤ Mf) (f₁ f₂ : α → ℝ → ℝ)
    (df₁ : ∀ ω t, HasDerivAt (fun t => f (Φ t ω)) (f₁ ω t) t)
    (df₂ : ∀ ω t, HasDerivAt (f₁ ω) (f₂ ω t) t) (A₁ A₂ : ℝ) (hA₁ : ∀ ω, |f₁ ω 0| ≤ A₁)
    (hA₂ : ∀ ω, |f₂ ω 0| ≤ A₂) (S : α → ℝ) (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω) (s₁ : α → ℝ → ℝ)
    (ds₁ : ∀ ω t, HasDerivAt (fun t => S (Φ t ω)) (s₁ ω t) t) (B : ℝ) (hB : ∀ ω, |s₁ ω 0| ≤ B) :
    ∫ ω, Real.exp (-S ω) * (f₂ ω 0 - s₁ ω 0 * f₁ ω 0) ∂ν = 0 := by
  have e₁ (s t : ℝ) (ω : α) : f₁ (Φ s ω) t = f₁ ω (t + s) := by
    have a := df₁ (Φ s ω) t
    have b := (df₁ ω (t + s)).comp_add_const t s
    simp only [hflow] at a
    exact a.unique b
  have e₂ (s t : ℝ) (ω : α) : f₂ (Φ s ω) t = f₂ ω (t + s) := by
    have a := df₂ (Φ s ω) t
    have hg : f₁ (Φ s ω) = fun t => f₁ ω (t + s) := funext fun t => e₁ s t ω
    rw [hg] at a
    exact a.unique ((df₂ ω (t + s)).comp_add_const t s)
  have e₃ (s t : ℝ) (ω : α) : s₁ (Φ s ω) t = s₁ ω (t + s) := by
    have a := ds₁ (Φ s ω) t
    have b := (ds₁ ω (t + s)).comp_add_const t s
    simp only [hflow] at a
    exact a.unique b
  have b₁ (ω : α) (t : ℝ) : |f₁ ω t| ≤ A₁ := by
    have := hA₁ (Φ t ω)
    rwa [e₁, zero_add] at this
  have b₂ (ω : α) (t : ℝ) : |f₂ ω t| ≤ A₂ := by
    have := hA₂ (Φ t ω)
    rwa [e₂, zero_add] at this
  have b₃ (ω : α) (t : ℝ) : |s₁ ω t| ≤ B := by
    have := hB (Φ t ω)
    rwa [e₃, zero_add] at this
  obtain ⟨m₁, -⟩ := ibp_first ν Φ hpres h0 f hf Mf hMf f₁ df₁ A₁ b₁
  have hw : Measurable fun ω => Real.exp (-S ω) := Real.measurable_exp.comp hS.neg
  have hex (ω : α) : Real.exp (-S ω) ≤ 1 := Real.exp_le_one_iff.2 (by linarith only [hS0 ω])
  let G : α → ℝ := fun ω => f₁ ω 0 * Real.exp (-S ω)
  let g : α → ℝ → ℝ := fun ω t => f₂ ω t * Real.exp (-S (Φ t ω)) +
    f₁ ω t * (Real.exp (-S (Φ t ω)) * (-s₁ ω t))
  have hG : Measurable G := m₁.mul hw
  have hGb (ω : α) : |G ω| ≤ A₁ := by
    simp only [G]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ A₁ * 1 := mul_le_mul (hA₁ ω) (hex ω) (Real.exp_pos _).le ((abs_nonneg _).trans (hA₁ ω))
      _ = A₁ := mul_one _
  have hg (ω : α) (t : ℝ) : HasDerivAt (fun t => G (Φ t ω)) (g ω t) t := by
    have e : (fun t => G (Φ t ω)) = fun t => f₁ ω t * Real.exp (-S (Φ t ω)) := by
      funext t
      simp only [G]
      rw [e₁, zero_add]
    rw [e]
    exact (df₂ ω t).mul (ds₁ ω t).neg.exp
  have hK (ω : α) (t : ℝ) : |g ω t| ≤ A₂ + A₁ * B := by
    simp only [g]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    have h1 := hex (Φ t ω)
    have p1 := Real.exp_pos (-S (Φ t ω))
    have a₁ : |f₂ ω t| * Real.exp (-S (Φ t ω)) ≤ A₂ * 1 :=
      mul_le_mul (b₂ ω t) h1 p1.le ((abs_nonneg _).trans (b₂ ω t))
    have a₂ : Real.exp (-S (Φ t ω)) * |s₁ ω t| ≤ 1 * B :=
      mul_le_mul h1 (b₃ ω t) (abs_nonneg _) (by norm_num)
    have a₃ : |f₁ ω t| * (Real.exp (-S (Φ t ω)) * |s₁ ω t|) ≤ A₁ * (1 * B) :=
      mul_le_mul (b₁ ω t) a₂ (by positivity) ((abs_nonneg _).trans (b₁ ω t))
    linarith only [a₁, a₃]
  obtain ⟨-, hz⟩ := ibp_first ν Φ hpres h0 G hG A₁ hGb g hg _ hK
  have e0 (ω : α) : g ω 0 = Real.exp (-S ω) * (f₂ ω 0 - s₁ ω 0 * f₁ ω 0) := by
    simp only [g, h0]
    ring
  simpa only [e0] using hz

end Abstract

/-! ### The flow on configurations -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The Haar-preserving flow `U ↦ exp(t X)·U`. -/
def flow (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (U : Configuration V' Q) : Configuration V' Q :=
  cfg n (linkValue (2 * n) Q U) X t

theorem linkValue_coords (U : Configuration V' Q) (e : Edge V') :
    linkValue (2 * n) Q U (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2 = U e :=
  congrArg U ((edgeCoordinates (2 * n)).left_inv e)

/-- The rotation carried by an edge. -/
def edgeRot (X : Fin 3 → Fin 4 → Section (2 * n)) (e : Edge V') : ℍ[ℝ] :=
  imag X (edgeCoordinates (2 * n) e).2 (edgeCoordinates (2 * n) e).1

theorem edgeRot_star (X : Fin 3 → Fin 4 → Section (2 * n)) (e : Edge V') :
    star (edgeRot n X e) = -edgeRot n X e := imag_star _ _ _

theorem flow_apply (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (U : Configuration V' Q) (e : Edge V') :
    flow n X t U e = expQ (t • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) t) * U e := by
  have h := linkValue_coords n U e
  change expQ (t • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) t) *
    linkValue (2 * n) Q U (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2 = _
  rw [h]

theorem flow_pres (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) :
    MeasurePreserving (flow n X t) (referenceMeasure Q V') (referenceMeasure Q V') := by
  have h : flow n X t = fun U e =>
      expQ (t • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) t) * U e :=
    funext fun U => funext fun e => flow_apply n X t U e
  rw [h]
  exact measurePreserving_pi (μ := fun _ : Edge V' => compactHaar Q) (fun _ => compactHaar Q)
    (f := fun e q => expQ (t • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) t) * q)
    fun e => measurePreserving_mul_left _ _

theorem flow_zero (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) :
    flow n X 0 U = U := by
  funext e
  rw [flow_apply]
  have : expQ ((0 : ℝ) • edgeRot n X e) (smul_skew _ (edgeRot_star n X e) 0) = 1 := by
    apply Subtype.ext
    change NormedSpace.exp ((0 : ℝ) • edgeRot n X e) = 1
    rw [zero_smul, NormedSpace.exp_zero]
  rw [this, one_mul]

theorem flow_flow (X : Fin 3 → Fin 4 → Section (2 * n)) (s t : ℝ) (U : Configuration V' Q) :
    flow n X t (flow n X s U) = flow n X (t + s) U := by
  funext e
  rw [flow_apply, flow_apply, flow_apply, ← mul_assoc]
  congr 1
  apply Subtype.ext
  change NormedSpace.exp (t • edgeRot n X e) * NormedSpace.exp (s • edgeRot n X e) =
    NormedSpace.exp ((t + s) • edgeRot n X e)
  have hc : Commute (t • edgeRot n X e) (s • edgeRot n X e) :=
    ((Commute.refl _).smul_left t).smul_right s
  letI : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
  rw [add_smul]
  exact (NormedSpace.exp_add_of_commute hc).symm

/-! ### The jet of the action along the flow -/

theorem re_G_mul_jet' (A B C D c : ℍ[ℝ]) :
    ∃ g₁ g₂ : ℝ → ℝ, (∀ t, HasDerivAt (fun s => (G A B C D s * c).re) (g₁ t) t) ∧
      (∀ t, HasDerivAt g₁ (g₂ t) t) ∧ g₁ 0 = ((A + B + C + D) * c).re ∧
        g₂ 0 = (secondCoeff A B C D * c).re := by
  have hj := ((Jet.exp A).mul (Jet.exp B)).mul ((Jet.exp C).mul (Jet.exp D))
  have hjc : Jet (fun t => G A B C D t * c) _ _ :=
    { d1 := fun t => (hj.d1 t).mul_const c
      d2 := fun t => (hj.d2 t).mul_const c }
  refine ⟨_, _, hjc.re.1, hjc.re.2, ?_, ?_⟩
  · simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, add_assoc]
  · simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, secondCoeff]

/-- The sum of the frame-transported rotations of a plaquette. -/
def Zp (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) : ℍ[ℝ] :=
  (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ + (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂ +
    (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃ + (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₄

/-- The second-order coefficient of a plaquette. -/
def Sc (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) : ℍ[ℝ] :=
  secondCoeff (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂
    (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₄

theorem action_jet (β : ℝ) (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∃ s₁ s₂ : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t => action n Q (spatialTwist n) character β 2 (cfg n L X t)) (s₁ t) t) ∧
      (∀ t, HasDerivAt s₁ (s₂ t) t) ∧
      s₁ 0 = β * ∑ p, -(2 * (Zp n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) ∧
      s₂ 0 = β * ∑ p, -(2 * (Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) := by
  choose g₁ g₂ h₁ h₂ h₀₁ h₀₂ using fun p : PlaquetteIndex (2 * n) =>
    re_G_mul_jet' (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂
      (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₄
      (plaqC n L X p.1 p.2.1.1 p.2.1.2)
  refine ⟨fun t => β * ∑ p, -(2 * g₁ p t), fun t => β * ∑ p, -(2 * g₂ p t), ?_, ?_, ?_, ?_⟩
  · intro t
    unfold action
    simp only [term_index]
    exact (HasDerivAt.fun_sum fun p _ => ((h₁ p t).const_mul 2).const_sub 2).const_mul β
  · intro t
    exact (HasDerivAt.fun_sum fun p _ => ((h₂ p t).const_mul 2).neg).const_mul β
  · simp only [h₀₁]
    rfl
  · simp only [h₀₂]
    rfl

theorem norm_plaqC (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖plaqC n L X x μ ν‖ = 1 := by
  unfold plaqC
  rw [norm_smul, norm_coe]
  split_ifs <;> simp

theorem Zp_re_le (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) :
    |(Zp n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re| ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 := by
  refine (re_abs_le _).trans ?_
  rw [norm_mul, norm_plaqC, mul_one, ← plaq_norms n L]
  unfold Zp
  refine (norm_add_le _ _).trans ?_
  have a := norm_add_le ((plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ + (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂)
    (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃
  have b := norm_add_le (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂
  linarith only [a, b]

theorem Sc_re_le (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (p : PlaquetteIndex (2 * n)) :
    |(Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re| ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 := by
  refine (re_abs_le _).trans ?_
  rw [norm_mul, norm_plaqC, mul_one, ← plaq_norms n L]
  exact secondCoeff_norm _ _ _ _

/-- The second derivative is at most `48 β ‖X‖²`, at every configuration. -/
theorem second_le (β : ℝ) (hβ : 0 ≤ β) (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    β * ∑ p, -(2 * (Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) ≤
      48 * β * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := by
  have h : ∑ p : PlaquetteIndex (2 * n), -(2 * (Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) ≤
      ∑ p : PlaquetteIndex (2 * n), 8 * linkSq n X p.1 p.2.1.1 p.2.1.2 := by
    refine Finset.sum_le_sum fun p _ => ?_
    have a := (abs_le.1 (Sc_re_le n L X p)).1
    have b := linkSum_sq n X p.1 p.2.1.1 p.2.1.2
    linarith only [a, b]
  rw [← Finset.mul_sum] at h
  have hl : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  rw [hl] at h
  have := mul_le_mul_of_nonneg_left h hβ
  linarith only [this]

/-! ### The identity -/

/-- The action along the flow from a configuration. -/
abbrev SAt (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) (U : Configuration V' Q) : ℝ → ℝ :=
  fun t => action n Q (spatialTwist n) character β 2 (flow n X t U)

theorem action_nonneg (β : ℝ) (hβ : 0 ≤ β) (U : Configuration V' Q) :
    0 ≤ action n Q (spatialTwist n) character β 2 U := by
  rw [action_eq_mul, TwistedNearFlat.actionOne_eq]
  exact mul_nonneg hβ (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The bounds on the first and second derivatives, uniform in the configuration. -/
def K1 (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) : ℝ :=
  β * ∑ p : PlaquetteIndex (2 * n), 2 * linkSum n X p.1 p.2.1.1 p.2.1.2

def K2 (β : ℝ) (X : Fin 3 → Fin 4 → Section (2 * n)) : ℝ :=
  β * ∑ p : PlaquetteIndex (2 * n), 2 * linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2

/-- **Integration by parts against Haar measure.** No smallness of any kind is assumed. -/
theorem ibp_reference (β : ℝ) (hβ : 0 ≤ β) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    Measurable (fun U => deriv (SAt n β X U) 0) ∧ Measurable (fun U => deriv (deriv (SAt n β X U)) 0) ∧
    (∀ U, |deriv (SAt n β X U) 0| ≤ K1 n β X) ∧ (∀ U, |deriv (deriv (SAt n β X U)) 0| ≤ K2 n β X) ∧
    (∀ U, deriv (deriv (SAt n β X U)) 0 ≤ 48 * β * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ∧
    ∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U) * (deriv (SAt n β X U) 0) ^ 2
        ∂referenceMeasure Q V' =
      ∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U) * deriv (deriv (SAt n β X U)) 0
        ∂referenceMeasure Q V' := by
  set S := action n Q (spatialTwist n) character β 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous β 2
  have hS0 : ∀ U, 0 ≤ S U := action_nonneg n β hβ
  choose s₁ s₂ h₁ h₂ h₀₁ h₀₂ using fun U : Configuration V' Q =>
    action_jet n β (linkValue (2 * n) Q U) X
  have ed (U : Configuration V' Q) : deriv (SAt n β X U) = s₁ U := funext fun t => (h₁ U t).deriv
  have ed0 (U : Configuration V' Q) : deriv (SAt n β X U) 0 = s₁ U 0 := by rw [ed]
  have edd0 (U : Configuration V' Q) : deriv (deriv (SAt n β X U)) 0 = s₂ U 0 := by
    rw [ed]
    exact (h₂ U 0).deriv
  have b₁ (U : Configuration V' Q) : |s₁ U 0| ≤ K1 n β X := by
    rw [h₀₁, abs_mul, abs_of_nonneg hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_neg, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (Zp_re_le n _ X p) (by norm_num)
  have b₂ (U : Configuration V' Q) : |s₂ U 0| ≤ K2 n β X := by
    rw [h₀₂, abs_mul, abs_of_nonneg hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_neg, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (Sc_re_le n _ X p) (by norm_num)
  have hK₁0 : 0 ≤ K1 n β X := (abs_nonneg _).trans (b₁ (fun _ => 1))
  -- The weight along the flow, and its two derivatives.
  let G : Configuration V' Q → ℝ := fun U => Real.exp (-S U)
  let g₁ : Configuration V' Q → ℝ → ℝ := fun U t => Real.exp (-S (flow n X t U)) * (-s₁ U t)
  let g₂ : Configuration V' Q → ℝ → ℝ := fun U t =>
    Real.exp (-S (flow n X t U)) * (-s₁ U t) * (-s₁ U t) + Real.exp (-S (flow n X t U)) * (-s₂ U t)
  have d₁ (U : Configuration V' Q) (t : ℝ) : HasDerivAt (fun t => G (flow n X t U)) (g₁ U t) t :=
    (h₁ U t).neg.exp
  have d₂ (U : Configuration V' Q) (t : ℝ) : HasDerivAt (g₁ U) (g₂ U t) t :=
    ((h₁ U t).neg.exp).mul (h₂ U t).neg
  have e0 (U : Configuration V' Q) : S (flow n X 0 U) = S U := by rw [flow_zero]
  have ex (U : Configuration V' Q) : Real.exp (-S U) ≤ 1 := by
    have := hS0 U
    exact Real.exp_le_one_iff.2 (by linarith only [this])
  have g₁0 (U : Configuration V' Q) : g₁ U 0 = Real.exp (-S U) * (-s₁ U 0) := by
    simp only [g₁, e0]
  have g₂0 (U : Configuration V' Q) : g₂ U 0 =
      Real.exp (-S U) * (s₁ U 0) ^ 2 - Real.exp (-S U) * s₂ U 0 := by
    simp only [g₂, e0]
    ring
  have hG : Measurable G := (Real.continuous_exp.comp hSc.neg).measurable
  have hGb (U : Configuration V' Q) : |G U| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact ex U
  have hb1 (U : Configuration V' Q) : |g₁ U 0| ≤ K1 n β X := by
    rw [g₁0, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ 1 * |s₁ U 0| := mul_le_mul_of_nonneg_right (ex U) (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact b₁ U
  have hb2 (U : Configuration V' Q) : |g₂ U 0| ≤ K1 n β X ^ 2 + K2 n β X := by
    rw [g₂0]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
    have a : Real.exp (-S U) * |s₁ U 0| ^ 2 ≤ 1 * K1 n β X ^ 2 :=
      mul_le_mul (ex U) (pow_le_pow_left₀ (abs_nonneg _) (b₁ U) 2) (by positivity) (by norm_num)
    have c : Real.exp (-S U) * |s₂ U 0| ≤ 1 * K2 n β X :=
      mul_le_mul (ex U) (b₂ U) (abs_nonneg _) (by norm_num)
    linarith only [a, c]
  obtain ⟨m₁, m₂, hz⟩ := ibp_second (referenceMeasure Q V') (flow n X) (flow_pres n X) (flow_zero n X)
    (flow_flow n X) G hG 1 hGb g₁ g₂ d₁ d₂ _ _ hb1 hb2
  have hexp : Measurable fun U => Real.exp (S U) := (Real.continuous_exp.comp hSc).measurable
  have ms₁ : Measurable fun U => s₁ U 0 := by
    have : (fun U => s₁ U 0) = fun U => -(Real.exp (S U) * g₁ U 0) := by
      funext U
      rw [g₁0, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      ring
    rw [this]
    exact (hexp.mul m₁).neg
  have ms₂ : Measurable fun U => s₂ U 0 := by
    have : (fun U => s₂ U 0) = fun U => (s₁ U 0) ^ 2 - Real.exp (S U) * g₂ U 0 := by
      funext U
      rw [g₂0, mul_sub, ← mul_assoc, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      ring
    rw [this]
    exact (ms₁.pow_const 2).sub (hexp.mul m₂)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ed0] using ms₁
  · simpa only [edd0] using ms₂
  · exact fun U => by
      rw [ed0]
      exact b₁ U
  · exact fun U => by
      rw [edd0]
      exact b₂ U
  · intro U
    rw [edd0, h₀₂]
    exact second_le n β hβ _ X
  · simp only [ed0, edd0]
    have hi₁ : Integrable (fun U => Real.exp (-S U) * (s₁ U 0) ^ 2) (referenceMeasure Q V') := by
      refine Integrable.of_bound (hG.mul (ms₁.pow_const 2)).aestronglyMeasurable (K1 n β X ^ 2)
        (Eventually.of_forall fun U => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow]
      calc _ ≤ 1 * K1 n β X ^ 2 :=
            mul_le_mul (ex U) (pow_le_pow_left₀ (abs_nonneg _) (b₁ U) 2) (by positivity) (by norm_num)
        _ = _ := one_mul _
    have hi₂ : Integrable (fun U => Real.exp (-S U) * s₂ U 0) (referenceMeasure Q V') := by
      refine Integrable.of_bound (hG.mul ms₂).aestronglyMeasurable (K2 n β X)
        (Eventually.of_forall fun U => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc _ ≤ 1 * K2 n β X := mul_le_mul (ex U) (b₂ U) (abs_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have : ∫ U, g₂ U 0 ∂referenceMeasure Q V' =
        ∫ U, Real.exp (-S U) * (s₁ U 0) ^ 2 ∂referenceMeasure Q V' -
          ∫ U, Real.exp (-S U) * s₂ U 0 ∂referenceMeasure Q V' := by
      simp only [g₂0]
      exact integral_sub hi₁ hi₂
    rw [hz] at this
    linarith only [this]

/-- Integrals against the twisted law, as weighted integrals against Haar measure. -/
theorem law_integral (β : ℝ) (f : Configuration V' Q → ℝ) :
    ∫ U, f U ∂twistedLaw n β =
      (gibbsPartition V' Q (action n Q (spatialTwist n) character β 2))⁻¹.toReal *
        ∫ U, Real.exp (-action n Q (spatialTwist n) character β 2 U) * f U
          ∂referenceMeasure Q V' := by
  have hSc : Continuous (action n Q (spatialTwist n) character β 2) :=
    continuous_action n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hd : Measurable (gibbsDensity V' Q (action n Q (spatialTwist n) character β 2)) :=
    (Real.continuous_exp.comp hSc.neg).measurable.ennreal_ofReal
  change ∫ U, f U ∂((gibbsPartition V' Q (action n Q (spatialTwist n) character β 2))⁻¹ •
    (referenceMeasure Q V').withDensity (gibbsDensity V' Q (action n Q (spatialTwist n) character β 2))) = _
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hd
    (Eventually.of_forall fun U => ENNReal.ofReal_lt_top), smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun U => ?_)
  change (ENNReal.ofReal (Real.exp (-_))).toReal • f U = _
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- **The integration-by-parts identity for the twisted Wilson measure.** For every direction, every
`β ≥ 0` and every lattice size, the variance of the force along `X` equals the mean second derivative. -/
theorem gibbs_ibp (β : ℝ) (hβ : 0 ≤ β) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∫ U, (deriv (SAt n β X U) 0) ^ 2 ∂twistedLaw n β =
      ∫ U, deriv (deriv (SAt n β X U)) 0 ∂twistedLaw n β := by
  obtain ⟨-, -, -, -, -, h⟩ := ibp_reference n β hβ X
  rw [law_integral, law_integral, h]

/-- **The force along any direction has variance at most `48 β ‖X‖²`, at every `β` and every size.** -/
theorem force_bound (β : ℝ) (hβ : 0 ≤ β) (X : Fin 3 → Fin 4 → Section (2 * n)) :
    ∫ U, (deriv (SAt n β X U) 0) ^ 2 ∂twistedLaw n β ≤ 48 * β * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := by
  obtain ⟨-, m₂, -, b₂, hle, -⟩ := ibp_reference n β hβ X
  rw [gibbs_ibp n β hβ X]
  haveI : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hi : Integrable (fun U => deriv (deriv (SAt n β X U)) 0) (twistedLaw n β) :=
    Integrable.of_bound m₂.aestronglyMeasurable (K2 n β X)
      (Eventually.of_forall fun U => by simpa using b₂ U)
  calc _ ≤ ∫ _, 48 * β * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 ∂twistedLaw n β :=
        integral_mono hi (integrable_const _) hle
    _ = _ := by simp

/-! ### The plaquette equation -/

/-- The first-order and second-order parts of a plaquette, for a configuration. -/
def Ap (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) : ℝ :=
  (Zp n (linkValue (2 * n) Q U) X q *
    plaqC n (linkValue (2 * n) Q U) X q.1 q.2.1.1 q.2.1.2).re

def Bp (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) : ℝ :=
  (Sc n (linkValue (2 * n) Q U) X q *
    plaqC n (linkValue (2 * n) Q U) X q.1 q.2.1.1 q.2.1.2).re

theorem term_jet (L : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n))
    (p : PlaquetteIndex (2 * n)) :
    ∃ f₁ f₂ : ℝ → ℝ,
      (∀ t, HasDerivAt (fun t => term n Q (spatialTwist n) character 2 (cfg n L X t) p) (f₁ t) t) ∧
      (∀ t, HasDerivAt f₁ (f₂ t) t) ∧
      f₁ 0 = -(2 * (Zp n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) ∧
      f₂ 0 = -(2 * (Sc n L X p * plaqC n L X p.1 p.2.1.1 p.2.1.2).re) := by
  obtain ⟨g₁, g₂, h₁, h₂, h₀₁, h₀₂⟩ := re_G_mul_jet' (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₁
    (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₂ (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₃
    (plaqOf n L X p.1 p.2.1.1 p.2.1.2).Y₄ (plaqC n L X p.1 p.2.1.1 p.2.1.2)
  refine ⟨fun t => -(2 * g₁ t), fun t => -(2 * g₂ t), ?_, ?_, ?_, ?_⟩
  · intro t
    simp only [term_index]
    have := ((h₁ t).const_mul 2).const_sub 2
    exact this
  · intro t
    exact ((h₂ t).const_mul 2).neg
  · simp only [h₀₁]
    rfl
  · simp only [h₀₂, Sc]

theorem term_abs_le (U : Configuration V' Q) (p : PlaquetteIndex (2 * n)) :
    |term n Q (spatialTwist n) character 2 U p| ≤ 4 := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  have e := term_eq_defect_sq n U x μ ν h
  have hd : defect (linkValue (2 * n) Q U) μ ν x ≤ 2 := by
    unfold defect d
    refine (norm_sub_le _ _).trans ?_
    rw [norm_coe, norm_coe]
    norm_num
  have h0 := defect_nonneg (linkValue (2 * n) Q U) μ ν x
  change |term n Q (spatialTwist n) character 2 U (x, ⟨(μ, ν), h⟩)| ≤ 4
  rw [e, abs_of_nonneg (sq_nonneg _)]
  nlinarith only [hd, h0]

theorem term_measurable (p : PlaquetteIndex (2 * n)) :
    Measurable fun U : Configuration V' Q => term n Q (spatialTwist n) character 2 U p :=
  (continuous_term n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous 2 p).measurable

theorem Ap_abs (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    |Ap n X q U| ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 := Zp_re_le n _ X q

theorem Bp_abs (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
    |Bp n X q U| ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 ^ 2 := Sc_re_le n _ X q

theorem Ap_Bp_measurable (X : Fin 3 → Fin 4 → Section (2 * n)) (q : PlaquetteIndex (2 * n)) :
    Measurable (Ap n X q) ∧ Measurable (Bp n X q) := by
  choose f₁ f₂ h₁ h₂ h₀₁ h₀₂ using fun U : Configuration V' Q =>
    term_jet n (linkValue (2 * n) Q U) X q
  obtain ⟨m₁, m₂, -⟩ := ibp_second (referenceMeasure Q V') (flow n X) (flow_pres n X) (flow_zero n X)
    (flow_flow n X) (fun U => term n Q (spatialTwist n) character 2 U q) (term_measurable n q) 4
    (fun U => term_abs_le n U q) f₁ f₂ h₁ h₂ (2 * linkSum n X q.1 q.2.1.1 q.2.1.2)
    (2 * linkSum n X q.1 q.2.1.1 q.2.1.2 ^ 2)
    (fun U => by
      rw [h₀₁, abs_neg, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Ap_abs n X q U) (by norm_num))
    (fun U => by
      rw [h₀₂, abs_neg, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Bp_abs n X q U) (by norm_num))
  constructor
  · have : Ap n X q = fun U => (-(1 / 2 : ℝ)) * f₁ U 0 := by
      funext U
      rw [h₀₁]
      simp only [Ap]
      ring
    rw [this]
    exact m₁.const_mul _
  · have : Bp n X q = fun U => (-(1 / 2 : ℝ)) * f₂ U 0 := by
      funext U
      rw [h₀₂]
      simp only [Bp]
      ring
    rw [this]
    exact m₂.const_mul _

/-- **The plaquette equation.** For every direction `X`, plaquette `p`, `β ≥ 0` and lattice size,
`2 β Σ_q E[A_q A_p] = -E[B_p]`, where `A_q` is the rate of change of `Re(z P_q)` along `X` and `B_q` its second
derivative. This is an exact loop equation for the twisted Wilson measure. -/
theorem plaquette_ibp (β : ℝ) (hβ : 0 ≤ β) (X : Fin 3 → Fin 4 → Section (2 * n))
    (p : PlaquetteIndex (2 * n)) :
    2 * β * ∑ q, ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β = -∫ U, Bp n X p U ∂twistedLaw n β := by
  set S := action n Q (spatialTwist n) character β 2 with hS
  have hSc : Continuous S := continuous_action n Q (spatialTwist n) character
    WilsonSingleLinkStaples.character_continuous β 2
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  choose f₁ f₂ h₁ h₂ h₀₁ h₀₂ using fun U : Configuration V' Q =>
    term_jet n (linkValue (2 * n) Q U) X p
  choose s₁ s₂ d₁ d₂ e₀₁ e₀₂ using fun U : Configuration V' Q =>
    action_jet n β (linkValue (2 * n) Q U) X
  have hB : ∀ U, |s₁ U 0| ≤ K1 n β X := by
    intro U
    rw [e₀₁, abs_mul, abs_of_nonneg hβ]
    refine mul_le_mul_of_nonneg_left ?_ hβ
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_neg, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (Zp_re_le n _ X q) (by norm_num)
  have hz := ibp_mixed (referenceMeasure Q V') (flow n X) (flow_pres n X) (flow_zero n X)
    (flow_flow n X) (fun U => term n Q (spatialTwist n) character 2 U p) (term_measurable n p) 4
    (fun U => term_abs_le n U p) f₁ f₂ h₁ h₂ (2 * linkSum n X p.1 p.2.1.1 p.2.1.2)
    (2 * linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2)
    (fun U => by
      rw [h₀₁, abs_neg, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Ap_abs n X p U) (by norm_num))
    (fun U => by
      rw [h₀₂, abs_neg, abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left (Bp_abs n X p U) (by norm_num))
    S hSc.measurable (action_nonneg n β hβ) s₁ d₁ _ hB
  -- Rewrite the integrand through `A` and `B`.
  let Lq : Configuration V' Q → ℝ := fun U => ∑ q, Ap n X q U * Ap n X p U
  have hint (U : Configuration V' Q) : f₂ U 0 - s₁ U 0 * f₁ U 0 =
      -(2 * Bp n X p U) - 4 * β * Lq U := by
    rw [h₀₂, h₀₁, e₀₁]
    simp only [Lq, Finset.mul_sum, Bp, Ap, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  simp only [hint] at hz
  have mA (q : PlaquetteIndex (2 * n)) := (Ap_Bp_measurable n X q).1
  have mB := (Ap_Bp_measurable n X p).2
  have hLm : Measurable Lq := Finset.measurable_sum _ fun q _ => (mA q).mul (mA p)
  have hwm : Measurable fun U => Real.exp (-S U) := (Real.continuous_exp.comp hSc.neg).measurable
  have hex (U : Configuration V' Q) : Real.exp (-S U) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith only [action_nonneg n β hβ U])
  have boundw (h : Configuration V' Q → ℝ) (hm : Measurable h) (K : ℝ) (hK : ∀ U, |h U| ≤ K) :
      Integrable (fun U => Real.exp (-S U) * h U) (referenceMeasure Q V') := by
    refine Integrable.of_bound (hwm.mul hm).aestronglyMeasurable K (Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc _ ≤ 1 * K := mul_le_mul (hex U) (hK U) (abs_nonneg _) (by norm_num)
      _ = K := one_mul _
  have hprod (q : PlaquetteIndex (2 * n)) (U : Configuration V' Q) :
      |Ap n X q U * Ap n X p U| ≤ linkSum n X q.1 q.2.1.1 q.2.1.2 * linkSum n X p.1 p.2.1.1 p.2.1.2 := by
    rw [abs_mul]
    exact mul_le_mul (Ap_abs n X q U) (Ap_abs n X p U) (abs_nonneg _)
      ((abs_nonneg _).trans (Ap_abs n X q U))
  have hLb (U : Configuration V' Q) : |Lq U| ≤
      ∑ q : PlaquetteIndex (2 * n), linkSum n X q.1 q.2.1.1 q.2.1.2 * linkSum n X p.1 p.2.1.1 p.2.1.2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => hprod q U)
  have iL := boundw Lq hLm _ hLb
  have iB := boundw (Bp n X p) mB _ (Bp_abs n X p)
  have split : ∫ U, Real.exp (-S U) * (-(2 * Bp n X p U) - 4 * β * Lq U) ∂referenceMeasure Q V' =
      -(2 * ∫ U, Real.exp (-S U) * Bp n X p U ∂referenceMeasure Q V') -
        4 * β * ∫ U, Real.exp (-S U) * Lq U ∂referenceMeasure Q V' := by
    have e (U : Configuration V' Q) : Real.exp (-S U) * (-(2 * Bp n X p U) - 4 * β * Lq U) =
        (-2) * (Real.exp (-S U) * Bp n X p U) - 4 * β * (Real.exp (-S U) * Lq U) := by ring
    simp only [e]
    rw [integral_sub (iB.const_mul _) (iL.const_mul _), integral_const_mul, integral_const_mul]
    ring
  rw [split] at hz
  have sumint : ∑ q, ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β = ∫ U, Lq U ∂twistedLaw n β := by
    symm
    refine integral_finset_sum _ fun q _ => ?_
    exact Integrable.of_bound ((mA q).mul (mA p)).aestronglyMeasurable _
      (Eventually.of_forall fun U => hprod q U)
  rw [sumint, law_integral, law_integral]
  set c := (gibbsPartition V' Q (action n Q (spatialTwist n) character β 2))⁻¹.toReal
  have hz' : 2 * β * ∫ U, Real.exp (-S U) * Lq U ∂referenceMeasure Q V' =
      -∫ U, Real.exp (-S U) * Bp n X p U ∂referenceMeasure Q V' := by
    linarith only [hz]
  calc 2 * β * (c * ∫ U, Real.exp (-S U) * Lq U ∂referenceMeasure Q V')
      = c * (2 * β * ∫ U, Real.exp (-S U) * Lq U ∂referenceMeasure Q V') := by ring
    _ = _ := by
      rw [hz']
      ring

/-- **Conditional local bound.** If the cross correlations of `p` with all other plaquettes are nonnegative
along `X`, then the rate of change of `p` has variance at most `T²/(2β)`, with no dependence on the volume. The
hypothesis is supported numerically, and it is open. -/
theorem own_le_of_cross (β : ℝ) (hβ : 0 < β) (X : Fin 3 → Fin 4 → Section (2 * n))
    (p : PlaquetteIndex (2 * n))
    (hcross : ∀ q, q ≠ p → 0 ≤ ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β) :
    ∫ U, Ap n X p U ^ 2 ∂twistedLaw n β ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 / (2 * β) := by
  have h := plaquette_ibp n β hβ.le X p
  haveI hprob : IsProbabilityMeasure (twistedLaw n β) :=
    law_probability n Q (spatialTwist n) character WilsonSingleLinkStaples.character_continuous β 2
  have hs : ∫ U, Ap n X p U * Ap n X p U ∂twistedLaw n β ≤
      ∑ q, ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β :=
    Finset.single_le_sum (f := fun q => ∫ U, Ap n X q U * Ap n X p U ∂twistedLaw n β)
      (fun q _ => by
        by_cases hq : q = p
        · subst hq
          exact integral_nonneg fun U => mul_self_nonneg _
        · exact hcross q hq) (Finset.mem_univ p)
  have mB := (Ap_Bp_measurable n X p).2
  have hB : -∫ U, Bp n X p U ∂twistedLaw n β ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 := by
    have : |∫ U, Bp n X p U ∂twistedLaw n β| ≤ linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2 := by
      have := norm_integral_le_of_norm_le_const (μ := twistedLaw n β) (f := Bp n X p)
        (C := linkSum n X p.1 p.2.1.1 p.2.1.2 ^ 2) (Eventually.of_forall fun U => Bp_abs n X p U)
      simpa using this
    linarith only [(abs_le.1 this).1]
  have e : ∫ U, Ap n X p U ^ 2 ∂twistedLaw n β = ∫ U, Ap n X p U * Ap n X p U ∂twistedLaw n β := by
    simp only [sq]
  rw [e, le_div_iff₀ (by positivity)]
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * β)
  nlinarith only [hm, h, hB]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedIBP
