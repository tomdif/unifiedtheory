/- Finite periodic Wilson law with real plaquette coefficients z, on an even
time circle. A reflection-invariant z gives reflection positivity through the
existing site-reflection coordinates. Invariance forces trivial Z2 flux in every
plane containing time, so a purely spatial twist is the compatible choice.
This is a finite-lattice statement; it constructs no continuum theory. -/
import UnifiedTheory.Clay.YangMills.PeriodicSiteReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 PeriodicHalfSplit PeriodicHalfAction
open PeriodicTimeReflection PeriodicPlaquetteReflection PeriodicSiteReflection

variable (n : ℕ) [NeZero n]

/-- Invariance of the plaquette coefficients under the actual site reflection. -/
def ReflectionInvariant (z : PlaquetteIndex (2 * n) → ℝ) : Prop :=
  ∀ p, z (reflectPlaquette (2 * n) p) = z p

variable (G : Type*) [Group G]

def term (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) (p : PlaquetteIndex (2 * n)) : ℝ :=
  c - z p * (χ (plaquetteProduct (2 * n) G U p.1 p.2.1.1 p.2.1.2)).re

def action (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) : ℝ :=
  β * ∑ p, term n G z χ c U p

def boundaryPart (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) : ℝ := by
  classical
  exact β * ∑ p, if BoundaryP n p then term n G z χ c U p else 0

def positivePart (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) : ℝ := by
  classical
  exact β * ∑ p, if PositiveP n p then term n G z χ c U p else 0

theorem action_decomposition (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) :
    action n G z χ β c U = boundaryPart n G z χ β c U + positivePart n G z χ β c U +
      positivePart n G z χ β c (reflectConfiguration (2 * n) G U) := by
  classical
  unfold action boundaryPart positivePart
  rw [sum_half_partition n (term n G z χ c U)]
  have hr (p : PlaquetteIndex (2 * n)) :
      term n G z χ c U (reflectPlaquette (2 * n) p) =
        term n G z χ c (reflectConfiguration (2 * n) G U) p := by
    unfold term
    rw [reflected_plaquette_character (2 * n) G χ hχ hinv U p, hz p]
    rfl
  simp only [hr, mul_add]

theorem action_split (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (b : BoundaryConfiguration n G) (x y : HalfConfiguration n G) :
    action n G z χ β c (assemble n G (b, (x, y))) =
      boundaryPart n G z χ β c (assemble n G (b, (1, 1))) +
      positivePart n G z χ β c (assemble n G (b, (x, 1))) +
      positivePart n G z χ β c (assemble n G (b, (y, 1))) := by
  classical
  rw [action_decomposition n G z hz χ hχ hinv, reflect_assemble]
  have hb : boundaryPart n G z χ β c (assemble n G (b, (x, y))) =
      boundaryPart n G z χ β c (assemble n G (b, (1, 1))) := by
    unfold boundaryPart
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : BoundaryP n p
    · simp only [if_pos hp, term, boundary_plaquette_independent n G p hp b x y 1 1]
    · simp only [if_neg hp]
  have hpos (s t : HalfConfiguration n G) :
      positivePart n G z χ β c (assemble n G (b, (s, t))) =
        positivePart n G z χ β c (assemble n G (b, (s, 1))) := by
    unfold positivePart
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : PositiveP n p
    · simp only [if_pos hp, term, positive_plaquette_independent n G p hp b s t 1]
    · simp only [if_neg hp]
  rw [hb, hpos x y, hpos y x]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_term (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ)
    (p : PlaquetteIndex (2 * n)) : Continuous (fun U => term n G z χ c U p) := by
  have h := continuous_holonomy (Quiver.Symmetrify (Vertex (2 * n))) G
    (plaquette (2 * n) p.1 p.2.1.1 p.2.1.2)
  have hh := h.comp (continuous_orientedExtension (Vertex (2 * n)) G)
  simp only [Function.comp_def, plaquette_holonomy_eq_product] at hh
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_re.comp (hχ.comp hh)))

theorem continuous_action (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (hχ : Continuous χ)
    (β c : ℝ) : Continuous (action n G z χ β c) :=
  continuous_const.mul (continuous_finset_sum _ (fun p _ => continuous_term n G z χ hχ c p))

theorem continuous_boundaryPart (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (hχ : Continuous χ)
    (β c : ℝ) : Continuous (boundaryPart n G z χ β c) := by
  classical
  apply continuous_const.mul
  apply continuous_finset_sum
  intro p _
  by_cases hp : BoundaryP n p
  · simpa only [hp, if_true] using continuous_term n G z χ hχ c p
  · simp only [hp, if_false]
    exact continuous_const

theorem continuous_positivePart (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (hχ : Continuous χ)
    (β c : ℝ) : Continuous (positivePart n G z χ β c) := by
  classical
  apply continuous_const.mul
  apply continuous_finset_sum
  intro p _
  by_cases hp : PositiveP n p
  · simpa only [hp, if_true] using continuous_term n G z χ hχ c p
  · simp only [hp, if_false]
    exact continuous_const

variable [CompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- The normalized twisted Wilson law. -/
def law (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ) :
    Measure (Configuration (Vertex (2 * n)) G) :=
  gibbsMeasure (Vertex (2 * n)) G (action n G z χ β c)

theorem law_probability (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (hχ : Continuous χ)
    (β c : ℝ) : IsProbabilityMeasure (law n G z χ β c) :=
  gibbsMeasure_probability _ _ _ (continuous_action n G z χ hχ β c)

def boundaryWeight (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ)
    (b : BoundaryConfiguration n G) : ℝ :=
  Real.exp (-boundaryPart n G z χ β c (assemble n G (b, (1, 1))))

def halfAction (z : PlaquetteIndex (2 * n) → ℝ) (χ : G → ℂ) (β c : ℝ)
    (s : BoundaryConfiguration n G × HalfConfiguration n G) : ℝ :=
  positivePart n G z χ β c (assemble n G (s.1, (s.2, 1)))

theorem density_identification (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hχ : ClassFunction G χ) (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (U : Configuration (Vertex (2 * n)) G) :
    Real.exp (-action n G z χ β c U) = BoundaryReflectionGluing.weight
      (boundaryWeight n G z χ β c) (halfAction n G z χ β c) (coordinates n G U) := by
  have he := action_split n G z hz χ hχ hinv β c
    (splitConfiguration n G U).1 (splitConfiguration n G U).2.1
    (splitConfiguration n G U).2.2
  rw [show ((splitConfiguration n G U).1,
    ((splitConfiguration n G U).2.1, (splitConfiguration n G U).2.2)) =
    splitConfiguration n G U from rfl, assemble_split] at he
  rw [he]
  simp only [neg_add_rev, Real.exp_add, BoundaryReflectionGluing.weight,
    boundaryWeight, halfAction, coordinates, configurationEquiv, MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk]
  ring

/-- Reflection positivity of the twisted law for every continuous closed-half observable. -/
theorem reflection_positive (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (χ : G → ℂ) (hcχ : Continuous χ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (f : BoundaryConfiguration n G × HalfConfiguration n G → ℂ) (hf : Continuous f) :
    0 ≤ (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂law n G z χ β c).re ∧
    (∫ U, star (observable n G f (reflectConfiguration (2 * n) G U)) *
      observable n G f U ∂law n G z χ β c).im = 0 := by
  have hw : Continuous (boundaryWeight n G z χ β c) := by
    apply Real.continuous_exp.comp
    apply Continuous.neg
    apply (continuous_boundaryPart n G z χ hcχ β c).comp
    exact (continuous_assemble n G).comp (continuous_id.prodMk continuous_const)
  have hA : Continuous (halfAction n G z χ β c) :=
    (continuous_positivePart n G z χ hcχ β c).comp ((continuous_assemble n G).comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)))
  exact GibbsReflectionTransport.reflection_positive_transport _ _ (Vertex (2 * n)) G _
    (coordinates n G) (splitConfiguration_preserves n G) (reflectConfiguration (2 * n) G)
    (split_reflection n G) _ hw (fun b => Real.exp_pos _) _ hA
    (density_identification n G z hz χ hχ hinv β c) f hf

/-! ### The flux constraint -/

omit [NeZero n] in
theorem odd_ne_zero (t : ZMod (2 * n)) : -(t + 1) ≠ t := by
  intro h
  have h2 : (2 : ℕ) ∣ 2 * n := Dvd.intro n rfl
  have hc := congrArg (ZMod.castHom h2 (ZMod 2)) h
  simp only [map_neg, map_add, map_one] at hc
  generalize (ZMod.castHom h2 (ZMod 2)) t = s at hc
  revert s
  decide

theorem temporal_reflect_time (x : Vertex (2 * n))
    (ν : Fin 4) (hp : (0 : Fin 4) < ν) :
    (reflectPlaquette (2 * n) (x, ⟨(0, ν), hp⟩)).1 0 = -(x 0 + 1) := by
  simp [reflectPlaquette, reflectIndex, reflectVertex, step]

theorem temporal_reflect_spatial (x : Vertex (2 * n)) (ν k : Fin 4) (hp : (0 : Fin 4) < ν)
    (hk : k ≠ 0) :
    (reflectPlaquette (2 * n) (x, ⟨(0, ν), hp⟩)).1 k = x k := by
  simp [reflectPlaquette, reflectIndex, reflectVertex, step, hk]

/-- The closed 2-torus of temporal plaquettes through `x₀` in the plane `(0, ν)`. -/
def fluxSheet (ν : Fin 4) (hν : (0 : Fin 4) < ν) (x₀ : Vertex (2 * n)) :
    Finset (PlaquetteIndex (2 * n)) := by
  classical
  exact Finset.univ.filter fun p =>
    p.2 = ⟨(0, ν), hν⟩ ∧ ∀ k, k ≠ 0 → k ≠ ν → p.1 k = x₀ k

/-- Total Z2 flux of the coefficients through a temporal 2-torus. -/
def temporalFlux (z : PlaquetteIndex (2 * n) → ℝ) (ν : Fin 4) (hν : (0 : Fin 4) < ν)
    (x₀ : Vertex (2 * n)) : ℝ := ∏ p ∈ fluxSheet n ν hν x₀, z p

/-- Reflection acts freely on each temporal sheet, so reflection-invariant Z2
coefficients have trivial flux through every plane containing time. -/
theorem temporalFlux_eq_one (z : PlaquetteIndex (2 * n) → ℝ) (hz : ReflectionInvariant n z)
    (hsq : ∀ p, z p * z p = 1) (ν : Fin 4) (hν : (0 : Fin 4) < ν) (x₀ : Vertex (2 * n)) :
    temporalFlux n z ν hν x₀ = 1 := by
  classical
  unfold temporalFlux
  apply Finset.prod_involution (fun p _ => reflectPlaquette (2 * n) p)
  · intro p _
    rw [hz p]
    exact hsq p
  · intro p hp _ heq
    have hm := (Finset.mem_filter.mp hp).2.1
    rcases p with ⟨x, μν⟩
    obtain rfl : μν = ⟨(0, ν), hν⟩ := hm
    have ht := temporal_reflect_time n x ν hν
    rw [heq] at ht
    exact odd_ne_zero n (x 0) ht.symm
  · intro p hp
    have hmem := (Finset.mem_filter.mp hp).2
    rcases p with ⟨x, μν⟩
    obtain ⟨hm, hk⟩ := hmem
    obtain rfl : μν = ⟨(0, ν), hν⟩ := hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, ?_⟩
    intro k h0 hkν
    rw [temporal_reflect_spatial n x ν k hν h0]
    exact hk k h0 hkν
  · intro p _
    exact reflectPlaquette_involutive (2 * n) p

/-- A nontrivial temporal flux rules out reflection invariance of the coefficients. -/
theorem not_invariant_of_temporalFlux (z : PlaquetteIndex (2 * n) → ℝ)
    (hsq : ∀ p, z p * z p = 1) (ν : Fin 4) (hν : (0 : Fin 4) < ν) (x₀ : Vertex (2 * n))
    (hflux : temporalFlux n z ν hν x₀ = -1) : ¬ ReflectionInvariant n z := by
  intro hz
  rw [temporalFlux_eq_one n z hz hsq ν hν x₀] at hflux
  norm_num at hflux

/-- The spatial twist `n₁₂ = 1`: sign `-1` on one stack of (1,2) plaquettes. -/
def spatialTwist (p : PlaquetteIndex (2 * n)) : ℝ := by
  classical
  exact if p.2.1 = (1, 2) ∧ p.1 1 = 0 ∧ p.1 2 = 0 then -1 else 1

theorem spatialTwist_sq (p : PlaquetteIndex (2 * n)) :
    spatialTwist n p * spatialTwist n p = 1 := by
  classical
  unfold spatialTwist
  split_ifs <;> norm_num

theorem spatialTwist_invariant : ReflectionInvariant n (spatialTwist n) := by
  classical
  rintro ⟨x, μν⟩
  have hk (k : Fin 4) (hk : k ≠ 0) : (reflectPlaquette (2 * n) (x, μν)).1 k = x k := by
    simp only [reflectPlaquette, reflectIndex]
    split_ifs with h
    · simp [reflectVertex, step, hk]
    · simp [reflectVertex, hk]
  have h1 := hk 1 (by decide)
  have h2 := hk 2 (by decide)
  unfold spatialTwist
  simp only [h1, h2]
  rfl

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedReflection
