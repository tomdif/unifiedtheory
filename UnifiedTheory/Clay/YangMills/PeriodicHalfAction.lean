/- Exact Wilson action separation across the actual even periodic site reflection.
Boundary plaquettes use boundary spatial links only; positive plaquettes use
positive and boundary links only. Reflection supplies the negative-half action. -/
import UnifiedTheory.Clay.YangMills.PeriodicHalfSplit
import UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PeriodicHalfAction
noncomputable section
open PeriodicLattice4 PeriodicTimeReflection PeriodicHalfGeometry PeriodicHalfSplit
open PeriodicPlaquetteReflection RegulatedGauge

variable (n : ℕ) [NeZero n]

def BoundaryP (p : PlaquetteIndex (2 * n)) : Prop := Boundary n (p.1, p.2.1.1)
def PositiveP (p : PlaquetteIndex (2 * n)) : Prop := Positive n (p.1, p.2.1.1)
def ClosedPositive (p : Index n) : Prop := Boundary n p ∨ Positive n p

theorem spatial_time (x : Vertex (2 * n)) (μ : Fin 4) (hμ : μ ≠ 0) :
    step (2 * n) x μ 0 = x 0 := by simp [step, hμ]

theorem next_time_val (x : Vertex (2 * n)) (ht : (x 0).val < n) :
    (step (2 * n) x 0 0).val = (x 0).val + 1 := by
  have hn := NeZero.pos n
  have h1 : (1 : ZMod (2 * n)).val = 1 := ZMod.val_one'' (by omega)
  change (x 0 + (Pi.single 0 (1 : ZMod (2 * n)) : Vertex (2 * n)) 0).val = _
  rw [Pi.single_eq_same, ZMod.val_add_of_lt (by rw [h1]; omega), h1]

theorem closed_spatial (x : Vertex (2 * n)) (μ : Fin 4) (hμ : μ ≠ 0)
    (ht : (x 0).val ≤ n) : ClosedPositive n (x, μ) := by
  by_cases h0 : (x 0).val = 0
  · exact Or.inl ⟨hμ, Or.inl h0⟩
  · by_cases hn : (x 0).val = n
    · exact Or.inl ⟨hμ, Or.inr hn⟩
    · right
      simp only [Positive, if_neg hμ]
      omega

theorem positive_plaquette_support (p : PlaquetteIndex (2 * n)) (hp : PositiveP n p) :
    ClosedPositive n (p.1, p.2.1.1) ∧
    ClosedPositive n (step (2 * n) p.1 p.2.1.1, p.2.1.2) ∧
    ClosedPositive n (step (2 * n) p.1 p.2.1.2, p.2.1.1) ∧
    ClosedPositive n (p.1, p.2.1.2) := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  have hν : ν ≠ 0 := by intro h; subst ν; exact (not_lt_of_ge (Fin.zero_le μ)) hμν
  change Positive n (x, μ) at hp
  have ht : (x 0).val < n := by
    by_cases hm : μ = 0
    · simpa only [Positive, if_pos hm] using hp
    · exact (show 0 < (x 0).val ∧ (x 0).val < n from by
        simpa only [Positive, if_neg hm] using hp).2
  refine ⟨Or.inr hp, ?_, ?_, closed_spatial n x ν hν ht.le⟩
  · by_cases hm : μ = 0
    · subst μ
      apply closed_spatial n _ ν hν
      rw [next_time_val n x ht]
      omega
    · apply closed_spatial n _ ν hν
      simpa only [spatial_time n x μ hm] using ht.le
  · right
    simpa only [Positive, spatial_time n x ν hν] using hp

theorem boundary_plaquette_support (p : PlaquetteIndex (2 * n)) (hp : BoundaryP n p) :
    Boundary n (p.1, p.2.1.1) ∧
    Boundary n (step (2 * n) p.1 p.2.1.1, p.2.1.2) ∧
    Boundary n (step (2 * n) p.1 p.2.1.2, p.2.1.1) ∧
    Boundary n (p.1, p.2.1.2) := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, hμν⟩⟩
  have hν : ν ≠ 0 := by intro h; subst ν; exact (not_lt_of_ge (Fin.zero_le μ)) hμν
  change Boundary n (x, μ) at hp
  refine ⟨hp, ?_, ?_, ⟨hν, hp.2⟩⟩
  · exact ⟨hν, by simpa only [spatial_time n x μ hp.1] using hp.2⟩
  · exact ⟨hp.1, by simpa only [spatial_time n x ν hν] using hp.2⟩

@[simp] theorem plaquette_reflect_twice (p : PlaquetteIndex (2 * n)) :
    reflectPlaquette (2 * n) (reflectPlaquette (2 * n) p) = p :=
  reflectPlaquette_involutive (2 * n) p

theorem boundaryP_fixed (p : PlaquetteIndex (2 * n)) (hp : BoundaryP n p) :
    reflectPlaquette (2 * n) p = p := by
  have h : (reflectIndex (2 * n) (p.1, p.2.1.1)).1 = p.1 :=
    congrArg (fun q : Index n => q.1) (boundary_fixed n (p.1, p.2.1.1) hp)
  exact Prod.ext h rfl

theorem positiveP_not_boundary (p : PlaquetteIndex (2 * n)) (hp : PositiveP n p) :
    ¬ BoundaryP n p := positive_not_boundary n (p.1, p.2.1.1) hp

theorem positiveP_disjoint (p : PlaquetteIndex (2 * n)) (hp : PositiveP n p) :
    ¬ PositiveP n (reflectPlaquette (2 * n) p) :=
  positive_reflection_disjoint n (p.1, p.2.1.1) hp

open scoped Classical in
theorem sum_half_partition (F : PlaquetteIndex (2 * n) → ℝ) :
    ∑ p, F p = (∑ p, if BoundaryP n p then F p else 0) +
      (∑ p, if PositiveP n p then F p else 0) +
      ∑ p, if PositiveP n p then F (reflectPlaquette (2 * n) p) else 0 := by
  classical
  have hp (p : PlaquetteIndex (2 * n)) : F p =
      (if BoundaryP n p then F p else 0) + (if PositiveP n p then F p else 0) +
      (if PositiveP n (reflectPlaquette (2 * n) p) then F p else 0) := by
    by_cases hb : BoundaryP n p
    · have hpos : ¬ PositiveP n p := fun h => positiveP_not_boundary n p h hb
      have hneg : ¬ PositiveP n (reflectPlaquette (2 * n) p) := by rwa [boundaryP_fixed n p hb]
      simp [hb, hpos, hneg]
    · by_cases hpos : PositiveP n p
      · simp [hb, hpos, positiveP_disjoint n p hpos]
      · have hneg : PositiveP n (reflectPlaquette (2 * n) p) :=
          nonboundary_nonpositive_reflect_positive n (p.1, p.2.1.1) hb hpos
        simp [hb, hpos, hneg]
  calc
    ∑ p, F p = ∑ p, ((if BoundaryP n p then F p else 0) +
        (if PositiveP n p then F p else 0) +
        (if PositiveP n (reflectPlaquette (2 * n) p) then F p else 0)) :=
      Finset.sum_congr rfl (fun p _ => hp p)
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      have h := Equiv.sum_comp (plaquetteEquiv (2 * n))
        (fun p => if PositiveP n p then F (reflectPlaquette (2 * n) p) else 0)
      change (∑ p, if PositiveP n (reflectPlaquette (2 * n) p) then
        F (reflectPlaquette (2 * n) (reflectPlaquette (2 * n) p)) else 0) = _ at h
      simpa only [plaquette_reflect_twice] using h

variable (G : Type*) [Group G]

def plaquetteTerm (χ : G → ℂ) (c : ℝ) (U : Configuration (Vertex (2 * n)) G)
    (p : PlaquetteIndex (2 * n)) : ℝ :=
  c - (χ (plaquetteProduct (2 * n) G U p.1 p.2.1.1 p.2.1.2)).re

def boundaryAction (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex (2 * n)) G) : ℝ := by
  classical
  exact β * ∑ p, if BoundaryP n p then plaquetteTerm n G χ c U p else 0

def positiveAction (χ : G → ℂ) (β c : ℝ) (U : Configuration (Vertex (2 * n)) G) : ℝ := by
  classical
  exact β * ∑ p, if PositiveP n p then plaquetteTerm n G χ c U p else 0

theorem wilsonAction_decomposition (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ) (U : Configuration (Vertex (2 * n)) G) :
    orientedWilsonAction (Vertex (2 * n)) G χ (base (2 * n)) (loops (2 * n)) β c U =
      boundaryAction n G χ β c U + positiveAction n G χ β c U +
      positiveAction n G χ β c (reflectConfiguration (2 * n) G U) := by
  classical
  change β * ∑ p : PlaquetteIndex (2 * n), (c - (χ (holonomy (Quiver.Symmetrify (Vertex (2 * n))) G
    (orientedExtension (Vertex (2 * n)) G U)
    (plaquette (2 * n) p.1 p.2.1.1 p.2.1.2))).re) = _
  simp only [plaquette_holonomy_eq_product]
  change β * ∑ p, plaquetteTerm n G χ c U p = _
  rw [sum_half_partition]
  simp only [boundaryAction, positiveAction, plaquetteTerm,
    reflected_plaquette_character (2 * n) G χ hχ hinv U, mul_add]
  rfl

theorem assemble_closed_link (p : Index n) (hp : ClosedPositive n p)
    (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    linkAt n G (assemble n G (b, (x, y))) p = linkAt n G (assemble n G (b, (x, z))) p := by
  rcases hp with hb | hp
  · exact (assemble_boundary n G (b, (x, y)) ⟨p, hb⟩).trans
      (assemble_boundary n G (b, (x, z)) ⟨p, hb⟩).symm
  · exact (assemble_positive n G (b, (x, y)) ⟨p, hp⟩).trans
      (assemble_positive n G (b, (x, z)) ⟨p, hp⟩).symm

theorem assemble_boundary_link (p : Index n) (hp : Boundary n p)
    (b : BoundaryConfiguration n G) (x y z w : HalfConfiguration n G) :
    linkAt n G (assemble n G (b, (x, y))) p = linkAt n G (assemble n G (b, (z, w))) p :=
  (assemble_boundary n G (b, (x, y)) ⟨p, hp⟩).trans
    (assemble_boundary n G (b, (z, w)) ⟨p, hp⟩).symm

theorem positive_plaquette_independent (p : PlaquetteIndex (2 * n)) (hp : PositiveP n p)
    (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    plaquetteProduct (2 * n) G (assemble n G (b, (x, y))) p.1 p.2.1.1 p.2.1.2 =
      plaquetteProduct (2 * n) G (assemble n G (b, (x, z))) p.1 p.2.1.1 p.2.1.2 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := positive_plaquette_support n p hp
  unfold plaquetteProduct
  change linkAt n G _ (p.1, p.2.1.1) * linkAt n G _ (step (2*n) p.1 p.2.1.1, p.2.1.2) *
    (linkAt n G _ (step (2*n) p.1 p.2.1.2, p.2.1.1))⁻¹ * (linkAt n G _ (p.1,p.2.1.2))⁻¹ = _
  rw [assemble_closed_link n G _ h₁ b x y z, assemble_closed_link n G _ h₂ b x y z,
    assemble_closed_link n G _ h₃ b x y z, assemble_closed_link n G _ h₄ b x y z]
  rfl

theorem boundary_plaquette_independent (p : PlaquetteIndex (2 * n)) (hp : BoundaryP n p)
    (b : BoundaryConfiguration n G) (x y z w : HalfConfiguration n G) :
    plaquetteProduct (2 * n) G (assemble n G (b, (x, y))) p.1 p.2.1.1 p.2.1.2 =
      plaquetteProduct (2 * n) G (assemble n G (b, (z, w))) p.1 p.2.1.1 p.2.1.2 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := boundary_plaquette_support n p hp
  unfold plaquetteProduct
  change linkAt n G _ (p.1, p.2.1.1) * linkAt n G _ (step (2*n) p.1 p.2.1.1, p.2.1.2) *
    (linkAt n G _ (step (2*n) p.1 p.2.1.2, p.2.1.1))⁻¹ * (linkAt n G _ (p.1,p.2.1.2))⁻¹ = _
  rw [assemble_boundary_link n G _ h₁ b x y z w, assemble_boundary_link n G _ h₂ b x y z w,
    assemble_boundary_link n G _ h₃ b x y z w, assemble_boundary_link n G _ h₄ b x y z w]
  rfl

theorem positiveAction_independent (χ : G → ℂ) (β c : ℝ)
    (b : BoundaryConfiguration n G) (x y z : HalfConfiguration n G) :
    positiveAction n G χ β c (assemble n G (b, (x, y))) =
      positiveAction n G χ β c (assemble n G (b, (x, z))) := by
  classical
  unfold positiveAction
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : PositiveP n p
  · simp only [if_pos hp, plaquetteTerm, positive_plaquette_independent n G p hp b x y z]
  · simp only [if_neg hp]

theorem boundaryAction_independent (χ : G → ℂ) (β c : ℝ)
    (b : BoundaryConfiguration n G) (x y z w : HalfConfiguration n G) :
    boundaryAction n G χ β c (assemble n G (b, (x, y))) =
      boundaryAction n G χ β c (assemble n G (b, (z, w))) := by
  classical
  unfold boundaryAction
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : BoundaryP n p
  · simp only [if_pos hp, plaquetteTerm, boundary_plaquette_independent n G p hp b x y z w]
  · simp only [if_neg hp]

/-- Exact action identity needed to apply conditional boundary reflection positivity. -/
theorem wilsonAction_split (χ : G → ℂ) (hχ : ClassFunction G χ)
    (hinv : ∀ g, (χ g⁻¹).re = (χ g).re) (β c : ℝ)
    (b : BoundaryConfiguration n G) (x y : HalfConfiguration n G) :
    orientedWilsonAction (Vertex (2 * n)) G χ (base (2 * n)) (loops (2 * n)) β c
      (assemble n G (b, (x, y))) =
      boundaryAction n G χ β c (assemble n G (b, (1, 1))) +
      positiveAction n G χ β c (assemble n G (b, (x, 1))) +
      positiveAction n G χ β c (assemble n G (b, (y, 1))) := by
  rw [wilsonAction_decomposition n G χ hχ hinv, reflect_assemble]
  rw [boundaryAction_independent n G χ β c b x y 1 1,
    positiveAction_independent n G χ β c b x y 1,
    positiveAction_independent n G χ β c b y x 1]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_plaquetteTerm (χ : G → ℂ) (hχ : Continuous χ) (c : ℝ)
    (p : PlaquetteIndex (2 * n)) : Continuous (fun U => plaquetteTerm n G χ c U p) := by
  have h := continuous_holonomy (Quiver.Symmetrify (Vertex (2 * n))) G
    (plaquette (2 * n) p.1 p.2.1.1 p.2.1.2)
  have hh := h.comp (continuous_orientedExtension (Vertex (2 * n)) G)
  simp only [Function.comp_def, plaquette_holonomy_eq_product] at hh
  exact continuous_const.sub (Complex.continuous_re.comp (hχ.comp hh))

theorem continuous_boundaryAction (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    Continuous (boundaryAction n G χ β c) := by
  classical
  apply continuous_const.mul
  apply continuous_finset_sum
  intro p _
  by_cases hp : BoundaryP n p
  · simpa only [hp, if_true] using continuous_plaquetteTerm n G χ hχ c p
  · simp only [hp, if_false]
    exact continuous_const

theorem continuous_positiveAction (χ : G → ℂ) (hχ : Continuous χ) (β c : ℝ) :
    Continuous (positiveAction n G χ β c) := by
  classical
  apply continuous_const.mul
  apply continuous_finset_sum
  intro p _
  by_cases hp : PositiveP n p
  · simpa only [hp, if_true] using continuous_plaquetteTerm n G χ hχ c p
  · simp only [hp, if_false]
    exact continuous_const

end
end UnifiedTheory.Clay.YangMills.PeriodicHalfAction
