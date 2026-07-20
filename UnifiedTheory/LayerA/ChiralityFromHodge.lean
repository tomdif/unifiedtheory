/-
  LayerA/ChiralityFromHodge.lean — abstract Hodge grading of the K/P sector

  THE GAP THIS FILE CLOSES:

  In ChiralityFromKP.lean, chirality is derived as an ALGEBRAIC asymmetry:
  the K-sector (source modes) is constrained by φ while the P-sector
  (dressing modes) is unconstrained. The K-sector is called "left-handed"
  and the P-sector "right-handed" — but these labels are in quotes because
  the connection to PHYSICAL spinorial chirality (γ₅) was a physical
  identification, not a theorem.

  Paper passage (lines 963-968): "The connection from algebraic asymmetry
  to physical chirality is a physical identification."

  HONEST SCOPE OF THIS FILE:

  This file proves the real-linear algebra behind an abstract Z/2 grading.  It
  does NOT construct a Lorentzian Clifford module, gamma matrices, a spin
  structure, Weyl fermions, or an SU(2)_L interaction.  Consequently it does
  not by itself upgrade the K/P labels to physical fermion chirality.  The
  executable Weyl-projector and weak-vertex bridge is formalized separately in
  Audit/KFCausalSetWeakHandednessBridge.lean, where the remaining causal-to-
  spinor locking law and oriented-branch condition are stated explicitly.

  THE ARGUMENT (three steps):

  STEP 1: Any supplied involution on ker(φ) gives complementary `+1` and `-1`
  eigenspaces.  In d=4, Hodge star supplies such an involution on Euclidean
  2-forms.  This file does not prove that the abstract `ker(φ)` is a 2-form
  or Weyl-curvature module; the capstone takes the involution on `ker(φ)` as
  an explicit hypothesis.

  STEP 2: The K-sector (1-dimensional, trace direction) does NOT carry this
  grading. A 1-dimensional space has only the trivial grading.

  CONTINUUM INTERPRETATION (not proved in this file): after complexification
  in Lorentzian signature, self-dual and anti-self-dual bivectors transform in
  the (1,0) and (0,1) Lorentz representations.  Relating those bivector
  representations to the (1/2,0) and (0,1/2) Weyl spinor modules requires a
  Clifford/spin construction.  Hodge star on Euclidean real 2-forms is not
  literally the gamma-five operator on spinors.

  CONCLUSION PROVED HERE: a supplied nontrivial involution on `ker(φ)` gives
  a complementary Z/2 grading, while a one-dimensional complement cannot carry
  a nontrivial complementary grading.

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerA.KPDecomposition
import UnifiedTheory.LayerB.ChiralityFromKP
import UnifiedTheory.LayerA.ChiralDistinctness

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerA.ChiralityFromHodge

open UnifiedTheory.LayerB.ChiralityFromKP
open UnifiedTheory.LayerA.ChiralDistinctness

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Structure: ℤ/2 chiral grading -/

/-- A **chiral grading** on a vector space: a decomposition into two
    complementary subspaces V⁺ (self-dual / left-handed) and V⁻
    (anti-self-dual / right-handed). -/
structure ChiralGrading (W : Type*) [AddCommGroup W] [Module ℝ W] where
  plus : Submodule ℝ W
  minus : Submodule ℝ W
  complementary : IsCompl plus minus

/-- A chiral grading is **nontrivial** if both V⁺ and V⁻ are nonzero. -/
def ChiralGrading.IsNontrivial {W : Type*} [AddCommGroup W] [Module ℝ W]
    (g : ChiralGrading W) : Prop :=
  g.plus ≠ ⊥ ∧ g.minus ≠ ⊥

/-! ### Step 1: The Hodge star induces a chiral grading -/

/-- An **involution** on a vector space: a linear map with ★² = id. -/
structure Involution (W : Type*) [AddCommGroup W] [Module ℝ W] where
  star : W →ₗ[ℝ] W
  involutive : ∀ w : W, star (star w) = w

/-- The self-dual subspace: {w | ★w = w}. -/
def Involution.plusSpace {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) : Submodule ℝ W where
  carrier := {w | inv.star w = w}
  add_mem' := by
    intro a b ha hb
    change inv.star (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := by
    change inv.star 0 = 0
    exact map_zero inv.star
  smul_mem' := by
    intro c w hw
    change inv.star (c • w) = c • w
    rw [map_smul, hw]

/-- The anti-self-dual subspace: {w | ★w = -w}. -/
def Involution.minusSpace {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) : Submodule ℝ W where
  carrier := {w | inv.star w = -w}
  add_mem' := by
    intro a b ha hb
    change inv.star (a + b) = -(a + b)
    rw [map_add, ha, hb, neg_add]
  zero_mem' := by
    change inv.star 0 = -0
    rw [map_zero, neg_zero]
  smul_mem' := by
    intro c w hw
    change inv.star (c • w) = -(c • w)
    rw [map_smul, hw, smul_neg]

/-- Every element decomposes as w = w⁺ + w⁻. -/
theorem involution_decomposition {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) (w : W) :
    ∃ (wp wm : W), wp ∈ inv.plusSpace ∧ wm ∈ inv.minusSpace ∧ w = wp + wm := by
  refine ⟨(2 : ℝ)⁻¹ • (w + inv.star w),
          (2 : ℝ)⁻¹ • (w - inv.star w), ?_, ?_, ?_⟩
  · change inv.star ((2 : ℝ)⁻¹ • (w + inv.star w)) = (2 : ℝ)⁻¹ • (w + inv.star w)
    rw [map_smul, map_add, inv.involutive]
    rw [add_comm]
  · change inv.star ((2 : ℝ)⁻¹ • (w - inv.star w)) = -((2 : ℝ)⁻¹ • (w - inv.star w))
    rw [map_smul, map_sub, inv.involutive]
    simp only [smul_sub, neg_sub]
  · have h1 : (2 : ℝ)⁻¹ • (w + inv.star w) + (2 : ℝ)⁻¹ • (w - inv.star w)
      = (2 : ℝ)⁻¹ • ((w + inv.star w) + (w - inv.star w)) := by
      rw [← smul_add]
    rw [h1]
    have h2 : (w + inv.star w) + (w - inv.star w) = (2 : ℝ) • w := by
      rw [two_smul]; abel
    rw [h2, ← mul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-- The eigenspaces have trivial intersection (characteristic ≠ 2). -/
theorem involution_plus_minus_disjoint {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) :
    inv.plusSpace ⊓ inv.minusSpace = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_inf] at hw
  obtain ⟨hp, hm⟩ := hw
  change inv.star w = w at hp
  change inv.star w = -w at hm
  have h : inv.star w = w := hp
  rw [h] at hm -- now hm : w = -w
  have h2 : w + w = 0 := by
    have := add_eq_zero_iff_eq_neg.mpr hm
    exact this
  have h3 : (2 : ℝ) • w = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

/-- The eigenspaces span the whole space. -/
theorem involution_plus_minus_span {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) :
    inv.plusSpace ⊔ inv.minusSpace = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro w
  obtain ⟨wp, wm, hp, hm, heq⟩ := involution_decomposition inv w
  rw [heq]
  exact Submodule.add_mem_sup hp hm

/-- **STEP 1**: An involution induces a chiral grading: W = W⁺ ⊕ W⁻. -/
theorem hodge_induces_chiral_grading {W : Type*} [AddCommGroup W] [Module ℝ W]
    (inv : Involution W) :
    ∃ g : ChiralGrading W, g.plus = inv.plusSpace ∧ g.minus = inv.minusSpace := by
  exact ⟨{
    plus := inv.plusSpace
    minus := inv.minusSpace
    complementary := {
      disjoint := disjoint_iff.mpr (involution_plus_minus_disjoint inv)
      codisjoint := codisjoint_iff.mpr (involution_plus_minus_span inv)
    }
  }, rfl, rfl⟩

/-! ### Step 2: A 1-dimensional space has no nontrivial chiral grading -/

/-- **STEP 2**: A 1-dimensional space cannot have a nontrivial ChiralGrading.
    dim(V⁺) + dim(V⁻) = 1 forces one to be zero. -/
theorem one_dim_no_nontrivial_grading
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (hdim : Module.finrank ℝ W = 1)
    (g : ChiralGrading W) :
    ¬g.IsNontrivial := by
  intro ⟨hp, hm⟩
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq g.plus g.minus
  rw [g.complementary.sup_eq_top, g.complementary.inf_eq_bot] at hsum
  simp only [finrank_top, finrank_bot] at hsum
  rw [hdim] at hsum
  have hp_pos : 0 < Module.finrank ℝ g.plus := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hp (Submodule.finrank_eq_zero.mp h0)
  have hm_pos : 0 < Module.finrank ℝ g.minus := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hm (Submodule.finrank_eq_zero.mp h0)
  omega

/-! ### Step 3: Gauge action relative to the abstract grading -/

/-- A **graded gauge action**: preserves the abstract grading but may act
    differently on V⁺ and V⁻.  Calling this physical fermion chirality needs
    an additional spinorial bridge. -/
structure GradedGaugeAction (W : Type*) [AddCommGroup W] [Module ℝ W]
    (grading : ChiralGrading W) where
  act : W →ₗ[ℝ] W
  preserves_plus : ∀ w ∈ grading.plus, act w ∈ grading.plus
  preserves_minus : ∀ w ∈ grading.minus, act w ∈ grading.minus

/-- A graded gauge action is **chirally asymmetric** if φ detects
    different behavior on V⁺ vs V⁻. -/
def GradedGaugeAction.IsChirallyAsymmetric
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    {grading : ChiralGrading W}
    (g : GradedGaugeAction W grading) (φ : W →ₗ[ℝ] ℝ) : Prop :=
  ∃ (wp : W) (wm : W), wp ∈ grading.plus ∧ wm ∈ grading.minus ∧
    φ (g.act wp) ≠ φ wp ∧ φ (g.act wm) = φ wm

/-! ### The main bridge theorem -/

/-- Gauge asymmetry can be expressed relative to the Hodge grading and implies
    the repo's algebraic `IsChiralAction` predicate.  This theorem does not
    identify the graded vector space with a physical Weyl spinor module. -/
theorem gauge_asymmetry_is_chiral_grading
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (grading : ChiralGrading W)
    (h_nontrivial : grading.IsNontrivial)
    (g : GradedGaugeAction W grading)
    (φ : W →ₗ[ℝ] ℝ)
    (h_asymm : g.IsChirallyAsymmetric φ) :
    grading.plus ≠ ⊥
    ∧ (∃ (wp : W) (wm : W), wp ∈ grading.plus ∧ wm ∈ grading.minus
        ∧ φ (g.act wp) ≠ φ wp ∧ φ (g.act wm) = φ wm)
    ∧ IsChiralAction φ ⟨g.act⟩ := by
  obtain ⟨wp, wm, hwp, hwm, hne, heq⟩ := h_asymm
  exact ⟨h_nontrivial.1, ⟨wp, wm, hwp, hwm, hne, heq⟩, ⟨wp, hne⟩⟩

/-! ### The capstone: the abstract grading is derived -/

/-- **CAPSTONE**: The derivation chain for a nontrivial abstract grading.

    Given: φ nonzero, K/P split with dim(K)=1, Hodge involution on ker(φ)
    with nontrivial eigenspaces.

    Concludes:
    (a) ker(φ) has a nontrivial chiral grading
    (b) K has NO nontrivial grading
    (c) ker(φ) is nontrivial.

    No Lorentz/Clifford representation or weak gauge vertex occurs in the
    statement. -/
theorem chirality_derived_not_identified
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (φ : W →ₗ[ℝ] ℝ) (_hφ : φ ≠ 0)
    (K_sub : Submodule ℝ W) (_hKP : IsCompl (LinearMap.ker φ) K_sub)
    (hK_dim : Module.finrank ℝ K_sub = 1)
    (star : (LinearMap.ker φ) →ₗ[ℝ] (LinearMap.ker φ))
    (h_star_inv : ∀ w : LinearMap.ker φ, star (star w) = w)
    (h_nontrivial_plus : Involution.plusSpace ⟨star, h_star_inv⟩ ≠ ⊥)
    (h_nontrivial_minus : Involution.minusSpace ⟨star, h_star_inv⟩ ≠ ⊥) :
    (∃ g : ChiralGrading (LinearMap.ker φ), g.IsNontrivial)
    ∧ (∀ g : ChiralGrading K_sub, ¬g.IsNontrivial)
    ∧ (LinearMap.ker φ ≠ ⊥) := by
  refine ⟨?_, ?_, ?_⟩
  · let inv : Involution (LinearMap.ker φ) := ⟨star, h_star_inv⟩
    obtain ⟨g, hgp, hgm⟩ := hodge_induces_chiral_grading inv
    exact ⟨g, hgp ▸ h_nontrivial_plus, hgm ▸ h_nontrivial_minus⟩
  · intro g
    exact one_dim_no_nontrivial_grading hK_dim g
  · intro h_bot
    have : Involution.plusSpace ⟨star, h_star_inv⟩ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro ⟨w, hw⟩ _
      have hw0 : w = 0 := by
        rw [h_bot] at hw
        exact (Submodule.mem_bot ℝ).mp hw
      exact Subtype.ext hw0
    exact h_nontrivial_plus this

/-! ### Summary: the abstract Hodge-grading derivation

  1. Partial order → causal structure (CausalFoundation)
  2. Causal structure → source functional φ (SourceFromMetric)
  3. φ → K/P decomposition: V = ker(φ) ⊕ K, dim(K)=1 (KPDecomposition)
  4. d = 4 derived (DimensionDerived)
  5. In d=4, Hodge ★² = id on Euclidean 2-forms (HodgeStarFourD)
  6. If an involution is supplied on ker(φ), it induces the grading
     ker(φ) = ker(φ)⁺ ⊕ ker(φ)⁻ (this file, Step 1)
  7. K has NO nontrivial grading (this file, Step 2)
  8. Gauge invariance of φ constrains ker(φ) (ChiralityFromKP)
  9. Constrained sector carries chiral grading (this file, bridge theorem)
  10. To obtain physical fermion chirality one must additionally construct a
      Lorentzian spinor module and connect this grading to gamma-five.

  The grading is derived.  The physical left/right interpretation is not a
  theorem of this file. -/

end UnifiedTheory.LayerA.ChiralityFromHodge
