/-
  Audit/KFCausalCSpecEdgeScaleDefect.lean   (Volume sector — edge-scale integrability defect)

  REFINEMENT of the relative-scale cocycle.  If every edge scale is derived from
  the SAME vertex counts, `r_uv = (n_u/n_v)^(1/d)`, the loop product telescopes to
  `1` identically — an algebraic identity, not an empirical test.  A genuine defect
  requires INDEPENDENTLY MEASURED, overlap-specific edge scales, whose exactness
  (existence of one global scale potential) is then a testable hypothesis.

  This file formalizes exactly that distinction as discrete Weyl integrability:

    * `IsExactScale r`  :  ∃ f > 0, r u v = f u / f v   (a global scale potential).
    * `chainProduct`    :  the oriented product of edge scales along a path.
    * `exact_loop_trivial`      : an exact scale has `H_gamma = 1` on every loop.
    * `nontrivialLoop_not_exact`: `H_gamma ≠ 1` ⟹ NO global scale potential exists.
    * gauge `r ↦ g_u r_uv g_v⁻¹`, and `loopHolonomy_gaugeInvariant`.
    * `countScale_isExact`      : node-count-derived scales are exact automatically
                                  (so their loops are trivial for free).
    * `chainProduct_mul` and `noisy_loop_holonomy` : for overlap estimates
      `r̂_uv = (f_u/f_v)(1+η)^(1/d)`, the loop holonomy equals the product of the
      per-edge error factors — the exact part cancels, only the non-integrable part
      survives.

  INTERPRETATION.  `H_gamma ≠ 1  ⟹  no single global scale potential explains all
  overlap measurements` (rejects integrability).  It does NOT by itself attribute
  the cause to Poisson noise, curvature, density variation, or mesoscopic failure —
  that separation is the next (Poisson/curvature) unit.

  Zero sorry. Zero custom axioms.
-/
import Mathlib

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecEdgeScaleDefect

variable {V : Type*}

/-- An edge scale cochain is exact if it comes from a single positive vertex
scale potential `f`. -/
def IsExactScale (r : V → V → ℝ) : Prop :=
  ∃ f : V → ℝ, (∀ v, 0 < f v) ∧ ∀ u v, r u v = f u / f v

/-- Oriented product of edge scales along the path `u :: l`. -/
def chainProduct (r : V → V → ℝ) : V → List V → ℝ
  | _, [] => 1
  | u, v :: rest => r u v * chainProduct r v rest

@[simp] theorem chainProduct_nil (r : V → V → ℝ) (u : V) : chainProduct r u [] = 1 := rfl

theorem chainProduct_cons (r : V → V → ℝ) (u v : V) (rest : List V) :
    chainProduct r u (v :: rest) = r u v * chainProduct r v rest := rfl

/-- **Telescoping.**  Along any path, an exact scale collapses to endpoints. -/
theorem chainProduct_coboundary (f : V → ℝ) (hf : ∀ v, 0 < f v) (u : V) (l : List V) :
    chainProduct (fun a b => f a / f b) u l = f u / f (l.getLastD u) := by
  induction l generalizing u with
  | nil => simp [div_self (hf u).ne']
  | cons v rest ih =>
      rw [chainProduct_cons, ih v, List.getLastD_cons]
      have h1 : f v ≠ 0 := (hf v).ne'
      have h2 : f (rest.getLastD v) ≠ 0 := (hf _).ne'
      field_simp

/-- **Exact loops are trivial.**  If a global scale potential exists, every closed
loop has holonomy `1`. -/
theorem exact_loop_trivial (r : V → V → ℝ) (h : IsExactScale r) (u : V) (l : List V)
    (hclosed : l.getLastD u = u) : chainProduct r u l = 1 := by
  obtain ⟨f, hf, hr⟩ := h
  have hre : r = fun a b => f a / f b := by funext a b; exact hr a b
  rw [hre, chainProduct_coboundary f hf u l, hclosed, div_self (hf u).ne']

/-- **A nontrivial loop rejects integrability.**  If some closed loop has holonomy
`≠ 1`, then NO global scale potential explains the edge scales. -/
theorem nontrivialLoop_not_exact (r : V → V → ℝ) (u : V) (l : List V)
    (hclosed : l.getLastD u = u) (hne : chainProduct r u l ≠ 1) : ¬ IsExactScale r :=
  fun h => hne (exact_loop_trivial r h u l hclosed)

/-! ## Vertex gauge -/

/-- A vertex gauge transformation of an edge cochain. -/
noncomputable def gaugeTransform (g : V → ℝ) (r : V → V → ℝ) : V → V → ℝ :=
  fun u v => g u * r u v / g v

theorem chainProduct_gauge (g : V → ℝ) (hg : ∀ v, 0 < g v) (r : V → V → ℝ)
    (u : V) (l : List V) :
    chainProduct (gaugeTransform g r) u l
      = (g u / g (l.getLastD u)) * chainProduct r u l := by
  induction l generalizing u with
  | nil => simp [div_self (hg u).ne']
  | cons v rest ih =>
      rw [chainProduct_cons, chainProduct_cons, gaugeTransform, ih v, List.getLastD_cons]
      have hgv := (hg v).ne'
      have hglast := (hg (rest.getLastD v)).ne'
      field_simp

/-- **Loop holonomy is gauge invariant.**  A change of scale potential leaves every
closed-loop holonomy unchanged. -/
theorem loopHolonomy_gaugeInvariant (g : V → ℝ) (hg : ∀ v, 0 < g v) (r : V → V → ℝ)
    (u : V) (l : List V) (hclosed : l.getLastD u = u) :
    chainProduct (gaugeTransform g r) u l = chainProduct r u l := by
  rw [chainProduct_gauge g hg r u l, hclosed, div_self (hg u).ne', one_mul]

/-! ## Node-count-derived scales are automatically exact -/

/-- The scale cochain read off a single vertex count field. -/
noncomputable def countScale (d : ℕ) (n : V → ℝ) : V → V → ℝ :=
  fun u v => (n u / n v) ^ ((d : ℝ)⁻¹)

/-- **Node-count-derived scales are exact.**  So their loops are trivial for free —
this is the algebraic telescoping identity, NOT an empirical test. -/
theorem countScale_isExact (d : ℕ) (n : V → ℝ) (hn : ∀ v, 0 < n v) :
    IsExactScale (countScale d n) := by
  refine ⟨fun v => (n v) ^ ((d : ℝ)⁻¹), fun v => Real.rpow_pos_of_pos (hn v) _, ?_⟩
  intro u v
  rw [countScale, Real.div_rpow (hn u).le (hn v).le]

/-! ## Overlap-estimate holonomy: only the non-integrable part survives -/

theorem chainProduct_mul (r s : V → V → ℝ) (u : V) (l : List V) :
    chainProduct (fun a b => r a b * s a b) u l
      = chainProduct r u l * chainProduct s u l := by
  induction l generalizing u with
  | nil => simp
  | cons v rest ih => rw [chainProduct_cons, chainProduct_cons, chainProduct_cons, ih v]; ring

/-- **Overlap-estimate loop holonomy.**  If each overlap estimate is an exact scale
times a per-edge error factor, `r̂_uv = (f_u/f_v) * e_uv`, then the closed-loop
holonomy is EXACTLY the product of the error factors — the integrable part cancels,
leaving only the non-integrable defect. -/
theorem noisy_loop_holonomy (f : V → ℝ) (hf : ∀ v, 0 < f v) (e : V → V → ℝ)
    (u : V) (l : List V) (hclosed : l.getLastD u = u) :
    chainProduct (fun a b => (f a / f b) * e a b) u l = chainProduct e u l := by
  rw [chainProduct_mul, chainProduct_coboundary f hf u l, hclosed, div_self (hf u).ne', one_mul]

#print axioms exact_loop_trivial
#print axioms nontrivialLoop_not_exact
#print axioms loopHolonomy_gaugeInvariant
#print axioms countScale_isExact
#print axioms noisy_loop_holonomy

end UnifiedTheory.Audit.KFCausalCSpecEdgeScaleDefect
