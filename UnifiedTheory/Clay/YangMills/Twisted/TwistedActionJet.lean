/- `hessianForm` is the actual second derivative of the twisted Wilson action along
`exp (t ξ) · flatLink`. No Taylor remainder or small-field estimate is claimed. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedHessian
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedActionJet
noncomputable section
open PeriodicLattice4 TwistedRectangle TwistedFlat CommutingShifts TwistedHessian
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion RealInnerProductSpace

/-! ### Second-order jets of products of exponentials -/

/-- `f` is twice differentiable everywhere with derivatives `f₁`, `f₂`. -/
structure Jet (f f₁ f₂ : ℝ → ℍ[ℝ]) : Prop where
  d1 : ∀ t, HasDerivAt f (f₁ t) t
  d2 : ∀ t, HasDerivAt f₁ (f₂ t) t

theorem Jet.exp (A : ℍ[ℝ]) :
    Jet (fun t => NormedSpace.exp (t • A)) (fun t => NormedSpace.exp (t • A) * A)
      (fun t => NormedSpace.exp (t • A) * A * A) where
  d1 t := hasDerivAt_exp_smul_const A t
  d2 t := (hasDerivAt_exp_smul_const A t).mul_const A

theorem Jet.mul {f f₁ f₂ g g₁ g₂ : ℝ → ℍ[ℝ]} (hf : Jet f f₁ f₂) (hg : Jet g g₁ g₂) :
    Jet (fun t => f t * g t) (fun t => f₁ t * g t + f t * g₁ t)
      (fun t => f₂ t * g t + f₁ t * g₁ t + (f₁ t * g₁ t + f t * g₂ t)) where
  d1 t := (hf.d1 t).mul (hg.d1 t)
  d2 t := ((hf.d2 t).mul (hg.d1 t)).add ((hf.d1 t).mul (hg.d2 t))

/-- The ordered product of four exponentials. -/
def G (A B C D : ℍ[ℝ]) (t : ℝ) : ℍ[ℝ] :=
  NormedSpace.exp (t • A) * NormedSpace.exp (t • B) *
    (NormedSpace.exp (t • C) * NormedSpace.exp (t • D))

theorem re_comm (x y : ℍ[ℝ]) : (x * y).re = (y * x).re := by
  simp only [Quaternion.re_mul]
  ring

/-- The real part as a continuous linear map. -/
def reCLM : ℍ[ℝ] →L[ℝ] ℝ :=
  ⟨{ toFun := fun q => q.re
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl }, Quaternion.continuous_re⟩

theorem Jet.re {f f₁ f₂ : ℝ → ℍ[ℝ]} (h : Jet f f₁ f₂) :
    (∀ t, HasDerivAt (fun s => (f s).re) ((f₁ t).re) t) ∧
      (∀ t, HasDerivAt (fun s => (f₁ s).re) ((f₂ t).re) t) :=
  ⟨fun t => reCLM.hasFDerivAt.comp_hasDerivAt t (h.d1 t),
    fun t => reCLM.hasFDerivAt.comp_hasDerivAt t (h.d2 t)⟩

/-- The real part of `G` has a second derivative at zero equal to `Re (A+B+C+D)²`. -/
theorem re_G_jet (A B C D : ℍ[ℝ]) :
    ∃ g₁ g₂ : ℝ → ℝ, (∀ t, HasDerivAt (fun s => (G A B C D s).re) (g₁ t) t) ∧
      (∀ t, HasDerivAt g₁ (g₂ t) t) ∧ g₂ 0 = ((A + B + C + D) * (A + B + C + D)).re := by
  have hj := ((Jet.exp A).mul (Jet.exp B)).mul ((Jet.exp C).mul (Jet.exp D))
  refine ⟨_, _, hj.re.1, hj.re.2, ?_⟩
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  simp only [add_mul, mul_add, Quaternion.re_add]
  rw [re_comm B A, re_comm C A, re_comm D A, re_comm C B, re_comm D B, re_comm D C]
  ring

/-! ### The perturbed field -/

variable (n : ℕ) [NeZero n]

/-- The imaginary quaternion with colour coordinates of `Ω`. -/
def imag {N : ℕ} [NeZero N] (Ω : Fin 3 → Fin 4 → Section N) (μ : Fin 4) (x : Vertex N) : ℍ[ℝ] :=
  ∑ a, Ω a μ x • basis a

theorem imag_star {N : ℕ} [NeZero N] (Ω : Fin 3 → Fin 4 → Section N) (μ : Fin 4) (x : Vertex N) :
    star (imag Ω μ x) = -imag Ω μ x := by
  ext <;> simp [imag, Fin.sum_univ_three, basis]

/-- `exp` of a skew element, as a unit quaternion. -/
def expQ (X : ℍ[ℝ]) (hX : star X = -X) : Q :=
  ⟨NormedSpace.exp X, by
    letI : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
    exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (x := X) hX⟩

theorem smul_skew (X : ℍ[ℝ]) (hX : star X = -X) (t : ℝ) : star (t • X) = -(t • X) := by
  rw [Quaternion.star_smul, hX, smul_neg]

/-- The perturbed link, with the perturbation in the frame at the tail. -/
def pertLink {N : ℕ} [NeZero N] (Ω : Fin 3 → Fin 4 → Section N) (t : ℝ) (x : Vertex N) (μ : Fin 4) :
    Q :=
  expQ (t • imag Ω μ x) (smul_skew _ (imag_star Ω μ x) t) * flatLink x μ

/-- Conjugation of an exponential by a unit quaternion. -/
theorem conj_exp (u : Q) (X : ℍ[ℝ]) :
    (u : ℍ[ℝ]) * NormedSpace.exp X * ((u⁻¹ : Q) : ℍ[ℝ]) =
      NormedSpace.exp ((u : ℍ[ℝ]) * X * ((u⁻¹ : Q) : ℍ[ℝ])) := by
  letI : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
  let y : (ℍ[ℝ])ˣ := ⟨u, ((u⁻¹ : Q) : ℍ[ℝ]), congrArg Subtype.val (mul_inv_cancel u),
    congrArg Subtype.val (inv_mul_cancel u)⟩
  exact (NormedSpace.exp_units_conj y X).symm

theorem expQ_inv (X : ℍ[ℝ]) (hX : star X = -X) :
    (((expQ X hX)⁻¹ : Q) : ℍ[ℝ]) = NormedSpace.exp (-X) := by
  change star (NormedSpace.exp X) = _
  rw [NormedSpace.star_exp, hX]

/-- Plaquette algebra: everything is moved to the base point. -/
theorem product_identity (E₁ E₂ E₃ E₄ a b c d w : Q) (hw : a * b * c⁻¹ * d⁻¹ = w)
    (hc : ∀ g : Q, Commute w g) :
    (E₁ * a) * (E₂ * b) * (E₃ * c)⁻¹ * (E₄ * d)⁻¹ =
      w * (E₁ * (a * E₂ * a⁻¹) * ((d * E₃⁻¹ * d⁻¹) * E₄⁻¹)) := by
  have h : (E₁ * a) * (E₂ * b) * (E₃ * c)⁻¹ * (E₄ * d)⁻¹ =
      E₁ * (a * E₂ * a⁻¹) * (a * b * c⁻¹ * d⁻¹) * ((d * E₃⁻¹ * d⁻¹) * E₄⁻¹) := by
    group
  rw [h, hw, mul_assoc (E₁ * (a * E₂ * a⁻¹)), ← mul_assoc, ((hc _).symm).eq, mul_assoc]

variable {N : ℕ} [NeZero N]

/-- Colour coordinates of conjugation by a flat link. -/
theorem conj_imag (Ω : Fin 3 → Fin 4 → Section N) (μ ν : Fin 4) (x : Vertex N) :
    ((flatLink x μ : Q) : ℍ[ℝ]) * imag Ω ν (step N x μ) * ((flatLink x μ)⁻¹ : Q) =
      ∑ a, ((shifts a μ).T (Ω a ν) x) • basis a := by
  simp only [imag, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ad_flatLink, smul_smul]
  congr 1
  change _ = eta (bundle a).1 (bundle a).2 x μ * Ω a ν (step N x μ)
  ring

/-- The total Lie element of a plaquette: its colour coordinates are the curl. -/
def plaquetteLie (Ω : Fin 3 → Fin 4 → Section N) (μ ν : Fin 4) (x : Vertex N) : ℍ[ℝ] :=
  imag Ω μ x + ((flatLink x μ : Q) : ℍ[ℝ]) * imag Ω ν (step N x μ) * ((flatLink x μ)⁻¹ : Q) +
    -(((flatLink x ν : Q) : ℍ[ℝ]) * imag Ω μ (step N x ν) * ((flatLink x ν)⁻¹ : Q)) +
    -imag Ω ν x

theorem plaquetteLie_eq (Ω : Fin 3 → Fin 4 → Section N) (μ ν : Fin 4) (x : Vertex N) :
    plaquetteLie Ω μ ν x = ∑ a, (curl (shifts a) (Ω a) μ ν x) • basis a := by
  unfold plaquetteLie
  rw [conj_imag, conj_imag]
  simp only [imag]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [curl, Shift.D]
  simp only [PiLp.sub_apply]
  rw [← neg_smul, ← neg_smul, ← add_smul, ← add_smul, ← add_smul]
  congr 1
  ring

/-- `Re Z² = -Σ cₐ²` for an imaginary quaternion with colour coordinates `c`. -/
theorem re_sq_basis (c : Fin 3 → ℝ) :
    ((∑ a, c a • basis a) * (∑ a, c a • basis a)).re = -∑ a, c a ^ 2 := by
  simp only [Fin.sum_univ_three, basis, Quaternion.re_mul]
  simp
  ring

/-! ### The actual action -/

open TwistedReflection PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge

/-- The perturbed configuration on the even periodic lattice. -/
def pertConfig (Ω : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) : Configuration (Vertex (2 * n)) Q :=
  fun e => pertLink Ω t (edgeCoordinates (2 * n) e).1 (edgeCoordinates (2 * n) e).2

theorem pertConfig_link (Ω : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) :
    linkValue (2 * n) Q (pertConfig n Ω t) = pertLink Ω t := rfl

/-- Conjugated Lie elements of a plaquette. -/
def lieA (Ω : Fin 3 → Fin 4 → Section (2 * n)) (μ _ν : Fin 4) (x : Vertex (2 * n)) : ℍ[ℝ] :=
  imag Ω μ x

def lieB (Ω : Fin 3 → Fin 4 → Section (2 * n)) (μ ν : Fin 4) (x : Vertex (2 * n)) : ℍ[ℝ] :=
  ((flatLink x μ : Q) : ℍ[ℝ]) * imag Ω ν (step (2 * n) x μ) * ((flatLink x μ)⁻¹ : Q)

def lieC (Ω : Fin 3 → Fin 4 → Section (2 * n)) (μ ν : Fin 4) (x : Vertex (2 * n)) : ℍ[ℝ] :=
  -(((flatLink x ν : Q) : ℍ[ℝ]) * imag Ω μ (step (2 * n) x ν) * ((flatLink x ν)⁻¹ : Q))

def lieD (Ω : Fin 3 → Fin 4 → Section (2 * n)) (_μ ν : Fin 4) (x : Vertex (2 * n)) : ℍ[ℝ] :=
  -imag Ω ν x

theorem conj_expQ (u : Q) (X : ℍ[ℝ]) (t : ℝ) (h : star (t • X) = -(t • X)) :
    ((u * expQ (t • X) h * u⁻¹ : Q) : ℍ[ℝ]) =
      NormedSpace.exp (t • ((u : ℍ[ℝ]) * X * ((u⁻¹ : Q) : ℍ[ℝ]))) := by
  change (u : ℍ[ℝ]) * NormedSpace.exp (t • X) * ((u⁻¹ : Q) : ℍ[ℝ]) = _
  rw [conj_exp, mul_smul_comm, smul_mul_assoc]

theorem conj_expQ_inv (u : Q) (X : ℍ[ℝ]) (t : ℝ) (h : star (t • X) = -(t • X)) :
    ((u * (expQ (t • X) h)⁻¹ * u⁻¹ : Q) : ℍ[ℝ]) =
      NormedSpace.exp (t • (-((u : ℍ[ℝ]) * X * ((u⁻¹ : Q) : ℍ[ℝ])))) := by
  change (u : ℍ[ℝ]) * (((expQ (t • X) h)⁻¹ : Q) : ℍ[ℝ]) * ((u⁻¹ : Q) : ℍ[ℝ]) = _
  rw [expQ_inv, conj_exp]
  congr 1
  rw [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, smul_neg]

theorem plaquette_pert (Ω : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (x : Vertex (2 * n))
    (μ ν : Fin 4) (h : μ < ν) :
    ((plaquetteProduct (2 * n) Q (pertConfig n Ω t) x μ ν : Q) : ℍ[ℝ]) =
      ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ]) *
        G (lieA n Ω μ ν x) (lieB n Ω μ ν x) (lieC n Ω μ ν x) (lieD n Ω μ ν x) t := by
  have hw := flatLink_flat (N := 2 * n) x μ ν h
  have hc : ∀ g : Q, Commute (ω ^ twistExp μ ν x) g := fun g => (ω_commute g).pow_left _
  unfold plaquetteProduct
  rw [pertConfig_link]
  unfold pertLink
  rw [product_identity _ _ _ _ _ _ _ _ _ hw hc]
  change ((ω ^ twistExp μ ν x : Q) : ℍ[ℝ]) *
    (((expQ _ _ : Q) : ℍ[ℝ]) * ((_ * expQ _ _ * _⁻¹ : Q) : ℍ[ℝ]) *
      (((_ * (expQ _ _)⁻¹ * _⁻¹ : Q) : ℍ[ℝ]) * (((expQ _ _)⁻¹ : Q) : ℍ[ℝ]))) = _
  rw [conj_expQ, conj_expQ_inv, expQ_inv]
  unfold G lieA lieB lieC lieD
  rw [← smul_neg t (imag Ω ν x)]
  rfl

theorem twistExp_cases (μ ν : Fin 4) (x : Vertex (2 * n)) :
    twistExp μ ν x = 0 ∨ twistExp μ ν x = 1 := by
  unfold twistExp
  split_ifs <;> simp

theorem term_pert (Ω : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (p : PlaquetteIndex (2 * n)) :
    term n Q (spatialTwist n) character 2 (pertConfig n Ω t) p =
      2 - 2 * (G (lieA n Ω p.2.1.1 p.2.1.2 p.1) (lieB n Ω p.2.1.1 p.2.1.2 p.1)
        (lieC n Ω p.2.1.1 p.2.1.2 p.1) (lieD n Ω p.2.1.1 p.2.1.2 p.1) t).re := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  unfold term
  rw [spatialTwist_eq, character_re]
  simp only
  rw [plaquette_pert n Ω t x μ ν h]
  rcases twistExp_cases n μ ν x with hc | hc
  · simp [hc]
  · simp [hc]

theorem plane_sum (g : Fin 4 → Fin 4 → ℝ) :
    ∑ d : Plane, g d.1.1 d.1.2 = ∑ μ, ∑ ν, if μ < ν then g μ ν else 0 := by
  have h : ∑ d ∈ Finset.univ.filter (fun d : Fin 4 × Fin 4 => d.1 < d.2), g d.1 d.2 =
      ∑ d : Plane, g d.1.1 d.1.2 := Finset.sum_subtype _ (by simp) _
  rw [← h, Finset.sum_filter, Fintype.sum_prod_type]

/-- **The quadratic form is the Hessian.** The second derivative at `t = 0` of the actual
twisted action along `exp (t ξ) · flatLink` equals `β` times `hessianForm`. -/
theorem second_derivative (β : ℝ) (Ω : Fin 3 → Fin 4 → Section (2 * n)) :
    deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (pertConfig n Ω t)) 0 =
      β * hessianForm Ω := by
  choose g₁ g₂ h₁ h₂ h₀ using fun p : PlaquetteIndex (2 * n) =>
    re_G_jet (lieA n Ω p.2.1.1 p.2.1.2 p.1) (lieB n Ω p.2.1.1 p.2.1.2 p.1)
      (lieC n Ω p.2.1.1 p.2.1.2 p.1) (lieD n Ω p.2.1.1 p.2.1.2 p.1)
  have hF : ∀ t, HasDerivAt (fun t => action n Q (spatialTwist n) character β 2 (pertConfig n Ω t))
      (β * ∑ p, -(2 * g₁ p t)) t := by
    intro t
    unfold action
    simp only [term_pert]
    exact (HasDerivAt.fun_sum fun p _ => ((h₁ p t).const_mul 2).const_sub 2).const_mul β
  have hd : (deriv fun t => action n Q (spatialTwist n) character β 2 (pertConfig n Ω t)) =
      fun t => β * ∑ p, -(2 * g₁ p t) := funext fun t => (hF t).deriv
  rw [hd]
  have h2 : HasDerivAt (fun t => β * ∑ p, -(2 * g₁ p t)) (β * ∑ p, -(2 * g₂ p 0)) 0 :=
    (HasDerivAt.fun_sum fun p _ => ((h₂ p 0).const_mul 2).neg).const_mul β
  rw [h2.deriv]
  congr 1
  have hval (p : PlaquetteIndex (2 * n)) : -(2 * g₂ p 0) =
      2 * ∑ a, (curl (shifts a) (Ω a) p.2.1.1 p.2.1.2 p.1) ^ 2 := by
    rw [h₀ p]
    have hl : lieA n Ω p.2.1.1 p.2.1.2 p.1 + lieB n Ω p.2.1.1 p.2.1.2 p.1 +
        lieC n Ω p.2.1.1 p.2.1.2 p.1 + lieD n Ω p.2.1.1 p.2.1.2 p.1 =
        ∑ a, (curl (shifts a) (Ω a) p.2.1.1 p.2.1.2 p.1) • basis a :=
      plaquetteLie_eq Ω _ _ _
    rw [hl, re_sq_basis]
    ring
  simp only [hval]
  unfold hessianForm curlEnergy
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hn (c : Section (2 * n)) : ‖c‖ ^ 2 = ∑ x, c x ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  rw [← plane_sum (fun μ ν => ‖curl (shifts a) (Ω a) μ ν‖ ^ 2), Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [hn]

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedActionJet
