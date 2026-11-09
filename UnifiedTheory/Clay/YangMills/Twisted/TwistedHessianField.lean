/- Lower bound on the second derivative of the actual twisted action at a general small-field
background, along exponentials in the tail frame. With every link within chord `r` of the flat field,
the second derivative is at least the flat curl energy minus `(3072 r² + 192 r)` times the norm.
On flat-divergence-free directions this is positive once `r ≲ 1/N²`. It is a pointwise statement about
the action along geodesics, not about the measure or about a coordinate chart. -/
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSmallField
import UnifiedTheory.Clay.YangMills.Twisted.TwistedLandau
import UnifiedTheory.Clay.YangMills.Twisted.TwistedTransfer
import UnifiedTheory.Clay.YangMills.Twisted.TwistedSeams
import UnifiedTheory.Clay.YangMills.Twisted.TwistedNearFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField
noncomputable section
open PeriodicLattice4 TwistedFlat CommutingShifts TwistedHessian TwistedActionJet TwistedSmallField
open TwistedStability TwistedLandau TwistedLocalization TwistedReflection
open PeriodicPlaquetteReflection PeriodicTimeReflection RegulatedGauge
open TwistedNearFlat
open WilsonSingleLinkStaples (Q character character_re)
open scoped Quaternion

/-- The full second-order coefficient of a four-exponential product. -/
def secondCoeff (A B C D : ℍ[ℝ]) : ℍ[ℝ] :=
  A * A + A * B + (A * B + B * B) + (A + B) * (C + D) +
    ((A + B) * (C + D) + (C * C + C * D + (C * D + D * D)))

/-- `Re (G(t) · c)` has a second derivative at zero equal to `Re (secondCoeff · c)`. -/
theorem re_G_mul_jet (A B C D c : ℍ[ℝ]) :
    ∃ g₁ g₂ : ℝ → ℝ, (∀ t, HasDerivAt (fun s => (G A B C D s * c).re) (g₁ t) t) ∧
      (∀ t, HasDerivAt g₁ (g₂ t) t) ∧ g₂ 0 = (secondCoeff A B C D * c).re := by
  have hj := ((Jet.exp A).mul (Jet.exp B)).mul ((Jet.exp C).mul (Jet.exp D))
  have hjc : Jet (fun t => G A B C D t * c) _ _ :=
    { d1 := fun t => (hj.d1 t).mul_const c
      d2 := fun t => (hj.d2 t).mul_const c }
  refine ⟨_, _, hjc.re.1, hjc.re.2, ?_⟩
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, secondCoeff]

/-- For imaginary entries, the real part of the coefficient is minus the squared norm of the sum. -/
theorem secondCoeff_re (A B C D : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0)
    (hD : D.re = 0) : (secondCoeff A B C D).re = -‖A + B + C + D‖ ^ 2 := by
  have hZ : (A + B + C + D).re = 0 := by
    simp [hA, hB, hC, hD]
  have e : (secondCoeff A B C D).re = ((A + B + C + D) * (A + B + C + D)).re := by
    simp only [secondCoeff, add_mul, mul_add, Quaternion.re_add]
    rw [re_comm B A, re_comm C A, re_comm D A, re_comm C B, re_comm D B, re_comm D C]
    ring
  rw [e, sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def', Quaternion.re_mul]
  generalize A + B + C + D = Z at hZ
  rw [hZ]
  ring

theorem secondCoeff_norm (A B C D : ℍ[ℝ]) :
    ‖secondCoeff A B C D‖ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 := by
  have hm (x y : ℍ[ℝ]) : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  have hab : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _
  have hcd : ‖C + D‖ ≤ ‖C‖ + ‖D‖ := norm_add_le _ _
  have hcross : ‖A + B‖ * ‖C + D‖ ≤ (‖A‖ + ‖B‖) * (‖C‖ + ‖D‖) :=
    mul_le_mul hab hcd (norm_nonneg _) (by positivity)
  unfold secondCoeff
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_add_le (A * A + A * B + (A * B + B * B)) ((A + B) * (C + D))
  have h2 := norm_add_le (A * A + A * B) (A * B + B * B)
  have h3 := norm_add_le (A * A) (A * B)
  have h4 := norm_add_le (A * B) (B * B)
  have h5 := norm_add_le ((A + B) * (C + D)) (C * C + C * D + (C * D + D * D))
  have h6 := norm_add_le (C * C + C * D) (C * D + D * D)
  have h7 := norm_add_le (C * C) (C * D)
  have h8 := norm_add_le (C * D) (D * D)
  simp only [hm] at h1 h2 h3 h4 h5 h6 h7 h8
  have e : (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 = ‖A‖ * ‖A‖ + ‖A‖ * ‖B‖ + (‖A‖ * ‖B‖ + ‖B‖ * ‖B‖) +
      (‖A‖ + ‖B‖) * (‖C‖ + ‖D‖) + ((‖A‖ + ‖B‖) * (‖C‖ + ‖D‖) +
        (‖C‖ * ‖C‖ + ‖C‖ * ‖D‖ + (‖C‖ * ‖D‖ + ‖D‖ * ‖D‖))) := by ring
  rw [e]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, hcross]

/-! ### Conjugation estimates -/

theorem norm_conj_sub (g h : Q) (X : ℍ[ℝ]) :
    ‖(g : ℍ[ℝ]) * X * ((g⁻¹ : Q) : ℍ[ℝ]) - (h : ℍ[ℝ]) * X * ((h⁻¹ : Q) : ℍ[ℝ])‖ ≤ 2 * d g h * ‖X‖ := by
  have hsp : (g : ℍ[ℝ]) * X * ((g⁻¹ : Q) : ℍ[ℝ]) - (h : ℍ[ℝ]) * X * ((h⁻¹ : Q) : ℍ[ℝ]) =
      ((g : ℍ[ℝ]) - h) * X * ((g⁻¹ : Q) : ℍ[ℝ]) +
        (h : ℍ[ℝ]) * X * (((g⁻¹ : Q) : ℍ[ℝ]) - ((h⁻¹ : Q) : ℍ[ℝ])) := by
    noncomm_ring
  have hinv : ‖((g⁻¹ : Q) : ℍ[ℝ]) - ((h⁻¹ : Q) : ℍ[ℝ])‖ = d g h := by
    have := TwistedLocalization.d_inv g h
    exact this
  rw [hsp]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hinv, TwistedStability.norm_coe, TwistedStability.norm_coe,
    mul_one, one_mul]
  have : ‖(g : ℍ[ℝ]) - h‖ = d g h := rfl
  rw [this]
  linarith only [le_refl (d g h * ‖X‖)]

theorem conj_re (g : Q) (X : ℍ[ℝ]) (hX : X.re = 0) :
    ((g : ℍ[ℝ]) * X * ((g⁻¹ : Q) : ℍ[ℝ])).re = 0 := by
  have : ((g⁻¹ : Q) : ℍ[ℝ]) * (g : ℍ[ℝ]) = 1 := congrArg Subtype.val (inv_mul_cancel g)
  rw [mul_assoc, TwistedActionJet.re_comm, mul_assoc, this, mul_one, hX]

theorem conj_norm (g : Q) (X : ℍ[ℝ]) : ‖(g : ℍ[ℝ]) * X * ((g⁻¹ : Q) : ℍ[ℝ])‖ = ‖X‖ := norm_conj g X

/-- Conjugation by a center element times `h` is conjugation by `h`. -/
theorem conj_center (k : ℕ) (h : Q) (X : ℍ[ℝ]) :
    ((ω ^ k * h : Q) : ℍ[ℝ]) * X * (((ω ^ k * h)⁻¹ : Q) : ℍ[ℝ]) =
      (h : ℍ[ℝ]) * X * ((h⁻¹ : Q) : ℍ[ℝ]) := by
  rcases (Nat.even_or_odd k) with he | ho
  · have : (ω : Q) ^ k = 1 := by
      obtain ⟨m, rfl⟩ := he
      rw [← two_mul, pow_mul, sq, TwistedTransfer.ω_mul_ω, one_pow]
    rw [this, one_mul]
  · have : (ω : Q) ^ k = ω := by
      obtain ⟨m, rfl⟩ := ho
      rw [pow_succ, pow_mul, sq, TwistedTransfer.ω_mul_ω, one_pow, one_mul]
    rw [this, TwistedTransfer.inv_ω_mul]
    change (-1 : ℍ[ℝ]) * (h : ℍ[ℝ]) * X * ((-1 : ℍ[ℝ]) * ((h⁻¹ : Q) : ℍ[ℝ])) = _
    simp

/-! ### The second derivative at a general background -/

variable (n : ℕ) [NeZero n]

local notation "V'" => Vertex (2 * n)

/-- The configuration `exp(t X) · U`. -/
def pertField (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) :
    V' → Fin 4 → Q :=
  fun x μ => expQ (t • imag X μ x) (smul_skew _ (imag_star X μ x) t) * U x μ

/-- The four frame-transported rotations of a plaquette, and its value. -/
structure Plaq where
  P : Q
  Y₁ : ℍ[ℝ]
  Y₂ : ℍ[ℝ]
  Y₃ : ℍ[ℝ]
  Y₄ : ℍ[ℝ]

/-- The plaquette data of a field along a perturbation. -/
def plaqOf (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : Plaq :=
  let a := U x μ
  let b := U (step (2 * n) x μ) ν
  let c := U (step (2 * n) x ν) μ
  let e := U x ν
  { P := a * b * c⁻¹ * e⁻¹
    Y₁ := imag X μ x
    Y₂ := (a : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((a⁻¹ : Q) : ℍ[ℝ])
    Y₃ := -(((a * b * c⁻¹ : Q) : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) *
      (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ]))
    Y₄ := -(((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * imag X ν x *
      (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ])) }

theorem product_identity' (E₁ E₂ E₃ E₄ a b c e : Q) :
    (E₁ * a) * (E₂ * b) * (E₃ * c)⁻¹ * (E₄ * e)⁻¹ =
      (E₁ * (a * E₂ * a⁻¹)) * (((a * b * c⁻¹) * E₃⁻¹ * (a * b * c⁻¹)⁻¹) *
        ((a * b * c⁻¹ * e⁻¹) * E₄⁻¹ * (a * b * c⁻¹ * e⁻¹)⁻¹)) * (a * b * c⁻¹ * e⁻¹) := by
  group

theorem coe_four (E A B C W : Q) :
    (((E * A) * (B * C) * W : Q) : ℍ[ℝ]) =
      (E : ℍ[ℝ]) * (A : ℍ[ℝ]) * ((B : ℍ[ℝ]) * (C : ℍ[ℝ])) * (W : ℍ[ℝ]) := rfl

/-- The abstract form of the plaquette expansion. -/
theorem coe_product (X₁ X₂ X₃ X₄ : ℍ[ℝ]) (t : ℝ) (h₁ : star (t • X₁) = -(t • X₁))
    (h₂ : star (t • X₂) = -(t • X₂)) (h₃ : star (t • X₃) = -(t • X₃))
    (h₄ : star (t • X₄) = -(t • X₄)) (a b c e : Q) :
    (((expQ _ h₁ * a) * (expQ _ h₂ * b) * (expQ _ h₃ * c)⁻¹ * (expQ _ h₄ * e)⁻¹ : Q) : ℍ[ℝ]) =
      G X₁ ((a : ℍ[ℝ]) * X₂ * ((a⁻¹ : Q) : ℍ[ℝ]))
        (-(((a * b * c⁻¹ : Q) : ℍ[ℝ]) * X₃ * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ])))
        (-(((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * X₄ * (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ]))) t *
      ((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) := by
  rw [product_identity', coe_four, conj_expQ a X₂ t h₂, conj_expQ_inv (a * b * c⁻¹) X₃ t h₃,
    conj_expQ_inv (a * b * c⁻¹ * e⁻¹) X₄ t h₄]
  rfl

theorem three (a b c a' b' c' : Q) :
    d (a * b * c⁻¹) (a' * b' * c'⁻¹) ≤ d a a' + d b b' + d c c' := by
  have s1 : d (a * b * c⁻¹) (a' * b * c⁻¹) = d a a' := by
    rw [mul_assoc, mul_assoc, d_mul_right]
  have s2 : d (a' * b * c⁻¹) (a' * b' * c⁻¹) = d b b' := by
    rw [mul_assoc, mul_assoc, d_mul_left, d_mul_right]
  have s3 : d (a' * b' * c⁻¹) (a' * b' * c'⁻¹) = d c c' := by
    rw [d_mul_left, TwistedLocalization.d_inv]
  have t1 := d_triangle (a * b * c⁻¹) (a' * b * c⁻¹) (a' * b' * c'⁻¹)
  have t2 := d_triangle (a' * b * c⁻¹) (a' * b' * c⁻¹) (a' * b' * c'⁻¹)
  linarith only [t1, t2, s1, s2, s3]

/-- The perturbed configuration. -/
abbrev cfg (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) :
    Configuration V' Q := ofLink (pertField n U X t)

/-- The plaquette data, spelled out as a term. -/
theorem term_cfg (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ) (x : V')
    (μ ν : Fin 4) (h : μ < ν) :
    term n Q (spatialTwist n) character 2 (cfg n U X t) (x, ⟨(μ, ν), h⟩) =
      2 - 2 * (G (plaqOf n U X x μ ν).Y₁ (plaqOf n U X x μ ν).Y₂ (plaqOf n U X x μ ν).Y₃
        (plaqOf n U X x μ ν).Y₄ t * ((if twistExp μ ν x = 1 then (-1 : ℝ) else 1) •
          ((plaqOf n U X x μ ν).P : ℍ[ℝ]))).re := by
  unfold term
  rw [spatialTwist_eq, character_re]
  have hl : linkValue (2 * n) Q (cfg n U X t) = pertField n U X t := rfl
  change 2 - _ * (2 * ((plaquetteProduct (2 * n) Q (cfg n U X t) x μ ν : Q) : ℍ[ℝ]).re) = _
  unfold plaquetteProduct
  rw [hl]
  unfold pertField
  rw [coe_product]
  rw [mul_smul_comm, Quaternion.re_smul]
  simp only [smul_eq_mul]
  dsimp only [plaqOf]
  ring

theorem Y_re (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    (plaqOf n U X x μ ν).Y₁.re = 0 ∧ (plaqOf n U X x μ ν).Y₂.re = 0 ∧
      (plaqOf n U X x μ ν).Y₃.re = 0 ∧ (plaqOf n U X x μ ν).Y₄.re = 0 := by
  refine ⟨imag_re _ _ _, conj_re _ _ (imag_re _ _ _), ?_, ?_⟩
  · change (-_ : ℍ[ℝ]).re = 0
    rw [Quaternion.re_neg, conj_re _ _ (imag_re _ _ _), neg_zero]
  · change (-_ : ℍ[ℝ]).re = 0
    rw [Quaternion.re_neg, conj_re _ _ (imag_re _ _ _), neg_zero]

/-- The sum of link norms of a plaquette. -/
def linkSum (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ‖imag X μ x‖ + ‖imag X ν (step (2 * n) x μ)‖ + ‖imag X μ (step (2 * n) x ν)‖ + ‖imag X ν x‖

/-- Comparison of the plaquette Lie element with the flat one. -/
theorem lie_compare (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ x μ, d (U x μ) (flatLink x μ) ≤ r) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    ‖(plaqOf n U X x μ ν).Y₁ + (plaqOf n U X x μ ν).Y₂ + (plaqOf n U X x μ ν).Y₃ +
        (plaqOf n U X x μ ν).Y₄ - plaquetteLie X μ ν x‖ ≤ 8 * r * linkSum n X x μ ν := by
  set a := U x μ
  set b := U (step (2 * n) x μ) ν
  set c := U (step (2 * n) x ν) μ
  set e := U x ν
  set Fa := flatLink x μ
  set Fb := flatLink (step (2 * n) x μ) ν
  set Fc := flatLink (step (2 * n) x ν) μ
  set Fe := flatLink x ν
  have hflat : Fa * Fb * Fc⁻¹ * Fe⁻¹ = ω ^ twistExp μ ν x := flatLink_flat (N := 2 * n) x μ ν h
  have hflat3 : Fa * Fb * Fc⁻¹ = ω ^ twistExp μ ν x * Fe := by
    rw [← hflat]
    group
  have ha := hr x μ
  have hb := hr (step (2 * n) x μ) ν
  have hc := hr (step (2 * n) x ν) μ
  have he := hr x ν
  have d3 : d (a * b * c⁻¹) (ω ^ twistExp μ ν x * Fe) ≤ 3 * r := by
    rw [← hflat3]
    have := three a b c Fa Fb Fc
    linarith only [this, ha, hb, hc]
  have d4 : d (a * b * c⁻¹ * e⁻¹) (ω ^ twistExp μ ν x * 1) ≤ 4 * r := by
    rw [mul_one, ← hflat]
    have := TwistedSeams.four a b c e Fa Fb Fc Fe
    linarith only [this, ha, hb, hc, he]
  have n2 := norm_conj_sub a Fa (imag X ν (step (2 * n) x μ))
  have n3 := norm_conj_sub (a * b * c⁻¹) (ω ^ twistExp μ ν x * Fe) (imag X μ (step (2 * n) x ν))
  have n4 := norm_conj_sub (a * b * c⁻¹ * e⁻¹) (ω ^ twistExp μ ν x * 1) (imag X ν x)
  rw [conj_center] at n3 n4
  have hone : ((1 : Q) : ℍ[ℝ]) * imag X ν x * (((1 : Q)⁻¹ : Q) : ℍ[ℝ]) = imag X ν x := by
    change (1 : ℍ[ℝ]) * imag X ν x * ((star (1 : Q) : Q) : ℍ[ℝ]) = _
    simp
  rw [hone] at n4
  have hdiff : (plaqOf n U X x μ ν).Y₁ + (plaqOf n U X x μ ν).Y₂ + (plaqOf n U X x μ ν).Y₃ +
      (plaqOf n U X x μ ν).Y₄ - plaquetteLie X μ ν x =
      ((a : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((a⁻¹ : Q) : ℍ[ℝ]) -
          (Fa : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((Fa⁻¹ : Q) : ℍ[ℝ])) -
        (((a * b * c⁻¹ : Q) : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ]) -
          (Fe : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * ((Fe⁻¹ : Q) : ℍ[ℝ])) -
        (((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * imag X ν x * (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ]) -
          imag X ν x) := by
    have y1 : (plaqOf n U X x μ ν).Y₁ = imag X μ x := rfl
    have y2 : (plaqOf n U X x μ ν).Y₂ =
        (a : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((a⁻¹ : Q) : ℍ[ℝ]) := rfl
    have y3 : (plaqOf n U X x μ ν).Y₃ = -(((a * b * c⁻¹ : Q) : ℍ[ℝ]) *
        imag X μ (step (2 * n) x ν) * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ])) := rfl
    have y4 : (plaqOf n U X x μ ν).Y₄ = -(((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * imag X ν x *
        (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ])) := rfl
    have lie : plaquetteLie X μ ν x = imag X μ x +
        (Fa : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((Fa⁻¹ : Q) : ℍ[ℝ]) +
        -((Fe : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * ((Fe⁻¹ : Q) : ℍ[ℝ])) + -imag X ν x := rfl
    rw [y1, y2, y3, y4, lie]
    abel
  rw [hdiff]
  have nn2 := norm_nonneg (imag X ν (step (2 * n) x μ))
  have nn3 := norm_nonneg (imag X μ (step (2 * n) x ν))
  have nn4 := norm_nonneg (imag X ν x)
  have nn1 := norm_nonneg (imag X μ x)
  have b2 : 2 * d a Fa * ‖imag X ν (step (2 * n) x μ)‖ ≤ 2 * r * ‖imag X ν (step (2 * n) x μ)‖ := by
    exact mul_le_mul_of_nonneg_right (by linarith only [ha]) nn2
  have b3 : 2 * d (a * b * c⁻¹) (ω ^ twistExp μ ν x * Fe) * ‖imag X μ (step (2 * n) x ν)‖ ≤
      2 * (3 * r) * ‖imag X μ (step (2 * n) x ν)‖ :=
    mul_le_mul_of_nonneg_right (by linarith only [d3]) nn3
  have b4 : 2 * d (a * b * c⁻¹ * e⁻¹) (ω ^ twistExp μ ν x * 1) * ‖imag X ν x‖ ≤
      2 * (4 * r) * ‖imag X ν x‖ :=
    mul_le_mul_of_nonneg_right (by linarith only [d4]) nn4
  have t1 := norm_sub_le
    (((a : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((a⁻¹ : Q) : ℍ[ℝ]) -
        (Fa : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((Fa⁻¹ : Q) : ℍ[ℝ])) -
      (((a * b * c⁻¹ : Q) : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ]) -
        (Fe : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * ((Fe⁻¹ : Q) : ℍ[ℝ])))
    (((a * b * c⁻¹ * e⁻¹ : Q) : ℍ[ℝ]) * imag X ν x * (((a * b * c⁻¹ * e⁻¹)⁻¹ : Q) : ℍ[ℝ]) - imag X ν x)
  have t2 := norm_sub_le
    ((a : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((a⁻¹ : Q) : ℍ[ℝ]) -
        (Fa : ℍ[ℝ]) * imag X ν (step (2 * n) x μ) * ((Fa⁻¹ : Q) : ℍ[ℝ]))
    (((a * b * c⁻¹ : Q) : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * (((a * b * c⁻¹)⁻¹ : Q) : ℍ[ℝ]) -
        (Fe : ℍ[ℝ]) * imag X μ (step (2 * n) x ν) * ((Fe⁻¹ : Q) : ℍ[ℝ]))
  unfold linkSum
  have hrp2 := mul_nonneg hr0 nn2
  have hrp3 := mul_nonneg hr0 nn3
  have hrp1 := mul_nonneg hr0 nn1
  nlinarith only [t1, t2, n2, n3, n4, b2, b3, b4, hrp1, hrp2, hrp3]

theorem re_abs_le (x : ℍ[ℝ]) : |x.re| ≤ ‖x‖ := by
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg x)
  rw [sq ‖x‖, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  nlinarith only [sq_nonneg x.imI, sq_nonneg x.imJ, sq_nonneg x.imK]

/-- The abstract form of the plaquette lower bound. -/
theorem second_lower (A B C D c L : ℍ[ℝ]) (hA : A.re = 0) (hB : B.re = 0) (hC : C.re = 0)
    (hD : D.re = 0) (δ ρ : ℝ) (hρ : 0 ≤ ρ) (hc : ‖c - 1‖ ≤ δ) (hZ : ‖A + B + C + D - L‖ ≤ ρ) :
    ‖L‖ ^ 2 - 2 * ρ ^ 2 - 2 * δ * (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 ≤
      -(2 * (secondCoeff A B C D * c).re) := by
  have e : secondCoeff A B C D * c = secondCoeff A B C D + secondCoeff A B C D * (c - 1) := by
    noncomm_ring
  rw [e, Quaternion.re_add, secondCoeff_re A B C D hA hB hC hD]
  have h1 := (abs_le.1 (re_abs_le (secondCoeff A B C D * (c - 1)))).2
  have h2 : ‖secondCoeff A B C D * (c - 1)‖ ≤ (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) ^ 2 * δ := by
    rw [norm_mul]
    exact mul_le_mul (secondCoeff_norm A B C D) hc (norm_nonneg _) (sq_nonneg _)
  have h3 : ‖L‖ ≤ ‖A + B + C + D‖ + ρ := by
    have := norm_sub_le (A + B + C + D) (A + B + C + D - L)
    rw [sub_sub_cancel] at this
    linarith only [this, hZ]
  have h4 : ‖L‖ ^ 2 ≤ (‖A + B + C + D‖ + ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg L) h3 2
  have h5 := sq_nonneg (‖A + B + C + D‖ - ρ)
  nlinarith only [h1, h2, h4, h5]

/-- The plaquette value, with the twist sign removed. -/
def plaqC (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℍ[ℝ] :=
  (if twistExp μ ν x = 1 then (-1 : ℝ) else 1) • ((plaqOf n U X x μ ν).P : ℍ[ℝ])

theorem plaqC_close (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ)
    (hr : ∀ x μ, d (U x μ) (flatLink x μ) ≤ r) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    ‖plaqC n U X x μ ν - 1‖ ≤ 4 * r := by
  have hflat := flatLink_flat (N := 2 * n) x μ ν h
  have hd : d (plaqOf n U X x μ ν).P (ω ^ twistExp μ ν x) ≤ 4 * r := by
    rw [← hflat]
    have := TwistedSeams.four (U x μ) (U (step (2 * n) x μ) ν) (U (step (2 * n) x ν) μ) (U x ν)
      (flatLink x μ) (flatLink (step (2 * n) x μ) ν) (flatLink (step (2 * n) x ν) μ) (flatLink x ν)
    have ha := hr x μ
    have hb := hr (step (2 * n) x μ) ν
    have hc := hr (step (2 * n) x ν) μ
    have he := hr x ν
    exact this.trans (by linarith only [ha, hb, hc, he])
  unfold plaqC
  rcases twistExp_cases n μ ν x with hc | hc
  · rw [hc, pow_zero] at hd
    rw [hc]
    simp only [zero_ne_one, if_false, one_smul]
    exact hd
  · rw [hc, pow_one] at hd
    rw [hc]
    simp only [if_true, neg_smul, one_smul]
    have e : -(((plaqOf n U X x μ ν).P : Q) : ℍ[ℝ]) - 1 =
        -(((plaqOf n U X x μ ν).P : ℍ[ℝ]) - (-1 : ℍ[ℝ])) := by noncomm_ring
    rw [e, norm_neg]
    exact hd

theorem plaq_norms (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    ‖(plaqOf n U X x μ ν).Y₁‖ + ‖(plaqOf n U X x μ ν).Y₂‖ + ‖(plaqOf n U X x μ ν).Y₃‖ +
      ‖(plaqOf n U X x μ ν).Y₄‖ = linkSum n X x μ ν := by
  dsimp only [plaqOf, linkSum]
  rw [norm_neg, norm_neg, conj_norm, conj_norm, conj_norm]

/-- The link norms squared of a plaquette. -/
def linkSq (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) : ℝ :=
  ‖imag X μ x‖ ^ 2 + ‖imag X ν (step (2 * n) x μ)‖ ^ 2 + ‖imag X μ (step (2 * n) x ν)‖ ^ 2 +
    ‖imag X ν x‖ ^ 2

theorem linkSum_sq (X : Fin 3 → Fin 4 → Section (2 * n)) (x : V') (μ ν : Fin 4) :
    linkSum n X x μ ν ^ 2 ≤ 4 * linkSq n X x μ ν := by
  unfold linkSum linkSq
  generalize ‖imag X μ x‖ = a
  generalize ‖imag X ν (step (2 * n) x μ)‖ = b
  generalize ‖imag X μ (step (2 * n) x ν)‖ = c
  generalize ‖imag X ν x‖ = e
  nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - e), sq_nonneg (b - c),
    sq_nonneg (b - e), sq_nonneg (c - e)]

/-- The lower bound on one plaquette's second derivative. -/
theorem plaq_bound (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ x μ, d (U x μ) (flatLink x μ) ≤ r) (x : V') (μ ν : Fin 4) (h : μ < ν) :
    ‖plaquetteLie X μ ν x‖ ^ 2 - (512 * r ^ 2 + 32 * r) * linkSq n X x μ ν ≤
      -(2 * (secondCoeff (plaqOf n U X x μ ν).Y₁ (plaqOf n U X x μ ν).Y₂ (plaqOf n U X x μ ν).Y₃
        (plaqOf n U X x μ ν).Y₄ * plaqC n U X x μ ν).re) := by
  obtain ⟨h1, h2, h3, h4⟩ := Y_re n U X x μ ν
  have hT0 : 0 ≤ linkSum n X x μ ν := by
    unfold linkSum
    positivity
  have key := second_lower _ _ _ _ (plaqC n U X x μ ν) (plaquetteLie X μ ν x) h1 h2 h3 h4 (4 * r)
    (8 * r * linkSum n X x μ ν) (by positivity) (plaqC_close n U X r hr x μ ν h)
    (lie_compare n U X r hr0 hr x μ ν h)
  rw [plaq_norms] at key
  have hS := linkSum_sq n X x μ ν
  have hcoef : 0 ≤ 128 * r ^ 2 + 8 * r := by positivity
  have hm := mul_le_mul_of_nonneg_left hS hcoef
  refine le_trans ?_ key
  nlinarith only [hm]

/-- The plaquette expansion, indexed by plaquettes. -/
theorem term_index (U : V' → Fin 4 → Q) (X : Fin 3 → Fin 4 → Section (2 * n)) (t : ℝ)
    (p : PlaquetteIndex (2 * n)) :
    term n Q (spatialTwist n) character 2 (cfg n U X t) p =
      2 - 2 * (G (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₂
        (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₄ t *
          plaqC n U X p.1 p.2.1.1 p.2.1.2).re := by
  rcases p with ⟨x, ⟨⟨μ, ν⟩, h⟩⟩
  exact term_cfg n U X t x μ ν h

/-- The exact second derivative of the action along `exp (t X) · U`. -/
theorem second_derivative_field (β : ℝ) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) :
    deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 =
      β * ∑ p : PlaquetteIndex (2 * n), -(2 * (secondCoeff (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₁
        (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₂ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₃
        (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₄ * plaqC n U X p.1 p.2.1.1 p.2.1.2).re) := by
  choose g₁ g₂ h₁ h₂ h₀ using fun p : PlaquetteIndex (2 * n) =>
    re_G_mul_jet (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₁ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₂
      (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₃ (plaqOf n U X p.1 p.2.1.1 p.2.1.2).Y₄
      (plaqC n U X p.1 p.2.1.1 p.2.1.2)
  have hF : ∀ t, HasDerivAt (fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t))
      (β * ∑ p, -(2 * g₁ p t)) t := by
    intro t
    unfold action
    simp only [term_index]
    exact (HasDerivAt.fun_sum fun p _ => ((h₁ p t).const_mul 2).const_sub 2).const_mul β
  have hd : (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) =
      fun t => β * ∑ p, -(2 * g₁ p t) := funext fun t => (hF t).deriv
  rw [hd]
  have h2 : HasDerivAt (fun t => β * ∑ p, -(2 * g₁ p t)) (β * ∑ p, -(2 * g₂ p 0)) 0 :=
    (HasDerivAt.fun_sum fun p _ => ((h₂ p 0).const_mul 2).neg).const_mul β
  rw [h2.deriv]
  simp only [h₀]

/-- **The Hessian at a small-field background.** With every link within chord `r` of the flat field,
the second derivative is at least `β` times the flat curl energy minus an error in the norm. -/
theorem hessian_field_lower (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (r : ℝ) (hr0 : 0 ≤ r)
    (hr : ∀ x μ, d (U x μ) (flatLink x μ) ≤ r) :
    β * (∑ a, curlEnergy (shifts a) (X a) - (3072 * r ^ 2 + 192 * r) * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 := by
  rw [second_derivative_field]
  refine mul_le_mul_of_nonneg_left ?_ hβ
  have hsum := Finset.sum_le_sum fun (p : PlaquetteIndex (2 * n)) (_ : p ∈ Finset.univ) =>
    plaq_bound n U X r hr0 hr p.1 p.2.1.1 p.2.1.2 p.2.2
  refine le_trans (le_of_eq ?_) hsum
  rw [Finset.sum_sub_distrib, lie_sum, ← Finset.mul_sum]
  have hl : ∑ p : PlaquetteIndex (2 * n), linkSq n X p.1 p.2.1.1 p.2.1.2 =
      6 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2 := link_count n X
  rw [hl]
  ring

/-- **Coercivity at a small-field background.** Along flat-divergence-free directions, with links
within `1/(100 N²)` of the flat field, the action is uniformly convex along the geodesic at `t = 0`. -/
theorem hessian_field_coercive (β : ℝ) (hβ : 0 ≤ β) (U : V' → Fin 4 → Q)
    (X : Fin 3 → Fin 4 → Section (2 * n)) (hdiv : ∀ a, div (shifts a) (X a) = 0) (r : ℝ) (hr0 : 0 ≤ r)
    (hrN : r ≤ 1 / (100 * ((2 * n : ℕ) : ℝ) ^ 2))
    (hr : ∀ x μ, d (U x μ) (flatLink x μ) ≤ r) :
    β * (2 / ((2 * n : ℕ) : ℝ) ^ 2 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
      deriv (deriv fun t => action n Q (spatialTwist n) character β 2 (cfg n U X t)) 0 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hβ) (hessian_field_lower n β hβ U X r hr0 hr)
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hN2 : (4 : ℝ) ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hn]
  set y : ℝ := 1 / ((2 * n : ℕ) : ℝ) ^ 2 with hy
  have hy0 : 0 < y := by positivity
  have hy4 : y ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hN2
  have hry : r ≤ y / 100 := by
    refine hrN.trans (le_of_eq ?_)
    rw [hy]
    field_simp
  have hW : 0 ≤ ∑ a : Fin 3, ∑ μ : Fin 4, ‖X a μ‖ ^ 2 := by positivity
  have hcol : 4 * y * ∑ a : Fin 3, ∑ μ : Fin 4, ‖X a μ‖ ^ 2 ≤
      ∑ a, curlEnergy (shifts a) (X a) := by
    have hl := lam_lower (2 * n)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have hc := colour_bound a (X a)
    rw [hdiv a, norm_zero] at hc
    have hq : 4 * y ≤ lam (2 * n) := by
      refine le_trans (le_of_eq ?_) hl
      rw [hy]
      ring
    have hS : 0 ≤ ∑ μ : Fin 4, ‖X a μ‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hq hS
    nlinarith only [this, hc]
  have hquad : 3072 * r ^ 2 + 192 * r ≤ 2 * y := by
    have h1 : r ^ 2 ≤ (y / 100) ^ 2 := pow_le_pow_left₀ hr0 hry 2
    nlinarith only [h1, hry, hy0, hy4, mul_nonneg hy0.le (sub_nonneg.2 hy4)]
  have hm := mul_le_mul_of_nonneg_right hquad hW
  have e : 2 / ((2 * n : ℕ) : ℝ) ^ 2 = 2 * y := by
    rw [hy]
    ring
  rw [e]
  nlinarith only [hm, hcol]

/-- A small squared distance bounds each link. -/
theorem link_le_of_distSq (U : V' → Fin 4 → Q) (r : ℝ) (hr0 : 0 ≤ r) (hD : D U ≤ r ^ 2) (x : V')
    (μ : Fin 4) : d (U x μ) (flatLink x μ) ≤ r := by
  refine abs_le_of_sq_le_sq' ?_ hr0 |>.2
  refine le_trans ?_ hD
  have h1 : d (U x μ) (flatLink x μ) ^ 2 ≤ ∑ y, d (U y μ) (flatLink y μ) ^ 2 :=
    Finset.single_le_sum (f := fun y => d (U y μ) (flatLink y μ) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
  have h2 : ∑ y, d (U y μ) (flatLink y μ) ^ 2 ≤ ∑ ν, ∑ y, d (U y ν) (flatLink y ν) ^ 2 :=
    Finset.single_le_sum (f := fun ν => ∑ y, d (U y ν) (flatLink y ν) ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  exact h1.trans h2

/-- **The small-action region is convex in the gauge-orthogonal directions.** Below the threshold of
`near_flat`, some gauge transform and center shift of the field has a coercive second derivative along
every flat-divergence-free geodesic. The threshold forces coupling polynomial in `N`. -/
theorem near_flat_coercive (β : ℝ) (hβ : 0 ≤ β) (L : V' → Fin 4 → Q)
    (hS : actionL L ≤ (1 / (1408 * ((2 * n : ℕ) : ℝ) ^ 5)) ^ 2) :
    ∃ (c₃ c₀ : Q) (g : V' → Q), (c₃ = 1 ∨ c₃ = ω) ∧ (c₀ = 1 ∨ c₀ = ω) ∧
      ∀ X : Fin 3 → Fin 4 → Section (2 * n), (∀ a, div (shifts a) (X a) = 0) →
        β * (2 / ((2 * n : ℕ) : ℝ) ^ 2 * ∑ a, ∑ μ, ‖X a μ‖ ^ 2) ≤
          deriv (deriv fun t => action n Q (spatialTwist n) character β 2
            (cfg n (act g (shift c₃ c₀ L)) X t)) 0 := by
  obtain ⟨c₃, c₀, g, h₃, h₀, hD⟩ := near_flat n L hS
  refine ⟨c₃, c₀, g, h₃, h₀, fun X hdiv => ?_⟩
  set N : ℝ := ((2 * n : ℕ) : ℝ) with hNd
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hN : (1 : ℝ) ≤ N := by
    rw [hNd]
    push_cast
    linarith only [hn]
  have hNpos : 0 < N := by linarith only [hN]
  have hr0 : (0 : ℝ) ≤ 1 / (100 * N ^ 2) := by positivity
  have hthr : N ^ 2 * (1 / (1408 * N ^ 5)) ^ 2 ≤ (1 / (100 * N ^ 2)) ^ 2 := by
    have e1 : N ^ 2 * (1 / (1408 * N ^ 5)) ^ 2 = 1 / (1408 ^ 2 * N ^ 8) := by
      field_simp
    have e2 : (1 / (100 * N ^ 2)) ^ 2 = 1 / (100 ^ 2 * N ^ 4) := by
      field_simp
    rw [e1, e2]
    apply one_div_le_one_div_of_le (by positivity)
    have h4 : (1 : ℝ) ≤ N ^ 4 := one_le_pow₀ hN
    have h8 : N ^ 4 ≤ N ^ 8 := pow_le_pow_right₀ hN (by norm_num)
    have hp : 0 < N ^ 4 := by positivity
    norm_num
    nlinarith only [h8, hp]
  have hD' : D (act g (shift c₃ c₀ L)) ≤ (1 / (100 * N ^ 2)) ^ 2 :=
    hD.trans ((mul_le_mul_of_nonneg_left hS (by positivity)).trans hthr)
  exact hessian_field_coercive n β hβ _ X hdiv _ hr0 le_rfl
    (fun x μ => link_le_of_distSq n _ _ hr0 hD' x μ)

end
end UnifiedTheory.Clay.YangMills.Twisted.TwistedHessianField
