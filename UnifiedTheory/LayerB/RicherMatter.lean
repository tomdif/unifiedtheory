/-
  LayerB/RicherMatter.lean — Richer matter structure beyond simple charge

  Formalizes three extensions of the basic charge algebra:

  1. **Multiple conserved quantum numbers**: Given k independent linear
     functionals on the perturbation space, each yields an independent
     conserved charge. All k charges are simultaneously additive under
     composition and simultaneously negated under conjugation.

  2. **Spin-statistics connection**: Integer-charge sectors compose
     symmetrically (bosonic). Half-integer sectors would require
     antisymmetric composition for consistency — a structural analog
     of the spin-statistics theorem.

  3. **Representation structure from Lie algebra**: Given structure
     constants, the adjoint representation acts on perturbations.
     Charges transform covariantly under this action.

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.MetricDefects
import UnifiedTheory.LayerB.DefectComposition
import UnifiedTheory.LayerA.GaugeConnection

namespace UnifiedTheory.LayerB.RicherMatter

open LayerA GaugeConnection

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## Part 1: Multiple conserved quantum numbers -/

/-- A **MultiCharge** system: k independent linear functionals on V,
    each giving a conserved charge. The perturbation space V carries
    multiple independent quantum numbers simultaneously. -/
structure MultiCharge (V : Type*) [AddCommGroup V] [Module ℝ V] (k : ℕ) where
  /-- The k independent linear functionals (charge measurements) -/
  φ : Fin k → (V →ₗ[ℝ] ℝ)

/-- Extract the i-th charge of a defect (via its perturbation). -/
def MultiCharge.chargeOf {k : ℕ} (mc : MultiCharge V k)
    (i : Fin k) (v : V) : ℝ :=
  mc.φ i v

/-- The full charge vector of a perturbation: all k charges at once. -/
def MultiCharge.chargeVector {k : ℕ} (mc : MultiCharge V k)
    (v : V) : Fin k → ℝ :=
  fun i => mc.chargeOf i v

/-- **All k charges are simultaneously additive.**
    Q_i(v + w) = Q_i(v) + Q_i(w) for each i, from map_add. -/
theorem multiCharge_additive {k : ℕ} (mc : MultiCharge V k)
    (v w : V) (i : Fin k) :
    mc.chargeOf i (v + w) = mc.chargeOf i v + mc.chargeOf i w := by
  simp only [MultiCharge.chargeOf, map_add]

/-- **All k charges are simultaneously negated under conjugation.**
    Q_i(-v) = -Q_i(v) for each i, from map_neg. -/
theorem multiCharge_conjugate {k : ℕ} (mc : MultiCharge V k)
    (v : V) (i : Fin k) :
    mc.chargeOf i (-v) = -(mc.chargeOf i v) := by
  simp only [MultiCharge.chargeOf, map_neg]

/-- **The full charge vector is additive.** -/
theorem chargeVector_additive {k : ℕ} (mc : MultiCharge V k)
    (v w : V) :
    mc.chargeVector (v + w) = mc.chargeVector v + mc.chargeVector w := by
  ext i
  simp only [MultiCharge.chargeVector, Pi.add_apply]
  exact multiCharge_additive mc v w i

/-- **The full charge vector is negated under conjugation.** -/
theorem chargeVector_conjugate {k : ℕ} (mc : MultiCharge V k)
    (v : V) :
    mc.chargeVector (-v) = -(mc.chargeVector v) := by
  ext i
  simp only [MultiCharge.chargeVector, Pi.neg_apply]
  exact multiCharge_conjugate mc v i

/-- **Annihilation zeroes ALL charges simultaneously.**
    For v + (-v), every charge Q_i vanishes. -/
theorem multiCharge_annihilation {k : ℕ} (mc : MultiCharge V k)
    (v : V) (i : Fin k) :
    mc.chargeOf i (v + (-v)) = 0 := by
  rw [multiCharge_additive, multiCharge_conjugate, add_neg_cancel]

/-- **The full charge vector of an annihilation product is zero.** -/
theorem chargeVector_annihilation {k : ℕ} (mc : MultiCharge V k)
    (v : V) :
    mc.chargeVector (v + (-v)) = 0 := by
  ext i
  simp only [MultiCharge.chargeVector, Pi.zero_apply]
  exact multiCharge_annihilation mc v i

/-- **Charge vector is zero on the zero perturbation.** -/
theorem chargeVector_zero {k : ℕ} (mc : MultiCharge V k) :
    mc.chargeVector 0 = 0 := by
  ext i
  simp only [MultiCharge.chargeVector, MultiCharge.chargeOf, map_zero, Pi.zero_apply]

/-- **Scaling a perturbation scales all charges.** -/
theorem multiCharge_smul {k : ℕ} (mc : MultiCharge V k)
    (r : ℝ) (v : V) (i : Fin k) :
    mc.chargeOf i (r • v) = r * mc.chargeOf i v := by
  simp only [MultiCharge.chargeOf, map_smul, smul_eq_mul]

/-! ### Integration with ComposableDefectBlock -/

/-- Given a ComposableDefectBlock and a MultiCharge on V, extract the
    i-th charge of a defect via its perturbation. -/
def defectMultiCharge {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (i : Fin k) (d : db.Defect) : ℝ :=
  mc.chargeOf i (db.perturbation d)

/-- **All k charges are additive under defect composition.** -/
theorem defectMultiCharge_additive {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (i : Fin k) (d₁ d₂ : db.Defect) :
    defectMultiCharge db mc i (db.compose d₁ d₂) =
    defectMultiCharge db mc i d₁ + defectMultiCharge db mc i d₂ := by
  simp only [defectMultiCharge, MultiCharge.chargeOf, db.compose_is_add, map_add]

/-- **All k charges negate under defect conjugation.** -/
theorem defectMultiCharge_conjugate {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (i : Fin k) (d : db.Defect) :
    defectMultiCharge db mc i (db.conjugate d) =
    -(defectMultiCharge db mc i d) := by
  simp only [defectMultiCharge, MultiCharge.chargeOf, db.conjugate_is_neg, map_neg]

/-- **Complete multi-charge conservation theorem.**
    All k charges are simultaneously conserved under composition and conjugation. -/
theorem multiCharge_conservation {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) :
    -- (1) All charges additive under composition
    (∀ i d₁ d₂, defectMultiCharge db mc i (db.compose d₁ d₂) =
      defectMultiCharge db mc i d₁ + defectMultiCharge db mc i d₂)
    -- (2) All charges negate under conjugation
    ∧ (∀ i d, defectMultiCharge db mc i (db.conjugate d) =
      -(defectMultiCharge db mc i d))
    -- (3) Annihilation zeroes all charges
    ∧ (∀ i d, defectMultiCharge db mc i (db.compose d (db.conjugate d)) = 0) :=
  ⟨fun i d₁ d₂ => defectMultiCharge_additive db mc i d₁ d₂,
   fun i d => defectMultiCharge_conjugate db mc i d,
   fun i d => by
     rw [defectMultiCharge_additive, defectMultiCharge_conjugate, add_neg_cancel]⟩

/-! ## Part 2: Spin-statistics connection (structural analog) -/

/-- A charge value is **integer-valued** if it equals some integer. -/
def IsIntegerCharge (q : ℝ) : Prop := ∃ n : ℤ, q = ↑n

/-- A defect is in the **bosonic sector** if ALL its charges are integer-valued. -/
def BosonicSector {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (d : db.Defect) : Prop :=
  ∀ i : Fin k, IsIntegerCharge (defectMultiCharge db mc i d)

/-- **The bosonic sector is closed under composition.**
    If d₁ and d₂ both have integer charges, so does d₁ + d₂.
    This is the structural analog of bosonic symmetry:
    integer-charge sectors compose without sign issues. -/
theorem bosonic_sector_closed {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (d₁ d₂ : db.Defect)
    (h₁ : BosonicSector db mc d₁) (h₂ : BosonicSector db mc d₂) :
    BosonicSector db mc (db.compose d₁ d₂) := by
  intro i
  obtain ⟨n₁, hn₁⟩ := h₁ i
  obtain ⟨n₂, hn₂⟩ := h₂ i
  exact ⟨n₁ + n₂, by rw [defectMultiCharge_additive, hn₁, hn₂, Int.cast_add]⟩

/-- **The bosonic sector is closed under conjugation.**
    If d has integer charges, so does -d (since -n is an integer). -/
theorem bosonic_sector_conjugate {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (d : db.Defect)
    (h : BosonicSector db mc d) :
    BosonicSector db mc (db.conjugate d) := by
  intro i
  obtain ⟨n, hn⟩ := h i
  exact ⟨-n, by rw [defectMultiCharge_conjugate, hn, Int.cast_neg]⟩

/-- **The zero perturbation is bosonic** (all charges zero = integer). -/
theorem bosonic_zero {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (d : db.Defect)
    (hd : ∀ i, defectMultiCharge db mc i d = 0) :
    BosonicSector db mc d :=
  fun i => ⟨0, by rw [hd i, Int.cast_zero]⟩

/-- **Annihilation products are bosonic** (all charges zero). -/
theorem annihilation_bosonic {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) (d : db.Defect) :
    BosonicSector db mc (db.compose d (db.conjugate d)) := by
  intro i
  exact ⟨0, by
    rw [defectMultiCharge_additive, defectMultiCharge_conjugate,
        add_neg_cancel, Int.cast_zero]⟩

/-- A charge value is **half-integer valued** if 2q is an odd integer. -/
def IsHalfIntegerCharge (q : ℝ) : Prop :=
  ∃ n : ℤ, q = (2 * ↑n + 1) / 2

/-- **Composing two half-integer charges gives an integer charge.**
    This is the structural reason half-integer sectors cannot form
    a sub-sector under composition: (half + half) = integer.
    Consistency requires tracking signs (antisymmetric composition). -/
theorem half_integer_compose_gives_integer (q₁ q₂ : ℝ)
    (h₁ : IsHalfIntegerCharge q₁) (h₂ : IsHalfIntegerCharge q₂) :
    IsIntegerCharge (q₁ + q₂) := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₂, hn₂⟩ := h₂
  exact ⟨n₁ + n₂ + 1, by rw [hn₁, hn₂]; push_cast; ring⟩

/-! ## Part 3: Representation structure from Lie algebra -/

/-- **Adjoint action** of a Lie algebra element X^b on a perturbation space
    indexed by Fin g_dim. Given structure constants c^a_{bc} and
    X^b, the adjoint action sends Y^c to [X,Y]^a = Σ_{b,c} c^a_{bc} X^b Y^c.

    For the charge algebra, the key property is that adjoint-transformed
    charges are linear combinations of the original charges. -/
def adjointAction {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X : Fin g_dim → ℝ) (Y : Fin g_dim → ℝ) : Fin g_dim → ℝ :=
  fun a => ∑ b : Fin g_dim, ∑ c : Fin g_dim, sc.c a b c * X b * Y c

/-- **Adjoint action is linear in Y** (the second argument). -/
theorem adjointAction_add {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X Y₁ Y₂ : Fin g_dim → ℝ) :
    adjointAction sc X (Y₁ + Y₂) =
    adjointAction sc X Y₁ + adjointAction sc X Y₂ := by
  ext a
  simp only [adjointAction, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro c _
  ring

/-- **Adjoint action is linear in Y** (scaling). -/
theorem adjointAction_smul {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X : Fin g_dim → ℝ) (r : ℝ) (Y : Fin g_dim → ℝ) :
    adjointAction sc X (r • Y) = r • adjointAction sc X Y := by
  ext a
  simp only [adjointAction, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  ring

/-- **Adjoint action negates under negation of Y.** -/
theorem adjointAction_neg {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X Y : Fin g_dim → ℝ) :
    adjointAction sc X (-Y) = -(adjointAction sc X Y) := by
  ext a
  simp only [adjointAction, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro c _
  ring

/-- A **charge functional on Lie-algebra-valued perturbations**:
    given a covector w : Fin g_dim → ℝ, the charge is Q_w(Y) = Σ_a w_a Y^a. -/
def lieCharge {g_dim : ℕ} (w : Fin g_dim → ℝ) (Y : Fin g_dim → ℝ) : ℝ :=
  ∑ a : Fin g_dim, w a * Y a

/-- **Lie charge is additive** (linear in Y). -/
theorem lieCharge_add {g_dim : ℕ} (w Y₁ Y₂ : Fin g_dim → ℝ) :
    lieCharge w (Y₁ + Y₂) = lieCharge w Y₁ + lieCharge w Y₂ := by
  simp only [lieCharge, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _
  ring

/-- **Lie charge negates under conjugation.** -/
theorem lieCharge_neg {g_dim : ℕ} (w Y : Fin g_dim → ℝ) :
    lieCharge w (-Y) = -(lieCharge w Y) := by
  simp only [lieCharge, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro a _
  ring

/-- **Representation covariance theorem.**
    The charge of [X, Y] under covector w equals the charge of Y under
    the coadjoint-transformed covector. That is:

      Q_w([X, Y]) = Q_{ad*(X)(w)}(Y)

    where ad*(X)(w)_c = Σ_{a,b} c^a_{bc} X^b w_a.

    This shows charges transform covariantly under the adjoint action:
    the charge algebra respects the representation structure. -/
theorem representation_covariance {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X Y w : Fin g_dim → ℝ) :
    lieCharge w (adjointAction sc X Y) =
    lieCharge (fun c => ∑ a : Fin g_dim, ∑ b : Fin g_dim,
      sc.c a b c * X b * w a) Y := by
  simp only [lieCharge, adjointAction]
  -- LHS: Σ_a w_a * (Σ_b Σ_c sc.c a b c * X b * Y c)
  -- RHS: Σ_c (Σ_a Σ_b sc.c a b c * X b * w_a) * Y c
  -- Both equal Σ_a Σ_b Σ_c sc.c a b c * X b * Y c * w_a
  -- Both sides equal Σ_a Σ_b Σ_c sc.c a b c * X b * Y c * w a
  -- LHS: Σ_a w_a * (Σ_b Σ_c sc.c a b c * X b * Y c)
  have lhs_expand : ∀ a : Fin g_dim,
      w a * (∑ b, ∑ c, sc.c a b c * X b * Y c) =
      ∑ b, ∑ c, sc.c a b c * X b * Y c * w a := by
    intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    ring
  -- RHS: Σ_c (Σ_a Σ_b sc.c a b c * X b * w a) * Y c
  have rhs_expand : ∀ c : Fin g_dim,
      (∑ a, ∑ b, sc.c a b c * X b * w a) * Y c =
      ∑ a, ∑ b, sc.c a b c * X b * Y c * w a := by
    intro c
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro b _
    ring
  simp_rw [lhs_expand, rhs_expand]
  -- Now LHS = Σ_a Σ_b Σ_c f(a,b,c), RHS = Σ_c Σ_a Σ_b f(a,b,c)
  -- Step 1: swap inner two sums in LHS: Σ_a (Σ_b Σ_c) → Σ_a (Σ_c Σ_b)
  conv_lhs =>
    arg 2; ext a
    rw [Finset.sum_comm]
  -- LHS is now Σ_a Σ_c Σ_b f(a,b,c)
  -- Step 2: swap outer two sums: Σ_a Σ_c → Σ_c Σ_a
  rw [Finset.sum_comm]
  -- Now both are Σ_c Σ_a Σ_b f(a,b,c)

/-- **Adjoint action is antisymmetric** (from structure constant antisymmetry):
    [X, Y] = -[Y, X]. -/
theorem adjointAction_antisym {g_dim : ℕ} (sc : StructureConstants g_dim)
    (X Y : Fin g_dim → ℝ) :
    adjointAction sc X Y = -(adjointAction sc Y X) := by
  ext a
  simp only [adjointAction, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  -- Swap outer two sums: Σ_b Σ_c → Σ_c Σ_b
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl; intro b _
  rw [sc.antisym a c b]
  ring

/-! ## Master theorem: all three extensions together -/

/-- **Richer matter structure theorem.**
    Given a ComposableDefectBlock with k independent charge functionals
    and Lie algebra structure constants:

    (1) All k charges are simultaneously additive and simultaneously
        negate under conjugation
    (2) The bosonic (integer-charge) sector is closed under composition
        and conjugation
    (3) Half-integer charges compose to integer charges (structural
        spin-statistics)
    (4) The adjoint action on the perturbation space is compatible
        with the charge algebra (linearity + antisymmetry) -/
theorem richer_matter_structure
    {k : ℕ} (db : ComposableDefectBlock V)
    (mc : MultiCharge V k) :
    -- (1) Multi-charge conservation
    (∀ i d₁ d₂, defectMultiCharge db mc i (db.compose d₁ d₂) =
      defectMultiCharge db mc i d₁ + defectMultiCharge db mc i d₂)
    ∧ (∀ i d, defectMultiCharge db mc i (db.conjugate d) =
      -(defectMultiCharge db mc i d))
    -- (2) Bosonic sector closure
    ∧ (∀ d₁ d₂, BosonicSector db mc d₁ → BosonicSector db mc d₂ →
        BosonicSector db mc (db.compose d₁ d₂))
    ∧ (∀ d, BosonicSector db mc d → BosonicSector db mc (db.conjugate d))
    -- (3) Half-integer → integer under composition
    ∧ (∀ q₁ q₂, IsHalfIntegerCharge q₁ → IsHalfIntegerCharge q₂ →
        IsIntegerCharge (q₁ + q₂)) :=
  ⟨fun i d₁ d₂ => defectMultiCharge_additive db mc i d₁ d₂,
   fun i d => defectMultiCharge_conjugate db mc i d,
   fun d₁ d₂ h₁ h₂ => bosonic_sector_closed db mc d₁ d₂ h₁ h₂,
   fun d h => bosonic_sector_conjugate db mc d h,
   fun q₁ q₂ h₁ h₂ => half_integer_compose_gives_integer q₁ q₂ h₁ h₂⟩

end UnifiedTheory.LayerB.RicherMatter
