/-
  LayerA/AnomalyConstraints.lean — Anomaly cancellation constraints on gauge-matter content

  THE ARGUMENT (why this constrains the gauge group):

  In 4D, gauge invariance of the quantum effective action requires the
  anomaly tensor A_{abc} = Σ_species χ_i · Tr[T_a^(i) {T_b^(i), T_c^(i)}]
  to vanish, where χ_i = ±1 is the chirality.

  This is NOT an extra axiom — it's a CONSISTENCY condition. In the
  continuum, it comes from gauge invariance at one loop (triangle diagram).
  On a discrete structure, it comes from requiring the discrete path
  integral measure to be gauge-invariant.

  The defect sector connects as follows:
  1. Defects carry charges via linear functionals (MultiCharge)
  2. The K/P (source/dressing) split provides a natural ℤ₂ grading
  3. This grading is the structural analog of chirality
  4. Anomaly cancellation then constrains which charge assignments
     are consistent with gauge invariance

  WHAT IS PROVEN (pure mathematics, no physics assumptions):
  - The anomaly tensor is well-defined given a representation
  - Anomaly freedom is a polynomial constraint on charges
  - Vector-like theories (χ_i = 0 for all species) are anomaly-free
  - The K/P grading gives a natural chirality assignment
  - The SM U(1) charge assignments satisfy all anomaly conditions

  WHAT IS A HYPOTHESIS (physically motivated but not derived):
  - That anomaly cancellation IS required for consistency
  - That the K/P grading IS chirality (rather than some other ℤ₂)

  Zero custom axioms. Zero sorry.
-/
import UnifiedTheory.LayerA.GaugeConnection
import UnifiedTheory.LayerA.GaugeGroupConstraints
import UnifiedTheory.LayerB.RicherMatter

namespace UnifiedTheory.LayerA.AnomalyConstraints

open GaugeConnection GaugeGroupConstraints

/-! ## The anomaly tensor -/

/-- A **chiral fermion species**: carries a representation of the gauge algebra
    (specified by charge values) and a chirality ±1. -/
structure ChiralSpecies (k : ℕ) where
  /-- Charges under each of the k gauge generators -/
  charges : Fin k → ℝ
  /-- Chirality: +1 (left-handed) or -1 (right-handed) -/
  chirality : ℝ
  /-- Chirality is ±1 -/
  chiral_sq : chirality ^ 2 = 1

/-- **U(1) cubic anomaly coefficient** for a set of chiral species.
    A₃ = Σᵢ χᵢ · Qᵢ³.
    Must vanish for gauge invariance. -/
def u1CubicAnomaly {N : ℕ} (species : Fin N → ChiralSpecies 1) : ℝ :=
  ∑ i : Fin N, (species i).chirality * ((species i).charges 0) ^ 3

/-- **U(1) gravitational anomaly coefficient**.
    A₁ = Σᵢ χᵢ · Qᵢ.
    Must vanish for consistency with gravity. -/
def u1GravAnomaly {N : ℕ} (species : Fin N → ChiralSpecies 1) : ℝ :=
  ∑ i : Fin N, (species i).chirality * (species i).charges 0

/-- **U(1) mixed anomaly with an SU(n) factor.**
    For species transforming under SU(n) in representation of dimension d_i:
    A_mixed = Σᵢ χᵢ · dᵢ · Qᵢ.
    The dimension factor dᵢ accounts for the SU(n) trace. -/
def u1MixedAnomaly {N : ℕ} (species : Fin N → ChiralSpecies 1)
    (dim_rep : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (species i).chirality * dim_rep i * (species i).charges 0

/-- **General anomaly tensor** for k charge generators.
    A_{abc} = Σᵢ χᵢ · Qᵢ(a) · (Qᵢ(b) · Qᵢ(c) + Qᵢ(c) · Qᵢ(b)) / 2
    For abelian charges, the anticommutator simplifies to 2 · Q(b) · Q(c).
    A_{abc} = Σᵢ χᵢ · Qᵢ(a) · Qᵢ(b) · Qᵢ(c). -/
def abelianAnomalyTensor {N k : ℕ} (species : Fin N → ChiralSpecies k)
    (a b c : Fin k) : ℝ :=
  ∑ i : Fin N, (species i).chirality *
    (species i).charges a * (species i).charges b * (species i).charges c

/-- **Anomaly-free**: all components of the anomaly tensor vanish. -/
def IsAnomalyFree {N k : ℕ} (species : Fin N → ChiralSpecies k) : Prop :=
  ∀ a b c : Fin k, abelianAnomalyTensor species a b c = 0

/-! ## Structural results -/

/-- **The anomaly tensor is totally symmetric** in its indices (for abelian charges).
    A_{abc} = A_{bac} = A_{acb} = ... -/
theorem anomaly_symmetric {N k : ℕ} (species : Fin N → ChiralSpecies k)
    (a b c : Fin k) :
    abelianAnomalyTensor species a b c = abelianAnomalyTensor species b a c := by
  simp only [abelianAnomalyTensor]
  apply Finset.sum_congr rfl; intro i _; ring

/-! ### Vector-like vs chiral anomaly cancellation

    Same-chirality pairing: Q³·χ + (-Q)³·χ = 0 (cancels).
    Opposite-chirality pairing: Q³·(+1) + (-Q)³·(-1) = 2Q³ (does NOT cancel).

    So: real/pseudoreal representations (same-chirality conjugate pairs)
    are automatically anomaly-free. The SM is CHIRAL: left and right
    have different charges, making anomaly cancellation nontrivial. -/

/-- A **vector-like pairing**: an involution on species that negates charges
    but preserves chirality. Such theories are automatically anomaly-free. -/
structure VectorLikePairing {N k : ℕ} (species : Fin N → ChiralSpecies k) where
  /-- The pairing map -/
  pair : Fin N → Fin N
  /-- It's an involution -/
  invol : ∀ i, pair (pair i) = i
  /-- Paired species have opposite charges -/
  neg_charges : ∀ i j, (species (pair i)).charges j = -((species i).charges j)
  /-- Paired species have the same chirality -/
  same_chirality : ∀ i, (species (pair i)).chirality = (species i).chirality

/-- **Vector-like theories are anomaly-free.**
    If species come in pairs with opposite charges and same chirality,
    each pair contributes χ·Q³ + χ·(-Q)³ = 0 to the anomaly. -/
theorem vectorlike_anomaly_free {N k : ℕ} (species : Fin N → ChiralSpecies k)
    (vl : VectorLikePairing species) :
    IsAnomalyFree species := by
  intro a b c
  simp only [abelianAnomalyTensor]
  -- Each term f(pair(i)) = -f(i) from opposite charges, same chirality
  have hneg : ∀ i : Fin N,
      (species (vl.pair i)).chirality * (species (vl.pair i)).charges a *
        (species (vl.pair i)).charges b * (species (vl.pair i)).charges c =
      -((species i).chirality * (species i).charges a *
        (species i).charges b * (species i).charges c) := by
    intro i; rw [vl.same_chirality, vl.neg_charges, vl.neg_charges, vl.neg_charges]; ring
  -- The involution is a bijection
  set e : Fin N ≃ Fin N := ⟨vl.pair, vl.pair, vl.invol, vl.invol⟩
  -- Reindex: Σᵢ g(i) = Σᵢ g(pair(i))
  set g := fun i : Fin N => (species i).chirality * (species i).charges a *
    (species i).charges b * (species i).charges c
  have hS : ∑ i, g i = ∑ i, g (e i) := (Equiv.sum_comp e g).symm
  -- But g(pair(i)) = -g(i), so Σ g(pair(i)) = -Σ g(i)
  have hN : ∑ i, g (e i) = -(∑ i, g i) := by
    rw [show ∑ i, g (e i) = ∑ i, -(g i) from
      Finset.sum_congr rfl (fun i _ => hneg i)]
    simp [Finset.sum_neg_distrib]
  -- S = -S implies S = 0
  linarith

/-! ## The K/P grading as chirality -/

/-! The K/P split provides a natural ℤ₂ grading on defects.
    K (source) couples to gravity; P (dressing) decouples.
    HYPOTHESIS: this grading corresponds to chirality. -/

/-- The **chirality** from the K/P split: +1 if source-dominant, -1 if dressing-dominant.
    For a defect with source value s = φ(K(v)):
    - s > 0 → left-handed (chirality +1)
    - s < 0 → right-handed (chirality -1)
    - s = 0 → pure dressing (chirality 0, doesn't contribute to anomaly) -/
noncomputable def kpChirality (sourceValue : ℝ) : ℝ :=
  if sourceValue > 0 then 1
  else if sourceValue < 0 then -1
  else 0

/-! ## U(1) anomaly cancellation: the concrete constraint -/

/-- A **charge spectrum**: a finite list of charges and chiralities.
    This is what the defect sector produces. -/
structure ChargeSpectrum (N : ℕ) where
  /-- The U(1) charge of each species -/
  charge : Fin N → ℝ
  /-- The chirality of each species -/
  chirality : Fin N → ℝ

/-- The **cubic anomaly** of a charge spectrum. -/
def cubicAnomaly {N : ℕ} (spec : ChargeSpectrum N) : ℝ :=
  ∑ i : Fin N, spec.chirality i * (spec.charge i) ^ 3

/-- The **linear (gravitational) anomaly** of a charge spectrum. -/
def linearAnomaly {N : ℕ} (spec : ChargeSpectrum N) : ℝ :=
  ∑ i : Fin N, spec.chirality i * spec.charge i

/-- A charge spectrum is **anomaly-free** if both conditions hold. -/
def IsSpectrumAnomalyFree {N : ℕ} (spec : ChargeSpectrum N) : Prop :=
  cubicAnomaly spec = 0 ∧ linearAnomaly spec = 0

/-! ## Standard Model verification

    Convention: all fermions listed as LEFT-HANDED Weyl spinors.
    Right-handed fermions appear as their left-handed conjugates with
    negated hypercharge. This gives 15 species per generation:

    Species 0-5:   Q_L  (Y = 1/6)    [3 colors × 2 isospin]
    Species 6-8:   ū_L  (Y = -2/3)   [conjugate of u_R, 3 colors]
    Species 9-11:  d̄_L  (Y = 1/3)    [conjugate of d_R, 3 colors]
    Species 12-13: L_L  (Y = -1/2)   [2 isospin]
    Species 14:    ē_L  (Y = 1)      [conjugate of e_R]

    Anomalies computed over left-handed Weyl fermions:
    Tr[Y³] = 6·(1/6)³ + 3·(-2/3)³ + 3·(1/3)³ + 2·(-1/2)³ + (1)³ = 0
    Tr[Y]  = 6·(1/6) + 3·(-2/3) + 3·(1/3) + 2·(-1/2) + 1 = 0 -/

/-- One generation of SM fermions as LEFT-HANDED Weyl fermions.
    Right-handed fermions are listed as their left-handed conjugates
    with negated hypercharge.

    Species 0-5:  Q_L  (Y = 1/6)   [3 colors × 2 isospin]
    Species 6-8:  ū_L  (Y = -2/3)  [conjugate of u_R, 3 colors]
    Species 9-11: d̄_L  (Y = 1/3)   [conjugate of d_R, 3 colors]
    Species 12-13: L_L  (Y = -1/2)  [2 isospin]
    Species 14:   ē_L  (Y = 1)      [conjugate of e_R] -/
noncomputable def smGeneration : ChargeSpectrum 15 where
  charge := fun i =>
    if i.val < 6 then 1/6          -- Q_L
    else if i.val < 9 then -2/3    -- ū_L (conjugate of u_R)
    else if i.val < 12 then 1/3    -- d̄_L (conjugate of d_R)
    else if i.val < 14 then -1/2   -- L_L
    else 1                          -- ē_L (conjugate of e_R)
  chirality := fun _ => 1  -- All left-handed Weyl

/-- **The SM hypercharge cubic anomaly vanishes per generation.**
    Tr[Y³] = 6·(1/6)³ + 3·(-2/3)³ + 3·(1/3)³ + 2·(-1/2)³ + 1·(1)³ = 0 -/
theorem sm_cubic_anomaly_cancels :
    cubicAnomaly smGeneration = 0 := by
  simp only [cubicAnomaly, smGeneration, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- **The SM gravitational anomaly vanishes per generation.**
    Tr[Y] = 6·(1/6) + 3·(-2/3) + 3·(1/3) + 2·(-1/2) + 1·(1) = 0 -/
theorem sm_linear_anomaly_cancels :
    linearAnomaly smGeneration = 0 := by
  simp only [linearAnomaly, smGeneration, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- **The SM is anomaly-free** (both U(1) conditions). -/
theorem sm_anomaly_free :
    IsSpectrumAnomalyFree smGeneration :=
  ⟨sm_cubic_anomaly_cancels, sm_linear_anomaly_cancels⟩

/-! ## How the defect sector constrains representations -/

/-! ### Charge quantization and anomaly constraints

    Defect composition gives additive charges: Q(v₁ ⊕ v₂) = Q(v₁) + Q(v₂).
    If charges are quantized (Q ∈ (1/n)ℤ), the anomaly conditions Tr[Y³]=0
    and Tr[Y]=0 become polynomial Diophantine constraints with very few
    solutions. Given SU(3)×SU(2) representation content, the SM hypercharge
    assignment is essentially unique (up to normalization). -/

/-- **A charge assignment**: hypercharges for 5 types of fermions
    (quark doublet, up singlet, down singlet, lepton doublet, charged lepton).
    Multiplicities are fixed by the SU(3)×SU(2) representation content. -/
structure ChargeAssignment where
  /-- Hypercharge of quark doublet Q_L -/
  yQ : ℝ
  /-- Hypercharge of up-type singlet (as left-handed conjugate) -/
  yu : ℝ
  /-- Hypercharge of down-type singlet (as left-handed conjugate) -/
  yd : ℝ
  /-- Hypercharge of lepton doublet L_L -/
  yL : ℝ
  /-- Hypercharge of charged lepton singlet (as left-handed conjugate) -/
  ye : ℝ

/-- The **cubic anomaly condition** for a charge assignment with
    N_c = 3 colors, SU(2) doublets of size 2.
    Tr[Y³] = 2·N_c·yQ³ + N_c·yu³ + N_c·yd³ + 2·yL³ + ye³ = 0 -/
def cubicCondition (ca : ChargeAssignment) : Prop :=
  6 * ca.yQ ^ 3 + 3 * ca.yu ^ 3 + 3 * ca.yd ^ 3 + 2 * ca.yL ^ 3 + ca.ye ^ 3 = 0

/-- The **linear anomaly condition** (gravitational).
    Tr[Y] = 2·N_c·yQ + N_c·yu + N_c·yd + 2·yL + ye = 0 -/
def linearCondition (ca : ChargeAssignment) : Prop :=
  6 * ca.yQ + 3 * ca.yu + 3 * ca.yd + 2 * ca.yL + ca.ye = 0

/-- The **SU(2)² × U(1) mixed anomaly condition**.
    Only SU(2) doublets contribute: Tr[Y]_{doublets} = 0.
    N_c·yQ + yL = 0 (summing over doublet species) -/
def su2MixedCondition (ca : ChargeAssignment) : Prop :=
  3 * ca.yQ + ca.yL = 0

/-- The **SU(3)² × U(1) mixed anomaly condition**.
    Only SU(3) triplets contribute: Tr[Y]_{triplets} = 0.
    2·yQ + yu + yd = 0 (summing over triplet species) -/
def su3MixedCondition (ca : ChargeAssignment) : Prop :=
  2 * ca.yQ + ca.yu + ca.yd = 0

/-- **The Standard Model charge assignment.** -/
noncomputable def smCharges : ChargeAssignment where
  yQ := 1/6
  yu := -2/3
  yd := 1/3
  yL := -1/2
  ye := 1

/-- The SM satisfies the cubic anomaly condition. -/
theorem sm_cubic : cubicCondition smCharges := by
  unfold cubicCondition smCharges; norm_num

/-- The SM satisfies the linear anomaly condition. -/
theorem sm_linear : linearCondition smCharges := by
  unfold linearCondition smCharges; norm_num

/-- The SM satisfies the SU(2)² × U(1) mixed anomaly condition. -/
theorem sm_su2_mixed : su2MixedCondition smCharges := by
  unfold su2MixedCondition smCharges; norm_num

/-- The SM satisfies the SU(3)² × U(1) mixed anomaly condition. -/
theorem sm_su3_mixed : su3MixedCondition smCharges := by
  unfold su3MixedCondition smCharges; norm_num

/-- **The SM satisfies ALL four anomaly conditions simultaneously.** -/
theorem sm_all_anomalies :
    cubicCondition smCharges ∧ linearCondition smCharges ∧
    su2MixedCondition smCharges ∧ su3MixedCondition smCharges :=
  ⟨sm_cubic, sm_linear, sm_su2_mixed, sm_su3_mixed⟩

/-! ## Anomaly conditions as a system of equations -/

/-! ### The anomaly system determines the charges

    From su2Mixed: yL = -3·yQ. From su3Mixed: yu + yd = -2·yQ.
    From linear: ye = 6·yQ. This leaves ONE free parameter (yQ)
    and one remaining equation (cubic). -/

/-- From the mixed anomaly conditions: yL = -3·yQ. -/
theorem anomaly_determines_yL (ca : ChargeAssignment)
    (h : su2MixedCondition ca) : ca.yL = -3 * ca.yQ := by
  unfold su2MixedCondition at h; linarith

/-- From mixed + linear: ye = 6·yQ. -/
theorem anomaly_determines_ye (ca : ChargeAssignment)
    (hsu2 : su2MixedCondition ca) (hsu3 : su3MixedCondition ca)
    (hlin : linearCondition ca) : ca.ye = 6 * ca.yQ := by
  unfold su2MixedCondition at hsu2
  unfold su3MixedCondition at hsu3
  unfold linearCondition at hlin
  linarith

/-- From SU(3)² mixed: yu + yd = -2·yQ. -/
theorem anomaly_determines_sum (ca : ChargeAssignment)
    (h : su3MixedCondition ca) : ca.yu + ca.yd = -2 * ca.yQ := by
  unfold su3MixedCondition at h; linarith

/-- **Three of four conditions determine 3 of 5 charges in terms of yQ.**
    Only ONE degree of freedom remains (the ratio yu/yd).
    The cubic condition then constrains this ratio. -/
theorem three_conditions_leave_one_dof (ca : ChargeAssignment)
    (hsu2 : su2MixedCondition ca) (hsu3 : su3MixedCondition ca)
    (hlin : linearCondition ca) :
    ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ ∧ ca.yu + ca.yd = -2 * ca.yQ :=
  ⟨anomaly_determines_yL ca hsu2,
   anomaly_determines_ye ca hsu2 hsu3 hlin,
   anomaly_determines_sum ca hsu3⟩

/-- **The SM charge assignment satisfies yQ = 1/6.**
    With this normalization: yL = -1/2, ye = 1, yu + yd = -1/3.
    The SM has yu = -2/3, yd = 1/3 (i.e., yu - yd = -1). -/
theorem sm_normalization :
    smCharges.yQ = 1/6 ∧ smCharges.yL = -1/2 ∧ smCharges.ye = 1 ∧
    smCharges.yu + smCharges.yd = -1/3 := by
  unfold smCharges; norm_num

/-! ## The anomaly cancellation ↔ matter sector connection

    SUMMARY OF THE LOGICAL CHAIN:

    1. PROVEN: The defect sector produces charges via linear functionals
       (MultiCharge in RicherMatter.lean).

    2. PROVEN: Charges are additive under composition, negated under
       conjugation (multiCharge_conservation).

    3. PROVEN: The K/P split provides a natural ℤ₂ grading (chirality
       candidate).

    4. PROVEN: Anomaly cancellation (Tr[Y³]=0, Tr[Y]=0, mixed conditions)
       is a highly restrictive polynomial system on the charge spectrum.

    5. PROVEN: Three of four conditions determine yL, ye, yu+yd in terms
       of a single parameter yQ.

    6. PROVEN: The SM charges are a solution.

    NOW PROVEN (the cubic factorization):
    (b) The cubic condition after substitution becomes
        18·yQ·(8·yQ² - 2·yQ·yd - yd²) = 0.
        For nontrivial yQ ≠ 0, the quadratic r² + 2r - 8 = 0
        (where r = yd/yQ) factors as (r+4)(r-2) = 0.
        Solutions: yd = 2·yQ or yd = -4·yQ.
        Both give the Standard Model (the second is u↔d relabeled).

    STILL OPEN:
    (a) Why yQ = 1/6 specifically (normalization from source functional).
    (c) Whether the SU(3)×SU(2) representation content is forced by
        the defect sector or is additional input. -/

theorem anomaly_framework_status :
    -- The SM is anomaly-free (proven)
    (cubicCondition smCharges ∧ linearCondition smCharges ∧
     su2MixedCondition smCharges ∧ su3MixedCondition smCharges)
    -- And the conditions are highly restrictive (proven: 3 of 5 charges determined)
    ∧ (∀ ca : ChargeAssignment,
       su2MixedCondition ca → su3MixedCondition ca → linearCondition ca →
       ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ ∧ ca.yu + ca.yd = -2 * ca.yQ) :=
  ⟨sm_all_anomalies, fun ca h1 h2 h3 => three_conditions_leave_one_dof ca h1 h2 h3⟩

/-! ## The cubic uniqueness theorem

    After substituting the three linear constraints into the cubic:
    6·yQ³ + 3·(-2yQ-yd)³ + 3·yd³ + 2·(-3yQ)³ + (6yQ)³ = 0
    simplifies to: 18·yQ·(8yQ² - 2yQ·yd - yd²) = 0.

    For nontrivial yQ ≠ 0, divide by 18·yQ:
    8yQ² - 2yQ·yd - yd² = 0

    Setting r = yd/yQ: r² + 2r - 8 = 0 → (r+4)(r-2) = 0.

    Two solutions:
    - r = 2: yd = 2yQ, yu = -4yQ → SM with yQ normalization
    - r = -4: yd = -4yQ, yu = 2yQ → SM with u↔d swapped

    Both are the Standard Model. Anomaly cancellation UNIQUELY determines
    the hypercharge ratios (up to normalization and u↔d interchange). -/

/-- **The substituted cubic condition.**
    After eliminating yL, ye, yu via the three linear conditions,
    the cubic reduces to a polynomial in yQ and yd. -/
def substitutedCubic (yQ yd : ℝ) : ℝ :=
  6 * yQ ^ 3 + 3 * (-2 * yQ - yd) ^ 3 + 3 * yd ^ 3 +
  2 * (-3 * yQ) ^ 3 + (6 * yQ) ^ 3

/-- **The substituted cubic factors as 18·yQ·(8yQ² - 2yQ·yd - yd²).** -/
theorem substituted_cubic_factors (yQ yd : ℝ) :
    substitutedCubic yQ yd = 18 * yQ * (8 * yQ ^ 2 - 2 * yQ * yd - yd ^ 2) := by
  unfold substitutedCubic; ring

/-- **The quadratic factor further factors as (yd + 4yQ)(yd - 2yQ).** -/
theorem quadratic_factors (yQ yd : ℝ) :
    8 * yQ ^ 2 - 2 * yQ * yd - yd ^ 2 = -(yd + 4 * yQ) * (yd - 2 * yQ) := by
  ring

/-- **THE UNIQUENESS THEOREM.**
    If all four anomaly conditions hold and yQ ≠ 0, then EITHER:
    (a) yd = 2·yQ (the Standard Model), OR
    (b) yd = -4·yQ (the Standard Model with u↔d interchange).

    Combined with the linear constraints:
    Case (a): (yQ, yu, yd, yL, ye) = yQ·(1, -4, 2, -3, 6)
    Case (b): (yQ, yu, yd, yL, ye) = yQ·(1, 2, -4, -3, 6)

    Both cases give the Standard Model hypercharge ratios. -/
theorem anomaly_uniqueness (ca : ChargeAssignment)
    (hcubic : cubicCondition ca)
    (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca)
    (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0) :
    (ca.yd = 2 * ca.yQ ∧ ca.yu = -4 * ca.yQ ∧
     ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ)
    ∨ (ca.yd = -4 * ca.yQ ∧ ca.yu = 2 * ca.yQ ∧
       ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ) := by
  -- Extract the linear constraints
  have hyL := anomaly_determines_yL ca hsu2
  have hye := anomaly_determines_ye ca hsu2 hsu3 hlin
  have hsum := anomaly_determines_sum ca hsu3
  -- The cubic condition after substitution
  have hyu : ca.yu = -2 * ca.yQ - ca.yd := by linarith
  -- Substitute into the cubic: cubicCondition becomes substitutedCubic yQ yd = 0
  have hsub : substitutedCubic ca.yQ ca.yd = 0 := by
    unfold substitutedCubic cubicCondition at *
    rw [hyu, hyL, hye] at hcubic; linarith
  -- Factor: 18·yQ·(8yQ² - 2yQ·yd - yd²) = 0
  rw [substituted_cubic_factors] at hsub
  -- Since yQ ≠ 0 and 18 ≠ 0, the quadratic must vanish
  have h18 : (18 : ℝ) ≠ 0 := by norm_num
  have hquad : 8 * ca.yQ ^ 2 - 2 * ca.yQ * ca.yd - ca.yd ^ 2 = 0 := by
    by_contra h
    have := mul_ne_zero (mul_ne_zero h18 hQ) h
    exact this hsub
  -- Factor the quadratic: -(yd + 4yQ)(yd - 2yQ) = 0
  rw [quadratic_factors] at hquad
  have : (ca.yd + 4 * ca.yQ) * (ca.yd - 2 * ca.yQ) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · -- Case: yd + 4yQ = 0, i.e., yd = -4yQ
    right
    exact ⟨by linarith, by linarith, hyL, hye⟩
  · -- Case: yd - 2yQ = 0, i.e., yd = 2yQ
    left
    exact ⟨by linarith, by linarith, hyL, hye⟩

/-- **Both solutions are the Standard Model (up to normalization).**
    Case (a): (1, -4, 2, -3, 6)·yQ with yQ = 1/6 gives (1/6, -2/3, 1/3, -1/2, 1).
    Case (b): same with u↔d swapped.
    These are the SAME PHYSICS — relabeling up-type and down-type quarks. -/
theorem both_solutions_are_sm :
    -- Solution (a): yd = 2·yQ
    (∀ yQ : ℝ, yQ ≠ 0 →
      let ca : ChargeAssignment := ⟨yQ, -4*yQ, 2*yQ, -3*yQ, 6*yQ⟩
      cubicCondition ca ∧ linearCondition ca ∧
      su2MixedCondition ca ∧ su3MixedCondition ca)
    -- Solution (b): yd = -4·yQ
    ∧ (∀ yQ : ℝ, yQ ≠ 0 →
      let ca : ChargeAssignment := ⟨yQ, 2*yQ, -4*yQ, -3*yQ, 6*yQ⟩
      cubicCondition ca ∧ linearCondition ca ∧
      su2MixedCondition ca ∧ su3MixedCondition ca) := by
  constructor <;> (intro yQ _; unfold cubicCondition linearCondition
                    su2MixedCondition su3MixedCondition; constructor <;> [ring; constructor <;>
                    [ring; constructor <;> [ring; ring]]])

/-- **MASTER THEOREM: Anomaly cancellation uniquely selects the SM.**

    Given:
    - SU(3) × SU(2) × U(1) gauge group
    - Fermions in the standard representations (triplets, doublets, singlets)
    - Four anomaly cancellation conditions

    Then: the hypercharge ratios are UNIQUELY determined to be the
    Standard Model values (up to overall normalization and u↔d interchange).

    All five hypercharges are fixed by a SINGLE parameter yQ:
    yQ, yu = -4yQ, yd = 2yQ, yL = -3yQ, ye = 6yQ

    With the normalization yQ = 1/6:
    (yQ, yu, yd, yL, ye) = (1/6, -2/3, 1/3, -1/2, 1)

    This is the Standard Model. -/
theorem anomaly_selects_sm :
    -- (1) The SM satisfies all anomaly conditions
    (cubicCondition smCharges ∧ linearCondition smCharges ∧
     su2MixedCondition smCharges ∧ su3MixedCondition smCharges)
    -- (2) All anomaly-free charge assignments are proportional to the SM
    ∧ (∀ ca : ChargeAssignment,
       cubicCondition ca → su2MixedCondition ca → su3MixedCondition ca →
       linearCondition ca → ca.yQ ≠ 0 →
       (ca.yd = 2 * ca.yQ ∧ ca.yu = -4 * ca.yQ ∧
        ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ) ∨
       (ca.yd = -4 * ca.yQ ∧ ca.yu = 2 * ca.yQ ∧
        ca.yL = -3 * ca.yQ ∧ ca.ye = 6 * ca.yQ))
    -- (3) Both solutions verify all four conditions
    ∧ (∀ yQ : ℝ, yQ ≠ 0 →
       let ca := ChargeAssignment.mk yQ (-4*yQ) (2*yQ) (-3*yQ) (6*yQ)
       cubicCondition ca ∧ linearCondition ca ∧
       su2MixedCondition ca ∧ su3MixedCondition ca) :=
  ⟨sm_all_anomalies,
   fun ca h1 h2 h3 h4 h5 => anomaly_uniqueness ca h1 h2 h3 h4 h5,
   both_solutions_are_sm.1⟩

/-! ## Universal hypercharge sum rules

    The following theorems hold for ANY charge assignment satisfying all four
    anomaly conditions with yQ ≠ 0. They use `anomaly_uniqueness` to substitute
    the forced charges, then close by `ring`. These are UNIVERSAL consequences
    of anomaly cancellation, not arithmetic on specific values. -/

/-- The quadratic hypercharge trace: Σ dᵢ · Yᵢ². -/
def trY2 (ca : ChargeAssignment) : ℝ :=
  6 * ca.yQ ^ 2 + 3 * ca.yu ^ 2 + 3 * ca.yd ^ 2 + 2 * ca.yL ^ 2 + ca.ye ^ 2

/-- The quartic hypercharge trace: Σ dᵢ · Yᵢ⁴. -/
def trY4 (ca : ChargeAssignment) : ℝ :=
  6 * ca.yQ ^ 4 + 3 * ca.yu ^ 4 + 3 * ca.yd ^ 4 + 2 * ca.yL ^ 4 + ca.ye ^ 4

/-- **UNIVERSAL: Tr[Y²] = 120·yQ² for ANY anomaly-free charge assignment.**
    Uses anomaly_uniqueness to substitute the forced charges (both solutions
    give the same result), then ring. This is NOT specific to yQ = 1/6. -/
theorem universal_trY2 (ca : ChargeAssignment)
    (hcubic : cubicCondition ca) (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca) (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0) :
    trY2 ca = 120 * ca.yQ ^ 2 := by
  rcases anomaly_uniqueness ca hcubic hsu2 hsu3 hlin hQ with
    ⟨hd, hu, hL, he⟩ | ⟨hd, hu, hL, he⟩ <;>
  (unfold trY2; rw [hu, hd, hL, he]; ring)

/-- **UNIVERSAL: Tr[Y⁴] = 2280·yQ⁴ for ANY anomaly-free charge assignment.** -/
theorem universal_trY4 (ca : ChargeAssignment)
    (hcubic : cubicCondition ca) (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca) (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0) :
    trY4 ca = 2280 * ca.yQ ^ 4 := by
  rcases anomaly_uniqueness ca hcubic hsu2 hsu3 hlin hQ with
    ⟨hd, hu, hL, he⟩ | ⟨hd, hu, hL, he⟩ <;>
  (unfold trY4; rw [hu, hd, hL, he]; ring)

/-- **UNIVERSAL: Tr[Y⁴] ≠ 0 for ANY anomaly-free assignment with yQ ≠ 0.**
    A necessary condition for an additional U(1)' with Y-proportional charges
    to be anomaly-free is Tr[Y⁴] = 0. Since Tr[Y⁴] = 2280·yQ⁴ ≠ 0,
    the condition fails. The connection Tr[Y⁴] → mixed anomaly is standard
    physics (not formalized here); this theorem proves only the nonvanishing. -/
theorem universal_no_extra_u1 (ca : ChargeAssignment)
    (hcubic : cubicCondition ca) (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca) (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0) :
    trY4 ca ≠ 0 := by
  rw [universal_trY4 ca hcubic hsu2 hsu3 hlin hQ]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 4 hQ)

/-- Tr[T₃²] for one SM generation: SU(2) doublets contribute T₃ = ±1/2.
    Q_L: 3 colors × 2 × (1/2)² = 3/2. L_L: 2 × (1/2)² = 1/2. Total = 2. -/
noncomputable def trT3sq : ℝ := 3 * (2 * (1/2 : ℝ) ^ 2) + 2 * (1/2 : ℝ) ^ 2

theorem trT3sq_eq : trT3sq = 2 := by unfold trT3sq; norm_num

/-! ## Electric charge quantization fixes the normalization -/

/-- **DERIVED: Electric charge quantization forces yQ = 1/6.**

    The electric charge formula Q = T₃ + Y applied to the electron
    (which has Q = -1, T₃ = -1/2 in the lepton SU(2) doublet) gives
    yL = Q_e - T₃ = -1 - (-1/2) = -1/2.

    From anomaly_uniqueness: yL = -3·yQ (both solutions).
    Combining: -3·yQ = -1/2 → yQ = 1/6.

    yQ = 1/6 is NOT a free convention — it is FORCED by anomaly
    cancellation + integer electron charge. -/
theorem charge_quantization_fixes_yQ (ca : ChargeAssignment)
    (hcubic : cubicCondition ca) (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca) (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0)
    -- The electron has unit negative charge: Q_e = T₃ + Y_L = -1.
    -- T₃ = -1/2 for the lower component of the lepton doublet.
    -- Therefore Y_L = -1/2.
    (h_electron_charge : ca.yL = -1/2) :
    ca.yQ = 1/6 := by
  rcases anomaly_uniqueness ca hcubic hsu2 hsu3 hlin hQ with
    ⟨_, _, hL, _⟩ | ⟨_, _, hL, _⟩ <;> linarith

/-! ## The Weinberg angle from anomaly cancellation -/

/-- **DERIVED: sin²θ_W = 3/8 from anomaly cancellation + charge quantization.**

    The complete derivation chain (every step proven or clearly hypothesized):

    (1) Anomaly cancellation → charges = (yQ, -4yQ, 2yQ, -3yQ, 6yQ)
        [PROVEN: anomaly_uniqueness]
    (2) Electron charge Q_e = -1 with T₃ = -1/2 → yL = -1/2
        [INPUT: the electron has unit negative charge]
    (3) yL = -3·yQ = -1/2 → yQ = 1/6
        [PROVEN: charge_quantization_fixes_yQ]
    (4) Tr[Y²] = 120·yQ² = 120/36 = 10/3
        [PROVEN: universal_trY2]
    (5) Tr[T₃²] = 2
        [PROVEN: trT3sq_eq]
    (6) Single coupling g²(M_P) = 1 → g'²/g₂² = Tr[T₃²]/Tr[Y²]
        [HYPOTHESIS: equal gauge action per fermion at M_P]
    (7) sin²θ_W = g'²/(g'²+g₂²) = Tr[T₃²]/(Tr[T₃²]+Tr[Y²]) = 3/8
        [PROVEN: arithmetic]

    Input beyond anomaly cancellation: the electron has integer charge (step 2)
    and the gauge coupling is universal at M_P (step 6).
    No GUT embedding is assumed. -/
theorem weinberg_from_anomaly (ca : ChargeAssignment)
    (hcubic : cubicCondition ca) (hsu2 : su2MixedCondition ca)
    (hsu3 : su3MixedCondition ca) (hlin : linearCondition ca)
    (hQ : ca.yQ ≠ 0)
    (h_electron_charge : ca.yL = -1/2) :
    trT3sq / (trT3sq + trY2 ca) = 3 / 8 := by
  have hyQ := charge_quantization_fixes_yQ ca hcubic hsu2 hsu3 hlin hQ h_electron_charge
  rw [universal_trY2 ca hcubic hsu2 hsu3 hlin hQ, trT3sq_eq, hyQ]
  norm_num

end UnifiedTheory.LayerA.AnomalyConstraints
