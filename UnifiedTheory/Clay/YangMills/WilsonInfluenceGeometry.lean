/- Exact shared-plaquette influence multiplicities for the periodic Wilson lattice.
The row count records plaquettes with multiplicity, so period two causes no
false assertion that all eighteen neighboring coordinates are distinct. -/
import UnifiedTheory.Clay.YangMills.WilsonIndependentBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
noncomputable section
open RegulatedGauge PeriodicLattice4 WilsonIndependentBlocks SingleLinkWilsonOscillation
open scoped BigOperators

variable (n : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _
local instance plaquetteDecidableEq : DecidableEq (PlaquetteIndex n) := Classical.decEq _

def incidentLinks (p : PlaquetteIndex n) : Finset (Link n) :=
  {(p.1, p.2.1.1), (step n p.1 p.2.1.1, p.2.1.2),
    (step n p.1 p.2.1.2, p.2.1.1), (p.1, p.2.1.2)}

omit [NeZero n] in
theorem mem_incidentLinks (p : PlaquetteIndex n) (a : Link n) :
    a ∈ incidentLinks n p ↔ incident n p a := by
  simp [incidentLinks, incident]

/-- The six-plaquette formula is exactly incidence in the actual oriented square. -/
theorem affected_iff_incident (p : PlaquetteIndex n) (a : Link n) :
    p ∈ affected n a.1 a.2 ↔ incident n p a := by
  constructor
  · intro hp
    obtain ⟨hplane, hbase⟩ := (mem_affected_iff n a.1 a.2 p).mp hp
    have hplane' : p.2.1.1 = a.2 ∨ p.2.1.2 = a.2 := by simpa [planes] using hplane
    rcases hplane' with hd | hd
    · have ht : transverse a.2 p.2 = p.2.1.2 := by simp [transverse, hd]
      rcases hbase with hb | hb
      · exact Or.inl (Prod.ext hb.symm hd.symm)
      · rw [ht] at hb
        exact Or.inr (Or.inr (Or.inl (Prod.ext (eq_sub_iff_add_eq.mp hb).symm hd.symm)))
    · have hn : p.2.1.1 ≠ a.2 := by rw [← hd]; exact ne_of_lt p.2.2
      have ht : transverse a.2 p.2 = p.2.1.1 := by simp [transverse, hn]
      rcases hbase with hb | hb
      · exact Or.inr (Or.inr (Or.inr (Prod.ext hb.symm hd.symm)))
      · rw [ht] at hb
        exact Or.inr (Or.inl (Prod.ext (eq_sub_iff_add_eq.mp hb).symm hd.symm))
  · exact incident_affected n p a

omit [NeZero n] in
theorem incidentLinks_card_le (p : PlaquetteIndex n) : (incidentLinks n p).card ≤ 4 := by
  have h1 := Finset.card_insert_le (p.1, p.2.1.1)
    ({(step n p.1 p.2.1.1, p.2.1.2), (step n p.1 p.2.1.2, p.2.1.1),
      (p.1, p.2.1.2)} : Finset (Link n))
  have h2 := Finset.card_insert_le (step n p.1 p.2.1.1, p.2.1.2)
    ({(step n p.1 p.2.1.2, p.2.1.1), (p.1, p.2.1.2)} : Finset (Link n))
  have h3 := Finset.card_insert_le (step n p.1 p.2.1.2, p.2.1.1)
    ({(p.1, p.2.1.2)} : Finset (Link n))
  simp only [Finset.card_singleton] at h3
  unfold incidentLinks
  omega

theorem other_incident_card_le (p : PlaquetteIndex n) (a : Link n)
    (ha : p ∈ affected n a.1 a.2) : ((incidentLinks n p).erase a).card ≤ 3 := by
  have hm : a ∈ incidentLinks n p :=
    (mem_incidentLinks n p a).mpr ((affected_iff_incident n p a).mp ha)
  have hc := Finset.card_erase_add_one hm
  have hb := incidentLinks_card_le n p
  omega

/-- Shared plaquettes of distinct coordinates; the diagonal is deliberately empty. -/
def sharedPlaquettes (a b : Link n) : Finset (PlaquetteIndex n) :=
  if a = b then ∅ else affected n a.1 a.2 ∩ affected n b.1 b.2

def multiplicity (a b : Link n) : ℕ := (sharedPlaquettes n a b).card

omit [NeZero n] in
theorem sharedPlaquettes_symm (a b : Link n) :
    sharedPlaquettes n a b = sharedPlaquettes n b a := by
  by_cases h : a = b
  · subst b; rfl
  · simp only [sharedPlaquettes, if_neg h, if_neg (Ne.symm h), Finset.inter_comm]

omit [NeZero n] in
@[simp] theorem multiplicity_self (a : Link n) : multiplicity n a a = 0 := by
  simp [multiplicity, sharedPlaquettes]

omit [NeZero n] in
theorem multiplicity_symm (a b : Link n) : multiplicity n a b = multiplicity n b a := by
  rw [multiplicity, sharedPlaquettes_symm]
  rfl

omit [NeZero n] in
theorem mem_sharedPlaquettes (a b : Link n) (p : PlaquetteIndex n) :
    p ∈ sharedPlaquettes n a b ↔
      a ≠ b ∧ p ∈ affected n a.1 a.2 ∧ p ∈ affected n b.1 b.2 := by
  by_cases h : a = b <;> simp [sharedPlaquettes, h]

omit [NeZero n] in
theorem multiplicity_eq_sum (a b : Link n) :
    multiplicity n a b =
      ∑ p ∈ affected n a.1 a.2, if a ≠ b ∧ p ∈ affected n b.1 b.2 then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b; simp
  · rw [multiplicity, sharedPlaquettes, if_neg h, Finset.card_eq_sum_ones]
    simp only [ne_eq, h, not_false_eq_true, true_and]
    rw [Finset.sum_ite_mem]

/-- Double counting counts neighboring coordinates separately for each shared plaquette. -/
theorem multiplicity_row_eq (a : Link n) :
    ∑ b, multiplicity n a b =
      ∑ p ∈ affected n a.1 a.2, ((incidentLinks n p).erase a).card := by
  classical
  simp_rw [multiplicity_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have he : ((incidentLinks n p).erase a) =
      Finset.univ.filter (fun b : Link n => a ≠ b ∧ p ∈ affected n b.1 b.2) := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_incidentLinks, affected_iff_incident, ne_comm]
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Six incident plaquettes, each with at most three other coordinates: eighteen incidences. -/
theorem multiplicity_row_le (a : Link n) : ∑ b, multiplicity n a b ≤ 18 := by
  rw [multiplicity_row_eq]
  calc
    _ ≤ ∑ _p ∈ affected n a.1 a.2, 3 :=
      Finset.sum_le_sum (fun p hp => other_incident_card_le n p a hp)
    _ ≤ 18 := by
      simp only [Finset.sum_const, smul_eq_mul]
      have h := affected_card n a.1 a.2
      omega

/-- The actual plaquette-multiplicity coefficient used by the SU(2) conditional influence bound. -/
def coefficient (β : ℝ) (a b : Link n) : ℝ := 2 * β * (multiplicity n a b : ℝ)

omit [NeZero n] in
theorem coefficient_nonneg (β : ℝ) (hβ : 0 ≤ β) (a b : Link n) :
    0 ≤ coefficient n β a b := by unfold coefficient; positivity

omit [NeZero n] in
@[simp] theorem coefficient_self (β : ℝ) (a : Link n) : coefficient n β a a = 0 := by
  simp [coefficient]

omit [NeZero n] in
theorem coefficient_symm (β : ℝ) (a b : Link n) :
    coefficient n β a b = coefficient n β b a := by
  simp only [coefficient, multiplicity_symm n a b]

/-- A volume-independent row bound, valid also when period-two neighbors repeat. -/
theorem coefficient_row_le (β : ℝ) (hβ : 0 ≤ β) (a : Link n) :
    ∑ b, coefficient n β a b ≤ 36 * β := by
  simp only [coefficient, ← Finset.mul_sum, ← Nat.cast_sum]
  have h : (↑(∑ b, multiplicity n a b) : ℝ) ≤ 18 := by
    exact_mod_cast multiplicity_row_le n a
  nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * β)]

end
end UnifiedTheory.Clay.YangMills.WilsonInfluenceGeometry
