/-
  Audit/KFFiniteProbeCode.lean

  FINITE-PROBE IDENTIFICATION AND ROBUST DECODING

  This module isolates the code-theoretic content of finite tomography.  A
  physical model supplies candidates, probes, and responses; the theorems
  below only say when those responses identify a candidate and how much noise
  that identification tolerates.

  The concrete application at the end uses the repository's three Pauli Born
  expectations for projective qubit carriers.  No arithmetic sequence or
  prime-selection mechanism is assumed.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.InformationTheory.Hamming
import UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFFiniteProbeCode

noncomputable section

/-! ## 1. Finite-valued response codes -/

/-- A candidate encoded by its responses to a finite family of probes. -/
structure FiniteResponseCode
    (Candidate Probe Response : Type*)
    [Fintype Probe] [Fintype Response] where
  response : Candidate → Probe → Response

namespace FiniteResponseCode

variable {Candidate Probe Response : Type*}
variable [Fintype Probe] [Fintype Response] [DecidableEq Response]

/-- A uniform lower bound on pairwise Hamming distance. -/
def MinimumDistanceAtLeast
    (C : FiniteResponseCode Candidate Probe Response) (d : ℕ) : Prop :=
  ∀ a b, a ≠ b → d ≤ hammingDist (C.response a) (C.response b)

/-- Some strictly positive pairwise Hamming lower bound exists. -/
def HasPositiveMinimumDistance
    (C : FiniteResponseCode Candidate Probe Response) : Prop :=
  ∃ d : ℕ, 0 < d ∧ C.MinimumDistanceAtLeast d

/-- For a finite response word, exact injectivity is equivalent to a positive
minimum-distance certificate.  In the forward direction distance one always
works. -/
theorem hasPositiveMinimumDistance_iff_injective
    (C : FiniteResponseCode Candidate Probe Response) :
    C.HasPositiveMinimumDistance ↔ Function.Injective C.response := by
  constructor
  · rintro ⟨d, hd, hdist⟩ a b hab
    by_contra hne
    have hzero : hammingDist (C.response a) (C.response b) = 0 :=
      hammingDist_eq_zero.mpr hab
    have := hdist a b hne
    omega
  · intro hinjective
    refine ⟨1, by omega, ?_⟩
    intro a b hab
    exact hammingDist_pos.mpr (fun h => hab (hinjective h))

/-- A received response word differs from a codeword in at most `t` probe
coordinates. -/
def WithinHammingErrors
    (C : FiniteResponseCode Candidate Probe Response)
    (t : ℕ) (received : Probe → Response) (candidate : Candidate) : Prop :=
  hammingDist received (C.response candidate) ≤ t

/-- Disjoint Hamming balls give exact unique decoding under `t` adversarial
response errors whenever every distinct pair is separated by more than
`2 * t` coordinates. -/
theorem unique_decode_of_hamming_separated
    (C : FiniteResponseCode Candidate Probe Response) {t : ℕ}
    (hsep : ∀ a b, a ≠ b →
      2 * t < hammingDist (C.response a) (C.response b))
    {received : Probe → Response} {a b : Candidate}
    (ha : C.WithinHammingErrors t received a)
    (hb : C.WithinHammingErrors t received b) :
    a = b := by
  by_contra hab
  have ha' : hammingDist (C.response a) received ≤ t := by
    simpa only [hammingDist_comm] using ha
  have hdist : hammingDist (C.response a) (C.response b) ≤ 2 * t := by
    calc
      hammingDist (C.response a) (C.response b) ≤
          hammingDist (C.response a) received +
            hammingDist received (C.response b) :=
        hammingDist_triangle _ _ _
      _ ≤ t + t := Nat.add_le_add ha' hb
      _ = 2 * t := (two_mul t).symm
  exact (Nat.not_lt_of_ge hdist) (hsep a b hab)

end FiniteResponseCode

/-! ## 2. Real-valued separation margins -/

/-- A real-valued response vector on a finite probe family. -/
structure RealProbeCode
    (Candidate Probe : Type*) [Fintype Probe] where
  response : Candidate → Probe → ℝ

namespace RealProbeCode

variable {Candidate Probe : Type*} [Fintype Probe]

/-- Distinct candidates differ by at least `gamma` on some probe, with
`gamma` strictly positive. -/
def HasSeparationMargin
    (C : RealProbeCode Candidate Probe) (gamma : ℝ) : Prop :=
  0 < gamma ∧
    ∀ a b, a ≠ b → ∃ p, gamma ≤ |C.response a p - C.response b p|

/-- Every reported coordinate lies strictly within half the certified
separation margin of one candidate. -/
def WithinHalfMargin
    (C : RealProbeCode Candidate Probe) (gamma : ℝ)
    (received : Probe → ℝ) (candidate : Candidate) : Prop :=
  ∀ p, |received p - C.response candidate p| < gamma / 2

theorem injective_of_separationMargin
    (C : RealProbeCode Candidate Probe) {gamma : ℝ}
    (hsep : C.HasSeparationMargin gamma) :
    Function.Injective C.response := by
  intro a b hab
  by_contra hne
  obtain ⟨p, hp⟩ := hsep.2 a b hne
  have hpEq := congrFun hab p
  rw [hpEq, sub_self, abs_zero] at hp
  linarith [hsep.1]

/-- A response vector cannot be strictly closer than `gamma / 2` in every
coordinate to two candidates whose codewords have separation margin
`gamma`. -/
theorem unique_recovery_within_half_margin
    (C : RealProbeCode Candidate Probe) {gamma : ℝ}
    (hsep : C.HasSeparationMargin gamma)
    {received : Probe → ℝ} {a b : Candidate}
    (ha : C.WithinHalfMargin gamma received a)
    (hb : C.WithinHalfMargin gamma received b) :
    a = b := by
  by_contra hab
  obtain ⟨p, hp⟩ := hsep.2 a b hab
  have htriangle :
      |C.response a p - C.response b p| ≤
        |C.response a p - received p| +
          |received p - C.response b p| := by
    calc
      |C.response a p - C.response b p| =
          |(C.response a p - received p) +
            (received p - C.response b p)| := by ring_nf
      _ ≤ |C.response a p - received p| +
          |received p - C.response b p| := abs_add_le _ _
  have ha' : |C.response a p - received p| < gamma / 2 := by
    simpa only [abs_sub_comm] using ha p
  have hstrict : |C.response a p - C.response b p| < gamma := by
    calc
      |C.response a p - C.response b p| ≤
          |C.response a p - received p| +
            |received p - C.response b p| := htriangle
      _ < gamma / 2 + gamma / 2 := add_lt_add ha' (hb p)
      _ = gamma := by ring
  exact (not_lt_of_ge hp) hstrict

/-- An injective real response code on a finite candidate type admits an
actual positive uniform separation margin.  We select one distinguishing
probe for each ordered unequal pair and take the minimum of the resulting
finite positive gaps (together with `1`, which handles empty/singleton
candidate types). -/
theorem exists_positive_separationMargin_of_finite_injective
    [Fintype Candidate]
    (C : RealProbeCode Candidate Probe)
    (hinjective : Function.Injective C.response) :
    ∃ gamma : ℝ, C.HasSeparationMargin gamma := by
  classical
  have hdifferent : ∀ a b : Candidate, a ≠ b →
      ∃ p : Probe, C.response a p ≠ C.response b p := by
    intro a b hab
    by_contra hnone
    push_neg at hnone
    exact hab (hinjective (funext hnone))
  let selected : ∀ a b : Candidate, a ≠ b → Probe :=
    fun a b hab => Classical.choose (hdifferent a b hab)
  have hselected : ∀ (a b : Candidate) (hab : a ≠ b),
      C.response a (selected a b hab) ≠
        C.response b (selected a b hab) := by
    intro a b hab
    exact Classical.choose_spec (hdifferent a b hab)
  let gap : Candidate → Candidate → ℝ := fun a b =>
    if hab : a = b then 1
    else |C.response a (selected a b hab) -
      C.response b (selected a b hab)|
  have hgap_pos : ∀ a b : Candidate, 0 < gap a b := by
    intro a b
    by_cases hab : a = b
    · simp [gap, hab]
    · have hne := hselected a b hab
      have habs : 0 < |C.response a (selected a b hab) -
          C.response b (selected a b hab)| :=
        abs_pos.mpr (sub_ne_zero.mpr hne)
      simpa [gap, hab] using habs
  let gaps : Finset ℝ :=
    {1} ∪ (Finset.univ.product Finset.univ).image
      (fun pair : Candidate × Candidate => gap pair.1 pair.2)
  have hgaps_nonempty : gaps.Nonempty := by
    exact ⟨1, by simp [gaps]⟩
  let gamma : ℝ := gaps.min' hgaps_nonempty
  have hgamma_pos : 0 < gamma := by
    have hmem : gamma ∈ gaps := Finset.min'_mem gaps hgaps_nonempty
    rcases Finset.mem_union.mp hmem with hOne | hImage
    · have hgamma : gamma = 1 := Finset.mem_singleton.mp hOne
      simpa [hgamma]
    · rcases Finset.mem_image.mp hImage with ⟨pair, _, hpair⟩
      rw [← hpair]
      exact hgap_pos pair.1 pair.2
  refine ⟨gamma, hgamma_pos, ?_⟩
  intro a b hab
  have hgap_mem : gap a b ∈ gaps := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(a, b), by simp, rfl⟩
  have hgamma_le : gamma ≤ gap a b :=
    Finset.min'_le (s := gaps) (gap a b) hgap_mem
  refine ⟨selected a b hab, ?_⟩
  simpa [gap, hab] using hgamma_le

end RealProbeCode

/-! ## 3. A finite cutoff for a bounded finite candidate family -/

/-- If a Nat-indexed observation separates a finite candidate type, some
finite initial segment already separates it.  The cutoff is constructed as
one plus the largest selected pairwise distinguishing probe. -/
theorem exists_finite_probe_cutoff_of_injective
    {Candidate Response : Type*} [Fintype Candidate]
    (observe : Candidate → ℕ → Response)
    (hinjective : Function.Injective observe) :
    ∃ cutoff : ℕ,
      Function.Injective
        (fun c : Candidate => fun p : Fin cutoff => observe c p.1) := by
  classical
  have hdifferent : ∀ a b : Candidate,
      ∃ n : ℕ, a ≠ b → observe a n ≠ observe b n := by
    intro a b
    by_cases hab : a = b
    · exact ⟨0, fun hne => (hne hab).elim⟩
    · have hfunctions : observe a ≠ observe b :=
        fun h => hab (hinjective h)
      have hexists : ∃ n : ℕ, observe a n ≠ observe b n := by
        by_contra hnone
        push_neg at hnone
        exact hfunctions (funext hnone)
      exact ⟨Classical.choose hexists,
        fun _ => Classical.choose_spec hexists⟩
  let witness : Candidate → Candidate → ℕ :=
    fun a b => Classical.choose (hdifferent a b)
  have hwitness : ∀ a b : Candidate, a ≠ b →
      observe a (witness a b) ≠ observe b (witness a b) := by
    intro a b hab
    exact Classical.choose_spec (hdifferent a b) hab
  let largest : ℕ :=
    Finset.univ.sup (fun a : Candidate =>
      Finset.univ.sup (fun b : Candidate => witness a b))
  refine ⟨largest + 1, ?_⟩
  intro a b hpref
  by_contra hab
  have hinner : witness a b ≤
      Finset.univ.sup (fun b' : Candidate => witness a b') :=
    Finset.le_sup (Finset.mem_univ b)
  have houter :
      Finset.univ.sup (fun b' : Candidate => witness a b') ≤ largest := by
    exact Finset.le_sup
      (f := fun a' : Candidate =>
        (Finset.univ.sup (fun b' : Candidate => witness a' b') : ℕ))
      (Finset.mem_univ a)
  let p : Fin (largest + 1) :=
    ⟨witness a b, Nat.lt_succ_of_le (hinner.trans houter)⟩
  exact hwitness a b hab (congrFun hpref p)

/-- Finset form of the cutoff theorem: only separation on the declared finite
candidate ledger is required. -/
theorem exists_finite_probe_cutoff_on_finset
    {Candidate Response : Type*}
    (candidates : Finset Candidate)
    (observe : Candidate → ℕ → Response)
    (hsep : Set.InjOn observe (candidates : Set Candidate)) :
    ∃ cutoff : ℕ,
      Set.InjOn
        (fun c : Candidate => fun p : Fin cutoff => observe c p.1)
        (candidates : Set Candidate) := by
  classical
  let BoundedCandidate := {c : Candidate // c ∈ candidates}
  have hinjective : Function.Injective
      (fun c : BoundedCandidate => observe c.1) := by
    intro a b hab
    apply Subtype.ext
    exact hsep a.2 b.2 hab
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_finite_probe_cutoff_of_injective
      (fun c : BoundedCandidate => observe c.1) hinjective
  refine ⟨cutoff, ?_⟩
  intro a ha b hb hab
  let a' : BoundedCandidate := ⟨a, ha⟩
  let b' : BoundedCandidate := ⟨b, hb⟩
  have hsub : a' = b' := hcutoff hab
  exact congrArg Subtype.val hsub

/-! ## 4. Existing Pauli/Born projective-carrier instantiation -/

open UnifiedTheory.Audit.KFHopfUnitSphereQuotient
open UnifiedTheory.Audit.KFRecoveredCSpecHopfBornObservable
open UnifiedTheory.Audit.KFRecoveredCSpecHopfProjectiveQubitCarrier

/-- The three actual Pauli probes used by the recovered Hopf/Born carrier
interface. -/
inductive PauliProbe
  | x | y | z
  deriving DecidableEq, Fintype

/-- The real response is the expectation of the corresponding Born pair. -/
noncomputable def projectivePauliExpectationCode :
    RealProbeCode ProjectiveQubitCarrier PauliProbe where
  response carrier probe :=
    match probe with
    | .x => carrier.bornX.expectation
    | .y => carrier.bornY.expectation
    | .z => carrier.bornZ.expectation

/-- The existing Pauli Born tomography theorem makes this three-probe real
code exactly injective on projective qubit carriers. -/
theorem projectivePauliExpectationCode_injective :
    Function.Injective projectivePauliExpectationCode.response := by
  intro C D hresponse
  apply (ProjectiveQubitCarrier.projective_qubit_carrier_interface C D).2.2.2.mp
  apply UnitBlochCoords.ext_coords
  · rw [← C.bornX_expectation_eq_bloch_x,
      ← D.bornX_expectation_eq_bloch_x]
    exact congrFun hresponse PauliProbe.x
  · rw [← C.bornY_expectation_eq_bloch_y,
      ← D.bornY_expectation_eq_bloch_y]
    exact congrFun hresponse PauliProbe.y
  · rw [← C.bornZ_expectation_eq_bloch_z,
      ← D.bornZ_expectation_eq_bloch_z]
    exact congrFun hresponse PauliProbe.z

/-- Consequently any finite ledger of distinct projective carriers has exact
three-Pauli observational identification. -/
theorem projectivePauliExpectationCode_injOn
    (candidates : Set ProjectiveQubitCarrier) :
    Set.InjOn projectivePauliExpectationCode.response candidates := by
  intro C _ D _ h
  exact projectivePauliExpectationCode_injective h

/-- Restrict the exact Pauli expectation code to a declared finite candidate
ledger. -/
noncomputable def projectivePauliExpectationCodeOn
    (candidates : Finset ProjectiveQubitCarrier) :
    RealProbeCode {C : ProjectiveQubitCarrier // C ∈ candidates} PauliProbe where
  response carrier := projectivePauliExpectationCode.response carrier.1

theorem projectivePauliExpectationCodeOn_injective
    (candidates : Finset ProjectiveQubitCarrier) :
    Function.Injective (projectivePauliExpectationCodeOn candidates).response := by
  intro C D hresponse
  apply Subtype.ext
  exact projectivePauliExpectationCode_injective hresponse

/-- Every finite ledger of projective qubit carriers therefore has a concrete
positive Pauli-response margin and inherits the `gamma / 2` robust unique
recovery theorem above. -/
theorem exists_projectivePauli_separationMargin
    (candidates : Finset ProjectiveQubitCarrier) :
    ∃ gamma : ℝ,
      (projectivePauliExpectationCodeOn candidates).HasSeparationMargin gamma :=
  RealProbeCode.exists_positive_separationMargin_of_finite_injective
    (projectivePauliExpectationCodeOn candidates)
    (projectivePauliExpectationCodeOn_injective candidates)

#print axioms FiniteResponseCode.hasPositiveMinimumDistance_iff_injective
#print axioms FiniteResponseCode.unique_decode_of_hamming_separated
#print axioms RealProbeCode.unique_recovery_within_half_margin
#print axioms RealProbeCode.exists_positive_separationMargin_of_finite_injective
#print axioms exists_finite_probe_cutoff_on_finset
#print axioms projectivePauliExpectationCode_injective
#print axioms exists_projectivePauli_separationMargin

end

end UnifiedTheory.Audit.KFFiniteProbeCode
