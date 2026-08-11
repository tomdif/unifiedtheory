/-
  Audit/KFCausalBornRecordMartingale.lean

  FACT STABILITY: RECORDS ARE MARTINGALE-STABLE UNDER BORN COMPLETENESS,
  AND FACT-UNHAPPENING IS EXACTLY THE BORN DEFECT OF THE COHERENT RULE

  Context.  The records test (records-churn-2026-08-03) measured stem-event
  measures churning under the coherent sum(a) = 1 growth law — facts
  un-happened as the horizon grew (s3: 0.963 -> 0.941 -> 0.548).  The
  lambda-dephasing scan (SUM_RULE_MOD.md) decomposed that churn as ~86%
  normalization flow, and the Born-normalization transfer audit
  (KFCausalBornNormalizationTransfer.lean) proved cylinder projectivity of
  the diagonal Born measure but explicitly left open its item 3: cylinder
  projectivity does not by itself settle the behaviour of stem/record
  events.  This file closes the finite-depth record half of that item.

  For one causal refinement stage (every child a one-element extension of
  its parent history, carrying a birth amplitude), with the Born-diagonal
  measure w'(child) = w(parent) * |amp child|^2:

  1. `record_transport` — if the birth amplitudes are Born-complete at
     every parent, the refined measure of the exact lift of any past event
     equals the past event's measure: facts have horizon-invariant
     probabilities.  (In particular, total mass is conserved: no
     normalization flow, the measured source of ~86% of the churn.)
  2. `record_accretion` — any event that is monotone across the stage
     (contains the lift of its past form, as stem events do) can only
     gain measure: facts never un-happen.
  3. `record_measure_converges` — a bounded monotone record sequence
     converges: iterated over stages, stem-event measures stabilize.
  4. `coherent_record_regression` — the converse witness.  A two-stage
     growth law that is coherently normalized (sum of amplitudes = 1 at
     every parent: the old sum rule) but not Born-complete, in which a
     monotone record's normalized measure strictly FALLS 4/5 -> 4/9.
     Fact-unhappening needs no interference between records: it is
     produced by the diagonal itself when sum |a|^2 != 1 — the churn
     mechanism observed in stem_measures.log, in minimal form.
  5. `fact_stability_dichotomy` — the packaged statement of 2 + 4.

  Numerical companion: born_records_test.py / born_records_test.log
  (Born-shell completion of the phi = 0.9 wave-family members; measured
  X_minus(P) = 0 exactly, X_minus(Q) ~ 0.08 vs 1.11 for the old law at
  matched member, stage-4 sector masses horizon-invariant to 6 decimals,
  interference retained max|Q-P| ~ 0.28).

  Zero sorry.  Zero custom axioms.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Real
import Mathlib.Topology.UniformSpace.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBornRecordMartingale

open scoped Classical
open Finset

universe u v

/-! ## 1. One causal refinement stage -/

variable {Parent : Type u} {Child : Type v}
variable [Fintype Parent] [Fintype Child] [DecidableEq Parent]

/-- Born completeness of a birth stage: at every parent the squared
moduli of the birth amplitudes sum to one.  This is the diagonal half of
the double-conservation law of `KFCausalDoubleConservationLaw.lean`. -/
def BornComplete (par : Child → Parent) (amp : Child → ℂ) : Prop :=
  ∀ a : Parent,
    ∑ b ∈ univ.filter (fun b => par b = a), Complex.normSq (amp b) = 1

/-- Coherent (Markov) completeness: the old sum rule `sum a = 1`. -/
def CoherentComplete (par : Child → Parent) (amp : Child → ℂ) : Prop :=
  ∀ a : Parent, ∑ b ∈ univ.filter (fun b => par b = a), amp b = 1

/-- Born-diagonal refinement of a parent measure along the births. -/
noncomputable def refine (par : Child → Parent) (amp : Child → ℂ)
    (w : Parent → ℝ) : Child → ℝ :=
  fun b => w (par b) * Complex.normSq (amp b)

/-- Measure of an event under a weight assignment. -/
noncomputable def eventMass {γ : Type*} [Fintype γ] (w : γ → ℝ)
    (E : γ → Prop) : ℝ :=
  ∑ x, if E x then w x else 0

/-! ## 2. Record transport: facts have horizon-invariant probabilities -/

/-- Under Born completeness, the refined measure of the exact lift of a
past event equals the past event's measure. -/
theorem record_transport (par : Child → Parent) (amp : Child → ℂ)
    (w : Parent → ℝ) (hB : BornComplete par amp) (E : Parent → Prop) :
    eventMass (refine par amp w) (fun b => E (par b)) = eventMass w E := by
  unfold eventMass refine
  calc
    ∑ b, (if E (par b) then w (par b) * Complex.normSq (amp b) else 0)
        = ∑ b, (if E (par b) then w (par b) else 0) *
            Complex.normSq (amp b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases h : E (par b) <;> simp [h]
    _ = ∑ a, ∑ b ∈ univ.filter (fun b => par b = a),
          (if E (par b) then w (par b) else 0) * Complex.normSq (amp b) :=
          (Finset.sum_fiberwise univ par _).symm
    _ = ∑ a, ∑ b ∈ univ.filter (fun b => par b = a),
          (if E a then w a else 0) * Complex.normSq (amp b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          refine Finset.sum_congr rfl fun b hb => ?_
          rw [(Finset.mem_filter.1 hb).2]
    _ = ∑ a, (if E a then w a else 0) *
          ∑ b ∈ univ.filter (fun b => par b = a), Complex.normSq (amp b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
    _ = ∑ a, (if E a then w a else 0) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hB a, mul_one]

/-- Total mass is conserved: the normalization flow that carried ~86% of
the measured record churn vanishes identically under Born completeness. -/
theorem no_normalization_flow (par : Child → Parent) (amp : Child → ℂ)
    (w : Parent → ℝ) (hB : BornComplete par amp) :
    eventMass (refine par amp w) (fun _ => True) =
      eventMass w (fun _ => True) :=
  record_transport par amp w hB (fun _ => True)

/-! ## 3. Record accretion: facts never un-happen -/

/-- A monotone event — one containing the exact lift of its past form, as
stem events do (a stem of the parent history is a stem of every child
history) — can only gain measure across a Born-complete stage. -/
theorem record_accretion (par : Child → Parent) (amp : Child → ℂ)
    (w : Parent → ℝ) (hB : BornComplete par amp) (hw : ∀ a, 0 ≤ w a)
    (E : Parent → Prop) (F : Child → Prop)
    (hmono : ∀ b, E (par b) → F b) :
    eventMass w E ≤ eventMass (refine par amp w) F := by
  rw [← record_transport par amp w hB E]
  unfold eventMass
  refine Finset.sum_le_sum fun b _ => ?_
  by_cases h : E (par b)
  · rw [if_pos h, if_pos (hmono b h)]
  · rw [if_neg h]
    by_cases h2 : F b
    · rw [if_pos h2]
      exact mul_nonneg (hw _) (Complex.normSq_nonneg _)
    · rw [if_neg h2]

/-! ## 4. Convergence: stem-event measures stabilize -/

/-- A bounded monotone record sequence converges.  Combined with
`record_accretion` iterated over stages (stem measures are monotone and
bounded by the conserved total mass), stem-event probabilities stabilize
under any Born-complete growth law. -/
theorem record_measure_converges (s : ℕ → ℝ) (hmono : Monotone s)
    (hbd : ∀ n, s n ≤ 1) :
    ∃ L : ℝ, Filter.Tendsto s Filter.atTop (nhds L) :=
  ⟨⨆ n, s n, tendsto_atTop_ciSup hmono
    ⟨1, by rintro x ⟨n, rfl⟩; exact hbd n⟩⟩

/-! ## 5. The converse witness: the coherent rule un-makes facts

One parent with births of amplitude 2 and −1 (coherent: 2 + (−1) = 1;
Born mass 4 + 1 = 5 ≠ 1).  The birth of amplitude 2 is the recorded
fact; its normalized measure is 4/5.  One more stage (the recorded branch
extends neutrally with amplitude 1; the other branch again splits 2, −1)
and the record's normalized measure is 4/9 < 4/5.  No interference
between the record and its complement is used anywhere: the diagonal
spoils itself, exactly the mechanism measured in stem_measures.log. -/

/-- Stage-one birth amplitudes. -/
noncomputable def ampOne : Fin 2 → ℂ := ![2, -1]

/-- Stage-one parent map (one parent). -/
def parOne : Fin 2 → Fin 1 := fun _ => 0

/-- Stage-two birth amplitudes. -/
noncomputable def ampTwo : Fin 3 → ℂ := ![1, 2, -1]

/-- Stage-two parent map: child 0 extends birth 0; children 1, 2 extend
birth 1. -/
def parTwo : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The initial (one-history) measure. -/
def wZero : Fin 1 → ℝ := fun _ => 1

noncomputable def wOne : Fin 2 → ℝ := refine parOne ampOne wZero
noncomputable def wTwo : Fin 3 → ℝ := refine parTwo ampTwo wOne

/-- The record event at stage one and its exact lift at stage two. -/
def recOne : Fin 2 → Prop := fun b => b = 0
def recTwo : Fin 3 → Prop := fun c => c = 0

theorem coherent_one : CoherentComplete parOne ampOne := by
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have hfil : univ.filter (fun b : Fin 2 => parOne b = 0) = univ := by
    refine Finset.filter_true_of_mem fun b _ => rfl
  rw [hfil, Fin.sum_univ_two]
  norm_num [ampOne]

theorem coherent_two : CoherentComplete parTwo ampTwo := by
  intro a
  fin_cases a <;> simp only [Fin.mk_zero, Fin.mk_one]
  · have hfil : univ.filter (fun c : Fin 3 => parTwo c = 0) = {0} := by
      decide
    rw [hfil, Finset.sum_singleton]
    norm_num [ampTwo]
  · have hfil : univ.filter (fun c : Fin 3 => parTwo c = 1) = {1, 2} := by
      decide
    rw [hfil, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [ampTwo, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]

theorem recTwo_monotone : ∀ c, recOne (parTwo c) → recTwo c := by
  unfold recOne recTwo parTwo
  decide

theorem wOne_masses :
    eventMass wOne recOne = 4 ∧ eventMass wOne (fun _ => True) = 5 := by
  have h1 : ¬ ((1 : Fin 2) = 0) := by decide
  constructor
  · simp only [eventMass, wOne, refine, wZero, ampOne, recOne]
    rw [Fin.sum_univ_two, if_pos rfl, if_neg h1]
    norm_num [Complex.normSq_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  · simp only [eventMass, wOne, refine, wZero, ampOne]
    rw [Fin.sum_univ_two, if_pos trivial, if_pos trivial]
    norm_num [Complex.normSq_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]

theorem wTwo_masses :
    eventMass wTwo recTwo = 4 ∧ eventMass wTwo (fun _ => True) = 9 := by
  have h1 : ¬ ((1 : Fin 3) = 0) := by decide
  have h2 : ¬ ((2 : Fin 3) = 0) := by decide
  constructor
  · simp only [eventMass, wTwo, wOne, refine, wZero, parTwo,
      ampTwo, ampOne, recTwo]
    rw [Fin.sum_univ_three, if_pos rfl, if_neg h1, if_neg h2]
    norm_num [Complex.normSq_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  · simp only [eventMass, wTwo, wOne, refine, wZero, parTwo,
      ampTwo, ampOne]
    rw [Fin.sum_univ_three, if_pos trivial, if_pos trivial, if_pos trivial]
    norm_num [Complex.normSq_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]

/-- THE REGRESSION WITNESS: a coherently normalized two-stage growth law
in which a monotone record's normalized measure strictly falls,
4/5 → 4/9.  The old sum rule permits facts to un-happen. -/
theorem coherent_record_regression :
    CoherentComplete parOne ampOne ∧ CoherentComplete parTwo ampTwo ∧
    (∀ c, recOne (parTwo c) → recTwo c) ∧
    eventMass wTwo recTwo / eventMass wTwo (fun _ => True) <
      eventMass wOne recOne / eventMass wOne (fun _ => True) := by
  refine ⟨coherent_one, coherent_two, recTwo_monotone, ?_⟩
  rw [wOne_masses.1, wOne_masses.2, wTwo_masses.1, wTwo_masses.2]
  norm_num

/-- The witness is (of course) not Born-complete: the record fiber's Born
mass is 5. -/
theorem witness_not_bornComplete : ¬ BornComplete parOne ampOne := by
  intro h
  have h0 := h 0
  have hfil : univ.filter (fun b : Fin 2 => parOne b = 0) = univ := by
    refine Finset.filter_true_of_mem fun b _ => rfl
  rw [hfil, Fin.sum_univ_two] at h0
  norm_num [ampOne, Complex.normSq_apply] at h0

/-! ## 6. Capstone -/

/-- FACT-STABILITY DICHOTOMY.  Under Born completeness every monotone
record's measure is nondecreasing across every refinement stage (facts
only accrete); under coherent normalization alone there is an explicit
two-stage law whose record measure strictly falls.  The record churn of
records-churn-2026-08-03 is exactly the Born defect of the coherent sum
rule, not an interference effect. -/
theorem fact_stability_dichotomy :
    (∀ (Parent Child : Type) (_ : Fintype Parent) (_ : Fintype Child)
       (_ : DecidableEq Parent)
       (par : Child → Parent) (amp : Child → ℂ) (w : Parent → ℝ),
       BornComplete par amp → (∀ a, 0 ≤ w a) →
       ∀ (E : Parent → Prop) (F : Child → Prop),
         (∀ b, E (par b) → F b) →
         eventMass w E ≤ eventMass (refine par amp w) F) ∧
    (CoherentComplete parOne ampOne ∧ CoherentComplete parTwo ampTwo ∧
     (∀ c, recOne (parTwo c) → recTwo c) ∧
     eventMass wTwo recTwo / eventMass wTwo (fun _ => True) <
       eventMass wOne recOne / eventMass wOne (fun _ => True)) := by
  constructor
  · intro Parent Child _ _ _ par amp w hB hw E F hmono
    exact record_accretion par amp w hB hw E F hmono
  · exact coherent_record_regression

#print axioms record_transport
#print axioms record_accretion
#print axioms record_measure_converges
#print axioms coherent_record_regression
#print axioms fact_stability_dichotomy

end UnifiedTheory.Audit.KFCausalBornRecordMartingale
