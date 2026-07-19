/-
  Audit/KFOrientationUnlabeledRefinement.lean

  UNLABELED REFINEMENT FRONTIER

  The finite orientation channel is already an explicit CPTP map.  This file
  isolates the remaining causal-set problem, constructs a covariant causal
  ordinal composition, and proves its descent to unlabeled histories.

  There are two independent constructions:

  * finite causal orders are quotiented by genuine order isomorphism, so a
    covariant labeled refinement descends to unlabeled orientation histories;
  * the four-Kraus channel is lifted to an explicit rectangular Stinespring
    isometry.  Its four pure input amplitudes implement orientation parity,
    and tracing out the four-state refinement record recovers the channel.

  The capstone says that the causal-order composition, label covariance, binary
  endpoint law, reversible dilation, and reduced channel can all coexist in one
  exact model.  The existing balanced-sector rigidity theorem then forces
  `Phi(D_y tensor D_z) = D_(2yz)` for every balanced input.

  This still does not manufacture a Rideout--Sorkin probability/amplitude law
  on growth trajectories.  It turns that open physical problem into the much
  smaller task of supplying a strongly positive covariant history measure.
-/

import UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel
import UnifiedTheory.Audit.OrderSensitiveObservables
import UnifiedTheory.LayerB.StinespringDilation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationUnlabeledRefinement

noncomputable section

open scoped BigOperators ComplexConjugate
open Matrix
open UnifiedTheory.LayerB.NoBackgroundSpace
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.Audit.OrderSensitiveObservables
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHistoryRefinement
open UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel

/-! ## 1. Unlabeled finite causal orders -/

/-- Two finite causal orders are isomorphic when a bijection of their event
carriers preserves the complete order relation.  Unlike equality of relation
matrices, this forgets every event label. -/
def FinPosetIsomorphic (P Q : FinPoset) : Prop :=
  ∃ e : Fin P.n ≃ Fin Q.n,
    ∀ i j : Fin P.n, P.rel i j = Q.rel (e i) (e j)

theorem finPosetIsomorphic_refl (P : FinPoset) :
    FinPosetIsomorphic P P := by
  refine ⟨Equiv.refl _, ?_⟩
  intro i j
  rfl

theorem finPosetIsomorphic_symm {P Q : FinPoset}
    (h : FinPosetIsomorphic P Q) : FinPosetIsomorphic Q P := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, ?_⟩
  intro i j
  simpa using (he (e.symm i) (e.symm j)).symm

theorem finPosetIsomorphic_trans {P Q R : FinPoset}
    (hPQ : FinPosetIsomorphic P Q) (hQR : FinPosetIsomorphic Q R) :
    FinPosetIsomorphic P R := by
  obtain ⟨e, he⟩ := hPQ
  obtain ⟨f, hf⟩ := hQR
  refine ⟨e.trans f, ?_⟩
  intro i j
  exact (he i j).trans (hf (e i) (e j))

theorem finPosetIsomorphic_relabel (P : FinPoset)
    (sigma : Equiv.Perm (Fin P.n)) :
    FinPosetIsomorphic P (relabel P sigma) := by
  refine ⟨sigma, ?_⟩
  intro i j
  simp [relabel]

/-- A labeled microscopic history carries a finite causal order and one of
the two curvature-orientation endpoints.  The endpoint is physical data; only
the event labels of `order` are quotiented out. -/
structure LabeledOrientationHistory where
  order : FinPoset
  endpoint : Fin 2

/-- Relabeling equivalence preserves the order only up to isomorphism and
preserves the physical orientation endpoint exactly. -/
def LabeledHistoryEquivalent
    (h k : LabeledOrientationHistory) : Prop :=
  FinPosetIsomorphic h.order k.order ∧ h.endpoint = k.endpoint

instance labeledOrientationHistorySetoid : Setoid LabeledOrientationHistory where
  r := LabeledHistoryEquivalent
  iseqv := {
    refl := fun h => ⟨finPosetIsomorphic_refl h.order, rfl⟩
    symm := fun hhk =>
      ⟨finPosetIsomorphic_symm hhk.1, hhk.2.symm⟩
    trans := fun hhk hkl =>
      ⟨finPosetIsomorphic_trans hhk.1 hkl.1, hhk.2.trans hkl.2⟩ }

/-- An unlabeled causal orientation history is an isomorphism class of finite
causal orders together with its physical orientation endpoint. -/
abbrev UnlabeledOrientationHistory :=
  Quotient labeledOrientationHistorySetoid

/-- Relabel a labeled history without changing its endpoint. -/
def relabelHistory (h : LabeledOrientationHistory)
    (sigma : Equiv.Perm (Fin h.order.n)) : LabeledOrientationHistory where
  order := relabel h.order sigma
  endpoint := h.endpoint

theorem relabelHistory_equivalent (h : LabeledOrientationHistory)
    (sigma : Equiv.Perm (Fin h.order.n)) :
    h ≈ relabelHistory h sigma := by
  exact ⟨finPosetIsomorphic_relabel h.order sigma, rfl⟩

theorem unlabeledHistory_forgets_relabeling (h : LabeledOrientationHistory)
    (sigma : Equiv.Perm (Fin h.order.n)) :
    (Quotient.mk _ h : UnlabeledOrientationHistory) =
      Quotient.mk _ (relabelHistory h sigma) := by
  exact Quotient.sound (relabelHistory_equivalent h sigma)

/-- The physical endpoint is well-defined on unlabeled histories because
order isomorphisms are not allowed to alter it. -/
def unlabeledEndpoint : UnlabeledOrientationHistory → Fin 2 :=
  Quotient.lift LabeledOrientationHistory.endpoint
    (fun _ _ h => h.2)

@[simp]
theorem unlabeledEndpoint_mk (h : LabeledOrientationHistory) :
    unlabeledEndpoint (Quotient.mk _ h) = h.endpoint := rfl

/-! ## 2. Covariant microscopic refinement and quotient descent -/

/-- Orientation parity in the repository's `D_y = I/2 - yY`
parameterization: equal input endpoints give endpoint `1`, unequal endpoints
give endpoint `0`. -/
def endpointCompose (a b : Fin 2) : Fin 2 :=
  if a = b then 1 else 0

/-- Convert the two endpoint labels to the extremal balanced parameters. -/
def endpointParameter (a : Fin 2) : ℝ :=
  if a = 0 then -1 / 2 else 1 / 2

theorem endpointParameter_compose (a b : Fin 2) :
    refinementCompose (endpointParameter a) (endpointParameter b) =
      endpointParameter (endpointCompose a b) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [endpointParameter, endpointCompose, refinementCompose,
      Fin.ext_iff]

theorem endpointCompose_assoc (a b c : Fin 2) :
    endpointCompose (endpointCompose a b) c =
      endpointCompose a (endpointCompose b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    decide

/-! ## 2. Concrete causal-order composition -/

/-- Relation of the ordinal sum `P then Q`: internal relations are retained,
every event of `P` precedes every event of `Q`, and no event of `Q` precedes an
event of `P`. -/
def causalOrdinalSumRel (P Q : FinPoset)
    (i j : Fin P.n ⊕ Fin Q.n) : Bool :=
  match i, j with
  | Sum.inl a, Sum.inl b => P.rel a b
  | Sum.inl _, Sum.inr _ => true
  | Sum.inr _, Sum.inl _ => false
  | Sum.inr a, Sum.inr b => Q.rel a b

/-- The ordinal sum is a nonempty finite causal order.  It is a genuine serial
composition: the first input is entirely in the causal past of the second. -/
def causalOrdinalSum (P Q : FinPoset) : FinPoset where
  n := P.n + Q.n
  hn := Nat.add_pos_left P.hn Q.n
  rel := fun i j => causalOrdinalSumRel P Q
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  refl := by
    intro i
    cases hi : finSumFinEquiv.symm i <;>
      simp [causalOrdinalSumRel, P.refl, Q.refl]
  antisymm := by
    intro i j hij hji
    apply finSumFinEquiv.symm.injective
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            congr 1
            exact P.antisymm a b
              (by simpa [causalOrdinalSumRel, hi, hj] using hij)
              (by simpa [causalOrdinalSumRel, hi, hj] using hji)
        | inr b =>
            simp [causalOrdinalSumRel, hi, hj] at hji
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            simp [causalOrdinalSumRel, hi, hj] at hij
        | inr b =>
            congr 1
            exact Q.antisymm a b
              (by simpa [causalOrdinalSumRel, hi, hj] using hij)
              (by simpa [causalOrdinalSumRel, hi, hj] using hji)
  trans := by
    intro i j k hij hjk
    cases hi : finSumFinEquiv.symm i with
    | inl a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c =>
                exact P.trans a b c
                  (by simpa [causalOrdinalSumRel, hi, hj] using hij)
                  (by simpa [causalOrdinalSumRel, hj, hk] using hjk)
            | inr c =>
                simp [causalOrdinalSumRel]
        | inr b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c =>
                simp [causalOrdinalSumRel, hj, hk] at hjk
            | inr c =>
                simp [causalOrdinalSumRel]
    | inr a =>
        cases hj : finSumFinEquiv.symm j with
        | inl b =>
            simp [causalOrdinalSumRel, hi, hj] at hij
        | inr b =>
            cases hk : finSumFinEquiv.symm k with
            | inl c =>
                simp [causalOrdinalSumRel, hj, hk] at hjk
            | inr c =>
                exact Q.trans a b c
                  (by simpa [causalOrdinalSumRel, hi, hj] using hij)
                  (by simpa [causalOrdinalSumRel, hj, hk] using hjk)

@[simp]
theorem causalOrdinalSum_left_precedes_right (P Q : FinPoset)
    (i : Fin P.n) (j : Fin Q.n) :
    (causalOrdinalSum P Q).rel
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = true := by
  simp [causalOrdinalSum, causalOrdinalSumRel]

@[simp]
theorem causalOrdinalSum_right_not_precedes_left (P Q : FinPoset)
    (i : Fin P.n) (j : Fin Q.n) :
    (causalOrdinalSum P Q).rel
        (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inl i)) = false := by
  simp [causalOrdinalSum, causalOrdinalSumRel]

/-- Three-stage serial relation on the fully exposed sum carrier. -/
private def causalTernarySumRel (P Q R : FinPoset)
    (i j : (Fin P.n ⊕ Fin Q.n) ⊕ Fin R.n) : Bool :=
  match i, j with
  | Sum.inl (Sum.inl a), Sum.inl (Sum.inl b) => P.rel a b
  | Sum.inl (Sum.inr a), Sum.inl (Sum.inr b) => Q.rel a b
  | Sum.inr a, Sum.inr b => R.rel a b
  | Sum.inl (Sum.inl _), _ => true
  | Sum.inl (Sum.inr _), Sum.inr _ => true
  | _, _ => false

/-- Serial causal composition is associative up to genuine order isomorphism.
The associator only changes the parenthesization of event labels. -/
theorem finPosetIsomorphic_causalOrdinalSum_assoc (P Q R : FinPoset) :
    FinPosetIsomorphic (causalOrdinalSum (causalOrdinalSum P Q) R)
      (causalOrdinalSum P (causalOrdinalSum Q R)) := by
  let exposeLeft : Fin ((P.n + Q.n) + R.n) ≃
      (Fin P.n ⊕ Fin Q.n) ⊕ Fin R.n :=
    finSumFinEquiv.symm.trans
      (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))
  let closeRight : (Fin P.n ⊕ Fin Q.n) ⊕ Fin R.n ≃
      Fin (P.n + (Q.n + R.n)) :=
    (Equiv.sumAssoc _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
        finSumFinEquiv)
  let reassociate : Fin ((P.n + Q.n) + R.n) ≃
      Fin (P.n + (Q.n + R.n)) := exposeLeft.trans closeRight
  have hleft (x y : (Fin P.n ⊕ Fin Q.n) ⊕ Fin R.n) :
      (causalOrdinalSum (causalOrdinalSum P Q) R).rel
          (exposeLeft.symm x) (exposeLeft.symm y) =
        causalTernarySumRel P Q R x y := by
    rcases x with ((a | b) | c) <;>
      rcases y with ((a' | b') | c') <;>
      simp [exposeLeft, causalOrdinalSum, causalOrdinalSumRel,
        causalTernarySumRel]
  have hright (x y : (Fin P.n ⊕ Fin Q.n) ⊕ Fin R.n) :
      (causalOrdinalSum P (causalOrdinalSum Q R)).rel
          (closeRight x) (closeRight y) =
        causalTernarySumRel P Q R x y := by
    rcases x with ((a | b) | c) <;>
      rcases y with ((a' | b') | c') <;>
      simp [closeRight, causalOrdinalSum, causalOrdinalSumRel,
        causalTernarySumRel]
  refine ⟨reassociate, ?_⟩
  intro i j
  change (causalOrdinalSum (causalOrdinalSum P Q) R).rel i j =
    (causalOrdinalSum P (causalOrdinalSum Q R)).rel
      (closeRight (exposeLeft i)) (closeRight (exposeLeft j))
  calc
    (causalOrdinalSum (causalOrdinalSum P Q) R).rel i j =
        causalTernarySumRel P Q R (exposeLeft i) (exposeLeft j) := by
      simpa using hleft (exposeLeft i) (exposeLeft j)
    _ = (causalOrdinalSum P (causalOrdinalSum Q R)).rel
        (closeRight (exposeLeft i)) (closeRight (exposeLeft j)) :=
      (hright (exposeLeft i) (exposeLeft j)).symm

/-- Ordinal sum respects genuine causal-order isomorphism in both arguments. -/
theorem finPosetIsomorphic_causalOrdinalSum {P P' Q Q' : FinPoset}
    (hP : FinPosetIsomorphic P P') (hQ : FinPosetIsomorphic Q Q') :
    FinPosetIsomorphic (causalOrdinalSum P Q) (causalOrdinalSum P' Q') := by
  obtain ⟨eP, heP⟩ := hP
  obtain ⟨eQ, heQ⟩ := hQ
  let e : Fin (P.n + Q.n) ≃ Fin (P'.n + Q'.n) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eP eQ).trans finSumFinEquiv)
  refine ⟨e, ?_⟩
  intro i j
  cases hi : finSumFinEquiv.symm i with
  | inl a =>
      cases hj : finSumFinEquiv.symm j with
      | inl b =>
          simpa [causalOrdinalSum, causalOrdinalSumRel, e, hi, hj] using
            heP a b
      | inr b =>
          simp [causalOrdinalSum, causalOrdinalSumRel, e, hi, hj]
  | inr a =>
      cases hj : finSumFinEquiv.symm j with
      | inl b =>
          simp [causalOrdinalSum, causalOrdinalSumRel, e, hi, hj]
      | inr b =>
          simpa [causalOrdinalSum, causalOrdinalSumRel, e, hi, hj] using
            heQ a b

/-- The exact interface a labeled causal-growth proposal must satisfy.

`covariant` is discrete general covariance: isomorphic input histories give
isomorphic output histories.  `endpointParity` is the only dynamical content
needed by the orientation sector. -/
structure CovariantCausalRefinement where
  refine : LabeledOrientationHistory → LabeledOrientationHistory →
    LabeledOrientationHistory
  covariant : ∀ {h h' k k'}, h ≈ h' → k ≈ k' →
    refine h k ≈ refine h' k'
  endpointParity : ∀ h k,
    (refine h k).endpoint = endpointCompose h.endpoint k.endpoint

/-- A concrete inhabitant of the refinement interface: serially compose the
two causal orders and compose their orientation endpoints by parity. -/
def ordinalCausalRefinement : CovariantCausalRefinement where
  refine := fun h k =>
    { order := causalOrdinalSum h.order k.order
      endpoint := endpointCompose h.endpoint k.endpoint }
  covariant := by
    intro h h' k k' hh kk
    exact ⟨finPosetIsomorphic_causalOrdinalSum hh.1 kk.1,
      by simp [hh.2, kk.2]⟩
  endpointParity := by
    intro h k
    rfl

/-- The labeled associator is precisely an allowed relabeling equivalence. -/
theorem ordinalCausalRefinement_refine_assoc
    (h k l : LabeledOrientationHistory) :
    ordinalCausalRefinement.refine
        (ordinalCausalRefinement.refine h k) l ≈
      ordinalCausalRefinement.refine h
        (ordinalCausalRefinement.refine k l) := by
  exact ⟨finPosetIsomorphic_causalOrdinalSum_assoc
      h.order k.order l.order,
    endpointCompose_assoc h.endpoint k.endpoint l.endpoint⟩

/-- A covariant labeled refinement descends canonically to the quotient of
unlabeled causal histories. -/
def CovariantCausalRefinement.descend (dynamics : CovariantCausalRefinement) :
    UnlabeledOrientationHistory → UnlabeledOrientationHistory →
      UnlabeledOrientationHistory :=
  Quotient.map₂ dynamics.refine
    (fun _ _ hh _ _ hk => dynamics.covariant hh hk)

@[simp]
theorem CovariantCausalRefinement.descend_mk
    (dynamics : CovariantCausalRefinement)
    (h k : LabeledOrientationHistory) :
    dynamics.descend (Quotient.mk _ h) (Quotient.mk _ k) =
      Quotient.mk _ (dynamics.refine h k) := rfl

/-- After label quotienting, the causal associator becomes exact equality. -/
theorem ordinalCausalRefinement_descend_assoc
    (h k l : UnlabeledOrientationHistory) :
    ordinalCausalRefinement.descend
        (ordinalCausalRefinement.descend h k) l =
      ordinalCausalRefinement.descend h
        (ordinalCausalRefinement.descend k l) := by
  refine Quotient.inductionOn₃ h k l ?_
  intro h' k' l'
  exact Quotient.sound (ordinalCausalRefinement_refine_assoc h' k' l')

/-- The microscopic endpoint law survives quotienting: it is a theorem on
unlabeled histories, not a representative-dependent assertion. -/
theorem CovariantCausalRefinement.unlabeled_endpoint_parity
    (dynamics : CovariantCausalRefinement)
    (h k : UnlabeledOrientationHistory) :
    unlabeledEndpoint (dynamics.descend h k) =
      endpointCompose (unlabeledEndpoint h) (unlabeledEndpoint k) := by
  refine Quotient.inductionOn₂ h k ?_
  intro h' k'
  exact dynamics.endpointParity h' k'

/-- Assign the extremal strongly-positive history kernel to an unlabeled
causal history through its invariant endpoint. -/
def unlabeledHistoryKernel (h : UnlabeledOrientationHistory) : SquareMatrix 2 :=
  balancedHistoryKernel (endpointParameter (unlabeledEndpoint h))

/-- **Channel descent on unlabeled endpoint histories.**  Any labeled causal
refinement satisfying covariance and endpoint parity is represented exactly
by the constructed CPTP channel after passage to unlabeled histories. -/
theorem CovariantCausalRefinement.channel_descends
    (dynamics : CovariantCausalRefinement)
    (h k : UnlabeledOrientationHistory) :
    orientationRefinementKraus.apply
        (historyKernelTensor (unlabeledHistoryKernel h)
          (unlabeledHistoryKernel k)) =
      unlabeledHistoryKernel (dynamics.descend h k) := by
  unfold unlabeledHistoryKernel
  rw [orientationRefinement_apply_balanced]
  rw [dynamics.unlabeled_endpoint_parity]
  congr 1
  exact endpointParameter_compose _ _

/-- **Unconditional causal realization.**  The concrete ordinal composition
descends to unlabeled finite causal orders, obeys orientation parity, and is
represented exactly by the proved CPTP refinement channel. -/
theorem ordinalCausalRefinement_unlabeled_realization
    (h k : UnlabeledOrientationHistory) :
    unlabeledEndpoint (ordinalCausalRefinement.descend h k) =
        endpointCompose (unlabeledEndpoint h) (unlabeledEndpoint k)
      ∧ orientationRefinementKraus.apply
          (historyKernelTensor (unlabeledHistoryKernel h)
            (unlabeledHistoryKernel k)) =
        unlabeledHistoryKernel (ordinalCausalRefinement.descend h k) := by
  exact ⟨ordinalCausalRefinement.unlabeled_endpoint_parity h k,
    ordinalCausalRefinement.channel_descends h k⟩

/-! ## 3. The orientation endpoint as a multiplicative character -/

/-- Rescale the extremal kernel parameter to its orientation sign `+1` or
`-1`. -/
def unlabeledOrientationSign (h : UnlabeledOrientationHistory) : ℝ :=
  2 * endpointParameter (unlabeledEndpoint h)

theorem endpointSign_sq_one (a : Fin 2) :
    (2 * endpointParameter a) ^ 2 = 1 := by
  fin_cases a <;> norm_num [endpointParameter]

theorem unlabeledOrientationSign_sq_one
    (h : UnlabeledOrientationHistory) :
    unlabeledOrientationSign h ^ 2 = 1 := by
  exact endpointSign_sq_one (unlabeledEndpoint h)

/-- The orientation sign is a multiplicative character of serial causal
composition.  All detailed order data is retained in the source history, while
its orientation shadow composes in the abelian group `{+1,-1}`. -/
theorem unlabeledOrientationSign_mul (h k : UnlabeledOrientationHistory) :
    unlabeledOrientationSign (ordinalCausalRefinement.descend h k) =
      unlabeledOrientationSign h * unlabeledOrientationSign k := by
  unfold unlabeledOrientationSign
  rw [ordinalCausalRefinement.unlabeled_endpoint_parity]
  rw [← endpointParameter_compose]
  unfold refinementCompose
  ring

/-- **Causal orientation character.**  Unlabeled serial composition is
associative, its sign is always binary, and that sign is multiplicative.  This
is the precise finite theorem behind the statement that orientation is a
`Z_2`-valued abelian shadow of causal composition. -/
theorem unlabeled_causal_orientation_character :
    (∀ h : UnlabeledOrientationHistory,
        unlabeledOrientationSign h ^ 2 = 1)
      ∧ (∀ h k : UnlabeledOrientationHistory,
        unlabeledOrientationSign (ordinalCausalRefinement.descend h k) =
          unlabeledOrientationSign h * unlabeledOrientationSign k)
      ∧ (∀ h k l : UnlabeledOrientationHistory,
        ordinalCausalRefinement.descend
            (ordinalCausalRefinement.descend h k) l =
          ordinalCausalRefinement.descend h
            (ordinalCausalRefinement.descend k l)) := by
  exact ⟨unlabeledOrientationSign_sq_one,
    unlabeledOrientationSign_mul,
    ordinalCausalRefinement_descend_assoc⟩

/-! ## 4. A reversible microscopic dilation -/

/-- Rectangular Kraus-to-Stinespring construction.  The output index is paired
with an environment record of which Kraus alternative occurred.  The existing
generic API treats square channels; refinement is genuinely `4 -> 2`, so the
rectangular construction is stated explicitly here. -/
def rectangularKrausDilation {m n k : ℕ}
    (K : Fin k → Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin n × Fin k) (Fin m) ℂ :=
  fun ia j => K ia.2 ia.1 j

lemma rectangularKrausDilation_dagger_self_apply {m n k : ℕ}
    (K : Fin k → Matrix (Fin n) (Fin m) ℂ) (j j' : Fin m) :
    ((rectangularKrausDilation K).conjTranspose *
      rectangularKrausDilation K) j j' =
      ∑ a, ((K a).conjTranspose * K a) j j' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_apply]
  rfl

/-- Completeness of a rectangular Kraus family is exactly isometry of its
microscopic dilation. -/
theorem rectangularKrausDilation_isIsometry {m n k : ℕ}
    (K : Fin k → Matrix (Fin n) (Fin m) ℂ)
    (complete : ∑ a, (K a).conjTranspose * K a =
      (1 : Matrix (Fin m) (Fin m) ℂ)) :
    IsIsometry (rectangularKrausDilation K) := by
  unfold IsIsometry
  ext j j'
  rw [rectangularKrausDilation_dagger_self_apply]
  have hsum : ∑ a, ((K a).conjTranspose * K a) j j' =
      (∑ a, (K a).conjTranspose * K a) j j' := by
    rw [Finset.sum_apply j Finset.univ
      (fun a => (K a).conjTranspose * K a)]
    rw [Finset.sum_apply j' Finset.univ
      (fun a => ((K a).conjTranspose * K a) j)]
  rw [hsum, complete]

lemma rectangularKrausDilation_conj_apply {m n k : ℕ}
    (K : Fin k → Matrix (Fin n) (Fin m) ℂ)
    (rho : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin n) (a : Fin k) (i' : Fin n) (a' : Fin k) :
    (rectangularKrausDilation K * rho *
      (rectangularKrausDilation K).conjTranspose) (i, a) (i', a') =
      (K a * rho * (K a').conjTranspose) i i' := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hLeft :
      (∑ j', rectangularKrausDilation K (i, a) j' * rho j' j) =
        ∑ j', K a i j' * rho j' j := by
    apply Finset.sum_congr rfl
    intro j' _
    rfl
  rw [hLeft, Matrix.conjTranspose_apply]
  change _ * star (K a' i' j) = _ * star (K a' i' j)
  rfl

/-- Tracing out the refinement record recovers the original rectangular
Kraus channel exactly. -/
theorem partialTrace_rectangularKrausDilation {m n k : ℕ}
    (K : Fin k → Matrix (Fin n) (Fin m) ℂ)
    (rho : Matrix (Fin m) (Fin m) ℂ) :
    partialTrace_right
        (rectangularKrausDilation K * rho *
          (rectangularKrausDilation K).conjTranspose) =
      ∑ a, K a * rho * (K a).conjTranspose := by
  ext i i'
  unfold partialTrace_right
  rw [Finset.sum_congr rfl (fun a _ =>
    rectangularKrausDilation_conj_apply K rho i a i' a)]
  symm
  rw [Finset.sum_apply]
  rw [Finset.sum_apply]

/-- The explicit microscopic isometry for orientation refinement.  Its input
is the four-dimensional product sector; its output is the orientation qubit
paired with a four-state refinement record. -/
def refinementDilation : Matrix (Fin 2 × Fin 4) (Fin 4) ℂ :=
  rectangularKrausDilation refinementKrausOperator

theorem refinementDilation_isIsometry :
    IsIsometry refinementDilation := by
  exact rectangularKrausDilation_isIsometry _ refinementKraus_complete

/-- The apparent irreversibility of the refinement channel is precisely the
loss of the microscopic four-state record. -/
theorem refinementDilation_recovers_channel (rho : SquareMatrix 4) :
    partialTrace_right
        (refinementDilation * rho * refinementDilation.conjTranspose) =
      orientationRefinementKraus.apply rho := by
  simpa [refinementDilation, orientationRefinementKraus,
    UnifiedTheory.LayerB.Kraus.KrausRepresentation.apply] using
    (partialTrace_rectangularKrausDilation refinementKrausOperator rho)

/-! ## 5. Microscopic endpoint amplitudes -/

abbrev DilatedOrientationKet := Matrix (Fin 2 × Fin 4) (Fin 1) ℂ

/-- A pure output orientation ket with an orthogonal environment record. -/
def recordedOutputKet (out : PathKet) (record : Fin 4) :
    DilatedOrientationKet :=
  fun ia _ => if ia.2 = record then out ia.1 0 else 0

/-- Inner product in the four-dimensional product-curvature basis. -/
def pairKetInner (measure input : PairKet) : ℂ :=
  (measure.conjTranspose * input) 0 0

/-- Rank-one measure-and-prepare action at the amplitude level. -/
theorem rankOneKraus_applyKet
    (out : PathKet) (measure input : PairKet) :
    (out * measure.conjTranspose) * input =
      pairKetInner measure input • out := by
  rw [Matrix.mul_assoc]
  ext i j
  fin_cases j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Fin.isValue,
    Matrix.smul_apply, smul_eq_mul]
  change out i 0 * pairKetInner measure input =
    pairKetInner measure input * out i 0
  ring

theorem refinementDilation_positivePositive_amplitude :
    refinementDilation * positivePositiveKet =
      recordedOutputKet negativeHolonomyKet 0 := by
  ext ia j
  obtain ⟨i, a⟩ := ia
  fin_cases j
  change (refinementKrausOperator a * positivePositiveKet) i 0 = _
  fin_cases a <;>
    simp only [refinementKrausOperator] <;>
    rw [rankOneKraus_applyKet] <;>
    fin_cases i <;>
    norm_num [recordedOutputKet, pairKetInner,
      positivePositiveKet, positiveNegativeKet,
      negativePositiveKet, negativeNegativeKet,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Fin.ext_iff,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      starRingEnd_two_complex, Complex.I_sq] <;>
    ring_nf <;>
    norm_num [Complex.I_sq] <;>
    ring

theorem refinementDilation_positiveNegative_amplitude :
    refinementDilation * positiveNegativeKet =
      recordedOutputKet positiveHolonomyKet 1 := by
  ext ia j
  obtain ⟨i, a⟩ := ia
  fin_cases j
  change (refinementKrausOperator a * positiveNegativeKet) i 0 = _
  fin_cases a <;>
    simp only [refinementKrausOperator] <;>
    rw [rankOneKraus_applyKet] <;>
    fin_cases i <;>
    norm_num [recordedOutputKet, pairKetInner,
      positivePositiveKet, positiveNegativeKet,
      negativePositiveKet, negativeNegativeKet,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Fin.ext_iff,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      starRingEnd_two_complex, Complex.I_sq] <;>
    ring_nf <;>
    norm_num [Complex.I_sq] <;>
    ring

theorem refinementDilation_negativePositive_amplitude :
    refinementDilation * negativePositiveKet =
      recordedOutputKet positiveHolonomyKet 2 := by
  ext ia j
  obtain ⟨i, a⟩ := ia
  fin_cases j
  change (refinementKrausOperator a * negativePositiveKet) i 0 = _
  fin_cases a <;>
    simp only [refinementKrausOperator] <;>
    rw [rankOneKraus_applyKet] <;>
    fin_cases i <;>
    norm_num [recordedOutputKet, pairKetInner,
      positivePositiveKet, positiveNegativeKet,
      negativePositiveKet, negativeNegativeKet,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Fin.ext_iff,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      starRingEnd_two_complex, Complex.I_sq] <;>
    ring_nf <;>
    norm_num [Complex.I_sq] <;>
    ring

theorem refinementDilation_negativeNegative_amplitude :
    refinementDilation * negativeNegativeKet =
      recordedOutputKet negativeHolonomyKet 3 := by
  ext ia j
  obtain ⟨i, a⟩ := ia
  fin_cases j
  change (refinementKrausOperator a * negativeNegativeKet) i 0 = _
  fin_cases a <;>
    simp only [refinementKrausOperator] <;>
    rw [rankOneKraus_applyKet] <;>
    fin_cases i <;>
    norm_num [recordedOutputKet, pairKetInner,
      positivePositiveKet, positiveNegativeKet,
      negativePositiveKet, negativeNegativeKet,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_four, Fin.ext_iff,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one, Fin.coe_ofNat_eq_mod, Nat.reduceMod,
      starRingEnd_two_complex, Complex.I_sq] <;>
    ring_nf <;>
    norm_num [Complex.I_sq] <;>
    ring

/-- The microscopic dilation computes the four endpoint outputs rather than
postulating them at density-matrix level.  Equal orientations produce the
negative-holonomy ket and unequal orientations the positive-holonomy ket;
the orthogonal record retains which of the four alternatives occurred. -/
theorem refinementDilation_endpoint_amplitude_truth_table :
    refinementDilation * positivePositiveKet =
        recordedOutputKet negativeHolonomyKet 0
      ∧ refinementDilation * positiveNegativeKet =
        recordedOutputKet positiveHolonomyKet 1
      ∧ refinementDilation * negativePositiveKet =
        recordedOutputKet positiveHolonomyKet 2
      ∧ refinementDilation * negativeNegativeKet =
        recordedOutputKet negativeHolonomyKet 3 :=
  ⟨refinementDilation_positivePositive_amplitude,
    refinementDilation_positiveNegative_amplitude,
    refinementDilation_negativePositive_amplitude,
    refinementDilation_negativeNegative_amplitude⟩

/-! ## 6. Frontier reduction theorem -/

/-- **Remaining-frontier reduction.**  Once a proposed labeled causal-growth
dynamics supplies the three fields of `CovariantCausalRefinement`, all of the
following are forced:

* refinement is a well-defined operation on unlabeled histories;
* its endpoint sector obeys orientation parity;
* the reversible microscopic dilation reduces to the CPTP channel;
* the channel acts on those unlabeled histories by `D_y tensor D_z -> D_(2yz)`.

Thus the physical frontier is no longer an infinite family of mixed-state
checks.  Those have a concrete causal composition and four pure endpoint
amplitudes here.  What remains is a strongly positive covariant amplitude law
on complete growth trajectories that selects this realization. -/
theorem unlabeled_refinement_frontier_reduction
    (dynamics : CovariantCausalRefinement) :
    IsIsometry refinementDilation
      ∧ (∀ rho : SquareMatrix 4,
        partialTrace_right
            (refinementDilation * rho * refinementDilation.conjTranspose) =
          orientationRefinementKraus.apply rho)
      ∧ (refinementDilation * positivePositiveKet =
          recordedOutputKet negativeHolonomyKet 0
        ∧ refinementDilation * positiveNegativeKet =
          recordedOutputKet positiveHolonomyKet 1
        ∧ refinementDilation * negativePositiveKet =
          recordedOutputKet positiveHolonomyKet 2
        ∧ refinementDilation * negativeNegativeKet =
          recordedOutputKet negativeHolonomyKet 3)
      ∧ (∀ h k : UnlabeledOrientationHistory,
        unlabeledEndpoint (dynamics.descend h k) =
          endpointCompose (unlabeledEndpoint h) (unlabeledEndpoint k)
        ∧ orientationRefinementKraus.apply
            (historyKernelTensor (unlabeledHistoryKernel h)
              (unlabeledHistoryKernel k)) =
            unlabeledHistoryKernel (dynamics.descend h k)) := by
  refine ⟨refinementDilation_isIsometry,
    refinementDilation_recovers_channel,
    refinementDilation_endpoint_amplitude_truth_table, ?_⟩
  intro h k
  exact ⟨dynamics.unlabeled_endpoint_parity h k,
    dynamics.channel_descends h k⟩

#print axioms unlabeledHistory_forgets_relabeling
#print axioms finPosetIsomorphic_causalOrdinalSum
#print axioms finPosetIsomorphic_causalOrdinalSum_assoc
#print axioms CovariantCausalRefinement.unlabeled_endpoint_parity
#print axioms CovariantCausalRefinement.channel_descends
#print axioms ordinalCausalRefinement_descend_assoc
#print axioms ordinalCausalRefinement_unlabeled_realization
#print axioms unlabeled_causal_orientation_character
#print axioms refinementDilation_isIsometry
#print axioms refinementDilation_recovers_channel
#print axioms refinementDilation_endpoint_amplitude_truth_table
#print axioms unlabeled_refinement_frontier_reduction

end

end UnifiedTheory.Audit.KFOrientationUnlabeledRefinement
