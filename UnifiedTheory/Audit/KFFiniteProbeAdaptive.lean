/-
  Audit/KFFiniteProbeAdaptive.lean

  Optional adaptive extension of the finite-probe code ledger.  The only
  conclusion is an information bound: a depth-`d` adaptive strategy with a
  finite response alphabet can identify at most `|Response|^d` candidates.

  Zero sorry. Zero custom axioms.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFFiniteProbeAdaptive

universe uP uR uC

/-- A fixed-depth adaptive probe tree.  A later probe may depend on all
responses encountered on the earlier path. -/
inductive AdaptiveProbeTree
    (Probe : Type uP) (Response : Type uR) (Candidate : Type uC) :
    ℕ → Type (max uP uR uC)
  | leaf (answer : Candidate) : AdaptiveProbeTree Probe Response Candidate 0
  | query {depth : ℕ} (probe : Probe)
      (next : Response → AdaptiveProbeTree Probe Response Candidate depth) :
      AdaptiveProbeTree Probe Response Candidate (depth + 1)

namespace AdaptiveProbeTree

variable {Probe : Type uP} {Response : Type uR} {Candidate : Type uC}

def decode (observe : Candidate → Probe → Response) :
    {depth : ℕ} → AdaptiveProbeTree Probe Response Candidate depth →
      Candidate → Candidate
  | 0, leaf answer, _ => answer
  | _ + 1, query probe next, candidate =>
      decode observe (next (observe candidate probe)) candidate

/-- The response transcript generated along the candidate-dependent path. -/
def transcript (observe : Candidate → Probe → Response) :
    {depth : ℕ} → AdaptiveProbeTree Probe Response Candidate depth →
      Candidate → Fin depth → Response
  | 0, leaf _, _ => fun p => Fin.elim0 p
  | _ + 1, query probe next, candidate =>
      Fin.cases (observe candidate probe)
        (transcript observe (next (observe candidate probe)) candidate)

def Identifies {depth : ℕ}
    (T : AdaptiveProbeTree Probe Response Candidate depth)
    (observe : Candidate → Probe → Response) : Prop :=
  ∀ candidate, T.decode observe candidate = candidate

theorem decode_eq_of_transcript_eq
    (observe : Candidate → Probe → Response)
    {depth : ℕ} (T : AdaptiveProbeTree Probe Response Candidate depth)
    {a b : Candidate}
    (h : T.transcript observe a = T.transcript observe b) :
    T.decode observe a = T.decode observe b := by
  induction T with
  | leaf answer => rfl
  | @query depth probe next ih =>
      have hhead : observe a probe = observe b probe := by
        simpa [transcript] using congrFun h (0 : Fin (depth + 1))
      have htail :
          (next (observe b probe)).transcript observe a =
            (next (observe b probe)).transcript observe b := by
        funext p
        have hp := congrFun h p.succ
        simpa [transcript, hhead] using hp
      simpa [decode, hhead] using ih (observe b probe) htail

theorem transcript_injective_of_identifies
    (observe : Candidate → Probe → Response)
    {depth : ℕ} (T : AdaptiveProbeTree Probe Response Candidate depth)
    (hidentifies : T.Identifies observe) :
    Function.Injective (T.transcript observe) := by
  intro a b htranscript
  calc
    a = T.decode observe a := (hidentifies a).symm
    _ = T.decode observe b := T.decode_eq_of_transcript_eq observe htranscript
    _ = b := hidentifies b

/-- A depth-`d` adaptive strategy over a finite response alphabet identifies
at most `|Response|^d` candidates. -/
theorem candidate_card_le_response_card_pow_depth
    [Fintype Candidate] [Fintype Response]
    (observe : Candidate → Probe → Response)
    {depth : ℕ} (T : AdaptiveProbeTree Probe Response Candidate depth)
    (hidentifies : T.Identifies observe) :
    Fintype.card Candidate ≤ Fintype.card Response ^ depth := by
  classical
  calc
    Fintype.card Candidate ≤ Fintype.card (Fin depth → Response) :=
      Fintype.card_le_of_injective (T.transcript observe)
        (T.transcript_injective_of_identifies observe hidentifies)
    _ = Fintype.card Response ^ depth := by simp

#print axioms decode_eq_of_transcript_eq
#print axioms transcript_injective_of_identifies
#print axioms candidate_card_le_response_card_pow_depth

end AdaptiveProbeTree

end UnifiedTheory.Audit.KFFiniteProbeAdaptive
