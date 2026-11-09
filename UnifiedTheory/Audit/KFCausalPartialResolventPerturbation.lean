/- A bounded perturbation of an actual partial-operator resolvent.
The inverse is constructed when the Neumann factor has norm below one;
the range and both inverse identities refer to the supplied operator graph. -/
import UnifiedTheory.Audit.KFCausalMassFormOperator
import Mathlib.Analysis.Normed.Ring.Units

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPartialResolventPerturbation
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def resolvent (R C : V →L[ℂ] V) : V →L[ℂ] V := R*Ring.inverse (1-C*R)

theorem factor_isUnit [CompleteSpace V] (R C : V →L[ℂ] V) (hn : ‖C*R‖ < 1) : IsUnit (1-C*R) :=
  isUnit_one_sub_of_norm_lt_one hn

theorem input_identity (R C : V →L[ℂ] V) (hu : IsUnit (1-C*R)) (f : V) :
    Ring.inverse (1-C*R) f-C (resolvent R C f) = f :=
  congrArg (fun T : V →L[ℂ] V => T f) (Ring.mul_inverse_cancel _ hu)

theorem resolvent_identity (R C : V →L[ℂ] V) (hu : IsUnit (1-C*R)) (f : V) :
    resolvent R C f = R (f+C (resolvent R C f)) := by
  exact congrArg (fun x : V => R x) (eq_add_of_sub_eq (input_identity R C hu f))

theorem resolvent_graph (G : V →ₗ.[ℂ] V) (R C : V →L[ℂ] V) (b : ℝ)
    (hu : IsUnit (1-C*R))
    (hg : ∀ f, (R f,b • R f-f+C (R f)) ∈ G.graph) (f : V) :
    (resolvent R C f,b • resolvent R C f-f) ∈ G.graph := by
  have he := input_identity R C hu f
  have h := hg (Ring.inverse (1-C*R) f)
  change (resolvent R C f,b • resolvent R C f-Ring.inverse (1-C*R) f+
    C (resolvent R C f)) ∈ G.graph at h
  have hv : b • resolvent R C f-Ring.inverse (1-C*R) f+C (resolvent R C f) =
      b • resolvent R C f-f := by
    calc
      _ = b • resolvent R C f-(Ring.inverse (1-C*R) f-C (resolvent R C f)) := by abel
      _ = _ := congrArg (fun z : V => b • resolvent R C f-z) he
  rw [hv] at h
  exact h

theorem resolvent_left (G : V →ₗ.[ℂ] V) (R C : V →L[ℂ] V) (b : ℝ)
    (hu : IsUnit (1-C*R))
    (hl : ∀ x : G.domain, R (b • (x:V)-G x+C x) = (x:V)) (x : G.domain) :
    resolvent R C (b • (x:V)-G x) = (x:V) := by
  have he : (1-C*R) (b • (x:V)-G x+C x) = b • (x:V)-G x := by
    change b • (x:V)-G x+C x-C (R (b • (x:V)-G x+C x)) = _
    rw [hl x,add_sub_cancel_right]
  have hi : Ring.inverse (1-C*R) (b • (x:V)-G x) = b • (x:V)-G x+C x := by
    calc
      _ = Ring.inverse (1-C*R) ((1-C*R) (b • (x:V)-G x+C x)) :=
        congrArg (fun z : V => Ring.inverse (1-C*R) z) he.symm
      _ = _ := congrArg (fun T : V →L[ℂ] V => T (b • (x:V)-G x+C x))
        (Ring.inverse_mul_cancel _ hu)
  change R (Ring.inverse (1-C*R) (b • (x:V)-G x)) = _
  rw [hi,hl x]

theorem factor_small (R C : V →L[ℂ] V) (b K : ℝ) (hb : 0 < b) (hK : 0 ≤ K)
    (hr : ∀ f, ‖R f‖ ≤ K/b*‖f‖) (hlarge : ‖C‖*K < b) : ‖C*R‖ < 1 := by
  have hn : ‖R‖ ≤ K/b := ContinuousLinearMap.opNorm_le_bound R (div_nonneg hK hb.le) hr
  calc
    ‖C*R‖ ≤ ‖C‖*‖R‖ := norm_mul_le _ _
    _ ≤ ‖C‖*(K/b) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ < 1 := by rw [← mul_div_assoc,div_lt_one hb]; exact hlarge

theorem resolvent_norm_bound [CompleteSpace V] (R C : V →L[ℂ] V) (b K : ℝ)
    (hb : 0 < b) (hK : 0 ≤ K) (hr : ∀ f, ‖R f‖ ≤ K/b*‖f‖)
    (hlarge : ‖C‖*K < b) (f : V) :
    ‖resolvent R C f‖ ≤ K/(b-‖C‖*K)*‖f‖ := by
  have hu := factor_isUnit R C (factor_small R C b K hb hK hr hlarge)
  have hbound : ‖resolvent R C f‖ ≤ K/b*(‖f‖+‖C‖*‖resolvent R C f‖) := by
    calc
      _ = ‖R (f+C (resolvent R C f))‖ := congrArg norm (resolvent_identity R C hu f)
      _ ≤ K/b*‖f+C (resolvent R C f)‖ := hr _
      _ ≤ K/b*(‖f‖+‖C‖*‖resolvent R C f‖) := mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add_right (C.le_opNorm _) _)) (div_nonneg hK hb.le)
  have hm := (le_div_iff₀ hb).mp (show ‖resolvent R C f‖ ≤
      (K*(‖f‖+‖C‖*‖resolvent R C f‖))/b by simpa only [div_mul_eq_mul_div] using hbound)
  rw [div_mul_eq_mul_div,le_div_iff₀ (sub_pos.mpr hlarge)]
  nlinarith only [hm]

theorem graph_of_eq (G : V →ₗ.[ℂ] V) (R C Z : V →L[ℂ] V) (b : ℝ)
    (hZ : Z = resolvent R C) (hu : IsUnit (1-C*R))
    (hg : ∀ f, (R f,b • R f-f+C (R f)) ∈ G.graph) (f : V) :
    (Z f,b • Z f-f) ∈ G.graph := by
  rw [hZ]
  exact resolvent_graph G R C b hu hg f

theorem left_of_eq (G : V →ₗ.[ℂ] V) (R C Z : V →L[ℂ] V) (b : ℝ)
    (hZ : Z = resolvent R C) (hu : IsUnit (1-C*R))
    (hl : ∀ x : G.domain, R (b • (x:V)-G x+C x) = (x:V)) (x : G.domain) :
    Z (b • (x:V)-G x) = (x:V) := by
  rw [hZ]
  exact resolvent_left G R C b hu hl x

theorem norm_bound_of_eq [CompleteSpace V] (R C Z : V →L[ℂ] V) (b K q : ℝ)
    (hZ : Z = resolvent R C) (hq : q = ‖C‖*K)
    (hb : 0 < b) (hK : 0 ≤ K) (hr : ∀ f, ‖R f‖ ≤ K/b*‖f‖)
    (hlarge : q < b) (f : V) : ‖Z f‖ ≤ K/(b-q)*‖f‖ := by
  rw [hZ,hq]
  exact resolvent_norm_bound R C b K hb hK hr (hq ▸ hlarge) f

theorem left_graph_of_eq (G : V →ₗ.[ℂ] V) (R C Z : V →L[ℂ] V) (b : ℝ)
    (hZ : Z = resolvent R C) (hu : IsUnit (1-C*R))
    (hl : ∀ x y, (x,y) ∈ G.graph → R (b • x-y+C x) = x)
    (x y : V) (hxy : (x,y) ∈ G.graph) : Z (b • x-y) = x := by
  obtain ⟨hx,hval⟩ := (KFCausalMassFormOperator.graph_domain_iff G x y).mp hxy
  have hleft (w : G.domain) : R (b • (w:V)-G w+C w) = w := hl w (G w) (G.mem_graph w)
  simpa only [hval] using left_of_eq G R C Z b hZ hu hleft ⟨x,hx⟩

#print axioms factor_isUnit
#print axioms input_identity
#print axioms resolvent_identity
#print axioms resolvent_graph
#print axioms resolvent_left
#print axioms factor_small
#print axioms resolvent_norm_bound
#print axioms graph_of_eq
#print axioms left_of_eq
#print axioms norm_bound_of_eq
#print axioms left_graph_of_eq
end
end UnifiedTheory.Audit.KFCausalPartialResolventPerturbation
