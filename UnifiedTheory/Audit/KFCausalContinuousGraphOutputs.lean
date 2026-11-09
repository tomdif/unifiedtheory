/- Continuity of physical Hamiltonian outputs from bounded lifted graphs
and a continuous mass-applied output, extended to all physical inputs. -/
import UnifiedTheory.Audit.KFCausalMassOutputContinuity
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalContinuousGraphOutputs
noncomputable section
variable {V H X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace X]

theorem continuous_output (J : V →L[ℂ] H) (M : V →L[ℂ] V) (Q : X → V →L[ℂ] V)
    (L : X → V →ₗ.[ℂ] V) (T : X → H →ₗ.[ℂ] H) (u : X → V) (e : X → H)
    (hm : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (hL : ∀ t x y, (x,y) ∈ (L t).graph → Q t x = M y)
    (hp : ∀ t x y, (x,y) ∈ (L t).graph → (J x,J y) ∈ (T t).graph)
    (he : ∀ t, (J (u t),e t) ∈ (T t).graph)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∃ v, ‖v‖ ≤ C ∧ (u t,v) ∈ (L t).graph)
    (hc : Continuous (fun t => Q t (u t))) : Continuous e := by
  obtain ⟨C,_,hb⟩ := hb
  choose v hv hg using hb
  have hmass (t : X) : M (v t) = Q t (u t) := (hL t _ _ (hg t)).symm
  have hmc : Continuous (fun t => M (v t)) := by simpa only [hmass] using hc
  have hjc := KFCausalMassOutputContinuity.continuous_embedding J M hm v C hv hmc
  have heq : e = fun t => J (v t) := funext (fun t =>
    (T t).mem_graph_snd_inj' (he t) (hp t _ _ (hg t)) rfl)
  simpa only [heq] using hjc

theorem augment_uniform_graph (J : V →L[ℂ] H) (hJ : DenseRange J)
    (M K : V →L[ℂ] V) (Q : X → V →L[ℂ] V) (f : X → V → V)
    (L : X → V →ₗ.[ℂ] V) (T : X → H →ₗ.[ℂ] H) (U : X → H →L[ℂ] H) (R : H →L[ℂ] H)
    (hm : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (hL : ∀ t x y, (x,y) ∈ (L t).graph → Q t x = M y)
    (hp : ∀ t x y, (x,y) ∈ (L t).graph → (J x,J y) ∈ (T t).graph)
    (hi : ∀ t v, U t (R (J v)) = J (f t (K v)))
    (hb : ∀ v, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∃ w, ‖w‖ ≤ C ∧ (f t (K v),w) ∈ (L t).graph)
    (hc : ∀ v, Continuous (fun t => Q t (f t (K v))))
    (hE : ∃ C : ℝ, 0 ≤ C ∧ ∃ E : X → H →L[ℂ] H,
      (∀ t, ‖E t‖ ≤ C) ∧ ∀ t v, (U t (R v),E t v) ∈ (T t).graph) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : X → H →L[ℂ] H,
      (∀ t, ‖E t‖ ≤ C) ∧ (∀ t v, (U t (R v),E t v) ∈ (T t).graph) ∧
      ∀ v, Continuous (fun t => E t v) := by
  obtain ⟨C,hC,E,hN,hg⟩ := hE
  refine ⟨C,hC,E,hN,hg,?_⟩
  apply KFCausalMassOutputContinuity.continuous_of_dense J hJ E C hC hN
  intro v
  exact continuous_output J M Q L T (fun t => f t (K v)) (fun t => E t (J v)) hm hL hp
    (fun t => by simpa only [hi] using hg t (J v)) (hb v) (hc v)

theorem intertwining (J : V →L[ℂ] H) (U R : H →L[ℂ] H) (K : V →L[ℂ] V)
    (f : V → V) (hR : ∀ v, R (J v) = J (K v)) (hf : ∀ v, U (J v) = J (f v))
    (v : V) : U (R (J v)) = J (f (K v)) := by rw [hR,hf]

theorem continuous_domain_curve (T₀ : H →ₗ.[ℂ] H) (T : ℝ → H →ₗ.[ℂ] H)
    (U : ℝ → H →L[ℂ] H) (R : H →L[ℂ] H) (I : Set ℝ) (c : ℂ)
    (hleft : ∀ x : T₀.domain, R ((x:H)+T₀ x) = (x:H))
    (hd : ∀ t ∈ I, ∀ x : T₀.domain, ∃ hx : U t x ∈ (T t).domain,
      HasDerivAt (fun r => U r x) (c • T t ⟨U t x,hx⟩) t)
    (hE : ∃ C : ℝ, 0 ≤ C ∧ ∃ E : I → H →L[ℂ] H,
      (∀ t, ‖E t‖ ≤ C) ∧ (∀ t : I, ∀ v, (U t (R v),E t v) ∈ (T t).graph) ∧
      ∀ v, Continuous (fun t => E t v)) (x : T₀.domain) :
    ∃ y : I → H, Continuous y ∧ ∀ t : I,
      (U t x,y t) ∈ (T t).graph ∧ HasDerivAt (fun r => U r x) (c • y t) t := by
  obtain ⟨_,_,E,_,hg,hc⟩ := hE
  refine ⟨fun t => E t ((x:H)+T₀ x),hc _,fun t => ?_⟩
  have hp : (U t x,E t ((x:H)+T₀ x)) ∈ (T t).graph := by simpa only [hleft] using hg t ((x:H)+T₀ x)
  refine ⟨hp,?_⟩
  obtain ⟨hx,hdx⟩ := hd t t.property x
  have he : T t ⟨U t x,hx⟩ = E t ((x:H)+T₀ x) :=
    (T t).mem_graph_snd_inj' ((T t).mem_graph ⟨U t x,hx⟩) hp rfl
  exact hdx.congr_deriv (congrArg (fun z : H => c • z) he)

theorem derivative_continuous (f : ℝ → H) (I : Set ℝ) (c : ℂ)
    (hy : ∃ y : I → H, Continuous y ∧ ∀ t : I, HasDerivAt f (c • y t) t) :
    Continuous (fun t : I => deriv f t) := by
  obtain ⟨y,hc,hd⟩ := hy
  have he : (fun t : I => deriv f t) = fun t => c • y t := funext (fun t => (hd t).deriv)
  rw [he]
  exact continuous_const.smul hc

#print axioms continuous_output
#print axioms augment_uniform_graph
#print axioms intertwining
#print axioms continuous_domain_curve
#print axioms derivative_continuous
end
end UnifiedTheory.Audit.KFCausalContinuousGraphOutputs
