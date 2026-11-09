/- Uniform physical graph operators from pointwise uniform lifted outputs,
Banach-Steinhaus and the proved embedded adjoint estimate. -/
import UnifiedTheory.Audit.KFCausalLiftedToPhysicalDomain
import UnifiedTheory.Audit.KFCausalUniformEmbeddedOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalUniformPhysicalGraphAssembly
noncomputable section
variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_uniform_graph (J : V →L[ℂ] H) (hJi : Function.Injective J) (hJd : DenseRange J)
    (M A₀ P : V →L[ℂ] V) (A : ι → V →L[ℂ] V)
    (L₀ : V →ₗ.[ℂ] V) (L : ι → V →ₗ.[ℂ] V) (T : ι → H →ₗ.[ℂ] H)
    (U : ι → H →L[ℂ] H) (R : H →L[ℂ] H) (f : ι → V →ₗ[ℂ] V) (a : ℝ)
    (hM : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (hA₀ : ∀ x y, inner ℂ (A₀ x) y = inner ℂ x (A₀ y))
    (hA : ∀ t x y, inner ℂ (A t x) y = inner ℂ x (A t y))
    (hAP : ∀ x, A₀ (P x) = x) (hLi : ∀ t, (L t).IsClosed) (hT : ∀ t, (T t).IsClosed)
    (hshift : ∀ t x y, (x,y) ∈ (L t).graph → M (a • x+y) = A t x)
    (hphysical : ∀ t x y, (x,y) ∈ (L t).graph → (J x,J y) ∈ (T t).graph)
    (hinit : ∀ v, P (M v) ∈ L₀.domain)
    (hlb : ∀ x : L₀.domain, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ∃ v,
      ‖v‖ ≤ C ∧ (f t x,v) ∈ (L t).graph)
    (hfb : ∀ x, ∃ C : ℝ, ∀ t, ‖f t x‖ ≤ C)
    (hAb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖A t‖ ≤ C)
    (hUb : ∀ t, ‖U t‖ ≤ 1)
    (he : ∀ t x, J (f t x) = U t (J x)) (hR : ∀ v, R (J v) = J (P (M v))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ E : ι → H →L[ℂ] H,
      (∀ t, ‖E t‖ ≤ C) ∧ ∀ t v, (U t (R v),E t v) ∈ (T t).graph := by
  choose F hF using fun t => KFCausalClosedGraphLift.exists_bounded_lift J hJi (U t) (f t) (he t)
  have hFb : ∀ x, ∃ C : ℝ, ∀ t, ‖F t x‖ ≤ C := by simpa only [hF] using hfb
  obtain ⟨N,hN,hFN⟩ := KFCausalUniformEmbeddedOperators.uniform_opNorm F hFb
  let K (t : ι) := (F t).comp (P.comp M)
  have hK (t : ι) (v : V) : K t v ∈ (L t).domain := by
    obtain ⟨_,_,hb⟩ := hlb ⟨P (M v),hinit v⟩
    obtain ⟨y,_,hy⟩ := hb t
    simpa only [K,ContinuousLinearMap.comp_apply,hF] using LinearPMap.mem_domain_of_mem_graph hy
  choose B hB using fun t => KFCausalClosedGraphLift.closed_action (L t) (hLi t) (K t) (hK t)
  have hBb (v : V) : ∃ C : ℝ, ∀ t, ‖B t v‖ ≤ C := by
    obtain ⟨C,_,hb⟩ := hlb ⟨P (M v),hinit v⟩
    refine ⟨C,fun t => ?_⟩
    obtain ⟨y,hy,hyg⟩ := hb t
    have heq : B t v = y := (L t).mem_graph_snd_inj' (hB t v) hyg (hF t (P (M v)))
    simpa only [heq] using hy
  let W (t : ι) : V →L[ℂ] V := a • K t+B t
  have hWb (v : V) : ∃ C : ℝ, ∀ t, ‖W t v‖ ≤ C := by
    obtain ⟨C,hC⟩ := hfb (P (M v))
    obtain ⟨D,hD⟩ := hBb v
    refine ⟨‖a‖*C+D,fun t => ?_⟩
    change ‖a • F t (P (M v))+B t v‖ ≤ _
    apply (norm_add_le _ _).trans
    rw [norm_smul,hF]
    exact add_le_add (mul_le_mul_of_nonneg_left (hC t) (norm_nonneg _)) (hD t)
  obtain ⟨NW,hNW,hWN⟩ := KFCausalUniformEmbeddedOperators.uniform_opNorm W hWb
  obtain ⟨NA,hNA,hAN⟩ := hAb
  let S (t : ι) : V →L[ℂ] V := P*(F t).adjoint*A t
  have hSN (t : ι) : ‖S t‖ ≤ ‖P‖*N*NA :=
    KFCausalUniformEmbeddedOperators.adjoint_composition_bound P (F t) (A t) N NA hN (hFN t) (hAN t)
  have hP := KFCausalLiftedToPhysicalDomain.inverse_pairing A₀ P hAP hA₀
  have hpair (t : ι) (v w : V) : inner ℂ (J (W t v)) (J w) = inner ℂ (J v) (J (S t w)) := by
    have hMW : M (W t v) = A t (K t v) := hshift t (K t v) (B t v) (hB t v)
    calc
      inner ℂ (J (W t v)) (J w) = inner ℂ (M (W t v)) w := (hM _ _).symm
      _ = inner ℂ (A t (K t v)) w := by rw [hMW]
      _ = inner ℂ (K t v) (A t w) := hA t _ _
      _ = inner ℂ (P (M v)) ((F t).adjoint (A t w)) := ((F t).adjoint_inner_right _ _).symm
      _ = inner ℂ (M v) (S t w) := hP _ _
      _ = inner ℂ (J v) (J (S t w)) := hM _ _
  choose E hE using fun t => KFCausalEmbeddedGraphExtension.exists_extension J hJd (W t) (S t) (hpair t)
  let C := Real.sqrt ((‖P‖*N*NA)*NW)
  have hEN (t : ι) : ‖E t‖ ≤ C :=
    KFCausalUniformEmbeddedOperators.embedded_opNorm J hJd (W t) (S t) (E t) (hpair t) (hE t)
      NW (‖P‖*N*NA) hNW (by positivity) (hWN t) (hSN t)
  let D (t : ι) : H →L[ℂ] H := E t-a • (U t*R)
  have hDN (t : ι) : ‖D t‖ ≤ C+‖a‖*‖R‖ := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul]
    apply add_le_add (hEN t)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hn : ‖U t‖*‖R‖ ≤ ‖R‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hUb t) (norm_nonneg R)
    exact (norm_mul_le _ _).trans hn
  have hg (t : ι) (v : V) : (U t (R (J v)),D t (J v)) ∈ (T t).graph := by
    have hstate : U t (R (J v)) = J (K t v) := by rw [hR,← he,← hF]; rfl
    change (U t (R (J v)),E t (J v)-a • U t (R (J v))) ∈ (T t).graph
    rw [hstate,hE]
    have hout : J (W t v)-a • J (K t v) = J (B t v) := by
      change J (a • K t v+B t v)-a • J (K t v) = J (B t v)
      rw [map_add,ContinuousLinearMap.map_smul_of_tower]
      abel
    rw [hout]
    exact hphysical t _ _ (hB t v)
  refine ⟨C+‖a‖*‖R‖,by positivity,D,hDN,fun t => ?_⟩
  exact KFCausalEmbeddedGraphExtension.closed_graph_extension J hJd (T t) (hT t) ((U t).comp R) (D t) (hg t)

#print axioms exists_uniform_graph
end
end UnifiedTheory.Audit.KFCausalUniformPhysicalGraphAssembly
