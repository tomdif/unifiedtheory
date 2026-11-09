/- The actual Hilbert span of sourced charged-coordinate polynomial
Gaussians is invariant under all four original transverse momenta.
Every derivative representative and its L2 membership is constructed. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMonomialDerivative
import UnifiedTheory.Audit.KFCausalChargeProfileMomentumGraph
import UnifiedTheory.Audit.KFCausalAntisymmetricMomentumGraphEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialMomentum
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalPhysicalTransverseMomentum (transverseMomentum)
open KFCausalSymmetricMomentumCoordinates (symmetricDirection)
open KFCausalAntisymmetricMomentumCoordinates (antiDirection antiSymbol)
open KFCausalIndependentRadialCoordinateMoments (coordinate profile monomial_memLp)
open KFCausalIndependentRadialMonomialDerivative (positionIndex profile_raise profile_derivative)
open KFCausalIndependentRadialKineticProfiles (coefficient neutral)
open KFCausalFiniteMonomialDerivative (lower raise)
open KFCausalNeutralLinePackets (step)
open KFCausalPairedModeCoordinates (scale)

variable (α β wL wR c : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : 0 < wL) (hR : 0 < wR)
  (hmatch : Real.pi^2/α=α*c^2) (b : ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume)

def state (P : Polynomial ℂ) (n : Fin 4 → ℕ) : Hilbert := chargeCoordinates.symm
  ((monomial_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg n).toLp
    (profile α β wL wR c b P g n))

theorem state_charge_coe (P : Polynomial ℂ) (n : Fin 4 → ℕ) :
    chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P n)=ᵐ[volume]
      profile α β wL wR c b P g n := by
  simp only [state,LinearIsometryEquiv.apply_symm_apply]
  exact (monomial_memLp α β wL wR c hα hβ hL hR hmatch b P g hc hg n).coeFn_toLp

def space : Submodule ℂ Hilbert := Submodule.span ℂ (Set.range
  (fun q : Polynomial ℂ × (Fin 4 → ℕ) => state α β wL wR c hα hβ hL hR hmatch b g hc hg q.1 q.2))

theorem state_mem (P : Polynomial ℂ) (n : Fin 4 → ℕ) :
    state α β wL wR c hα hβ hL hR hmatch b g hc hg P n ∈
      space α β wL wR c hα hβ hL hR hmatch b g hc hg :=
  Submodule.subset_span ⟨(P,n),rfl⟩

def derivativeState (P : Polynomial ℂ) (n : Fin 4 → ℕ) (i : Fin 2) : Hilbert :=
  (2*(scale:ℂ)*(n (positionIndex i):ℂ)) •
      state α β wL wR c hα hβ hL hR hmatch b g hc hg P (lower n (positionIndex i))+
    coefficient α wL wR i • state α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n (positionIndex i))+
    (neutral i:ℂ) • state α β wL wR c hα hβ hL hR hmatch b g hc hg (step β b P) n

theorem derivativeState_coe (P : Polynomial ℂ) (n : Fin 4 → ℕ) (i : Fin 2) :
    chargeCoordinates (derivativeState α β wL wR c hα hβ hL hR hmatch b g hc hg P n i)=ᵐ[volume]
      fun x => (2*(scale:ℂ)*(n (positionIndex i):ℂ))*profile α β wL wR c b P g (lower n (positionIndex i)) x+
        coefficient α wL wR i*profile α β wL wR c b P g (raise n (positionIndex i)) x+
        (neutral i:ℂ)*profile α β wL wR c b (step β b P) g n x := by
  unfold derivativeState
  simp only [map_add,map_smul]
  let u := chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (lower n (positionIndex i)))
  let v := chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n (positionIndex i)))
  let w := chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg (step β b P) n)
  let A := 2*(scale:ℂ)*(n (positionIndex i):ℂ)
  let B := coefficient α wL wR i
  let N := (neutral i:ℂ)
  filter_upwards [Lp.coeFn_add (A • u+B • v) (N • w),Lp.coeFn_add (A • u) (B • v),
    Lp.coeFn_smul A u,Lp.coeFn_smul B v,Lp.coeFn_smul N w,
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (lower n (positionIndex i)),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n (positionIndex i)),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg (step β b P) n]
      with x hsum hpair hA hB hN hl hr hn
  change (A • u+B • v+N • w) x=_
  rw [hsum]
  simp only [Pi.add_apply]
  rw [hpair]
  simp only [Pi.add_apply]
  rw [hA,hB,hN]
  simp only [Pi.smul_apply,smul_eq_mul]
  change A*(chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (lower n (positionIndex i)))) x+
    B*(chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n (positionIndex i)))) x+
    N*(chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg (step β b P) n)) x=_
  rw [hl,hr,hn]

theorem derivativeState_mem (P : Polynomial ℂ) (n : Fin 4 → ℕ) (i : Fin 2) :
    derivativeState α β wL wR c hα hβ hL hR hmatch b g hc hg P n i ∈
      space α β wL wR c hα hβ hL hR hmatch b g hc hg := by
  apply Submodule.add_mem
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
      (Submodule.smul_mem _ _ (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  · exact Submodule.smul_mem _ _ (state_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem symmetric_state_graph (h : ℝ) (hh : h ≠ 0) (P : Polynomial ℂ) (n : Fin 4 → ℕ) (i : Fin 2) :
    (state α β wL wR c hα hβ hL hR hmatch b g hc hg P n,
      (-Complex.I*(h:ℂ)) • derivativeState α β wL wR c hα hβ hL hR hmatch b g hc hg P n i) ∈
        (transverseMomentum h (symmetricDirection i)).graph :=
  KFCausalChargeProfileMomentumGraph.derivative_graph h hh i _ _ _ _
    (state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P n)
    (derivativeState_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P n i)
    (profile_derivative α β wL wR c b P g n i)

theorem symmetric_invariant (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg) :
    ∃ d : Hilbert, d ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg ∧
      (f,d) ∈ (transverseMomentum h (symmetricDirection i)).graph := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨P,n⟩,rfl⟩ := hf
      exact ⟨_,Submodule.smul_mem _ _ (derivativeState_mem α β wL wR c hα hβ hL hR hmatch b g hc hg P n i),
        symmetric_state_graph α β wL wR c hα hβ hL hR hmatch b g hc hg h hh P n i⟩
  | zero => exact ⟨0,Submodule.zero_mem _,(transverseMomentum h (symmetricDirection i)).graph.zero_mem⟩
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      obtain ⟨d₁,hd₁,hg₁⟩ := hf₁
      obtain ⟨d₂,hd₂,hg₂⟩ := hf₂
      exact ⟨d₁+d₂,Submodule.add_mem _ hd₁ hd₂,(transverseMomentum h (symmetricDirection i)).graph.add_mem hg₁ hg₂⟩
  | smul z f _ hf =>
      obtain ⟨d,hd,hfg⟩ := hf
      exact ⟨z • d,Submodule.smul_mem _ z hd,(transverseMomentum h (symmetricDirection i)).graph.smul_mem z hfg⟩

private theorem scale_ne_zero (α c : ℝ) (hα : 0 < α) (hmatch : Real.pi^2/α=α*c^2) : c ≠ 0 := by
  intro he
  simp only [he,zero_pow (by decide : 2 ≠ 0),mul_zero] at hmatch
  exact (div_pos (sq_pos_of_pos Real.pi_pos) hα).ne' hmatch

theorem antisymmetric_state_graph (h : ℝ) (hh : h ≠ 0) (P : Polynomial ℂ) (n : Fin 4 → ℕ) (i : Fin 2) :
    (state α β wL wR c hα hβ hL hR hmatch b g hc hg P n,
      ((2*Real.pi*h*(2*scale)/c:ℝ):ℂ) •
        state α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n i.castSucc.castSucc)) ∈
      (transverseMomentum h (antiDirection i)).graph := by
  apply (KFCausalAntisymmetricMomentumGraphEquivalence.antisymmetric_graph_iff h hh i _ _).mpr
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul ((2*Real.pi*h*(2*scale)/c:ℝ):ℂ)
    (chargeCoordinates (state α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n i.castSucc.castSucc))),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P (raise n i.castSucc.castSucc),
    state_charge_coe α β wL wR c hα hβ hL hR hmatch b g hc hg P n] with x hs hr hn
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hr,hn,profile_raise]
  have hc0 := scale_ne_zero α c hα hmatch
  have he : (2*Real.pi*h*(2*scale)/c)*coordinate c x i.castSucc.castSucc=antiSymbol h i x := by
    have hi : coordinate c x i.castSucc.castSucc=c*x (.inl i) := by
      fin_cases i <;> rfl
    rw [hi]
    unfold antiSymbol
    field_simp
  rw [← mul_assoc,← Complex.ofReal_mul,he]

theorem antisymmetric_invariant (h : ℝ) (hh : h ≠ 0) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg) :
    ∃ d : Hilbert, d ∈ space α β wL wR c hα hβ hL hR hmatch b g hc hg ∧
      (f,d) ∈ (transverseMomentum h (antiDirection i)).graph := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨⟨P,n⟩,rfl⟩ := hf
      exact ⟨_,Submodule.smul_mem _ _ (state_mem α β wL wR c hα hβ hL hR hmatch b g hc hg P _),
        antisymmetric_state_graph α β wL wR c hα hβ hL hR hmatch b g hc hg h hh P n i⟩
  | zero => exact ⟨0,Submodule.zero_mem _,(transverseMomentum h (antiDirection i)).graph.zero_mem⟩
  | add f₁ f₂ _ _ hf₁ hf₂ =>
      obtain ⟨d₁,hd₁,hg₁⟩ := hf₁
      obtain ⟨d₂,hd₂,hg₂⟩ := hf₂
      exact ⟨d₁+d₂,Submodule.add_mem _ hd₁ hd₂,(transverseMomentum h (antiDirection i)).graph.add_mem hg₁ hg₂⟩
  | smul z f _ hf =>
      obtain ⟨d,hd,hfg⟩ := hf
      exact ⟨z • d,Submodule.smul_mem _ z hd,(transverseMomentum h (antiDirection i)).graph.smul_mem z hfg⟩

#print axioms state_charge_coe
#print axioms state_mem
#print axioms derivativeState_coe
#print axioms derivativeState_mem
#print axioms symmetric_state_graph
#print axioms symmetric_invariant
#print axioms antisymmetric_state_graph
#print axioms antisymmetric_invariant
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPolynomialMomentum
