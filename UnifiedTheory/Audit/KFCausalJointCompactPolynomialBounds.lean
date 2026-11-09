/- Polynomial majorants uniform over a compact parameter set. These
bounds retain arbitrary finite degrees and supply spatial integrability. -/
import UnifiedTheory.Audit.KFCausalClusteredClockDerivativeLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointCompactPolynomialBounds
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)

abbrev RPoly := MvPolynomial (Fin 4) ℝ
def coords (p : Joint) : Fin 4 → ℝ := ![p.1.1,p.1.2 0,p.1.2 1,p.2]
def val (Q : RPoly) (p : Joint) : ℝ := MvPolynomial.eval (coords p) Q

def Controlled {X : Type*} (K : Set X) (f : X → Joint → ℂ) : Prop :=
  ∃ Q : RPoly, (∀ p, 0 ≤ val Q p) ∧ ∀ s ∈ K, ∀ p, ‖f s p‖ ≤ val Q p

theorem controlled_const {X : Type*} (K : Set X) (c : ℂ) :
    Controlled K (fun _ _ => c) := by
  refine ⟨MvPolynomial.C ‖c‖, ?_, ?_⟩
  · intro p; simp [val]
  · intro s _ p; simp [val]

theorem controlled_coefficient {X : Type*} [TopologicalSpace X] (K : Set X)
    (hK : IsCompact K) (f : X → ℂ) (hf : ContinuousOn f K) :
    Controlled K (fun s _ => f s) := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨MvPolynomial.C (max 0 M), ?_, ?_⟩
  · intro p; simp [val]
  · intro s hs p; simpa [val] using (hM s hs).trans (le_max_right 0 M)

theorem controlled_coordinate {X : Type*} (K : Set X) (i : Fin 4) :
    Controlled K (fun _ p => (coords p i:ℂ)) := by
  refine ⟨1+MvPolynomial.X i^2, ?_, ?_⟩
  · intro p; simp only [val,map_add,map_one,map_pow,MvPolynomial.eval_X]; positivity
  · intro s _ p
    simp only [val,map_add,map_one,map_pow,MvPolynomial.eval_X,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [sq_nonneg (|coords p i|-1),sq_abs (coords p i)]

theorem Controlled.add {X : Type*} {K : Set X} {f g : X → Joint → ℂ}
    (hf : Controlled K f) (hg : Controlled K g) : Controlled K (fun s p => f s p+g s p) := by
  obtain ⟨Q,hQ,hf⟩ := hf
  obtain ⟨R,hR,hg⟩ := hg
  refine ⟨Q+R,fun p => ?_,fun s hs p => ?_⟩
  · simpa only [val,map_add] using add_nonneg (hQ p) (hR p)
  · simpa only [val,map_add] using (norm_add_le _ _).trans (add_le_add (hf s hs p) (hg s hs p))

theorem Controlled.mul {X : Type*} {K : Set X} {f g : X → Joint → ℂ}
    (hf : Controlled K f) (hg : Controlled K g) : Controlled K (fun s p => f s p*g s p) := by
  obtain ⟨Q,hQ,hf⟩ := hf
  obtain ⟨R,hR,hg⟩ := hg
  refine ⟨Q*R,fun p => ?_,fun s hs p => ?_⟩
  · simpa only [val,map_mul] using mul_nonneg (hQ p) (hR p)
  · rw [norm_mul]
    simpa only [val,map_mul] using mul_le_mul (hf s hs p) (hg s hs p) (norm_nonneg _) (hQ p)

theorem Controlled.neg {X : Type*} {K : Set X} {f : X → Joint → ℂ}
    (hf : Controlled K f) : Controlled K (fun s p => -f s p) := by
  obtain ⟨Q,hQ,hf⟩ := hf
  exact ⟨Q,hQ,fun s hs p => (norm_neg _).trans_le (hf s hs p)⟩

theorem Controlled.pow {X : Type*} {K : Set X} {f : X → Joint → ℂ}
    (hf : Controlled K f) (n : ℕ) : Controlled K (fun s p => f s p^n) := by
  obtain ⟨Q,hQ,hf⟩ := hf
  refine ⟨Q^n,fun p => ?_,fun s hs p => ?_⟩
  · simpa only [val,map_pow] using pow_nonneg (hQ p) n
  · rw [norm_pow]
    simpa only [val,map_pow] using pow_le_pow_left₀ (norm_nonneg _) (hf s hs p) n

theorem controlled_sum {X ι : Type*} (K : Set X) (I : Finset ι) (f : ι → X → Joint → ℂ)
    (hf : ∀ i ∈ I, Controlled K (f i)) : Controlled K (fun s p => ∑ i ∈ I, f i s p) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using controlled_const K 0
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i I)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem Controlled.eval {X : Type*} {K : Set X} {f : X → Joint → ℂ}
    (hf : Controlled K f) (P : Polynomial ℂ) : Controlled K (fun s p => P.eval (f s p)) := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  exact controlled_sum K P.support _ (fun i _ => (controlled_const K (P.coeff i)).mul (hf.pow i))

theorem val_complex (Q : RPoly) (p : Joint) :
    MvPolynomial.eval (KFCausalJointPolynomialIntegrability.coordinates p)
      (MvPolynomial.map Complex.ofRealHom Q) = (val Q p:ℂ) := by
  rw [MvPolynomial.eval_map]
  have he : KFCausalJointPolynomialIntegrability.coordinates p = Complex.ofRealHom ∘ coords p := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact (MvPolynomial.eval₂_comp_left Complex.ofRealHom (RingHom.id ℝ) (coords p) Q).symm

theorem val_squared_integrable (Q : RPoly) (a c d l m : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    Integrable (fun p => val Q p^2*KFCausalJointPolynomialIntegrability.weight a c d l m p) jointMeasure := by
  have hi := KFCausalJointPolynomialIntegrability.squared_polynomial_integrable a c d l m ha hc hd
    (MvPolynomial.map Complex.ofRealHom Q)
  simpa only [val_complex,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hi

#print axioms controlled_const
#print axioms controlled_coefficient
#print axioms controlled_coordinate
#print axioms Controlled.add
#print axioms Controlled.mul
#print axioms Controlled.neg
#print axioms Controlled.pow
#print axioms controlled_sum
#print axioms Controlled.eval
#print axioms val_complex
#print axioms val_squared_integrable
end
end UnifiedTheory.Audit.KFCausalJointCompactPolynomialBounds
