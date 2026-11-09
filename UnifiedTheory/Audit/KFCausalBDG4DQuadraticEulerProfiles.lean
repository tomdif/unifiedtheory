import UnifiedTheory.Audit.KFCausalBDG4DCompactSymmetricTensor

/- Actual compact quadratic profiles and their Euler companions. The cutoff
is retained exactly; only their origin jets are homogeneous quadratic jets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DQuadraticEulerProfiles
noncomputable section
open MeasureTheory Real Set Filter Topology
open scoped BigOperators
open KFCausalBDG4DCompactTensorFactors KFCausalBDG4DCompactSymmetricTensor
open KFCausalMinkowski4DMoments (f4D)

def terms (A B : ℝ) : Fin 2 → Term :=
  ![⟨A,polynomial 0,polynomial 2⟩,⟨B/2,polynomial 1,polynomial 1⟩]

def eulerTerms (A B : ℝ) : Fin 5 → Term :=
  ![⟨4*A,polynomial 0,polynomial 2⟩,⟨2*B,polynomial 1,polynomial 1⟩,
    ⟨A,polynomial 0,euler (polynomial 2)⟩,
    ⟨A,polynomial 2,euler (polynomial 0)⟩,
    ⟨B,polynomial 1,euler (polynomial 1)⟩]

def profile (A B : ℝ) : ℝ → ℝ → ℝ := component (terms A B) 0 0
def profileU (A B : ℝ) : ℝ → ℝ → ℝ := component (terms A B) 1 0
def profileV (A B : ℝ) : ℝ → ℝ → ℝ := component (terms A B) 0 1
def eulerProfile (A B : ℝ) : ℝ → ℝ → ℝ := component (eulerTerms A B) 0 0

def profileData (A B : ℝ) := data (terms A B)
def eulerData (A B : ℝ) := data (eulerTerms A B)

theorem profile_formula (A B u v : ℝ) :
    profile A B u v=KFCausalBDG4DCompactProfile.profile u*
      KFCausalBDG4DCompactProfile.profile v*(A*(u^2+v^2)+B*u*v) := by
  simp [profile,component,terms,jet,polynomial,Fin.sum_univ_succ]
  ring

theorem profile_symmetric (A B u v : ℝ) : profile A B u v=profile A B v u :=
  component_swap (terms A B) 0 0 u v

theorem euler_symmetric (A B u v : ℝ) : eulerProfile A B u v=eulerProfile A B v u :=
  component_swap (eulerTerms A B) 0 0 u v

theorem profile_continuous (A B : ℝ) : Continuous (Function.uncurry (profile A B)) :=
  component_continuous (terms A B) 0 0

theorem profileU_continuous (A B : ℝ) : Continuous (Function.uncurry (profileU A B)) :=
  component_continuous (terms A B) 1 0

theorem profileV_continuous (A B : ℝ) : Continuous (Function.uncurry (profileV A B)) :=
  component_continuous (terms A B) 0 1

theorem euler_continuous (A B : ℝ) : Continuous (Function.uncurry (eulerProfile A B)) :=
  component_continuous (eulerTerms A B) 0 0

theorem profile_derivative_u (A B u v : ℝ) :
    HasDerivAt (fun x => profile A B x v) (profileU A B u v) u :=
  component_derivative_u (terms A B) 0 0 u v

theorem profile_derivative_v (A B u v : ℝ) :
    HasDerivAt (fun x => profile A B u x) (profileV A B u v) v :=
  component_derivative_v (terms A B) 0 0 u v

theorem euler_identity (A B u v : ℝ) :
    eulerProfile A B u v=4*profile A B u v+u*profileU A B u v+v*profileV A B u v := by
  simp [profile,profileU,profileV,eulerProfile,component,terms,eulerTerms,
    jet,euler,Fin.sum_univ_succ]
  ring

theorem profile_outside (A B u v : ℝ) (h : 3 ≤ |u| ∨ 3 ≤ |v|) :
    profile A B u v=0 ∧ profileU A B u v=0 ∧ profileV A B u v=0 :=
  ⟨component_outside (terms A B) 0 0 u v h,
    component_outside (terms A B) 1 0 u v h,
    component_outside (terms A B) 0 1 u v h⟩

theorem euler_outside (A B u v : ℝ) (h : 3 ≤ |u| ∨ 3 ≤ |v|) :
    eulerProfile A B u v=0 := component_outside (eulerTerms A B) 0 0 u v h

private theorem compact_of_outside (F : ℝ → ℝ → ℝ)
    (hF : ∀ u v, 3 ≤ |u| ∨ 3 ≤ |v| → F u v=0) :
    HasCompactSupport (Function.uncurry F) := by
  apply ((isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).prod
    (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3))).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_Icc.prod isClosed_Icc)
  intro p hp
  have hu : |p.1| < 3 := lt_of_not_ge (fun h => hp (hF p.1 p.2 (Or.inl h)))
  have hv : |p.2| < 3 := lt_of_not_ge (fun h => hp (hF p.1 p.2 (Or.inr h)))
  exact ⟨abs_le.mp hu.le,abs_le.mp hv.le⟩

theorem profile_compact (A B : ℝ) : HasCompactSupport (Function.uncurry (profile A B)) :=
  compact_of_outside _ (fun u v h => (profile_outside A B u v h).1)

theorem euler_compact (A B : ℝ) : HasCompactSupport (Function.uncurry (eulerProfile A B)) :=
  compact_of_outside _ (euler_outside A B)

theorem profile_jets (A B : ℝ) :
    profile A B 0 0=0 ∧ component (terms A B) 2 0 0 0=2*A ∧
    component (terms A B) 0 2 0 0=2*A ∧ component (terms A B) 1 1 0 0=B := by
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [profile,component,terms,jet,Fin.sum_univ_succ,
    polynomial_zero_jet.1,polynomial_zero_jet.2.1,polynomial_zero_jet.2.2,
    polynomial_one_jet.1,polynomial_one_jet.2.1,polynomial_one_jet.2.2,
    polynomial_two_jet.1,polynomial_two_jet.2.1,polynomial_two_jet.2.2] <;> ring

theorem euler_jets (A B : ℝ) :
    eulerProfile A B 0 0=0 ∧ component (eulerTerms A B) 2 0 0 0=12*A ∧
    component (eulerTerms A B) 0 2 0 0=12*A ∧ component (eulerTerms A B) 1 1 0 0=6*B := by
  have h0 := euler_origin_jet (polynomial 0)
  have h1 := euler_origin_jet (polynomial 1)
  have h2 := euler_origin_jet (polynomial 2)
  refine ⟨?_,?_,?_,?_⟩ <;>
    simp [eulerProfile,component,eulerTerms,jet,Fin.sum_univ_succ,
    h0.1,h0.2.1,h0.2.2,h1.1,h1.2.1,h1.2.2,h2.1,h2.2.1,h2.2.2,
    polynomial_zero_jet.1,polynomial_zero_jet.2.1,polynomial_zero_jet.2.2,
    polynomial_one_jet.1,polynomial_one_jet.2.1,polynomial_one_jet.2.2,
    polynomial_two_jet.1,polynomial_two_jet.2.1,polynomial_two_jet.2.2] <;> ring

theorem profile_tendsto (A B : ℝ) :
    Tendsto (fun a : ℝ => sqrt a*(∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      a*(v-u)^2*f4D (a*u^2*v^2)*profile A B u v)) atTop (𝓝 (sqrt π*(A-B)/6)) := by
  have h := quadrant_tendsto (terms A B)
  obtain ⟨h0,h20,h02,h11⟩ := profile_jets A B
  change component (terms A B) 0 0 0 0=0 at h0
  simp only [h0,zero_div,sub_zero,h20,h02,h11] at h
  have he : sqrt π/24*(2*A+2*A)-sqrt π/6*B=sqrt π*(A-B)/6 := by ring
  rw [he] at h
  exact h

theorem euler_tendsto (A B : ℝ) :
    Tendsto (fun a : ℝ => sqrt a*(∫ v in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ),
      a*(v-u)^2*f4D (a*u^2*v^2)*eulerProfile A B u v)) atTop (𝓝 (sqrt π*(A-B))) := by
  have h := quadrant_tendsto (eulerTerms A B)
  obtain ⟨h0,h20,h02,h11⟩ := euler_jets A B
  change component (eulerTerms A B) 0 0 0 0=0 at h0
  simp only [h0,zero_div,sub_zero,h20,h02,h11] at h
  have he : sqrt π/24*(12*A+12*A)-sqrt π/6*(6*B)=sqrt π*(A-B) := by ring
  rw [he] at h
  exact h

#print axioms profile_formula
#print axioms profile_symmetric
#print axioms euler_symmetric
#print axioms profile_continuous
#print axioms profileU_continuous
#print axioms profileV_continuous
#print axioms euler_continuous
#print axioms profile_derivative_u
#print axioms profile_derivative_v
#print axioms euler_identity
#print axioms profile_outside
#print axioms euler_outside
#print axioms profile_compact
#print axioms euler_compact
#print axioms profile_jets
#print axioms euler_jets
#print axioms profile_tendsto
#print axioms euler_tendsto
end
end UnifiedTheory.Audit.KFCausalBDG4DQuadraticEulerProfiles
