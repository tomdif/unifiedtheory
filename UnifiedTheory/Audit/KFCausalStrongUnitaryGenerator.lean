/- The maximal strong derivative of a strongly continuous unitary group.
Its domain is defined by actual Hilbert-space differentiation. Density is
proved from explicit orbit averages, not assumed. -/
import UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (U : StrongUnitaryGroup H)

def domain : Submodule ℂ H where
  carrier := {x | DifferentiableAt ℝ (fun t => U.action t x) 0}
  zero_mem' := by simpa only [Set.mem_setOf_eq,map_zero] using (differentiableAt_const (𝕜 := ℝ) (x := (0:ℝ)) (0: H))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_setOf_eq,map_add,Pi.add_apply] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_setOf_eq,map_smul,Pi.smul_apply] using hx.const_smul c

def generator : H →ₗ.[ℂ] H where
  domain := domain U
  toFun :=
    { toFun := fun x => deriv (fun t => U.action t (x:H)) 0
      map_add' := by
        intro x y
        simpa only [Submodule.coe_add,map_add] using (x.property.hasDerivAt.add y.property.hasDerivAt).deriv
      map_smul' := by
        intro c x
        simpa only [Submodule.coe_smul,map_smul,RingHom.id_apply] using
          (x.property.hasDerivAt.const_smul c).deriv }

theorem generator_derivative (x : (generator U).domain) :
    HasDerivAt (fun t => U.action t (x:H)) (generator U x) 0 := x.property.hasDerivAt

theorem generator_graph_iff (x y : H) :
    (x,y) ∈ (generator U).graph ↔ HasDerivAt (fun t => U.action t x) y 0 := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨v,hv,hy⟩
    simpa only [hv,hy] using generator_derivative U v
  · intro hh
    exact ⟨⟨x,hh.differentiableAt⟩,rfl,hh.deriv⟩

theorem generator_dense [CompleteSpace H] : Dense ((generator U).domain : Set H) := by
  apply (averages_dense U).mono
  rintro _ ⟨⟨x,a⟩,rfl⟩
  exact (average_derivative U x a).differentiableAt

theorem derivative_at_time (x y : H) (hxy : HasDerivAt (fun t => U.action t x) y 0)
    (t : ℝ) : HasDerivAt (fun s => U.action s x) (U.action t y) t := by
  have hshift : HasDerivAt (fun s => U.action (s-t) x) y t := by
    have hh : HasDerivAt (fun s => U.action s x) y (t-t) := by simpa using hxy
    exact hh.comp_sub_const t t
  have hh := ((U.action t : H →L[ℂ] H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hshift
  change HasDerivAt (fun s => U.action t (U.action (s-t) x)) (U.action t y) t at hh
  simpa only [U.compose,sub_add_cancel] using hh

theorem transported_derivative (x y : H) (hxy : HasDerivAt (fun t => U.action t x) y 0)
    (t : ℝ) : HasDerivAt (fun s => U.action s (U.action t x)) (U.action t y) 0 := by
  have hh := ((U.action t : H →L[ℂ] H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hxy
  change HasDerivAt (fun s => U.action t (U.action s x)) (U.action t y) 0 at hh
  simpa only [U.compose,add_comm] using hh

def domainAction (t : ℝ) (x : (generator U).domain) : (generator U).domain :=
  ⟨U.action t x,(transported_derivative U x (generator U x) (generator_derivative U x) t).differentiableAt⟩

theorem generator_commutes (t : ℝ) (x : (generator U).domain) :
    generator U (domainAction U t x) = U.action t (generator U x) :=
  (transported_derivative U x (generator U x) (generator_derivative U x) t).deriv

theorem generator_skew_symmetric (x y : (generator U).domain) :
    inner ℂ (x:H) (generator U y)+inner ℂ (generator U x) (y:H) = 0 := by
  have hh := (generator_derivative U x).inner ℂ (generator_derivative U y)
  have hc : HasDerivAt (fun _ : ℝ => inner ℂ (x:H) (y:H))
      (inner ℂ (x:H) (generator U y)+inner ℂ (generator U x) (y:H)) 0 := by
    simpa only [LinearIsometryEquiv.inner_map_map,U.initial] using hh
  exact hc.unique (hasDerivAt_const 0 _)

theorem generator_integral [CompleteSpace H] (x : (generator U).domain) (a b : ℝ) :
    (∫ t in a..b, U.action t (generator U x)) = U.action b x-U.action a x :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => derivative_at_time U x (generator U x) (generator_derivative U x) t)
    ((U.continuous_orbit (generator U x)).intervalIntegrable a b)

#print axioms generator
#print axioms generator_graph_iff
#print axioms generator_dense
#print axioms derivative_at_time
#print axioms transported_derivative
#print axioms generator_commutes
#print axioms generator_skew_symmetric
#print axioms generator_integral

end
end UnifiedTheory.Audit.KFCausalStrongUnitaryGenerator
