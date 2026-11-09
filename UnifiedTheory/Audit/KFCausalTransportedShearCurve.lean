/- Exact transport of a field component whose shear commutator is a
constant multiple of itself. The compensating bounded clock multiplier
restores the unforced equation, retaining its positive production. -/
import UnifiedTheory.Audit.KFCausalClockProfileCalculus
import UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalTransportedShearCurve
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)

theorem multiply_commute (p q : Profiles) (f : Hilbert) :
    multiply p (multiply q f) = multiply q (multiply p f) := by
  rw [← multiply_mul,mul_comm,multiply_mul]

theorem transported_derivative (c : Profiles) (z : ℂ) (U : ℝ → Hilbert) (v : Hilbert)
    (t : ℝ) (hu : HasDerivAt U (multiply c v) t) :
    HasDerivAt (fun r => transport (z • c) r (U r))
      (multiply c (transport (z • c) t (v+z • U t))) t := by
  let R := ContinuousLinearMap.restrictScalarsL ℂ Hilbert Hilbert ℝ ℝ
  have hd := (R.hasFDerivAt.comp_hasDerivAt t (transport_derivative (z • c) t)).clm_apply hu
  convert hd using 1
  change multiply c (transport (z • c) t (v+z • U t)) =
    multiply (NormedSpace.exp ((t-1) • (z • c))*(z • c)) (U t)+
      transport (z • c) t (multiply c v)
  simp only [transport,multiply_mul,multiply_smul,ContinuousLinearMap.smul_apply,map_add,map_smul]
  rw [multiply_commute c,multiply_commute c]
  exact add_comm _ _

theorem transported_continuous (p : Profiles) (U : ℝ → Hilbert) (hU : Continuous U) :
    Continuous (fun t => transport p t (U t)) :=
  (transport_continuous p).clm_apply hU

theorem transported_graph (p : Profiles) (h : ℝ) (hh : h ≠ 0) (u j : Hilbert)
    (hu : (u,j) ∈ (shearMomentum h).graph) (t : ℝ) :
    (transport p t u,transport p t j) ∈ (shearMomentum h).graph :=
  KFCausalClockShearRealMultiplier.clock_graph (transport p t)
    (fun s => Complex.exp ((t-1:ℝ)*p s)) (transport_coe p t) h hh u j hu

variable (c : Profiles) (z : ℂ) (h : ℝ) (hh : h ≠ 0)
  (U V : ℝ → Hilbert) (K : Interval → Hilbert)

def first (t : ℝ) : Hilbert := V t+z • U t
def second (t : Interval) : Hilbert := K t+z • V t+z • first z U V t
def input (t : ℝ) : Hilbert := transport (z • c) t (U t)
def output (t : ℝ) : Hilbert := transport (z • c) t (first z U V t)
def output2 (t : Interval) : Hilbert := transport (z • c) t (second z U V K t)

variable
  (hU : Continuous U) (hV : Continuous V)
  (dU : ∀ t, t ∈ Ioo (0:ℝ) 1 → HasDerivAt U (multiply c (V t)) t)
  (dV : ∀ t (ht : t ∈ Ioo (0:ℝ) 1), HasDerivAt V (multiply c (K ⟨t,ht.1.le,ht.2.le⟩)) t)
  (gU : ∀ t : Interval, (U t,first z U V t) ∈ (shearMomentum h).graph)
  (gV : ∀ t : Interval, (V t,K t+z • V t) ∈ (shearMomentum h).graph)

include dU in
theorem input_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (input c z U) (multiply c (output c z U V t)) t :=
  transported_derivative c z U (V t) t (dU t ht)

include dU dV in
theorem output_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (output c z U V) (multiply c (output2 c z U V K ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hd := (dV t ht).add ((dU t ht).const_smul z)
  have he : HasDerivAt (first z U V)
      (multiply c (K ⟨t,ht.1.le,ht.2.le⟩+z • V t)) t := by
    simpa only [first,map_add,map_smul] using hd
  exact transported_derivative c z (first z U V) _ t he

include hh gU in
theorem input_graph (t : Interval) :
    (input c z U t,output c z U V t) ∈ (shearMomentum h).graph :=
  transported_graph (z • c) h hh _ _ (gU t) t

include hh gU gV in
theorem output_graph (t : Interval) :
    (output c z U V t,output2 c z U V K t) ∈ (shearMomentum h).graph := by
  apply transported_graph (z • c) h hh
  simpa only [first,second,Prod.smul_mk] using
    (shearMomentum h).graph.add_mem (gV t) ((shearMomentum h).graph.smul_mem z (gU t))

include hh hU hV dU dV gU gV in
theorem expectation_monotone (hc : ∀ s, 0 ≤ (c s).re)
    (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
    (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x) :
    MonotoneOn (expectation W (input c z U) (output c z U V)) (Icc (0:ℝ) 1) := by
  exact KFCausalClockShearPositiveVariation.expectation_monotone (multiply c) W c w
    (multiply_coe c) hW hc h hh (input c z U) (output c z U V) (output2 c z U V K)
    (transported_continuous _ _ hU) (transported_continuous _ _ (hV.add (hU.const_smul z)))
    (input_derivative c z U V dU) (output_derivative c z U V K dU dV)
    (input_graph c z h hh U V gU) (output_graph c z h hh U V K gU gV)

#print axioms multiply_commute
#print axioms transported_derivative
#print axioms transported_continuous
#print axioms transported_graph
#print axioms input_derivative
#print axioms output_derivative
#print axioms input_graph
#print axioms output_graph
#print axioms expectation_monotone
end
end UnifiedTheory.Audit.KFCausalTransportedShearCurve
