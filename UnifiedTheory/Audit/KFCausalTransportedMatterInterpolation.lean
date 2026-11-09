/- Recombine the transported eigenpolynomials before taking expectations.
The resulting monotone path ends at the original field-weighted output,
for arbitrary finite complex superpositions with all cross terms retained.
Its initial signed expectation replaces the previous integrated path cost. -/
import UnifiedTheory.Audit.KFCausalActualTransportedField
import UnifiedTheory.Audit.KFCausalFieldShearInterpolationEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalTransportedMatterInterpolation
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalImaginaryShearSuperposition (Seed graph_sum)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalFieldEigenpolynomials (modes modes_sum)
open UnifiedTheory.Audit.KFCausalClockShearPositiveVariation (expectation)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockProfileCalculus (multiply multiply_coe)
open UnifiedTheory.Audit.KFCausalActualTransportedField (profile)

theorem finite_sum_representatives {ι : Type*} (s : Finset ι) (f : ι → Hilbert)
    (v : ι → Configuration → ℂ) (hf : ∀ k ∈ s, f k =ᵐ[volume] v k) :
    (∑ k ∈ s, f k : Hilbert) =ᵐ[volume] fun x => ∑ k ∈ s, v k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using Lp.coeFn_zero ℂ 2 (volume : Measure Configuration)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    have hi := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    filter_upwards [Lp.coeFn_add (f k) (∑ j ∈ s, f j),hf k (Finset.mem_insert_self k s),hi]
      with x ha hb hc
    simp only [ha,Pi.add_apply,hb,hc]

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)
  (l : Transverse →L[ℝ] ℝ) (i : Fin 2) {n : ℕ} (s : Fin n → Seed) (z : Fin n → ℂ)

def input (t : ℝ) : Hilbert := ∑ r, z r • ∑ k,
  KFCausalActualTransportedField.input ε h hε hb hh (s r) (modes l i k) t
def output (t : ℝ) : Hilbert := ∑ r, z r • ∑ k,
  KFCausalActualTransportedField.output ε h hε hb hh (s r) (modes l i k) t
def output2 (t : Interval) : Hilbert := ∑ r, z r • ∑ k,
  KFCausalActualTransportedField.output2 ε h hε hb hh (s r) (modes l i k) t

local notation "U" => input ε h hε hb hh l i s z
local notation "J" => output ε h hε hb hh l i s z
local notation "K" => output2 ε h hε hb hh l i s z
local notation "c" => profile ε h hε hb hh
local notation "C" => multiply c

theorem curves_continuous : Continuous U ∧ Continuous J := by
  constructor
  · exact continuous_finset_sum Finset.univ (fun r _ =>
      (continuous_finset_sum Finset.univ (fun k _ =>
        KFCausalActualTransportedField.input_continuous ε h hε hb hh (s r) (modes l i k))).const_smul (z r))
  · exact continuous_finset_sum Finset.univ (fun r _ =>
      (continuous_finset_sum Finset.univ (fun k _ =>
        KFCausalActualTransportedField.output_continuous ε h hε hb hh (s r) (modes l i k))).const_smul (z r))

theorem input_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt U (C (J t)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (r : Fin n) _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun (k : Fin 3) _ =>
      KFCausalActualTransportedField.input_derivative ε h hε hb hh (s r) (modes l i k) t ht)).const_smul (z r))
  simpa only [input,output,map_sum,map_smul] using hd

theorem output_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt J (C (K ⟨t,ht.1.le,ht.2.le⟩)) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (r : Fin n) _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) (fun (k : Fin 3) _ =>
      KFCausalActualTransportedField.output_derivative ε h hε hb hh (s r) (modes l i k) t ht)).const_smul (z r))
  simpa only [output,output2,map_sum,map_smul] using hd

theorem input_graph (t : Interval) : (U t,J t) ∈ (shearMomentum h).graph := by
  apply graph_sum h z
  intro r
  simpa only [one_smul] using graph_sum h (fun _ : Fin 3 => (1:ℂ)) _ _
    (fun k => KFCausalActualTransportedField.input_graph ε h hε hb hh (s r) (modes l i k) t)

theorem output_graph (t : Interval) : (J t,K t) ∈ (shearMomentum h).graph := by
  apply graph_sum h z
  intro r
  simpa only [one_smul] using graph_sum h (fun _ : Fin 3 => (1:ℂ)) _ _
    (fun k => KFCausalActualTransportedField.output_graph ε h hε hb hh (s r) (modes l i k) t)

omit s z in
theorem seed_endpoint (r : Seed) :
    (∑ k, KFCausalActualTransportedField.input ε h hε hb hh r (modes l i k) 1) =
      KFCausalFieldShearPathGraphs.state ε h hε hb r
        (KFCausalPolynomialImaginaryShearCurve.fieldWeight l i) 1 := by
  simp_rw [KFCausalActualTransportedField.input_one]
  let G := KFCausalImaginaryShearInterpolation.actualPath ε r.a r.α r.β r.p h r.b 1
  have hs := finite_sum_representatives Finset.univ
    (fun k => KFCausalFieldShearPathGraphs.state ε h hε hb r (modes l i k).toWeight 1)
    (fun k x => (modes l i k).value x*G x)
    (fun k _ => KFCausalActualPolynomialShearCurve.input_coe (modes l i k).toWeight
      ε r.a r.p h r.α r.β hε r.ha r.hα r.hβ r.hw hb r.b ⟨1,by constructor <;> norm_num⟩)
  apply Lp.ext
  filter_upwards [hs,KFCausalActualPolynomialShearCurve.input_coe
    (KFCausalPolynomialImaginaryShearCurve.fieldWeight l i)
    ε r.a r.p h r.α r.β hε r.ha r.hα r.hβ r.hw hb r.b ⟨1,by constructor <;> norm_num⟩]
    with x hs hg
  change KFCausalFieldShearPathGraphs.state ε h hε hb r
    (KFCausalPolynomialImaginaryShearCurve.fieldWeight l i) 1 x = _ at hg
  rw [hs,hg,← Finset.sum_mul,modes_sum]
  rfl

theorem endpoints : U 1 = KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z 1 ∧
    J 1 = KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i s z 1 := by
  have hu : U 1 = KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z 1 := by
    exact Finset.sum_congr rfl (fun r _ => congrArg (fun v : Hilbert => z r • v)
      (seed_endpoint ε h hε hb hh l i (s r)))
  have hj : (U 1,J 1) ∈ (shearMomentum h).graph :=
    input_graph ε h hε hb hh l i s z ⟨1,by constructor <;> norm_num⟩
  have ho : (KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z 1,
      KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i s z 1) ∈ (shearMomentum h).graph :=
    KFCausalFieldShearInterpolationEstimate.shear_graph_sum ε h hε hb l i s z hh
      ⟨1,by constructor <;> norm_num⟩
  exact ⟨hu,(shearMomentum h).mem_graph_snd_inj' hj ho hu⟩

variable (W : Hilbert →L[ℂ] Hilbert) (w : ℝ → ℂ)
  (hW : ∀ f : Hilbert, W f =ᵐ[volume] fun x => w x.1*f x)

include hW in
theorem expectation_derivative (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (expectation W U J) (2*(inner ℂ (W (J t)) (C (W (J t)))).re) t :=
  KFCausalClockShearPositiveVariation.expectation_derivative C W c w (multiply_coe c) hW h hh
    U J (K ⟨t,ht.1.le,ht.2.le⟩) t
    (input_derivative ε h hε hb hh l i s z t ht) (output_derivative ε h hε hb hh l i s z t ht)
    (input_graph ε h hε hb hh l i s z ⟨t,ht.1.le,ht.2.le⟩)
    (output_graph ε h hε hb hh l i s z ⟨t,ht.1.le,ht.2.le⟩)

include hW in
theorem expectation_monotone : MonotoneOn (expectation W U J) (Icc (0:ℝ) 1) :=
  KFCausalClockShearPositiveVariation.expectation_monotone C W c w (multiply_coe c) hW
    (fun r => (KFCausalImaginaryShearCoefficient.coefficient_re_positive ε h r hε hh hb).le)
    h hh U J K (curves_continuous ε h hε hb hh l i s z).1 (curves_continuous ε h hε hb hh l i s z).2
    (input_derivative ε h hε hb hh l i s z) (output_derivative ε h hε hb hh l i s z)
    (input_graph ε h hε hb hh l i s z) (output_graph ε h hε hb hh l i s z)

include hW in
theorem endpoint_lower : expectation W U J 0 ≤
    expectation W (KFCausalFieldShearInterpolationEstimate.field ε h hε hb l i s z)
      (KFCausalFieldShearInterpolationEstimate.shear ε h hε hb l i s z) 1 := by
  have he := expectation_monotone ε h hε hb hh l i s z W w hW
    (by constructor <;> norm_num) (by constructor <;> norm_num) (by norm_num : (0:ℝ) ≤ 1)
  obtain ⟨hu,hj⟩ := endpoints ε h hε hb hh l i s z
  simpa only [expectation,hu,hj] using he

#print axioms finite_sum_representatives
#print axioms curves_continuous
#print axioms input_derivative
#print axioms output_derivative
#print axioms input_graph
#print axioms output_graph
#print axioms seed_endpoint
#print axioms endpoints
#print axioms expectation_derivative
#print axioms expectation_monotone
#print axioms endpoint_lower
end
end UnifiedTheory.Audit.KFCausalTransportedMatterInterpolation
