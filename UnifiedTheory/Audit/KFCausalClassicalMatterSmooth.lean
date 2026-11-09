/- Smoothness of the full weighted classical matter Hamiltonian. Polynomial
field profiles multiply the same Banach-algebra exponential used in vacuum. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
import UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean (mean_eq_angle)
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (q p q_apply p_apply Index TimePhase shearProfile shearProfile_apply shearProfile_contDiff kineticMean_contDiff)
open UnifiedTheory.Audit.KFCausalBoundedAngleExponential (Profiles meanL meanL_apply sinAngle cosAngle exponential_apply exponential_contDiff)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale)

def fieldProfile (z : Phase) : Profiles :=
  (2*scale*q (.inr 2) z) • cosAngle+(2*scale*p (.inl 1) z) • sinAngle+q (.inr 3) z • (1:Profiles)

theorem fieldProfile_apply (z : Phase) (θ : ℝ) :
    fieldProfile z θ = fieldValue (rotate (2*Real.pi*θ) z) := by
  rw [fieldValue_rotate]
  change (2*scale*q (.inr 2) z)*Real.cos (2*Real.pi*θ)+
    (2*scale*p (.inl 1) z)*Real.sin (2*Real.pi*θ)+q (.inr 3) z*1 = _
  simp only [q_apply,p_apply]
  ring

def potentialProfile (m g κ : ℝ) (z : Phase) : Profiles :=
  κ • (1:Profiles)+(m/2) • fieldProfile z^2+(g/4) • fieldProfile z^4

theorem potentialProfile_apply (m g κ : ℝ) (z : Phase) (θ : ℝ) :
    potentialProfile m g κ z θ = potential m g κ (rotate (2*Real.pi*θ) z) := by
  change κ*1+(m/2)*(fieldProfile z θ)^2+(g/4)*(fieldProfile z θ)^4 = _
  simp only [fieldProfile_apply,potential,mul_one]

theorem potentialProfile_contDiff (m g κ : ℝ) (n : WithTop ℕ∞) :
    ContDiff ℝ n (potentialProfile m g κ) := by
  have hf : ContDiff ℝ n fieldProfile := by unfold fieldProfile; fun_prop
  unfold potentialProfile
  fun_prop

theorem weightedMean_eq_profiles (ε m g κ : ℝ) (z : Phase) :
    weightedMean m g κ (clock ε (q (.inr 0) z)) z =
      meanL (potentialProfile m g κ z*NormedSpace.exp (shearProfile ε z)) := by
  rw [weightedMean,mean_eq_angle,meanL_apply]
  simp only [BoundedContinuousFunction.mul_apply,potentialProfile_apply,exponential_apply,shearProfile_apply]

theorem weightedMean_contDiff (ε m g κ : ℝ) (hε : 0 ≤ ε) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : Phase => weightedMean m g κ (clock ε (q (.inr 0) z)) z) := by
  simp_rw [weightedMean_eq_profiles]
  exact meanL.contDiff.comp ((potentialProfile_contDiff m g κ n).mul
    ((exponential_contDiff n).comp (shearProfile_contDiff ε hε n)))

def fullHamiltonian (ε m g κ : ℝ) (x : TimePhase) : ℝ :=
  hamiltonian ε m g κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)

theorem fullHamiltonian_contDiff (ε m g κ : ℝ) (hε : 0 ≤ ε) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fullHamiltonian ε m g κ) := by
  have hc : ContDiff ℝ n (fun x : TimePhase => clock ε (q (.inr 0) x.2)) := by unfold clock; fun_prop
  have hn (x : TimePhase) : clock ε (q (.inr 0) x.2) ≠ 0 := (clock_positive ε _ hε).ne'
  have hf := (weightedMean_contDiff ε m g κ hε n).comp (contDiff_snd : ContDiff ℝ n (fun x : TimePhase => x.2))
  have hk := kineticMean_contDiff n
  have hp : ContDiff ℝ n (fun x : TimePhase => p (.inr 0) x.2) := (p (.inr 0)).contDiff.comp contDiff_snd
  unfold fullHamiltonian hamiltonian amplitude
  fun_prop (disch := exact hn)

theorem fullHamiltonian_vacuum (ε κ : ℝ) :
    fullHamiltonian ε 0 0 κ = KFCausalClassicalVacuumSmooth.fullHamiltonian ε κ := by
  funext x
  exact hamiltonian_vacuum ε κ x.1 x.2 _ _

#print axioms fieldProfile_apply
#print axioms potentialProfile_apply
#print axioms potentialProfile_contDiff
#print axioms weightedMean_eq_profiles
#print axioms weightedMean_contDiff
#print axioms fullHamiltonian_contDiff
#print axioms fullHamiltonian_vacuum

end
end UnifiedTheory.Audit.KFCausalClassicalMatterSmooth
