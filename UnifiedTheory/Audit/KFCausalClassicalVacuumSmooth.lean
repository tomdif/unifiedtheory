/- Smoothness of the full charge-averaged classical vacuum Hamiltonian,
including its transverse exponential integral. This supplies actual
regularity for the canonical ODE rather than assuming differentiability. -/
import UnifiedTheory.Audit.KFCausalBoundedAngleExponential
import UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalBoundedAngleExponential (Profiles harmonics harmonics_apply)

abbrev Index := Fin 2 ⊕ Fin 4
abbrev TimePhase := ℝ × Phase

def q (i : Index) : Phase →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Index => ℝ) i).comp (ContinuousLinearMap.fst ℝ _ _)

def p (i : Index) : Phase →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Index => ℝ) i).comp (ContinuousLinearMap.snd ℝ _ _)

theorem q_apply (i : Index) (z : Phase) : q i z = z.1 i := rfl
theorem p_apply (i : Index) (z : Phase) : p i z = z.2 i := rfl

theorem diagonalPairing_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n diagonalPairing := by
  change ContDiff ℝ n (fun z => q (.inl 0) z*p (.inl 0) z+q (.inr 1) z*p (.inr 1) z+
    q (.inl 1) z*p (.inl 1) z+q (.inr 2) z*p (.inr 2) z)
  fun_prop

theorem crossPairing_contDiff (n : WithTop ℕ∞) : ContDiff ℝ n crossPairing := by
  change ContDiff ℝ n (fun z => p (.inl 0) z*p (.inr 1) z-q (.inl 0) z*q (.inr 1) z+
    p (.inl 1) z*p (.inr 2) z-q (.inl 1) z*q (.inr 2) z)
  fun_prop

def shearProfile (ε : ℝ) (z : Phase) : Profiles :=
  harmonics (diagonalPairing z/(2*clock ε (q (.inr 0) z)))
    (crossPairing z/clock ε (q (.inr 0) z))
    (2*KFCausalPairedModeCoordinates.scale*p (.inl 1) z*p (.inr 3) z/clock ε (q (.inr 0) z))
    (2*KFCausalPairedModeCoordinates.scale*q (.inr 2) z*p (.inr 3) z/clock ε (q (.inr 0) z))

theorem shearProfile_apply (ε θ : ℝ) (z : Phase) :
    shearProfile ε z θ = shear (rotate (2*Real.pi*θ) z)/clock ε (q (.inr 0) z) := by
  rw [shearProfile, harmonics_apply, shear_rotate]
  simp only [p_apply, q_apply]
  ring

theorem shearProfile_contDiff (ε : ℝ) (hε : 0 ≤ ε) (n : WithTop ℕ∞) :
    ContDiff ℝ n (shearProfile ε) := by
  have hc : ContDiff ℝ n (fun z => clock ε (q (.inr 0) z)) := by unfold clock; fun_prop
  have hn (z : Phase) : clock ε (q (.inr 0) z) ≠ 0 := (clock_positive ε _ hε).ne'
  have hd := diagonalPairing_contDiff n
  have hx := crossPairing_contDiff n
  have h2 (z : Phase) : 2*clock ε (q (.inr 0) z) ≠ 0 := mul_ne_zero two_ne_zero (hn z)
  unfold shearProfile harmonics
  fun_prop (disch := first | exact hn | exact h2)

theorem exponentialMean_eq (ε : ℝ) (z : Phase) :
    KFCausalBoundedAngleExponential.exponentialMean (shearProfile ε z) =
      exponentialMean (clock ε (q (.inr 0) z)) z := by
  rw [KFCausalBoundedAngleExponential.exponentialMean_integral, exponentialMean, mean_eq_angle]
  simp only [shearProfile_apply]

theorem exponentialMean_contDiff (ε : ℝ) (hε : 0 ≤ ε) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : Phase => exponentialMean (clock ε (q (.inr 0) z)) z) := by
  have h := (KFCausalBoundedAngleExponential.exponentialMean_contDiff n).comp (shearProfile_contDiff ε hε n)
  simpa only [Function.comp_def, exponentialMean_eq] using h

def fullHamiltonian (ε κ : ℝ) (x : TimePhase) : ℝ :=
  hamiltonian ε κ x.1 x.2 (q (.inr 0) x.2) (p (.inr 0) x.2)

theorem kineticMean_contDiff (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : TimePhase => kineticMean x.1 x.2) := by
  simp_rw [kineticMean_eq]
  change ContDiff ℝ n (fun x : TimePhase =>
    (p (.inr 1) x.2^2+q (.inl 0) x.2^2+p (.inr 2) x.2^2+q (.inl 1) x.2^2+p (.inr 3) x.2^2)/2+
    Real.exp (2*x.1)*(p (.inl 0) x.2^2+q (.inr 1) x.2^2+p (.inl 1) x.2^2+q (.inr 2) x.2^2)/2)
  fun_prop

theorem fullHamiltonian_contDiff (ε κ : ℝ) (hε : 0 ≤ ε) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fullHamiltonian ε κ) := by
  have hc : ContDiff ℝ n (fun x : TimePhase => clock ε (q (.inr 0) x.2)) := by unfold clock; fun_prop
  have hn (x : TimePhase) : clock ε (q (.inr 0) x.2) ≠ 0 := (clock_positive ε _ hε).ne'
  have hf := (exponentialMean_contDiff ε hε n).comp (contDiff_snd : ContDiff ℝ n (fun x : TimePhase => x.2))
  have hk := kineticMean_contDiff n
  have hp : ContDiff ℝ n (fun x : TimePhase => p (.inr 0) x.2) :=
    (p (.inr 0)).contDiff.comp contDiff_snd
  unfold fullHamiltonian hamiltonian amplitude
  fun_prop (disch := exact hn)

#print axioms q_apply
#print axioms p_apply
#print axioms diagonalPairing_contDiff
#print axioms crossPairing_contDiff
#print axioms shearProfile_apply
#print axioms shearProfile_contDiff
#print axioms exponentialMean_eq
#print axioms exponentialMean_contDiff
#print axioms kineticMean_contDiff
#print axioms fullHamiltonian_contDiff

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
