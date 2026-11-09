/- Transfer two-spacing Gram estimates to the actual physical Hilbert
outputs by subtracting finite packet families before applying the exact
positive-energy identity. No pointwise identification with a reduced
Laplace coordinate wavefunction is assumed. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredL2Error
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalClockLimit
import UnifiedTheory.Audit.KFCausalReciprocalNeutralDifference

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalCauchy
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredGlobalEnvelope (reweight)
open KFCausalCorrelatedClusteredDensity (energyOf)
open KFCausalCorrelatedClusteredWholeClock (Whole wholeMeasure)
open KFCausalCorrelatedClusteredL2Error
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift amplitudes coefficient_identity shift_bound amplitudes_continuous amplitudes_memLp)
open KFCausalReciprocalNeutralDifference
open KFCausalReciprocalNeutralPositiveForm (positiveDensity profileSum)
open KFCausalNeutralExponentialProfiles (exponentialProfile)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)

local instance : SFinite jointMeasure := by unfold jointMeasure; infer_instance

theorem neutral_join (n m : ℕ) (b : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (b' : Fin m → ℂ) (P' : Fin m → Polynomial ℂ) :
    (fun i => exponentialProfile (join b b' i) 1 (join P P' i)) =
      join (fun i => exponentialProfile (b i) 1 (P i)) (fun i => exponentialProfile (b' i) 1 (P' i)) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [KFCausalReciprocalNeutralDifference.join,Fin.addCases_left,Fin.addCases_right]

theorem clock_join (n m : ℕ) (ε h : ℝ) (a p : Fin n → ℝ) (c : Fin n → ℂ)
    (a' p' : Fin m → ℝ) (c' : Fin m → ℂ) (s : ℝ) :
    KFCausalReciprocalNeutralPositiveEnergy.coefficients (n+m) ε h (join a a') (join p p')
      (join c (fun i => -c' i)) s =
    join (KFCausalReciprocalNeutralPositiveEnergy.coefficients n ε h a p c s)
      (fun i => -KFCausalReciprocalNeutralPositiveEnergy.coefficients m ε h a' p' c' s i) := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp only [KFCausalReciprocalNeutralPositiveEnergy.coefficients,KFCausalReciprocalNeutralDifference.join,
      Fin.addCases_left,Fin.addCases_right,neg_mul]

variable {m : ℕ} (f : Family m)

theorem density_difference (α β δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (r : ℂ) (q : Joint) :
    positiveDensity (count f+count f) α β (join (widths f δ) (widths f η)) r
      (join (coefficients f δ) (fun i => -coefficients f η i))
      (fun i => exponentialProfile (join (sources f) (sources f) i) 1 (join (polynomials f) (polynomials f) i)) q =
    energyOf (fun k => factor f k α β δ r q-factor f k α β η r q) := by
  rw [positiveDensity_factors,neutral_join,profileSum_difference]
  congr 1
  funext k
  rw [factor_joint f k α β δ hδ,factor_joint f k α β η hη]
  ring

variable (ε h : ℝ) (a p : Fin m → ℝ)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "c" => amplitudes ε (-h/2) a p

theorem slice_difference (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (s : ℝ) :
    KFCausalReciprocalNeutralPositiveEnergy.positiveSlice (count f+count f) ε h
      (join (lift f a) (lift f a)) (join (widths f δ) (widths f η)) (join (lift f p) (lift f p))
      (join (coefficients f δ) (fun i => -coefficients f η i))
      (join (sources f) (sources f)) (join (polynomials f) (polynomials f)) s =
      Real.pi/4*∫ q, difference f c α β ε (-h/2) δ η (s,q) ∂jointMeasure := by
  unfold KFCausalReciprocalNeutralPositiveEnergy.positiveSlice
  rw [clock_join,coefficient_identity,coefficient_identity]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with q
  exact density_difference (reweight f (c s)) α β δ η hδ hη (scale ε (-h/2) s) q

variable (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (ha : ∀ i, 0 < a i)

def finiteOutput (δ : ℝ) (j : Fin 8) : Hilbert := if hδ : 0 < δ then
  KFCausalReciprocalNeutralSuperposition.output (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) hε (fun i => ha (index f i).1) hh
    (widths_admissible f δ hδ.le) hb j else 0

theorem difference_energy (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖finiteOutput f ε h a p hε hh hb ha δ 7-finiteOutput f ε h a p hε hh hb ha η 7‖^2+
    ‖finiteOutput f ε h a p hε hh hb ha δ 5-finiteOutput f ε h a p hε hh hb ha η 5‖^2/2+
    ‖finiteOutput f ε h a p hε hh hb ha δ 6-finiteOutput f ε h a p hε hh hb ha η 6‖^2/4 =
      Real.pi/4*∫ x, difference f c α β ε (-h/2) δ η x ∂wholeMeasure := by
  have he := KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy_positive_integral (count f+count f) ε h
    (join (lift f a) (lift f a)) (join (widths f δ) (widths f η)) (join (lift f p) (lift f p))
    (join (coefficients f δ) (fun i => -coefficients f η i))
    (join (sources f) (sources f)) (join (polynomials f) (polynomials f)) hε
    (join_property (lift f a) (lift f a) (fun t => 0 < t) (fun i => ha (index f i).1) (fun i => ha (index f i).1)) hh
    (join_property (widths f δ) (widths f η) (fun t => 1 ≤ t)
      (widths_admissible f δ hδ.le) (widths_admissible f η hη.le)) hb
  unfold KFCausalReciprocalNeutralPositiveEnergy.potentialEnergy at he
  simp only [output_difference (count f) (count f) ε h (lift f a) (widths f δ) (lift f p)
    (coefficients f δ) (sources f) (polynomials f) (lift f a) (widths f η) (lift f p)
    (coefficients f η) (sources f) (polynomials f) hε (fun i => ha (index f i).1)
    (fun i => ha (index f i).1) hh (widths_admissible f δ hδ.le) (widths_admissible f η hη.le) hb,
    slice_difference f ε h a p δ η hδ hη] at he
  have hy := shift_bound ε h hb
  have hi := difference_integrable f c α β ε (-h/2) (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (amplitudes_continuous ε (-h/2) a p hε hy) (amplitudes_memLp ε (-h/2) a p hε hy ha) δ η hδ hη
  rw [integral_const_mul,← integral_prod _ hi] at he
  simpa only [finiteOutput,dif_pos hδ,dif_pos hη] using he

theorem difference_energy_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ‖finiteOutput f ε h a p hε hh hb ha δ 7-finiteOutput f ε h a p hε hh hb ha η 7‖^2+
    ‖finiteOutput f ε h a p hε hh hb ha δ 5-finiteOutput f ε h a p hε hh hb ha η 5‖^2/2+
    ‖finiteOutput f ε h a p hε hh hb ha δ 6-finiteOutput f ε h a p hε hh hb ha η 6‖^2/4 ≤
      2*errorMass f c α β ε (-h/2) δ+2*errorMass f c α β ε (-h/2) η := by
  rw [difference_energy f ε h a p hε hh hb ha δ η hδ hη]
  have hy := shift_bound ε h hb
  exact difference_integral_bound f c α β ε (-h/2) (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε hy
    (amplitudes_continuous ε (-h/2) a p hε hy) (amplitudes_memLp ε (-h/2) a p hε hy ha) δ η hδ hη

def potentialIndex : Fin 3 → Fin 8 := ![7,5,6]

theorem output_distance_bound (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) (k : Fin 3) :
    ‖finiteOutput f ε h a p hε hh hb ha δ (potentialIndex k)-
      finiteOutput f ε h a p hε hh hb ha η (potentialIndex k)‖^2 ≤
      8*(errorMass f c α β ε (-h/2) δ+errorMass f c α β ε (-h/2) η) := by
  have he := difference_energy_bound f ε h a p hε hh hb ha δ η hδ hη
  have h0 := sq_nonneg ‖finiteOutput f ε h a p hε hh hb ha δ 7-finiteOutput f ε h a p hε hh hb ha η 7‖
  have h1 := sq_nonneg ‖finiteOutput f ε h a p hε hh hb ha δ 5-finiteOutput f ε h a p hε hh hb ha η 5‖
  have h2 := sq_nonneg ‖finiteOutput f ε h a p hε hh hb ha δ 6-finiteOutput f ε h a p hε hh hb ha η 6‖
  fin_cases k <;> norm_num [potentialIndex] <;> linarith

#print axioms neutral_join
#print axioms clock_join
#print axioms density_difference
#print axioms slice_difference
#print axioms difference_energy
#print axioms difference_energy_bound
#print axioms output_distance_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredPhysicalCauchy
