/- Actual ordered potential outputs for finite reciprocal-packet sums,
with independent clock widths, reduce to the complex Gram kernel.
Global integrability comes from the already constructed L2 outputs. -/
import UnifiedTheory.Audit.KFCausalReciprocalCrossResponse
import UnifiedTheory.Audit.KFCausalReciprocalGaussianOutputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalCrossPhysical
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalReciprocalGaussianOutputs (shifted output_coe momentumOutput_coe)
open KFCausalReciprocalCrossGram (packetSum pairDensity pairing)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open KFCausalClockResponseTransport (weakSlope)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth)
open KFCausalSourcedResponseFactorBridge (index)

variable (n : ℕ) (ε h : ℝ) (a w : Fin n → ℝ) (c : Fin n → ℂ)

def coefficients (s : ℝ) (i : Fin n) : ℂ := c i*clockAmplitude ε (a i) 0 (-h/2) s

def momentumCoefficients (s : ℝ) (i : Fin n) : ℂ :=
  (-Complex.I*(h:ℂ))*weakSlope ε (a i) 0 (-h/2) s*coefficients n ε h a c s i

def factorSum (k : Fin 3) (x : Configuration) : ℂ := ∑ i, c i*shifted ε (a i) h (w i) k x

def momentumFactorSum (k : Fin 3) (x : Configuration) : ℂ :=
  ∑ i, c i*((-Complex.I*(h:ℂ))*weakSlope ε (a i) 0 (-h/2) x.1*shifted ε (a i) h (w i) k x)

def potentialPair (x : Configuration) : ℂ :=
  conj (factorSum n ε h a w c 0 x)*momentumFactorSum n ε h a w c 0 x+
    conj (factorSum n ε h a w c 1 x)*momentumFactorSum n ε h a w c 1 x/2+
    conj (factorSum n ε h a w c 2 x)*momentumFactorSum n ε h a w c 2 x/4

def energyDensity (x : Configuration) : ℝ :=
  ‖factorSum n ε h a w c 0 x‖^2+‖factorSum n ε h a w c 1 x‖^2/2+
    ‖factorSum n ε h a w c 2 x‖^2/4

theorem factorSum_factorization (k : Fin 3) (x : Configuration) :
    factorSum n ε h a w c k x = (pointField x.2:ℂ)^k.val*
      packetSum n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1)
        (coefficients n ε h a c x.1) x.2 := by
  unfold factorSum packetSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold coefficients shifted
  ring

theorem momentumFactorSum_factorization (k : Fin 3) (x : Configuration) :
    momentumFactorSum n ε h a w c k x = (pointField x.2:ℂ)^k.val*
      packetSum n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1)
        (momentumCoefficients n ε h a c x.1) x.2 := by
  unfold momentumFactorSum packetSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentumCoefficients coefficients shifted
  ring

theorem potentialPair_factorization (x : Configuration) :
    potentialPair n ε h a w c x =
      pairDensity n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1)
        (coefficients n ε h a c x.1) (momentumCoefficients n ε h a c x.1) x.2 := by
  unfold potentialPair
  simp_rw [factorSum_factorization,momentumFactorSum_factorization]
  simp only [map_mul,map_pow,Complex.conj_ofReal,Fin.val_zero,Fin.val_one,
    show (2:Fin 3).val=2 by rfl,pow_zero,pow_one,one_mul]
  unfold pairDensity KFCausalQuarticPlaneDomination.potential
  push_cast
  ring

theorem energyDensity_factorization (x : Configuration) :
    energyDensity n ε h a w c x =
      KFCausalQuarticPlaneDomination.potential (pointField x.2)*
        ‖packetSum n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) x.1)
          (coefficients n ε h a c x.1) x.2‖^2 := by
  unfold energyDensity
  simp_rw [factorSum_factorization]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Fin.val_zero,Fin.val_one,show (2:Fin 3).val=2 by rfl,pow_zero,pow_one,one_mul,
    mul_pow,sq_abs]
  unfold KFCausalQuarticPlaneDomination.potential
  ring

variable (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha hh hw hb in
theorem factorSum_memLp (k : Fin 3) : MemLp (factorSum n ε h a w c k) 2 volume := by
  exact memLp_finset_sum Finset.univ (fun i _ =>
    ((Lp.memLp (KFCausalReciprocalGaussianMomentum.output ε (a i) h (w i)
      hε (ha i) hh (hw i) hb (index k))).ae_eq
        (output_coe ε (a i) h (w i) hε (ha i) hh (hw i) hb k)).const_mul (c i))

include hε ha hh hw hb in
theorem momentumFactorSum_memLp (k : Fin 3) : MemLp (momentumFactorSum n ε h a w c k) 2 volume := by
  exact memLp_finset_sum Finset.univ (fun i _ =>
    ((Lp.memLp (KFCausalReciprocalGaussianMomentum.momentumOutput ε (a i) h (w i)
      hε (ha i) hh (hw i) hb (index k))).ae_eq
        (momentumOutput_coe ε (a i) h (w i) hε (ha i) hh (hw i) hb k)).const_mul (c i))

include hε ha hh hw hb in
theorem potentialPair_integrable : Integrable (potentialPair n ε h a w c) := by
  have hi (k : Fin 3) := (factorSum_memLp n ε h a w c hε ha hh hw hb k).star.integrable_mul
    (momentumFactorSum_memLp n ε h a w c hε ha hh hw hb k)
  simpa only [potentialPair,Complex.star_def] using ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

include hε ha hh hw hb in
theorem energyDensity_integrable : Integrable (energyDensity n ε h a w c) := by
  have hi (k : Fin 3) := (factorSum_memLp n ε h a w c hε ha hh hw hb k).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)
  exact ((hi 0).add ((hi 1).div_const 2)).add ((hi 2).div_const 4)

include hε hh hb in
private theorem actual_widths (s : ℝ) :
    0 < groundWidth h*KFCausalReciprocalGaussianCoordinates.area (scale ε (-h/2) s) ∧
    0 < groundWidth h*KFCausalReciprocalGaussianCoordinates.area (scale ε (-h/2) s)-
      8*neutralWidth h*(scale ε (-h/2) s).im^2 ∧ 0 < neutralWidth h := by
  have hα := groundWidth_positive h hh
  have hβ : 0 < neutralWidth h := by unfold neutralWidth; positivity
  have hwidth : 32*neutralWidth h ≤ groundWidth h := by unfold neutralWidth; linarith
  have hy : |-h/2| ≤ Real.pi*ε/3 := by rw [abs_div,abs_neg]; norm_num; linarith
  obtain ⟨hc,ha'⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive _ _ hα _
    (KFCausalChargedPairCompactGeometry.actual_mem_region _ _ ε (-h/2) s hα hβ.le hwidth hε hy)
  exact ⟨ha',hc,hβ⟩

include hε hh hw hb in
theorem potentialPair_slice (s : ℝ) :
    (∫ q : Transverse, potentialPair n ε h a w c (s,q)) =
      pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
        (coefficients n ε h a c s) (momentumCoefficients n ε h a c s) := by
  simp_rw [potentialPair_factorization]
  obtain ⟨hA,hC,hβ⟩ := actual_widths ε h hε hh hb s
  exact (KFCausalReciprocalCrossGram.pairing_integral n _ _ w _ _ _ hw hA hC hβ).symm

include hε hh hw hb in
theorem energyDensity_slice (s : ℝ) :
    (∫ q : Transverse, energyDensity n ε h a w c (s,q)) =
      (pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
        (coefficients n ε h a c s) (coefficients n ε h a c s)).re := by
  simp_rw [energyDensity_factorization]
  obtain ⟨hA,hC,hβ⟩ := actual_widths ε h hε hh hb s
  rw [KFCausalReciprocalCrossGram.pairing_norm_integral n _ _ w _ _ hw hA hC hβ,Complex.ofReal_re]

include hε ha hh hw hb in
theorem clock_pairing_integrable :
    Integrable (fun s => pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
      (coefficients n ε h a c s) (momentumCoefficients n ε h a c s)) :=
  (potentialPair_integrable n ε h a w c hε ha hh hw hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (potentialPair_slice n ε h a w c hε hh hw hb))

include hε ha hh hw hb in
theorem clock_energy_integrable :
    Integrable (fun s => (pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
      (coefficients n ε h a c s) (coefficients n ε h a c s)).re) :=
  (energyDensity_integrable n ε h a w c hε ha hh hw hb).integral_prod_left.congr
    (Filter.Eventually.of_forall (energyDensity_slice n ε h a w c hε hh hw hb))

include hε ha hh hw hb in
theorem potentialPair_clock_integral :
    (∫ x, potentialPair n ε h a w c x) =
      ∫ s, pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
        (coefficients n ε h a c s) (momentumCoefficients n ε h a c s) := by
  change (∫ x : ℝ × Transverse, potentialPair n ε h a w c x ∂volume.prod volume) = _
  rw [integral_prod _ (potentialPair_integrable n ε h a w c hε ha hh hw hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (potentialPair_slice n ε h a w c hε hh hw hb))

include hε ha hh hw hb in
theorem energyDensity_clock_integral :
    (∫ x, energyDensity n ε h a w c x) =
      ∫ s, (pairing n (groundWidth h) (neutralWidth h) w (scale ε (-h/2) s)
        (coefficients n ε h a c s) (coefficients n ε h a c s)).re := by
  change (∫ x : ℝ × Transverse, energyDensity n ε h a w c x ∂volume.prod volume) = _
  rw [integral_prod _ (energyDensity_integrable n ε h a w c hε ha hh hw hb)]
  exact integral_congr_ae (Filter.Eventually.of_forall (energyDensity_slice n ε h a w c hε hh hw hb))

#print axioms factorSum_factorization
#print axioms momentumFactorSum_factorization
#print axioms potentialPair_factorization
#print axioms energyDensity_factorization
#print axioms factorSum_memLp
#print axioms momentumFactorSum_memLp
#print axioms potentialPair_integrable
#print axioms energyDensity_integrable
#print axioms potentialPair_slice
#print axioms energyDensity_slice
#print axioms clock_pairing_integrable
#print axioms clock_energy_integrable
#print axioms potentialPair_clock_integral
#print axioms energyDensity_clock_integral
end
end UnifiedTheory.Audit.KFCausalReciprocalCrossPhysical
