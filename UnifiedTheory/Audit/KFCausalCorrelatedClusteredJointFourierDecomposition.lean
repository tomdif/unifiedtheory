/- Exact decomposition of the original Fourier profiles and normalized
clock expressions into controlled joint Gaussian terms. The only extra
clock coefficient is one actual Gaussian clock moment. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowNormalizedCoefficients
import UnifiedTheory.Audit.KFCausalShiftedNarrowWeightedProfiles

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierDecomposition
noncomputable section
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalClockFloorRelativeShift (scale argument)
open KFCausalShiftedNarrowJointGaussian (narrow spectator N Z gaussian)
open KFCausalShiftedNarrowControlledFactors (F normalization amplitudeRate normalizedRadius)
open KFCausalShiftedNarrowNormalizedCoefficients
open KFCausalShiftedNarrowWeightedProfiles (weighted weightedJet quotientJet)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalCorrelatedClusteredPotentialFourierClock
open KFCausalCorrelatedClusteredShiftedNarrowProfiles (coefficient)
open KFCausalShiftedNarrowFourierClockDerivative (coefficientSlope)

theorem gaussian_neutral_split (α β ε y : ℝ) (b : ℂ) (x : Configuration) :
    gaussian α β ε y b x = Complex.exp (-Z α ε y x)*Complex.exp (-(β:ℂ)*N ε y x^2+b*N ε y x) := by
  rw [← Complex.exp_add]
  unfold gaussian
  congr 1
  ring

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
local notation "c" => amplitudes ε y a p
local notation "r" => scale ε y
local notation "t" => scale ε z

def momentAmplitude (s : ℝ) (i : Fin m) : ℂ := argument ε y s*c s i
def inputPart (i : Fin m) := inputCoefficient α ε y z (f.amplitude i) (f.polynomial i) k
def regularPart (i : Fin m) := regularCoefficient α β ε y z (p i) (f.amplitude i) (f.source i) (f.polynomial i) k
def chargedPart (i : Fin m) := chargedCoefficient α ε y z (f.amplitude i) (f.polynomial i) k

theorem coefficient_eq (x : Configuration) (i : Fin m) :
    coefficient f (c x.1) α β (r x.1) (t x.1) k i (spectator x) =
      c x.1 i*Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*inputPart f α ε y z k i x := by
  unfold coefficient inputPart inputCoefficient core
    KFCausalShiftedNarrowFourierSlices.neutralPacket
  rw [normalization_eq]
  dsimp [N,F]
  ring

variable (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)

include hα hε hy hz in
theorem coefficient_clock_eq (x : Configuration) (i : Fin m) :
    realInverse ε x.1*coefficientSlope f (c x.1) (amplitudeDerivative ε y a p x.1) α β
      (r x.1) (KFCausalNeutralPlaneClockGeometry.velocity ε (Real.exp x.1) (r x.1))
      (t x.1) (KFCausalNeutralPlaneClockGeometry.velocity ε (Real.exp x.1) (t x.1)) k i (spectator x)+
      (KFCausalClockFloorPureClockDerivative.rate ε x.1:ℂ)*coefficient f (c x.1) α β (r x.1) (t x.1) k i (spectator x) =
      c x.1 i*Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*
        (regularPart f α β ε y z p k i x-2*(a i:ℂ)*argument ε y x.1*inputPart f α ε y z k i x) := by
  have hd := normalization_normalized α ε y hα hε hy x
  have ha := amplitude_normalized ε (a i) (p i) y hε x
  have hf := field_normalized ε z hε hz x
  have hn := neutral_normalized ε y hε hy x
  unfold coefficientSlope coefficient amplitudeDerivative
    KFCausalShiftedNarrowFourierSlices.neutralPacket KFCausalShiftedNarrowFourierClockDerivative.packetSlope
    regularPart regularCoefficient inputPart inputCoefficient coreRate core amplitudeRate
  simp only [normalization_eq] at hd ⊢
  dsimp [N,F] at *
  linear_combination (norm := (simp only [N,F,normalization_eq]; ring))
    (f.amplitude i*c x.1 i*(F ε z x)^k*Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*
      (f.polynomial i).eval (N ε y x))*hd +
    (normalization α ε y x*f.amplitude i*c x.1 i*(F ε z x)^k*
      Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*(f.polynomial i).eval (N ε y x))*ha +
    (normalization α ε y x*f.amplitude i*c x.1 i*(k:ℂ)*(F ε z x)^(k-1)*
      Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*(f.polynomial i).eval (N ε y x))*hf +
    (normalization α ε y x*f.amplitude i*c x.1 i*(F ε z x)^k*
      Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*
        ((f.source i-2*(β:ℂ)*N ε y x)*(f.polynomial i).eval (N ε y x)+
          (f.polynomial i).derivative.eval (N ε y x)))*hn

include hα hε hy in
theorem input_decomposition (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x) =
      ∑ i, weighted α β ε y (f.source i) (fun s => c s i) (inputPart f α ε y z k i) (f.degree i) δ x := by
  rw [fourierProfile_eq f α β ε y z a p k hα hε hy δ x.1 hδ,
    KFCausalCorrelatedClusteredShiftedNarrowProfiles.transformed_exact _ _ _ _ _ _ _ δ hδ]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_eq]
  unfold weighted
  rw [gaussian_neutral_split]
  unfold Z
  ring

include hα hε hy hz in
theorem clock_decomposition (δ : ℝ) (hδ : 0 < δ) (x : Configuration) :
    clockExpression f α β ε y z a p k δ x.1 (narrow x) (spectator x) =
      ∑ i, (weighted α β ε y (f.source i) (fun s => c s i)
          (regularPart f α β ε y z p k i) (f.degree i) δ x+
        weightedJet α β ε y (f.source i) (fun s => c s i)
          (chargedPart f α ε y z k i) (f.degree i) δ x-
        (2*(a i:ℂ))*weighted α β ε y (f.source i) (fun s => momentAmplitude ε y a p s i)
          (inputPart f α ε y z k i) (f.degree i) δ x) := by
  rw [clockExpression,fourierProfile_eq f α β ε y z a p k hα hε hy δ x.1 hδ]
  unfold fourierJet KFCausalCorrelatedClusteredShiftedNarrowJet.clockJet
    KFCausalCorrelatedClusteredShiftedNarrowProfiles.transformed
  simp_rw [KFCausalClusteredWidthProfiles.laplaceSum_exact _ δ hδ]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hC := coefficient_clock_eq f α β ε y z a p k hα hε hy hz x i
  have hR := radius_normalized α ε y hα hε hy x
  rw [coefficient_eq f α β ε y z a p k x i] at hC ⊢
  unfold weighted weightedJet chargedPart chargedCoefficient momentAmplitude
    KFCausalClusteredWidthChargedJet.jet
  rw [gaussian_neutral_split]
  unfold quotientJet
  linear_combination (norm := (simp only [Z,inputPart]; ring))
    (Complex.exp (-Z α ε y x)*KFCausalClusteredWidthProfiles.quotient δ (Z α ε y x)^(f.degree i))*hC +
    (c x.1 i*Complex.exp (-(β:ℂ)*N ε y x^2+f.source i*N ε y x)*inputPart f α ε y z k i x*
      Complex.exp (-Z α ε y x)*
      ((f.degree i:ℂ)*KFCausalClusteredWidthProfiles.quotient δ (Z α ε y x)^(f.degree i-1)*
        Complex.exp (-(δ:ℂ)*Z α ε y x)-KFCausalClusteredWidthProfiles.quotient δ (Z α ε y x)^(f.degree i)))*hR

#print axioms gaussian_neutral_split
#print axioms coefficient_eq
#print axioms coefficient_clock_eq
#print axioms input_decomposition
#print axioms clock_decomposition
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierDecomposition
