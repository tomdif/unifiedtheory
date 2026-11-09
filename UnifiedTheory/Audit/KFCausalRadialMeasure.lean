/-
  Kernel-projector radial measure: closed curvature algebra, its integrated
  Ward defect, local pair flux, and hypercharge cancellation.
  These results do not supply the gauge-invariant local anomaly primitive.
  See RADIAL_MEASURE_RECONSTRUCTION.md for analytic and numerical scope.
-/
import UnifiedTheory.Audit.KFCausalPositiveMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRadialMeasure
noncomputable section
open Matrix KFCausalChiralMeasure
open scoped BigOperators

section Reflection
variable {R : Type*} [Ring R]

def reflection (P : R) : R := 1 - 2 * P

theorem reflection_involution (P : R) (hP : P * P = P) :
    reflection P * reflection P = 1 := by
  unfold reflection
  noncomm_ring [hP]

theorem tangent_reflection (P A : R) (hP : P * P = P)
    (hA : A * P + P * A = A) : reflection P * A * reflection P = -A := by
  have hdiag := tangent_diagonal_zero P A hP hA
  calc
    _ = A - 2 * (A * P + P * A) + 4 * (P * A * P) := by
      unfold reflection
      noncomm_ring
    _ = -A := by rw [hA, hdiag]; noncomm_ring

/-- A moving gauge frame adds this off-diagonal generator term. -/
theorem moving_generator_term (P X : R) (hP : P * P = P) :
    kato P (KFCausalChiralMeasure.comm X P) =
      X * P + P * X - 2 * (P * X * P) := by
  have hp (A : R) : P * (P * A) = P * A := by rw [← mul_assoc, hP]
  unfold kato KFCausalChiralMeasure.comm
  noncomm_ring [hP, hp]

end Reflection

section Curvature
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Op" => Matrix n n ℂ

omit [DecidableEq n] in
/-- Three tangent matrices have zero trace: they are odd under the projector reflection. -/
theorem triple_tangent_trace_zero (P A B C : Op) (hP : P * P = P)
    (hA : A * P + P * A = A) (hB : B * P + P * B = B)
    (hC : C * P + P * C = C) : trace (A * B * C) = 0 := by
  classical
  let Q := reflection P
  have hQ : Q * Q = 1 := reflection_involution P hP
  have ha : Q * A * Q = -A := tangent_reflection P A hP hA
  have hb : Q * B * Q = -B := tangent_reflection P B hP hB
  have hc : Q * C * Q = -C := tangent_reflection P C hP hC
  have hh (Z : Op) : Q * (Q * Z) = Z := by rw [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hproduct : Q * (A * B * C) * Q = -(A * B * C) := by
    calc
      _ = (Q * A * Q) * (Q * B * Q) * (Q * C * Q) := by
        simp only [Matrix.mul_assoc, hh]
      _ = _ := by rw [ha, hb, hc]; simp
  have htrace : trace (Q * (A * B * C) * Q) = trace (A * B * C) := by
    rw [trace_mul_cycle, hQ, Matrix.one_mul]
  rw [hproduct, trace_neg] at htrace
  linear_combination (-1 / 2 : ℂ) * htrace

/-- The cubic term in the exterior derivative of projector curvature vanishes. -/
theorem curvature_cubic_zero (P A B C : Op) (hP : P * P = P)
    (hA : A * P + P * A = A) (hB : B * P + P * B = B)
    (hC : C * P + P * C = C) : trace (A * KFCausalChiralMeasure.comm B C) = 0 := by
  simp only [KFCausalChiralMeasure.comm, Matrix.mul_sub, trace_sub, ← Matrix.mul_assoc]
  rw [triple_tangent_trace_zero P A B C hP hA hB hC,
    triple_tangent_trace_zero P A C B hP hA hC hB, sub_self]

/-- Swapping the gauge direction fixes the sign in the radial Ward calculation. -/
theorem radial_gauge_integrand (P A X : Op) (hP : P * P = P)
    (hA : A * P + P * A = A) :
    curvature P A (KFCausalChiralMeasure.comm X P) = Complex.I * trace (X * A) := by
  rw [curvature_antisymmetric, gauge_direction_curvature P X A hP hA]
  ring

end Curvature

section WardIntegral
open MeasureTheory

/-- The radial gauge contraction is an integration-by-parts identity. -/
theorem radial_weighted_derivative (a da : ℝ → ℝ)
    (ha : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt a (da t) t)
    (hai : IntervalIntegrable a volume 0 1)
    (hti : IntervalIntegrable (fun t => t * da t) volume 0 1) :
    (∫ t in (0 : ℝ)..1, t * da t) = a 1 - ∫ t in (0 : ℝ)..1, a t := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => s * a s) (a t + t * da t) t := by
    intro t ht
    simpa using (hasDerivAt_id t).mul (ha t ht)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hai.add hti)
  rw [intervalIntegral.integral_add hai hti] at h
  simp only [one_mul, zero_mul, sub_zero] at h
  linarith

/-- The radial current misses precisely the average density along the path. -/
theorem radial_ward_defect (a da : ℝ → ℝ)
    (ha : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt a (da t) t)
    (hai : IntervalIntegrable a volume 0 1)
    (hti : IntervalIntegrable (fun t => t * da t) volume 0 1) :
    -(∫ t in (0 : ℝ)..1, t * da t) + a 1 = ∫ t in (0 : ℝ)..1, a t := by
  rw [radial_weighted_derivative a da ha hai hti]
  ring

end WardIntegral

section PairFlux
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Op" => Matrix n n ℂ

/-- A bilocal flux; internal spin indices may be summed after this identity. -/
def pairFlux (K P : Op) (x y : n) : ℂ := K x y * P y x - P x y * K y x

omit [Fintype n] [DecidableEq n] in
theorem pairFlux_antisymmetric (K P : Op) (x y : n) :
    pairFlux K P x y = -pairFlux K P y x := by
  unfold pairFlux
  ring

theorem pairFlux_divergence (K P : Op) (x : n) :
    ∑ y, pairFlux K P x y = (KFCausalChiralMeasure.comm K P) x x := by
  simp [pairFlux, KFCausalChiralMeasure.comm, Matrix.mul_apply, Finset.sum_sub_distrib]

/-- Kato's generator supplies a finite local-in-potential divergence transgression. -/
theorem tangent_pairFlux_divergence (P A : Op) (hP : P * P = P)
    (hA : A * P + P * A = A) (x : n) :
    ∑ y, pairFlux (kato P A) P x y = A x x := by
  rw [pairFlux_divergence, kato_intertwining_generator P A hP hA]

omit [DecidableEq n] in
theorem pairFlux_total_zero (K P : Op) : ∑ x, ∑ y, pairFlux K P x y = 0 := by
  classical
  simp only [pairFlux_divergence]
  change trace (KFCausalChiralMeasure.comm K P) = 0
  rw [KFCausalChiralMeasure.comm, trace_sub, trace_mul_comm, sub_self]

omit [Fintype n] [DecidableEq n] in
/-- Covariance of BOTH supplied matrices makes each pair flux gauge invariant.
A radial gauge path has an extra generator term, so it does not meet this hypothesis. -/
theorem pairFlux_diagonal_covariance (K P : Op) (g : n → ℂ)
    (hg : ∀ x, g x ≠ 0) (x y : n) :
    pairFlux (fun i j => g i * K i j / g j) (fun i j => g i * P i j / g j) x y =
      pairFlux K P x y := by
  unfold pairFlux
  field_simp [hg x, hg y]

/-- A diagonal gauge motion changes pair flux by a divergence-free term. -/
theorem diagonal_gauge_flux_divergence (P : Op) (hP : P * P = P)
    (g : n → ℂ) (x : n) :
    ∑ y, pairFlux (kato P (KFCausalChiralMeasure.comm (diagonal g) P)) P x y = 0 := by
  have hA : KFCausalChiralMeasure.comm (diagonal g) P * P +
      P * KFCausalChiralMeasure.comm (diagonal g) P =
        KFCausalChiralMeasure.comm (diagonal g) P := by
    have hp (A : Op) : P * (P * A) = P * A := by rw [← Matrix.mul_assoc, hP]
    unfold KFCausalChiralMeasure.comm
    noncomm_ring [hP, hp]
  rw [tangent_pairFlux_divergence P _ hP hA]
  simp [KFCausalChiralMeasure.comm, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

end PairFlux

section ChargeMoments
/-- Supplied Standard Model hypercharges in the integer normalization q=6Y. -/
def hyperchargeSum (f : ℝ → ℝ) : ℝ :=
  6 * f 1 + 3 * f (-4) + 3 * f 2 + 2 * f (-3) + f 6

theorem hypercharge_low_orders (α β : ℝ) :
    hyperchargeSum (fun q => α * q + β * q ^ 3) = 0 := by
  unfold hyperchargeSum
  ring

theorem hypercharge_fifth_moment : hyperchargeSum (fun q => q ^ 5) = 4320 := by
  norm_num [hyperchargeSum]

/-- Cancellation removes the linear/cubic charge terms, not the higher remainder. -/
theorem hypercharge_remainder (α β : ℝ) (r : ℝ → ℝ) :
    hyperchargeSum (fun q => α * q + β * q ^ 3 + r q) = hyperchargeSum r := by
  unfold hyperchargeSum
  ring

/-- A uniform fifth-charge remainder bound gives a fourth-order field bound. -/
theorem hypercharge_remainder_bound (r : ℝ → ℝ) (C s : ℝ)
    (hr : ∀ q ∈ ({1, -4, 2, -3, 6} : Finset ℝ), |r q| ≤ C * |q| ^ 5 * |s| ^ 4) :
    |hyperchargeSum r| ≤ 11436 * C * |s| ^ 4 := by
  have h1 := hr 1 (by simp)
  have h4 := hr (-4) (by simp)
  have h2 := hr 2 (by simp)
  have h3 := hr (-3) (by simp)
  have h6 := hr 6 (by simp)
  norm_num at h1 h4 h2 h3 h6
  have hsum : |hyperchargeSum r| ≤
      6 * |r 1| + 3 * |r (-4)| + 3 * |r 2| + 2 * |r (-3)| + |r 6| := by
    unfold hyperchargeSum
    calc
      _ ≤ |6 * r 1 + 3 * r (-4) + 3 * r 2 + 2 * r (-3)| + |r 6| := abs_add_le _ _
      _ ≤ |6 * r 1 + 3 * r (-4) + 3 * r 2| + |2 * r (-3)| + |r 6| := by
        gcongr; exact abs_add_le _ _
      _ ≤ |6 * r 1 + 3 * r (-4)| + |3 * r 2| + |2 * r (-3)| + |r 6| := by
        gcongr; exact abs_add_le _ _
      _ ≤ |6 * r 1| + |3 * r (-4)| + |3 * r 2| + |2 * r (-3)| + |r 6| := by
        gcongr; exact abs_add_le _ _
      _ = _ := by norm_num [abs_mul]
  nlinarith

end ChargeMoments

#print axioms reflection_involution
#print axioms moving_generator_term
#print axioms tangent_reflection
#print axioms triple_tangent_trace_zero
#print axioms curvature_cubic_zero
#print axioms radial_gauge_integrand
#print axioms radial_weighted_derivative
#print axioms radial_ward_defect
#print axioms pairFlux_antisymmetric
#print axioms pairFlux_divergence
#print axioms tangent_pairFlux_divergence
#print axioms pairFlux_total_zero
#print axioms pairFlux_diagonal_covariance
#print axioms diagonal_gauge_flux_divergence
#print axioms hypercharge_low_orders
#print axioms hypercharge_fifth_moment
#print axioms hypercharge_remainder
#print axioms hypercharge_remainder_bound

end
end UnifiedTheory.Audit.KFCausalRadialMeasure
