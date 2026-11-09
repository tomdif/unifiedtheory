/-
  A positive finite Weyl determinant, its Ward/curvature algebra, and
  two locality diagnostics. The matrix identities have explicit inverse
  and projector hypotheses. Differential and locality assemblies are in
  POSITIVE_MEASURE_LOCALITY.md; a physical chiral continuum is not claimed.
-/
import UnifiedTheory.Audit.KFCausalGaugeDressedMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPositiveMeasure
noncomputable section
open scoped BigOperators
open Matrix KFCausalChiralMeasure KFCausalGaugeDressedMeasure

/-- Single-valued on the punctured complex plane; no argument branch is chosen. -/
def positivePhase (z : ℂ) : ℂ := (‖z‖ : ℂ) / z

theorem positivePhase_corrects (z : ℂ) (hz : z ≠ 0) :
    positivePhase z * z = (‖z‖ : ℂ) := by
  exact div_mul_cancel₀ _ hz

theorem positivePhase_unit_norm (z : ℂ) (hz : z ≠ 0) : ‖positivePhase z‖ = 1 := by
  simp [positivePhase, norm_ne_zero_iff.mpr hz]

theorem positivePhase_unitary (z : ℂ) (hz : z ≠ 0) :
    star (positivePhase z) * positivePhase z = 1 := by
  change starRingEnd ℂ (positivePhase z) * positivePhase z = 1
  rw [Complex.conj_mul', positivePhase_unit_norm z hz]
  norm_num

section MatrixCurrent
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Op" => Matrix n n ℂ

/-- D intertwines P with the fixed antifermion projector B. -/
theorem inverse_intertwines (D R P B : Op) (hDR : D * R = 1)
    (hDP : D * P = B * D) : D * P * R = B := by
  rw [hDP, Matrix.mul_assoc, hDR, Matrix.mul_one]

/-- The inverse maps the fixed antifermion space into the chiral domain. -/
theorem inverse_projector (D R P B : Op) (hDR : D * R = 1)
    (hRD : R * D = 1) (hDP : D * P = B * D) : P * R = R * B := by
  calc
    _ = R * (D * P * R) := by simp only [← Matrix.mul_assoc, hRD, Matrix.one_mul]
    _ = _ := by rw [inverse_intertwines D R P B hDR hDP]

/-- The logarithmic determinant term on a gauge tangent gives the anomaly. -/
theorem inverse_current_ward (D R P B X : Op) (hDR : D * R = 1)
    (hRD : R * D = 1) (hDP : D * P = B * D) :
    trace (R * comm X D * P) = trace (X * (B - P)) := by
  have hfirst : trace (R * X * D * P) = trace (X * B) := by
    calc
      _ = trace (R * (X * D * P)) := by simp only [Matrix.mul_assoc]
      _ = trace (X * D * P * R) := trace_mul_comm _ _
      _ = trace (X * (D * P * R)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [inverse_intertwines D R P B hDR hDP]
  have hsecond : R * (D * X) * P = X * P := by
    rw [← Matrix.mul_assoc R D X, hRD, Matrix.one_mul]
  simp only [KFCausalChiralMeasure.comm, Matrix.mul_sub, Matrix.sub_mul, trace_sub]
  rw [← Matrix.mul_assoc R X D, hfirst, hsecond]

omit [DecidableEq n] in
/-- Trace reduction for an idempotent, without Hermiticity assumptions. -/
theorem trace_projector_sandwich (P Z : Op) (hP : P * P = P) :
    trace (P * Z * P) = trace (P * Z) := by
  rw [trace_mul_cycle, hP]

/-- Projector curvature expressed in logarithmic Dirac derivatives. -/
theorem logarithmic_projector_curvature (P X Y : Op) (hP : P * P = P) :
    trace (P * comm (comm P X) (comm P Y)) = -trace (P * comm X Y) := by
  have hp (Z : Op) : P * (P * Z) = P * Z := by rw [← Matrix.mul_assoc, hP]
  have expand : P * comm (comm P X) (comm P Y) =
      (P * (X * P * Y) * P - P * (Y * P * X) * P) -
        (P * (X * Y) * P - P * (Y * X) * P) := by
    simp only [KFCausalChiralMeasure.comm]
    noncomm_ring [hP, hp]
  have cyc : trace (P * (X * P * Y)) = trace (P * (Y * P * X)) := by
    calc
      _ = trace ((P * X) * (P * Y)) := by simp only [Matrix.mul_assoc]
      _ = trace ((P * Y) * (P * X)) := trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [expand]
  simp only [trace_sub, trace_projector_sandwich P _ hP]
  rw [cyc]
  simp only [KFCausalChiralMeasure.comm, Matrix.mul_sub, trace_sub]
  abel

/-- Algebra left after differentiating Tr(D⁻¹ dD P) in commuting directions. -/
theorem logarithmic_current_exterior (P X Y : Op) :
    trace ((Y * X - X * Y) * P + Y * comm P X - X * comm P Y) =
      trace (P * comm X Y) := by
  have expand : (Y * X - X * Y) * P + Y * comm P X - X * comm P Y =
      Y * P * X - X * P * Y := by
    simp only [KFCausalChiralMeasure.comm]
    noncomm_ring
  rw [expand, trace_sub]
  have h1 : trace (Y * P * X) = trace (P * (X * Y)) := by
    rw [trace_mul_cycle', Matrix.mul_assoc]
  have h2 : trace (X * P * Y) = trace (P * (Y * X)) := by
    rw [trace_mul_cycle', Matrix.mul_assoc]
  rw [h1, h2]
  simp only [KFCausalChiralMeasure.comm, Matrix.mul_sub, trace_sub]

/-- The real current Im Tr(D⁻¹ dD P) has the required projector curvature. -/
theorem positive_current_curvature (P X Y : Op) (hP : P * P = P) :
    (trace ((Y * X - X * Y) * P + Y * comm P X - X * comm P Y)).im =
      (Complex.I * trace (P * comm (comm P X) (comm P Y))).re := by
  rw [logarithmic_current_exterior, logarithmic_projector_curvature P X Y hP]
  simp [Complex.mul_re]

end MatrixCurrent

section DirectFrame
variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
local notation "Op" => Matrix n n ℂ
local notation "Frame" => Matrix n k ℂ

/-- S is the positive inverse square root of the inverse-column Gram matrix. -/
def inverseFrame (R : Op) (B₀ : Frame) (S : Matrix k k ℂ) : Frame := R * B₀ * S

omit [DecidableEq n] [DecidableEq k] in
theorem inverseFrame_range (P R B : Op) (B₀ : Frame) (S : Matrix k k ℂ)
    (hPR : P * R = R * B) (hB : B * B₀ = B₀) :
    P * inverseFrame R B₀ S = inverseFrame R B₀ S := by
  simp only [inverseFrame, ← Matrix.mul_assoc, hPR]
  rw [Matrix.mul_assoc R B B₀, hB]

omit [DecidableEq n] in
theorem inverseFrame_isometry (R : Op) (B₀ : Frame) (S : Matrix k k ℂ)
    (hS : Sᴴ * ((R * B₀)ᴴ * (R * B₀)) * S = 1) :
    (inverseFrame R B₀ S)ᴴ * inverseFrame R B₀ S = 1 := by
  simpa only [inverseFrame, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hS

/-- The Weyl matrix itself is S, hence positive when the analytic Gram factor is. -/
theorem inverseFrame_weyl (D R : Op) (B₀ : Frame) (S : Matrix k k ℂ)
    (hDR : D * R = 1) (hB : B₀ᴴ * B₀ = 1) :
    weylMatrix D (inverseFrame R B₀ S) B₀ = S := by
  calc
    _ = B₀ᴴ * (D * R) * B₀ * S := by
      simp only [weylMatrix, inverseFrame, Matrix.mul_assoc]
    _ = S := by rw [hDR, Matrix.mul_one, hB, Matrix.one_mul]

end DirectFrame

section Counterterms
variable {E : Type*} [AddCommGroup E]

/-- A rectangular field-space increment measures the mixed response of a phase. -/
def mixedIncrement (f : E → ℝ) (x u v : E) : ℝ :=
  f (x + u + v) - f (x + u) - f (x + v) + f x

theorem mixedIncrement_zero_left (f : E → ℝ) (u v x : E)
    (hu : ∀ y, f (y + u) = f y) : mixedIncrement f x u v = 0 := by
  have h : x + u + v = (x + v) + u := by abel
  simp only [mixedIncrement, h, hu]
  ring

theorem mixedIncrement_zero_right (f : E → ℝ) (u v x : E)
    (hv : ∀ y, f (y + v) = f y) : mixedIncrement f x u v = 0 := by
  simp only [mixedIncrement, hv]
  ring

/-- Each local summand misses at least one of the separated field increments. -/
theorem separated_counterterm_zero {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (x u v : E)
    (hlocal : ∀ i ∈ s, (∀ y, f i (y + u) = f i y) ∨ (∀ y, f i (y + v) = f i y)) :
    mixedIncrement (fun y => ∑ i ∈ s, f i y) x u v = 0 := by
  have hz : ∀ i ∈ s, mixedIncrement (f i) x u v = 0 := by
    intro i hi
    rcases hlocal i hi with h | h
    · exact mixedIncrement_zero_left (f i) u v x h
    · exact mixedIncrement_zero_right (f i) u v x h
  unfold mixedIncrement
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero hz

/-- A bounded correction can reduce a response by at most its own magnitude. -/
theorem response_lower_bound (a b ε : ℝ) (hb : |b| ≤ ε) : |a| - ε ≤ |a + b| := by
  have h := abs_add_le (a + b) (-b)
  simp only [add_neg_cancel_right, abs_neg] at h
  linarith

end Counterterms

section AntiperiodicInverse
/-- Exact inverse of the one-dimensional difference with antiperiodic closure. -/
def antiperiodicInverse (a : ℕ → ℝ) (N i : ℕ) : ℝ :=
  prefixCurrent a i - prefixCurrent a N / 2

theorem antiperiodic_inverse_bulk (a : ℕ → ℝ) (N i : ℕ) :
    antiperiodicInverse a N (i + 1) - antiperiodicInverse a N i = a (i + 1) := by
  unfold antiperiodicInverse
  have h := prefixCurrent_divergence a i
  linarith

theorem antiperiodic_inverse_boundary (a : ℕ → ℝ) (N : ℕ) :
    antiperiodicInverse a N 0 + antiperiodicInverse a N N = a 0 := by
  simp only [antiperiodicInverse, prefixCurrent_first]
  ring

theorem antiperiodic_inverse_unique (a x : ℕ → ℝ) (N : ℕ)
    (h0 : x 0 + x N = a 0)
    (hstep : ∀ i < N, x (i + 1) - x i = a (i + 1)) :
    ∀ i ≤ N, x i = antiperiodicInverse a N i := by
  have hc : ∀ i ≤ N, x i = prefixCurrent a i + (x 0 - a 0) := by
    intro i hi
    induction i with
    | zero => simp [prefixCurrent_first]
    | succ i ih =>
      have hs := hstep i (by omega)
      have hp := prefixCurrent_divergence a i
      have hh := ih (by omega)
      linarith
  have hn := hc N (le_refl N)
  intro i hi
  have hh := hc i hi
  unfold antiperiodicInverse
  linarith

/-- Every inverse entry is ±1/2, however far its two sites are separated. -/
theorem antiperiodic_inverse_delta (N i j : ℕ) (hj : j ≤ N) :
    antiperiodicInverse (fun k => if k = j then 1 else 0) N i =
      if j ≤ i then (1 / 2 : ℝ) else -(1 / 2 : ℝ) := by
  have hN : j ∈ Finset.range (N + 1) := by simp; omega
  unfold antiperiodicInverse prefixCurrent
  simp only [Finset.sum_ite_eq', hN, if_true]
  by_cases hji : j ≤ i
  · have hmem : j ∈ Finset.range (i + 1) := by simp; omega
    norm_num [hmem, hji]
  · have hmem : j ∉ Finset.range (i + 1) := by simp; omega
    norm_num [hmem, hji]

/-- Increasing the antiperiodic circumference does not make inverse entries decay. -/
theorem antiperiodic_inverse_remote (r : ℕ) :
    |antiperiodicInverse (fun k => if k = 0 then 1 else 0) (2 * r + 1) r| = 1 / 2 := by
  rw [antiperiodic_inverse_delta _ _ _ (by omega)]
  norm_num

end AntiperiodicInverse

#print axioms positivePhase_corrects
#print axioms positivePhase_unit_norm
#print axioms positivePhase_unitary
#print axioms inverse_intertwines
#print axioms inverse_projector
#print axioms inverseFrame_range
#print axioms inverseFrame_isometry
#print axioms inverseFrame_weyl
#print axioms inverse_current_ward
#print axioms trace_projector_sandwich
#print axioms logarithmic_projector_curvature
#print axioms logarithmic_current_exterior
#print axioms positive_current_curvature
#print axioms mixedIncrement_zero_left
#print axioms mixedIncrement_zero_right
#print axioms separated_counterterm_zero
#print axioms response_lower_bound
#print axioms antiperiodic_inverse_bulk
#print axioms antiperiodic_inverse_boundary
#print axioms antiperiodic_inverse_unique
#print axioms antiperiodic_inverse_delta
#print axioms antiperiodic_inverse_remote

end
end UnifiedTheory.Audit.KFCausalPositiveMeasure
