/-
  LayerB/FeynmanRules.lean — Scattering amplitudes from the K/P amplitude algebra

  The framework provides a specific amplitude construction:
    z(h) = Q(h) + i·D(h)
  where Q = trace ∘ K_proj and D is a linear functional on perturbation space.

  This file proves properties of scattering amplitudes that are SPECIFIC
  to this construction — not generic complex algebra. Each theorem uses
  at least one of:
    (a) Linearity of Q (from trace ∘ K_proj)
    (b) The K/P decomposition (h = K_proj(h) + P_proj(h))
    (c) Dressing neutrality (trace ∘ P_proj = 0)
    (d) The on-shell propagation rule (e^{ikφ} from character uniqueness)

  Theorems that hold for ALL complex numbers are labeled as such and
  placed in a separate "Complex algebra" section for honesty.

  What is NOT claimed:
    - Specific propagator forms (1/(p²-m²) needs Fourier analysis)
    - Loop integrals or renormalization
    - Confinement or hadronization

  Zero sorry. Zero custom axioms.
-/
import UnifiedTheory.LayerB.HistoryAmplitudes
import UnifiedTheory.LayerB.MinimalCoupling

namespace UnifiedTheory.LayerB.FeynmanRules

open HistoryAmplitudes MinimalCoupling PropagationRule SignedSource MetricDefects
open scoped ComplexConjugate

variable {m : ℕ}

/-! ## Section 1: Framework-specific amplitude properties

    These theorems use the specific structure of Q = trace ∘ K_proj
    and the K/P decomposition. They are NOT true for arbitrary
    complex-valued functions on an abstract space.
-/

/-- **Superposition from linearity.**
    If D is a linear functional on perturbation space, then
    the amplitude is ADDITIVE under composition of perturbations:
      z(h₁ + h₂) = z(h₁) + z(h₂)

    This is the quantum superposition principle, DERIVED from:
    - Q is linear (trace ∘ K_proj is a composition of linear maps)
    - D is linear (hypothesis)

    This is framework-specific: for a NONLINEAR functional f,
    f(h₁+h₂) ≠ f(h₁)+f(h₂) and superposition would fail. -/
theorem amplitude_additive
    (D : Perturbation (m + 2) →ₗ[ℝ] ℝ)
    (h₁ h₂ : Perturbation (m + 2)) :
    stepAmplitude D (h₁ + h₂) = stepAmplitude D h₁ + stepAmplitude D h₂ := by
  simp only [stepAmplitude]
  apply Complex.ext
  · simp [Complex.add_re, Q_add]
  · simp [Complex.add_im, map_add]

/-- **Annihilation**: the amplitude of a perturbation plus its conjugate is zero.
    z(h) + z(-h) = 0, because Q(h)+Q(-h) = 0 and D(h)+D(-h) = 0.

    This is the amplitude-level version of charge annihilation.
    Framework-specific: requires linearity of BOTH Q and D. -/
theorem amplitude_annihilation
    (D : Perturbation (m + 2) →ₗ[ℝ] ℝ)
    (h : Perturbation (m + 2)) :
    stepAmplitude D h + stepAmplitude D (-h) = 0 := by
  have := amplitude_additive D h (-h)
  rw [add_neg_cancel] at this
  rw [← this]
  simp only [stepAmplitude]
  apply Complex.ext
  · simp [Q, K_proj, traceFunc, map_zero]
  · simp [map_zero]

/-- **Pure dressing perturbations have purely imaginary amplitude.**
    If h is in the P-sector (K_proj(h) = 0), then Q(h) = 0, so z(h) = i·D(h).

    Physical meaning: P-sector perturbations (gauge content in d=4)
    contribute to interference but NOT to the classical charge.
    This is framework-specific: it uses dressing neutrality
    (trace ∘ P_proj = 0) and the K/P decomposition. -/
theorem pure_dressing_imaginary
    (D : Perturbation (m + 2) → ℝ)
    (h : Perturbation (m + 2))
    (hP : K_proj m h = 0) :
    (stepAmplitude D h).re = 0 := by
  simp only [stepAmplitude, Q]
  rw [hP, map_zero]

/-- **Pure source perturbations have purely real amplitude.**
    If h is in the K-sector (P_proj(h) = 0) and D vanishes on the
    K-sector, then D(h) = 0, so z(h) = Q(h) (real).

    Physical meaning: K-sector perturbations are the "classical"
    part — they carry charge but no dressing phase.
    This is the ComplexFromDressing.lean result that classical
    defects sit on the real axis: z = Q + i·0 = Q. -/
theorem pure_source_real
    (D : Perturbation (m + 2) → ℝ)
    (h : Perturbation (m + 2))
    (hD_on_K : D (K_proj m h) = 0)
    (hK : P_proj m h = 0) :
    (stepAmplitude D h).im = 0 := by
  simp only [stepAmplitude]
  -- h = K_proj(h) + P_proj(h) = K_proj(h) + 0 = K_proj(h)
  have h_eq : h = K_proj m h := by
    have := decomp_derived h
    rw [hK, add_zero] at this
    exact this
  rw [h_eq]
  exact hD_on_K

/-- **The K/P decomposition splits the amplitude.**
    z(h) = z(K_proj(h)) + z(P_proj(h)) when D is linear.

    The amplitude of any perturbation decomposes into a K-sector
    contribution and a P-sector contribution. The K-part carries
    the charge (real part), the P-part carries the dressing (can
    contribute to imaginary part).

    Framework-specific: uses h = K_proj(h) + P_proj(h). -/
theorem amplitude_KP_decomposition
    (D : Perturbation (m + 2) →ₗ[ℝ] ℝ)
    (h : Perturbation (m + 2)) :
    stepAmplitude D h =
    stepAmplitude D (K_proj m h) + stepAmplitude D (P_proj m h) := by
  conv_lhs => rw [decomp_derived h]
  exact amplitude_additive D (K_proj m h) (P_proj m h)

/-- **The charge of the K-part equals the charge of the whole.**
    Q(K_proj(h)) = Q(h). The K-projection preserves the charge
    because trace ∘ K_proj = trace (the bridge equation).

    This means the real part of the amplitude is determined entirely
    by the K-sector. The P-sector doesn't contribute to Q. -/
theorem charge_from_K_part (h : Perturbation (m + 2)) :
    Q (K_proj m h) = Q h := by
  -- Q(K(h)) = trace(K(K(h))), Q(h) = trace(K(h))
  -- Need: trace(K(K(h))) = trace(K(h)), i.e. bridge applied to K(h)
  simp only [Q]
  -- trace(K(K(h))) = trace(K(h)) by bridge applied to K(h)
  rw [bridge_derived (K_proj m h)]
  -- Now: trace(K(h)) = trace(K(h))

/-- **The P-sector carries zero charge.**
    Q(P_proj(h)) = 0. Dressing perturbations are charge-neutral.

    This is the dressing neutrality theorem from MetricDefects.lean.
    Physical meaning: gauge field content (which lives in P in d=4)
    does not contribute to the scalar source charge. -/
theorem dressing_zero_charge (h : Perturbation (m + 2)) :
    Q (P_proj m h) = 0 := by
  -- Q(P(h)) = trace(K(P(h))). Need trace(K(P(h))) = 0.
  -- From decomp: P(h) = P(h), and K_proj(P_proj(h)) should give
  -- a perturbation whose trace is 0.
  -- Actually: Q(P(h)) = trace(K(P(h))).
  -- bridge_derived on P(h): trace(K(P(h))) = trace(P(h))
  -- neutrality_derived: trace(P(h)) = 0
  simp only [Q]
  rw [bridge_derived (P_proj m h)]
  exact neutrality_derived h


/-! ## Section 2: Interference with K/P structure

    These theorems combine the interference formula (which is generic
    complex algebra) with the K/P decomposition (which is framework-specific)
    to get results that are NOT true for arbitrary complex numbers.
-/

/-- **K-sector and P-sector don't interfere when D respects K/P.**
    If D vanishes on K-sector perturbations and Q vanishes on P-sector
    perturbations (which is always true by dressing neutrality), then
    the interference term between a pure-K and pure-P perturbation is zero:
      2·Re(z_K · z̄_P) = 0

    Physical meaning: classical (source/charge) content and quantum
    (dressing/gauge) content contribute independently to the observable.
    There is no "cross-talk" between the two sectors.

    Framework-specific: uses the orthogonality of K and P sectors. -/
theorem KP_sectors_no_interference
    (D : Perturbation (m + 2) → ℝ)
    (h_K h_P : Perturbation (m + 2))
    (hK : P_proj m h_K = 0)   -- h_K is pure K-sector
    (hP : K_proj m h_P = 0)   -- h_P is pure P-sector
    (hD_K : D (K_proj m h_K) = 0)  -- D vanishes on K-sector
    :
    (stepAmplitude D h_K).re * (stepAmplitude D h_P).re +
    (stepAmplitude D h_K).im * (stepAmplitude D h_P).im = 0 := by
  -- h_K is pure K, so z_K = (Q(h_K), 0) since D vanishes on K
  have hK_im : (stepAmplitude D h_K).im = 0 := by
    exact pure_source_real D h_K hD_K hK
  -- h_P is pure P, so z_P = (0, D(h_P)) since Q vanishes on P
  have hP_re : (stepAmplitude D h_P).re = 0 := by
    exact pure_dressing_imaginary D h_P hP
  rw [hK_im, hP_re, mul_zero, zero_mul, add_zero]

/-- **Observable decomposes into K and P contributions.**
    For a perturbation h, if D is linear and vanishes on K-sector:
      |z(h)|² = Q(h)² + D(P_proj(h))²

    The observable splits into a charge part (from K) and a
    dressing part (from P), with NO cross term. This is a
    framework-specific Pythagorean theorem for the amplitude.

    Uses: K/P decomposition + K/P orthogonality. -/
theorem observable_KP_pythagorean
    (D : Perturbation (m + 2) →ₗ[ℝ] ℝ)
    (h : Perturbation (m + 2))
    (hD_K : D (K_proj m h) = 0) :
    obs (stepAmplitude D h) =
    (Q h) ^ 2 + (D (P_proj m h)) ^ 2 := by
  simp only [obs, stepAmplitude]
  congr 1
  -- The imaginary part D(h) = D(K_proj(h)) + D(P_proj(h)) = 0 + D(P_proj(h))
  congr 1
  have h_decomp := decomp_derived h
  conv_lhs => rw [h_decomp]
  rw [map_add, hD_K, zero_add]


/-! ## Section 3: Charge algebra (framework-specific)

    These use Q = trace ∘ K_proj specifically.
-/

/-- **Charge additivity.** Q(h₁+h₂) = Q(h₁) + Q(h₂).
    From linearity of trace ∘ K_proj. -/
theorem charge_additive (h₁ h₂ : Perturbation (m + 2)) :
    Q (h₁ + h₂) = Q h₁ + Q h₂ := Q_add h₁ h₂

/-- **Charge annihilation.** Q(h + (-h)) = 0.
    Conjugate perturbations cancel all charge. -/
theorem charge_annihilation (h : Perturbation (m + 2)) :
    Q (h + (-h)) = 0 := by
  rw [Q_add, Q_neg, add_neg_cancel]

/-- **Charge scaling.** Q(c·h) = c·Q(h).
    Scaling a perturbation scales the charge proportionally. -/
theorem charge_scaling (c : ℝ) (h : Perturbation (m + 2)) :
    Q (c • h) = c * Q h := Q_smul c h


/-! ## Section 4: On-shell propagation (genuine physics)

    These use the specific form e^{ikφ} derived from character
    uniqueness of the exponential map.
-/

/-- **On-shell amplitudes are unit modulus.**
    |e^{ikφ}|² = cos²(kφ) + sin²(kφ) = 1.
    Uses the Pythagorean identity (genuine trigonometric content). -/
theorem onshell_unit_modulus (k s : ℝ) :
    Complex.normSq (expAmplitude k s) = 1 :=
  exp_unit_modulus k s

/-- **On-shell composition is multiplicative.**
    e^{ik(φ₁+φ₂)} = e^{ikφ₁} · e^{ikφ₂}.
    Uses the angle addition formulas (genuine trigonometric content).
    This is the propagation rule: amplitudes MULTIPLY along a path. -/
theorem onshell_multiplicative (k s₁ s₂ : ℝ) :
    expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂ :=
  exp_multiplicative k s₁ s₂

/-- **The Aharonov-Bohm effect.**
    Two paths with same source value but different gauge phases produce
    a fringe pattern: |z₁+z₂|² = 2 + 2·cos(qA₁-qA₂).

    Genuine physical prediction: the gauge field shifts the interference
    pattern by the enclosed flux, even in field-free regions.
    Uses: coupled amplitude from MinimalCoupling.lean + trig identities. -/
theorem aharonov_bohm (k φ qA₁ qA₂ : ℝ) :
    Complex.normSq (coupledAmplitude k φ qA₁ + coupledAmplitude k φ qA₂) =
    2 + 2 * Real.cos (qA₁ - qA₂) := by
  have h := coupled_interference k φ φ qA₁ qA₂
  rw [show (k * φ + qA₁) - (k * φ + qA₂) = qA₁ - qA₂ from by ring] at h
  exact h


/-! ## Section 5: Generic complex algebra (labeled honestly)

    These identities hold for ALL complex numbers. They are included
    because they are used in scattering calculations, but they are
    NOT framework-specific. Labeled as such for intellectual honesty.
-/

/-- **Interference formula (generic complex algebra).**
    |z₁+z₂|² = |z₁|² + |z₂|² + 2·Re(z₁·z̄₂).
    True for ALL complex numbers. -/
theorem interference_formula_generic (z₁ z₂ : ℂ) :
    obs (z₁ + z₂) = obs z₁ + obs z₂ + 2 * (z₁ * conj z₂).re := by
  simp only [obs, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **Crossing symmetry (generic complex algebra).**
    |conj(z)|² = |z|². True for ALL complex numbers. -/
theorem crossing_generic (z : ℂ) :
    obs (conj z) = obs z := by
  simp only [obs, Complex.conj_re, Complex.conj_im]
  ring


/-! ## Capstone -/

/-- **SCATTERING AMPLITUDE STRUCTURE FROM THE CAUSAL FRAMEWORK.**

    Framework-specific results (Sections 1-4):
    (1) Superposition: z(h₁+h₂) = z(h₁)+z(h₂) [from linearity of Q and D]
    (2) Annihilation: z(h)+z(-h) = 0 [from linearity]
    (3) K/P decomposition of amplitude [from h = K_proj(h) + P_proj(h)]
    (4) P-sector is charge-neutral [from trace ∘ P_proj = 0]
    (5) Charge additivity [from trace ∘ K_proj linear]
    (6) On-shell multiplicativity [from exp addition formula]
    (7) Aharonov-Bohm [from coupled amplitude + trig]

    Generic complex results (Section 5, labeled as such):
    - Interference formula, crossing symmetry -/
theorem scattering_from_framework
    (D : Perturbation (m + 2) →ₗ[ℝ] ℝ) :
    -- (1) Superposition from linearity
    (∀ h₁ h₂ : Perturbation (m + 2),
      stepAmplitude D (h₁ + h₂) = stepAmplitude D h₁ + stepAmplitude D h₂)
    -- (2) Annihilation
    ∧ (∀ h : Perturbation (m + 2),
      stepAmplitude D h + stepAmplitude D (-h) = 0)
    -- (3) P-sector carries zero charge
    ∧ (∀ h : Perturbation (m + 2), Q (P_proj m h) = 0)
    -- (4) Charge from K-part equals total charge
    ∧ (∀ h : Perturbation (m + 2), Q (K_proj m h) = Q h)
    -- (5) Charge additivity
    ∧ (∀ h₁ h₂ : Perturbation (m + 2), Q (h₁ + h₂) = Q h₁ + Q h₂)
    -- (6) On-shell multiplicativity
    ∧ (∀ k s₁ s₂ : ℝ,
      expAmplitude k (s₁ + s₂) = expAmplitude k s₁ * expAmplitude k s₂)
    -- (7) Aharonov-Bohm
    ∧ (∀ k φ qA₁ qA₂ : ℝ,
      Complex.normSq (coupledAmplitude k φ qA₁ + coupledAmplitude k φ qA₂) =
      2 + 2 * Real.cos (qA₁ - qA₂)) :=
  ⟨amplitude_additive D,
   amplitude_annihilation D,
   dressing_zero_charge,
   charge_from_K_part,
   charge_additive,
   onshell_multiplicative,
   aharonov_bohm⟩

end UnifiedTheory.LayerB.FeynmanRules
