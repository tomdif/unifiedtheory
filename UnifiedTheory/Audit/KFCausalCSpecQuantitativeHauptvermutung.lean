/-
  Audit/KFCausalCSpecQuantitativeHauptvermutung.lean
  — ORDER + NUMBER = GEOMETRY, WITH ERROR BARS

  The quantitative Hauptvermutung, local/flat sector.  The composition the
  program was built for:

  counting  →  proper time  →  metric components  →  point location,
  with every constant explicit and every step machine-checked.

  1.  `polarization`:  the metric components in an anchor frame are LINEAR in
      the squared-interval data:  B(aᵢ−a₀, aⱼ−a₀) = ½(σ²ᵢ₀ + σ²ⱼ₀ − σ²ᵢⱼ).
  2.  `gram_reconstruction_lipschitz`:  interval errors ≤ δ  ⟹  metric
      component error ≤ (3/2)·δ.  The Lipschitz constant of geometry against
      interval data is 3/2.
  3.  `trilateration_stability`:  the quantitative upgrade of Step-4
      trilateration — with a stability constant C for the anchor frame, any
      two points consistent with the same interval data within δ satisfy
      ‖p − q‖ ≤ 2·C·δ.
  4.  `count_estimator_error`:  the 4D counting dictionary V = (π/24)τ⁴ with
      Poisson-concentrated counts |n/ρV − 1| ≤ ε gives the proper-time
      estimator  τ̂² = √(24n/(πρ))  with  |τ̂² − τ²| ≤ ε·τ².
  5.  `quantitative_hauptvermutung`:  THE COMPOSITION — the metric component
      B(aᵢ−a₀, aⱼ−a₀) is estimated from THREE COUNTS by the explicit formula
      ½(√(24nᵢ₀/πρ) + √(24nⱼ₀/πρ) − √(24nᵢⱼ/πρ)) with error ≤ (3/2)·ε·S,
      S = max σ².  With ε = k/√(ρV_min) this is the O((ρV)^{−1/2}) law.
  6.  `hauptvermutung_failure_probability`:  the concentration windows hold
      jointly outside probability  m·(1/(ρV_min·ε²))  (union bound over the
      m pairs; each marginal bounded by `poisson_count_concentration`).

  Fifty years of "order + number = geometry" folklore, now with constants:
  3/2 (polarization), 2C (trilateration), π/24 (the 4D dictionary), 1/(rε²)
  (Chebyshev–Poisson).  Zero sorry.  Zero custom axioms.
-/
import Mathlib
import UnifiedTheory.Audit.KFCausalCSpecTrilateration
import UnifiedTheory.Audit.KFCausalCSpecCountConcentration
import UnifiedTheory.Audit.KFCausalCSpecPoissonConcentration

set_option autoImplicit false

open MeasureTheory

namespace UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung

/-! ## 1. Polarization: geometry is linear in interval data -/

/-- The squared interval of the bilinear metric form `B`. -/
noncomputable def sigma2 {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x y : V) : ℝ := B (x - y) (x - y)

/-- **Polarization.**  The metric components in the anchor frame are linear
functionals of the squared-interval data. -/
theorem polarization {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (ai aj ao : V) :
    B (ai - ao) (aj - ao)
      = (sigma2 B ai ao + sigma2 B aj ao - sigma2 B ai aj) / 2 := by
  unfold sigma2
  simp only [map_sub, LinearMap.sub_apply]
  have s1 := hsymm ai aj
  have s2 := hsymm ai ao
  have s3 := hsymm aj ao
  linarith

/-! ## 2. Lipschitz recovery of the metric components -/

/-- **The metric is 3/2-Lipschitz in interval data.**  If each of the three
squared intervals is measured to accuracy δ, the polarization estimator
recovers the metric component to accuracy (3/2)·δ. -/
theorem gram_reconstruction_lipschitz {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (ai aj ao : V) (mio mjo mij δ : ℝ)
    (hio : |mio - sigma2 B ai ao| ≤ δ)
    (hjo : |mjo - sigma2 B aj ao| ≤ δ)
    (hij : |mij - sigma2 B ai aj| ≤ δ) :
    |(mio + mjo - mij) / 2 - B (ai - ao) (aj - ao)| ≤ 3/2 * δ := by
  rw [polarization B hsymm ai aj ao]
  rw [abs_le] at hio hjo hij ⊢
  constructor
  · linarith [hio.1, hjo.1, hij.2]
  · linarith [hio.2, hjo.2, hij.1]

/-! ## 3. Quantitative trilateration: point location stability -/

/-- **Quantitative trilateration.**  `Cstab` is the stability constant of the
anchor frame (the quantitative general-position datum: any vector whose inner
products against all anchor differences are ≤ η has norm ≤ Cstab·η; at η = 0
this is exactly the `hdet` of `lorentzian_trilateration`).  Two points both
consistent with the same measured interval data within δ are within 2·Cstab·δ
of each other. -/
theorem trilateration_stability {V : Type*} [NormedAddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    {ι : Type*} (a : ι → V) (o : ι) (Cstab δ : ℝ) (hδ : 0 ≤ δ)
    (hstab : ∀ (η : ℝ) (w : V), 0 ≤ η →
      (∀ i, |B w (a i - a o)| ≤ η) → ‖w‖ ≤ Cstab * η)
    (p q : V) (m : ι → ℝ)
    (hp : ∀ i, |sigma2 B p (a i) - m i| ≤ δ)
    (hq : ∀ i, |sigma2 B q (a i) - m i| ≤ δ) :
    ‖p - q‖ ≤ Cstab * (2 * δ) := by
  apply hstab (2 * δ) (p - q) (by linarith)
  intro i
  have key : B (p - q) (a i - a o)
      = (sigma2 B q (a i) - sigma2 B p (a i)) / 2
        - (sigma2 B q (a o) - sigma2 B p (a o)) / 2 := by
    unfold sigma2
    simp only [map_sub, LinearMap.sub_apply]
    have s1 := hsymm p (a i)
    have s2 := hsymm q (a i)
    have s3 := hsymm p (a o)
    have s4 := hsymm q (a o)
    linarith
  rw [key]
  have h1 := hp i
  have h2 := hq i
  have h3 := hp o
  have h4 := hq o
  rw [abs_le] at h1 h2 h3 h4 ⊢
  constructor
  · linarith [h1.1, h2.2, h3.2, h4.1]
  · linarith [h1.2, h2.1, h3.1, h4.2]

/-! ## 4. The counting dictionary with error -/

/-- `|√u − 1| ≤ |u − 1|` for `u ≥ 0`: square-root estimation never amplifies
relative error. -/
theorem sqrt_error_le (u : ℝ) (hu : 0 ≤ u) :
    |Real.sqrt u - 1| ≤ |u - 1| := by
  rcases le_or_gt 1 u with h | h
  · have hs1 : 1 ≤ Real.sqrt u := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt h
    have hs2 : Real.sqrt u ≤ u := by
      calc Real.sqrt u ≤ Real.sqrt (u^2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = u := Real.sqrt_sq hu
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · have hs1 : Real.sqrt u ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt h.le
    have hs2 : u ≤ Real.sqrt u := by
      calc u = Real.sqrt (u^2) := (Real.sqrt_sq hu).symm
        _ ≤ Real.sqrt u := Real.sqrt_le_sqrt (by nlinarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- **The counting dictionary with error.**  In 4D, `V = (π/24)τ⁴`; a count
within the ε-concentration window gives the proper-time estimator
`τ̂² = √(24n/(πρ))` with relative error at most ε. -/
theorem count_estimator_error (rho tau2 n ε : ℝ)
    (hρ : 0 < rho) (hτ : 0 < tau2) (hn : 0 ≤ n)
    (hconc : |n / (rho * ((Real.pi/24) * tau2^2)) - 1| ≤ ε) :
    |Real.sqrt (24 * n / (Real.pi * rho)) - tau2| ≤ ε * tau2 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set u := n / (rho * ((Real.pi/24) * tau2^2)) with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have harg : 24 * n / (Real.pi * rho) = tau2^2 * u := by
    rw [hu]
    field_simp
  rw [harg, Real.sqrt_mul (by positivity) u, Real.sqrt_sq hτ.le,
    show tau2 * Real.sqrt u - tau2 = tau2 * (Real.sqrt u - 1) from by ring,
    abs_mul, abs_of_pos hτ]
  calc tau2 * |Real.sqrt u - 1|
      ≤ tau2 * |u - 1| :=
        mul_le_mul_of_nonneg_left (sqrt_error_le u hu0) hτ.le
    _ ≤ tau2 * ε := mul_le_mul_of_nonneg_left hconc hτ.le
    _ = ε * tau2 := by ring

/-! ## 5. THE QUANTITATIVE HAUPTVERMUTUNG -/

/-- **ORDER + NUMBER = GEOMETRY, WITH ERROR BARS.**  Three interval counts
`n_io, n_jo, n_ij` (the discrete data of the causal set: cardinalities of
order intervals between three timelike-separated anchor pairs), each in its
Poisson ε-concentration window, determine the metric component
`B(aᵢ−a₀, aⱼ−a₀)` through the EXPLICIT estimator

    Ĝᵢⱼ = ½·( √(24·nᵢ₀/(πρ)) + √(24·nⱼ₀/(πρ)) − √(24·nᵢⱼ/(πρ)) )

with error at most `(3/2)·ε·S`, where `S` bounds the squared intervals.
Every constant is derived: π/24 is the 4D interval-volume constant, 3/2 the
polarization Lipschitz constant, and ε is controlled by Chebyshev–Poisson
(`poisson_count_concentration`: each window fails with probability at most
`1/(ρV·ε²)`).  With `ε = k/√(ρV_min)` the error is `(3/2)·k·S·(ρV_min)^{-1/2}`
— the discrete-to-continuum reconstruction rate. -/
theorem quantitative_hauptvermutung {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsymm : ∀ x y, B x y = B y x)
    (ai aj ao : V) (rho ε S : ℝ)
    (t_io t_jo t_ij n_io n_jo n_ij : ℝ)
    (hρ : 0 < rho) (hε : 0 ≤ ε)
    (ht_io : sigma2 B ai ao = t_io) (ht_jo : sigma2 B aj ao = t_jo)
    (ht_ij : sigma2 B ai aj = t_ij)
    (hpos_io : 0 < t_io) (hpos_jo : 0 < t_jo) (hpos_ij : 0 < t_ij)
    (hS_io : t_io ≤ S) (hS_jo : t_jo ≤ S) (hS_ij : t_ij ≤ S)
    (hn_io : 0 ≤ n_io) (hn_jo : 0 ≤ n_jo) (hn_ij : 0 ≤ n_ij)
    (hconc_io : |n_io / (rho * ((Real.pi/24) * t_io^2)) - 1| ≤ ε)
    (hconc_jo : |n_jo / (rho * ((Real.pi/24) * t_jo^2)) - 1| ≤ ε)
    (hconc_ij : |n_ij / (rho * ((Real.pi/24) * t_ij^2)) - 1| ≤ ε) :
    |(Real.sqrt (24 * n_io / (Real.pi * rho))
        + Real.sqrt (24 * n_jo / (Real.pi * rho))
        - Real.sqrt (24 * n_ij / (Real.pi * rho))) / 2
      - B (ai - ao) (aj - ao)| ≤ 3/2 * (ε * S) := by
  have e_io := count_estimator_error rho t_io n_io ε hρ hpos_io hn_io hconc_io
  have e_jo := count_estimator_error rho t_jo n_jo ε hρ hpos_jo hn_jo hconc_jo
  have e_ij := count_estimator_error rho t_ij n_ij ε hρ hpos_ij hn_ij hconc_ij
  apply gram_reconstruction_lipschitz B hsymm ai aj ao _ _ _ (ε * S)
  · rw [ht_io]
    exact le_trans e_io (mul_le_mul_of_nonneg_left hS_io hε)
  · rw [ht_jo]
    exact le_trans e_jo (mul_le_mul_of_nonneg_left hS_jo hε)
  · rw [ht_ij]
    exact le_trans e_ij (mul_le_mul_of_nonneg_left hS_ij hε)

/-! ## 6. The joint probability bound -/

/-- **All concentration windows hold jointly** outside probability
`m·(1/(r_min·ε²))`:  union bound over the `m` measured pairs, each marginal
window bounded by Chebyshev–Poisson.  With `ε = k/√r_min` the failure
probability is at most `m/k²`. -/
theorem hauptvermutung_failure_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {ι : Type*} (s : Finset ι) (Bad : ι → Set Ω) (r : ι → ℝ) (ε rmin : ℝ)
    (hbound : ∀ i ∈ s, μ (Bad i) ≤ ENNReal.ofReal (1 / (r i * ε^2)))
    (hrmin : ∀ i ∈ s, rmin ≤ r i) (hrpos : 0 < rmin) (hε : 0 < ε) :
    μ (⋃ i ∈ s, Bad i)
      ≤ (s.card : ENNReal) * ENNReal.ofReal (1 / (rmin * ε^2)) := by
  have hmono : ∀ i ∈ s, μ (Bad i) ≤ ENNReal.ofReal (1 / (rmin * ε^2)) := by
    intro i hi
    refine le_trans (hbound i hi) (ENNReal.ofReal_le_ofReal ?_)
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_right (hrmin i hi) (sq_nonneg ε)
  calc μ (⋃ i ∈ s, Bad i)
      ≤ ∑ _i ∈ s, ENNReal.ofReal (1 / (rmin * ε^2)) :=
        KFCausalCSpecCountConcentration.loop_failure_union_bound s Bad _ hmono
    _ = (s.card : ENNReal) * ENNReal.ofReal (1 / (rmin * ε^2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

#print axioms polarization
#print axioms gram_reconstruction_lipschitz
#print axioms trilateration_stability
#print axioms count_estimator_error
#print axioms quantitative_hauptvermutung
#print axioms hauptvermutung_failure_probability

end UnifiedTheory.Audit.KFCausalCSpecQuantitativeHauptvermutung
