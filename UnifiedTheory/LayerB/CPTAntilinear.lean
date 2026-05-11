/-
  LayerB/CPTAntilinear.lean — Antilinear sharpening of CPTFromKP.

  HONEST SCOPE STATEMENT (read this first).

  The companion file `LayerB/CPTFromKP.lean` proves only the trivial
  sign-flip invariance of the Born observable:
      (±Q)² + (±P)² = Q² + P².
  That is *not* the Jost-Lüders-Pauli CPT theorem of axiomatic QFT.
  CPT in QFT requires:
    (i)   antiunitary T on a complex Hilbert space (antilinearity);
    (ii)  Lorentz invariance (a relativistic spacetime structure);
    (iii) locality / microcausality of the field algebra;
    (iv)  spin-statistics for the field representations.
  None of (i)–(iv) is supplied by `CPTFromKP.lean`. In particular,
  the "T" there does not perform complex conjugation `i ↦ -i`, so the
  *defining* feature of T (antilinearity) is absent.

  This file makes a *partial* sharpening: we promote CPT from a real
  sign-flip on the K/P pair to an explicit *antilinear involution* on
  the framework's complex amplitude space ℂ, and we verify it preserves
  the Born observable. Concretely we:
    (a) define C, P, T as endo-maps of ℂ;
    (b) prove C and P are ℝ-linear (packaged as `→ₗ[ℝ]`);
    (c) prove T is genuinely antilinear (packaged as `→ₛₗ[starRingEnd ℂ]`);
    (d) define `cptOp = C ∘ P ∘ T` and prove it is antilinear, an
        involution, and preserves `Complex.normSq` (= `obs`);
    (e) check that `cptOp` interacts correctly with `amplitudeFromKP`,
        and that it specialises to the K/P sign-flip identity already
        used in `CPTFromKP.lean`.

  WHAT THIS FILE STILL DOES *NOT* PROVE.
    * No Lorentz invariance: ℂ here is the algebra of single-amplitude
      values, not a relativistic field algebra over Minkowski space.
    * No locality / microcausality: there is no notion of spacelike
      separation or commuting field operators here.
    * No antiunitarity on a Hilbert space of states: `ℂ` is one-
      dimensional as a complex vector space; there is no inner-product
      structure being preserved beyond the modulus.
    * No Jost-Lüders-Pauli axiomatic input: no Wightman axioms, no
      tempered distributions, no spectrum condition.
    * No spin-statistics connection.

  In short: we sharpen the existing real-pair sign-flip with the one
  ingredient (antilinearity, T) that CPT *requires* — but we do not
  derive the QFT CPT theorem.

  Zero `sorry`. Zero custom axioms.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Tactic.Linarith
import UnifiedTheory.LayerB.ComplexFromDressing
import UnifiedTheory.LayerB.CPTFromKP

namespace UnifiedTheory.LayerB.CPTAntilinear

open UnifiedTheory.LayerB
open Complex

/-! ## Part 1. The three operators on ℂ -/

/-- **Charge conjugation, C.**
    Acts on the framework's complex amplitude by flipping the real part
    while leaving the imaginary part fixed. Written componentwise:
        C(a + b·i) = -a + b·i. -/
def chargeConj (z : ℂ) : ℂ := ⟨-z.re, z.im⟩

/-- **Parity, P (algebraic stand-in).**
    Flips the imaginary part. At the level of the K/P amplitude algebra
    this plays the rôle of an internal parity; it is *not* a spatial
    parity (the framework's ℂ has no spatial structure attached here). -/
def parityOp (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

/-- **Time reversal, T.**
    Complex conjugation. This is the genuinely antilinear ingredient
    of CPT — the one that was missing from `CPTFromKP.lean`. -/
def timeReversal (z : ℂ) : ℂ := starRingEnd ℂ z

/-- **The combined CPT operator.** `cptOp = C ∘ P ∘ T`. -/
def cptOp (z : ℂ) : ℂ := chargeConj (parityOp (timeReversal z))

/-! ## Part 2. Componentwise computations -/

@[simp] theorem chargeConj_re (z : ℂ) : (chargeConj z).re = -z.re := rfl
@[simp] theorem chargeConj_im (z : ℂ) : (chargeConj z).im = z.im := rfl

@[simp] theorem parityOp_re (z : ℂ) : (parityOp z).re = z.re := rfl
@[simp] theorem parityOp_im (z : ℂ) : (parityOp z).im = -z.im := rfl

@[simp] theorem timeReversal_re (z : ℂ) : (timeReversal z).re = z.re := by
  simp [timeReversal]

@[simp] theorem timeReversal_im (z : ℂ) : (timeReversal z).im = -z.im := by
  simp [timeReversal]

@[simp] theorem cptOp_re (z : ℂ) : (cptOp z).re = -z.re := by
  simp [cptOp]

@[simp] theorem cptOp_im (z : ℂ) : (cptOp z).im = z.im := by
  simp [cptOp]

/-! ## Part 3. C is ℝ-linear -/

/-- C distributes over ℂ-addition. -/
theorem chargeConj_add (z w : ℂ) : chargeConj (z + w) = chargeConj z + chargeConj w := by
  apply Complex.ext
  · simp [chargeConj, Complex.add_re]; ring
  · simp [chargeConj, Complex.add_im]

/-- C commutes with real scalar multiplication. -/
theorem chargeConj_smul_real (a : ℝ) (z : ℂ) :
    chargeConj ((a : ℂ) * z) = (a : ℂ) * chargeConj z := by
  apply Complex.ext
  · simp [chargeConj, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  · simp [chargeConj, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **C as an ℝ-linear map ℂ →ₗ[ℝ] ℂ.**
    (C is *not* ℂ-linear in general because it flips Re but not Im.) -/
def chargeConjLin : ℂ →ₗ[ℝ] ℂ where
  toFun := chargeConj
  map_add' := chargeConj_add
  map_smul' := by
    intro a z
    apply Complex.ext
    · simp [chargeConj]
    · simp [chargeConj]

/-! ## Part 4. P is ℝ-linear -/

/-- P distributes over ℂ-addition. -/
theorem parityOp_add (z w : ℂ) : parityOp (z + w) = parityOp z + parityOp w := by
  apply Complex.ext
  · simp [parityOp, Complex.add_re]
  · simp [parityOp, Complex.add_im]; ring

/-- P commutes with real scalar multiplication. -/
theorem parityOp_smul_real (a : ℝ) (z : ℂ) :
    parityOp ((a : ℂ) * z) = (a : ℂ) * parityOp z := by
  apply Complex.ext
  · simp [parityOp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  · simp [parityOp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

/-- **P as an ℝ-linear map ℂ →ₗ[ℝ] ℂ.** -/
def parityOpLin : ℂ →ₗ[ℝ] ℂ where
  toFun := parityOp
  map_add' := parityOp_add
  map_smul' := by
    intro a z
    apply Complex.ext
    · simp [parityOp]
    · simp [parityOp]

/-! ## Part 5. T is antilinear (the genuine new content) -/

/-- T distributes over ℂ-addition. -/
theorem timeReversal_add (z w : ℂ) : timeReversal (z + w) = timeReversal z + timeReversal w := by
  simp [timeReversal]

/-- **The antilinearity of T.**
    For any complex scalar `c` and amplitude `z`,
        T(c · z) = (conj c) · T(z).
    This is the defining feature of an antilinear map and is the
    ingredient `CPTFromKP.lean` does *not* contain. -/
theorem timeReversal_antilinear (c z : ℂ) :
    timeReversal (c * z) = (starRingEnd ℂ c) * timeReversal z := by
  simp [timeReversal, map_mul]

/-- **T as a semilinear (antilinear) map ℂ →ₛₗ[starRingEnd ℂ] ℂ.**
    Recall that `→ₛₗ[σ]` denotes a σ-semilinear map; with σ = `starRingEnd ℂ`
    (the conjugation ring endomorphism on ℂ) this is exactly antilinearity. -/
def timeReversalAntilin : ℂ →ₛₗ[starRingEnd ℂ] ℂ where
  toFun := timeReversal
  map_add' := timeReversal_add
  map_smul' := by
    intro c z
    -- goal: timeReversal (c • z) = (starRingEnd ℂ c) • timeReversal z
    change timeReversal (c * z) = (starRingEnd ℂ c) * timeReversal z
    exact timeReversal_antilinear c z

/-! ## Part 6. cptOp is antilinear -/

/-- cptOp distributes over ℂ-addition (linear part). -/
theorem cptOp_add (z w : ℂ) : cptOp (z + w) = cptOp z + cptOp w := by
  simp [cptOp, chargeConj_add, parityOp_add, timeReversal_add]

/-- **The CPT operator is antilinear**:
        cptOp(c · z) = (conj c) · cptOp(z).
    Proof: T already supplies the conjugation; C and P only flip
    component signs and so commute with multiplication by `conj c`. -/
theorem cptOp_antilinear (c z : ℂ) :
    cptOp (c * z) = (starRingEnd ℂ c) * cptOp z := by
  -- A direct componentwise computation.
  -- cptOp(z) = -z.re + z.im * I = -conj(z).
  have h1 : ∀ w : ℂ, cptOp w = -starRingEnd ℂ w := by
    intro w
    apply Complex.ext
    · simp [cptOp_re]
    · simp [cptOp_im]
  rw [h1, h1]
  -- Now goal: -conj(c*z) = conj(c) * (-conj(z))
  rw [map_mul]
  ring

/-- **cptOp as a semilinear (antilinear) map ℂ →ₛₗ[starRingEnd ℂ] ℂ.** -/
def cptOpAntilin : ℂ →ₛₗ[starRingEnd ℂ] ℂ where
  toFun := cptOp
  map_add' := cptOp_add
  map_smul' := by
    intro c z
    change cptOp (c * z) = (starRingEnd ℂ c) * cptOp z
    exact cptOp_antilinear c z

/-! ## Part 7. cptOp is an involution -/

/-- **CPT is involutive: applying it twice is the identity.**
    This holds because both T and (CP) square to id, and they
    commute on the imaginary axis. -/
theorem cptOp_involution (z : ℂ) : cptOp (cptOp z) = z := by
  apply Complex.ext
  · simp [cptOp_re]
  · simp [cptOp_im]

/-- The functional version of involution: `cptOp ∘ cptOp = id`. -/
theorem cptOp_comp_self : cptOp ∘ cptOp = id := by
  funext z; exact cptOp_involution z

/-! ## Part 8. cptOp preserves the Born observable -/

/-- **CPT preserves `Complex.normSq`.**
    Since cptOp(z) = -conj(z), |cptOp(z)|² = |conj(z)|² = |z|². -/
theorem cptOp_normSq (z : ℂ) :
    Complex.normSq (cptOp z) = Complex.normSq z := by
  simp [Complex.normSq_apply, cptOp_re, cptOp_im]

/-- **CPT preserves the framework's Born observable** `obs`. -/
theorem cptOp_preserves_obs (z : ℂ) : obs (cptOp z) = obs z := by
  simp [obs, cptOp_re, cptOp_im]

/-! ## Part 9. Interaction with the K/P amplitude -/

/-- **CPT on a K/P amplitude flips the K-component and conjugates.**
    Computed directly: `cptOp ⟨Q, P⟩ = ⟨-Q, P⟩`. -/
theorem cptOp_amplitudeFromKP (Q P : ℝ) :
    cptOp (amplitudeFromKP Q P) = amplitudeFromKP (-Q) P := by
  apply Complex.ext
  · simp [cptOp_re, amplitudeFromKP]
  · simp [cptOp_im, amplitudeFromKP]

/-- **Compatibility with the existing real sign-flip CPT.**
    The Born observable of the antilinear CPT image equals the Born
    observable of the K/P sign-flip image used in `CPTFromKP.lean`. -/
theorem cptOp_obs_matches_KP_signflip (Q P : ℝ) :
    obs (cptOp (amplitudeFromKP Q P)) = obs (amplitudeFromKP (-Q) (-P)) := by
  rw [cptOp_amplitudeFromKP]
  -- both sides equal Q² + P² by `obs_from_KP`
  rw [obs_from_KP, obs_from_KP]
  ring

/-- **Bridge to `CPTFromKP.full_cpt_preserves_obs`.**
    The antilinear CPT preserves `obs` on K/P amplitudes, agreeing
    with the real sign-flip statement already proven. -/
theorem antilinear_cpt_preserves_kp_obs (Q P : ℝ) :
    obs (cptOp (amplitudeFromKP Q P)) = obs (amplitudeFromKP Q P) :=
  cptOp_preserves_obs (amplitudeFromKP Q P)

/-! ## Part 10. The genuine new content: T is antilinear and nontrivial -/

/-- **T is *not* the identity.** Concretely, T(i) = -i ≠ i.
    Together with `timeReversal_antilinear`, this records that we have
    introduced a nontrivial antilinear operator — the ingredient missing
    from `CPTFromKP.lean`. -/
theorem timeReversal_nontrivial : timeReversal Complex.I ≠ Complex.I := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- **C is *not* the identity.** Concretely, C(1) = -1 ≠ 1. -/
theorem chargeConj_nontrivial : chargeConj 1 ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [chargeConj] at hre
  linarith

/-- **P is *not* the identity.** Concretely, P(i) = -i ≠ i. -/
theorem parityOp_nontrivial : parityOp Complex.I ≠ Complex.I := by
  intro h
  have him := congrArg Complex.im h
  simp [parityOp] at him
  linarith

/-! ## Part 11. Master theorem -/

/-- **MASTER THEOREM (antilinear sharpening of CPT on the K/P amplitude algebra).**

    HONEST CLAIM (in three numbered parts).

    1. (Antilinearity.) The combined operator `cptOp = C ∘ P ∘ T` on the
       framework's complex amplitude space ℂ is antilinear:
         cptOp(c · z) = (conj c) · cptOp(z),  for all c, z ∈ ℂ.
       This is provided by the explicit semilinear-map structure
       `cptOpAntilin : ℂ →ₛₗ[starRingEnd ℂ] ℂ`.

    2. (Involution.) cptOp ∘ cptOp = id.

    3. (Born preservation.) For all z, `obs (cptOp z) = obs z`,
       equivalently `Complex.normSq (cptOp z) = Complex.normSq z`.
       In particular, on K/P amplitudes the antilinear CPT agrees on
       observables with the real sign-flip CPT proved in
       `CPTFromKP.full_cpt_preserves_obs`.

    HONEST CAVEAT (repeated). This is a sharpening — not a derivation —
    of the QFT CPT theorem. The Jost-Lüders-Pauli theorem also requires
    Lorentz invariance, locality, antiunitarity on a state Hilbert space,
    and spin-statistics. None of those is supplied here. -/
theorem antilinear_cpt_master :
    -- (1) Antilinear on ℂ
    (∀ c z : ℂ, cptOp (c * z) = (starRingEnd ℂ c) * cptOp z)
    -- (2) Additive on ℂ
    ∧ (∀ z w : ℂ, cptOp (z + w) = cptOp z + cptOp w)
    -- (3) Involution
    ∧ (∀ z : ℂ, cptOp (cptOp z) = z)
    -- (4) Preserves Born observable on ℂ
    ∧ (∀ z : ℂ, obs (cptOp z) = obs z)
    -- (5) Preserves Complex.normSq on ℂ
    ∧ (∀ z : ℂ, Complex.normSq (cptOp z) = Complex.normSq z)
    -- (6) Agrees on K/P amplitudes with the real sign-flip
    ∧ (∀ Q P : ℝ, obs (cptOp (amplitudeFromKP Q P)) = obs (amplitudeFromKP Q P))
    -- (7) T is genuinely antilinear (not merely a linear map)
    ∧ (∀ c z : ℂ, timeReversal (c * z) = (starRingEnd ℂ c) * timeReversal z) :=
  ⟨cptOp_antilinear,
   cptOp_add,
   cptOp_involution,
   cptOp_preserves_obs,
   cptOp_normSq,
   antilinear_cpt_preserves_kp_obs,
   timeReversal_antilinear⟩

end UnifiedTheory.LayerB.CPTAntilinear
