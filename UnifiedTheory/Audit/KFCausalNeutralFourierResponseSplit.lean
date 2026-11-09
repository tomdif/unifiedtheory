/- Exact integrated response split for a moving neutral family, real
field shift and imaginary translation. The imaginary adjacent-field
term cancels by proved weighted symmetry. Charged coefficient motion is
retained as an unrestricted pairing, not bounded or discarded. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierResponseSplit
noncomputable section
open MeasureTheory
open scoped FourierTransform ComplexConjugate
open KFCausalNeutralFourierField
open KFCausalNeutralFourierPairing
open KFCausalNeutralFourierMomentum
open KFCausalNeutralLinePackets (step)
open KFCausalNeutralFourierEnergy (frequencyMoment)

variable (n : ℕ) (β : ℝ) (b c cd : Fin n → ℂ) (P : Fin n → Polynomial ℂ)

def slope (j : ℕ) (a y ad yd x : ℝ) : ℂ :=
  fieldLine n β b cd P j a y x+(j:ℂ)*(ad:ℂ)*fieldLine n β b c P (j-1) a y x+
    (Complex.I*(yd:ℂ))*fieldLine n β b c (fun i => step β (b i) (P i)) j a y x

def response (j : ℕ) (a y ad yd x : ℝ) : ℝ :=
  2*(conj (fieldLine n β b c P j a y x)*slope n β b c cd P j a y ad yd x).re

def frequencyResponse (j : ℕ) (a y ad yd k : ℝ) : ℝ :=
  2*(weightedCross n β b c cd P P j j a y k).re+
    2*(j:ℝ)*ad*(weightedCross n β b c c P P j (j-1) a y k).re-
    4*Real.pi*yd*(k*frequencyMoment n β b c P j a y k)

variable (hβ : 0 < β)
include hβ

theorem slope_integrable (j : ℕ) (a y ad yd : ℝ) :
    Integrable (slope n β b c cd P j a y ad yd) :=
  ((fieldLine_integrable n β hβ b cd P j a y).add
    ((fieldLine_integrable n β hβ b c P (j-1) a y).const_mul ((j:ℂ)*(ad:ℂ)))).add
    ((fieldLine_integrable n β hβ b c _ j a y).const_mul (Complex.I*(yd:ℂ)))

theorem slope_memLp (j : ℕ) (a y ad yd : ℝ) :
    MemLp (slope n β b c cd P j a y ad yd) 2 volume :=
  ((fieldLine_memLp n β hβ b cd P j a y).add
    ((fieldLine_memLp n β hβ b c P (j-1) a y).const_mul ((j:ℂ)*(ad:ℂ)))).add
    ((fieldLine_memLp n β hβ b c _ j a y).const_mul (Complex.I*(yd:ℂ)))

theorem response_integrable (j : ℕ) (a y ad yd : ℝ) :
    Integrable (response n β b c cd P j a y ad yd) := by
  have hi := ((fieldLine_memLp n β hβ b c P j a y).star.integrable_mul
    (slope_memLp n β b c cd P hβ j a y ad yd)).re.const_mul 2
  change Integrable (fun x => 2*(star (fieldLine n β b c P j a y x)*slope n β b c cd P j a y ad yd x).re) at hi
  exact hi

theorem frequencyResponse_integrable (j : ℕ) (a y ad yd : ℝ) :
    Integrable (frequencyResponse n β b c cd P j a y ad yd) :=
  (((weightedCross_integrable n β b c cd P P hβ j j a y).re.const_mul 2).add
    ((weightedCross_integrable n β b c c P P hβ j (j-1) a y).re.const_mul (2*(j:ℝ)*ad))).sub
    ((KFCausalNeutralFourierMomentum.frequencyMoment_integrable n β b c P hβ j a y).const_mul (4*Real.pi*yd))

theorem slope_fourier (j : ℕ) (a y ad yd k : ℝ) :
    (𝓕 (slope n β b c cd P j a y ad yd)) k =
      (𝓕 (fieldLine n β b cd P j a y)) k+
      (j:ℂ)*((ad:ℂ)-Complex.I*(yd:ℂ))*(𝓕 (fieldLine n β b c P (j-1) a y)) k-
      (2*(Real.pi:ℂ)*(yd:ℂ)*(k:ℂ))*(𝓕 (fieldLine n β b c P j a y)) k := by
  have hc := fieldLine_integrable n β hβ b cd P j a y
  have hp := (fieldLine_integrable n β hβ b c P (j-1) a y).const_mul ((j:ℂ)*(ad:ℂ))
  have hs := (fieldLine_integrable n β hβ b c (fun i => step β (b i) (P i)) j a y).const_mul (Complex.I*(yd:ℂ))
  have hcp : Integrable (fun x => fieldLine n β b cd P j a y x+
      (j:ℂ)*(ad:ℂ)*fieldLine n β b c P (j-1) a y x) := hc.add hp
  unfold slope
  rw [fourier_add _ _ hcp hs,fourier_add _ _ hc hp,fourier_const_mul,fourier_const_mul,
    step_fourier n β b c P hβ]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem frequency_pairing (j : ℕ) (a y ad yd k : ℝ) :
    conj ((𝓕 (fieldLine n β b c P j a y)) k)*(𝓕 (slope n β b c cd P j a y ad yd)) k =
      weightedCross n β b c cd P P j j a y k+
      (j:ℂ)*((ad:ℂ)-Complex.I*(yd:ℂ))*weightedCross n β b c c P P j (j-1) a y k-
      (2*(Real.pi:ℂ)*(yd:ℂ))*((k*frequencyMoment n β b c P j a y k:ℝ):ℂ) := by
  rw [slope_fourier n β b c cd P hβ,
    weightedCross_identity n β b c cd P P hβ,weightedCross_identity n β b c c P P hβ]
  have he : conj ((𝓕 (fieldLine n β b c P j a y)) k)*(𝓕 (fieldLine n β b c P j a y)) k =
      (frequencyMoment n β b c P j a y k:ℂ) := by
    rw [Complex.conj_mul',← Complex.ofReal_pow,fieldLine_fourier_square n β hβ]
    rfl
  push_cast
  linear_combination -(2*(Real.pi:ℂ)*(yd:ℂ)*(k:ℂ))*he

theorem response_integral_split (j : ℕ) (a y ad yd : ℝ) :
    (∫ x, response n β b c cd P j a y ad yd x) =
      2*(∫ k, weightedCross n β b c cd P P j j a y k).re+
      2*(j:ℝ)*ad*(∫ k, weightedCross n β b c c P P j (j-1) a y k).re-
      4*Real.pi*yd*(∫ k, k*frequencyMoment n β b c P j a y k) := by
  have hA := weightedCross_integrable n β b c cd P P hβ j j a y
  have hB := weightedCross_integrable n β b c c P P hβ j (j-1) a y
  have hM := KFCausalNeutralFourierMomentum.frequencyMoment_integrable n β b c P hβ j a y
  have hi := (fieldLine_memLp n β hβ b c P j a y).star.integrable_mul
    (slope_memLp n β b c cd P hβ j a y ad yd)
  change Integrable (fun x => conj (fieldLine n β b c P j a y x)*slope n β b c cd P j a y ad yd x) at hi
  have he := cross_plancherel _ _ (fieldLine_integrable n β hβ b c P j a y)
    (slope_integrable n β b c cd P hβ j a y ad yd)
    (fieldLine_memLp n β hβ b c P j a y) (slope_memLp n β b c cd P hβ j a y ad yd)
  simp_rw [frequency_pairing n β b c cd P hβ] at he
  have hMc : Integrable (fun k => ((k*frequencyMoment n β b c P j a y k:ℝ):ℂ)) := hM.ofReal
  have hBc : Integrable (fun k => (j:ℂ)*((ad:ℂ)-Complex.I*(yd:ℂ))*
      weightedCross n β b c c P P j (j-1) a y k) := hB.const_mul _
  have hAB : Integrable (fun k => weightedCross n β b c cd P P j j a y k+
      (j:ℂ)*((ad:ℂ)-Complex.I*(yd:ℂ))*weightedCross n β b c c P P j (j-1) a y k) := hA.add hBc
  rw [integral_sub hAB (hMc.const_mul _),integral_add hA hBc,
    integral_const_mul,integral_const_mul,integral_complex_ofReal] at he
  have hre : (∫ x, (conj (fieldLine n β b c P j a y x)*slope n β b c cd P j a y ad yd x).re) =
      (∫ x, conj (fieldLine n β b c P j a y x)*slope n β b c cd P j a y ad yd x).re := integral_re hi
  unfold response
  rw [integral_const_mul,hre,← he]
  have him := same_profile_pairing_real n β b c P hβ j (j-1) a y
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.natCast_re,Complex.natCast_im,
    Complex.I_re,Complex.I_im,Complex.re_ofNat,zero_mul,mul_zero,sub_zero,add_zero,him]
  ring

theorem response_frequency_integral (j : ℕ) (a y ad yd : ℝ) :
    (∫ x, response n β b c cd P j a y ad yd x) =
      ∫ k, frequencyResponse n β b c cd P j a y ad yd k := by
  rw [response_integral_split n β b c cd P hβ]
  have hA := weightedCross_integrable n β b c cd P P hβ j j a y
  have hB := weightedCross_integrable n β b c c P P hβ j (j-1) a y
  have hM := KFCausalNeutralFourierMomentum.frequencyMoment_integrable n β b c P hβ j a y
  have hAr : Integrable (fun k => (weightedCross n β b c cd P P j j a y k).re) := hA.re
  have hBr : Integrable (fun k => (weightedCross n β b c c P P j (j-1) a y k).re) := hB.re
  have hAB : Integrable (fun k => 2*(weightedCross n β b c cd P P j j a y k).re+
      2*(j:ℝ)*ad*(weightedCross n β b c c P P j (j-1) a y k).re) :=
    (hAr.const_mul 2).add (hBr.const_mul _)
  have hreA : (∫ k, (weightedCross n β b c cd P P j j a y k).re) =
      (∫ k, weightedCross n β b c cd P P j j a y k).re := integral_re hA
  have hreB : (∫ k, (weightedCross n β b c c P P j (j-1) a y k).re) =
      (∫ k, weightedCross n β b c c P P j (j-1) a y k).re := integral_re hB
  unfold frequencyResponse
  rw [integral_sub hAB (hM.const_mul _),integral_add (hAr.const_mul 2) (hBr.const_mul _),
    integral_const_mul,integral_const_mul,integral_const_mul,hreA,hreB]

#print axioms slope_integrable
#print axioms slope_memLp
#print axioms response_integrable
#print axioms frequencyResponse_integrable
#print axioms slope_fourier
#print axioms frequency_pairing
#print axioms response_integral_split
#print axioms response_frequency_integral
end
end UnifiedTheory.Audit.KFCausalNeutralFourierResponseSplit
