/- Transfer the mixed field/Gaussian contour identity to the full
six-dimensional Fourier transform. Joint integrability is proved,
so the transfer uses the actual Fubini identity. -/
import UnifiedTheory.Audit.KFCausalMixedFieldGaussianContour
import UnifiedTheory.Audit.KFCausalClockFourierFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldGaussianFullFourier
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanConfiguration (Space)
open KFCausalEuclideanClockSplit (TailSpace euclideanSplit)
open KFCausalClockFloorGaussianL1
  (pairGrouping pairGrouping_preserves_volume tailGrouping tailGrouping_continuous)
open KFCausalClockFourierFubini (clockFourier fourier_iterated)
open KFCausalMixedFieldGaussianStrip
open KFCausalMixedFieldGaussianContour (clockSlice exponential_fourier_identity strip_pair)

def euclideanLine (ε a α β δ y : ℝ) (j : Fin 2) (z : ℝ × TailSpace) : ℂ :=
  line ε a α β δ y j (pairGrouping z)

theorem euclideanLine_continuous (ε a α β δ y : ℝ) (hε : 0 < ε)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    Continuous (euclideanLine ε a α β δ y j) :=
  (line_continuous ε a α β δ y hε hy hyr j).comp
    (continuous_fst.prodMk (tailGrouping_continuous.comp continuous_snd))

theorem euclideanLine_integrable (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    Integrable (euclideanLine ε a α β δ y j) :=
  pairGrouping_preserves_volume.integrable_comp_of_integrable
    (line_integrable ε a α β δ y hε ha hα hβ hw hy hyr j)

theorem euclideanLine_memLp (ε a α β δ y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hy : |y| ≤ Real.pi*ε/3) (hyr : |y+δ| ≤ Real.pi*ε/3) (j : Fin 2) :
    MemLp (euclideanLine ε a α β δ y j) 2 :=
  (line_memLp ε a α β δ y hε ha hα hβ hw hy hyr j).comp_measurePreserving
    pairGrouping_preserves_volume

theorem full_fourier_shift (ε a α β δ h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
    (hb : |-h/2|+|δ| ≤ Real.pi*ε/3) (j : Fin 2) (k : Space) :
    (Real.exp (Real.pi*h*k 0):ℂ)*(𝓕 (euclideanLine ε a α β δ 0 j ∘ euclideanSplit)) k =
      (𝓕 (euclideanLine ε a α β δ (-h/2) j ∘ euclideanSplit)) k := by
  have h0 := strip_pair ε δ |-h/2| 0 hb (by simp)
  have hs := strip_pair ε δ |-h/2| (-h/2) hb le_rfl
  have hpoint (q : ℝ) (y : TailSpace) :
      (Real.exp (Real.pi*h*q):ℂ)*clockFourier (euclideanLine ε a α β δ 0 j) (q,y) =
        clockFourier (euclideanLine ε a α β δ (-h/2) j) (q,y) :=
    exponential_fourier_identity ε a α β δ h hε ha hα hβ hw hb j (tailGrouping y) q
  rw [fourier_iterated _ (euclideanLine_continuous ε a α β δ 0 hε h0.1 h0.2 j)
      (euclideanLine_integrable ε a α β δ 0 hε ha hα hβ hw h0.1 h0.2 j),
    fourier_iterated _ (euclideanLine_continuous ε a α β δ (-h/2) hε hs.1 hs.2 j)
      (euclideanLine_integrable ε a α β δ (-h/2) hε ha hα hβ hw hs.1 hs.2 j)]
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← hpoint]
  ring

#print axioms euclideanLine_continuous
#print axioms euclideanLine_integrable
#print axioms euclideanLine_memLp
#print axioms full_fourier_shift
end
end UnifiedTheory.Audit.KFCausalMixedFieldGaussianFullFourier
