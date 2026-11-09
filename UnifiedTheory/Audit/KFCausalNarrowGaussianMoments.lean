/- First position moments in narrow Fourier tensor factors, with exact
Fourier constants and derived L1/L2 integrability. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowGaussianMoments
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianQuadraticFourier (moment moment_continuous moment_memLp first_moment_fourier)
open KFCausalReciprocalGaussianFourier (product)
open KFCausalNarrowFourierPackets (spectator)
open KFCausalNeutralLinePackets (packet packet_memLp)

def narrowMoment (a : ℝ) (i : Fin 2) : Block 2 → ℂ :=
  KFCausalPairedQuadraticFourier.product a (if i=0 then 1 else 0) (if i=1 then 1 else 0)

theorem narrowMoment_eq (a : ℝ) (i : Fin 2) (u : Block 2) :
    narrowMoment a i u = (u i:ℂ)*product a a u := by
  fin_cases i <;> simp [narrowMoment,KFCausalPairedQuadraticFourier.product,moment,product] <;> ring

theorem narrowMoment_memLp (a : ℝ) (ha : 0 < a) (i : Fin 2) : MemLp (narrowMoment a i) 2 volume :=
  KFCausalPairedQuadraticFourier.product_memLp a ha _ _

theorem narrowMoment_integrable (a : ℝ) (ha : 0 < a) (i : Fin 2) : Integrable (narrowMoment a i) :=
  KFCausalPairedQuadraticFourier.product_integrable a ha _ _

theorem narrowMoment_fourier (a : ℝ) (ha : 0 < a) (i : Fin 2) (u : Block 2) :
    (𝓕 (narrowMoment a i)) u = (-(Real.pi:ℂ)*Complex.I*(u i:ℂ)/(a:ℂ))*(𝓕 (product a a)) u := by
  have h0 : moment a 0 = KFCausalGaussianSliceDomain.gaussian (a:ℂ) := by
    funext x
    simp [moment]
  fin_cases i
  · change (𝓕 (KFCausalPairedQuadraticFourier.product a 1 0)) u =
      (-(Real.pi:ℂ)*Complex.I*(u 0:ℂ)/(a:ℂ))*(𝓕 (product a a)) u
    unfold KFCausalPairedQuadraticFourier.product product
    rw [KFCausalPairedQuadraticFourier.two_fourier,KFCausalPairedQuadraticFourier.two_fourier,
      first_moment_fourier a ha,h0]
    ring
  · change (𝓕 (KFCausalPairedQuadraticFourier.product a 0 1)) u =
      (-(Real.pi:ℂ)*Complex.I*(u 1:ℂ)/(a:ℂ))*(𝓕 (product a a)) u
    unfold KFCausalPairedQuadraticFourier.product product
    rw [KFCausalPairedQuadraticFourier.two_fourier,KFCausalPairedQuadraticFourier.two_fourier,
      first_moment_fourier a ha,h0]
    ring

def broadMoment (a β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (i : Fin 2) (v : Block 4) : ℂ :=
  (v i.castSucc.succ:ℂ)*spectator a β b P g v

theorem broadMoment_memLp (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (i : Fin 2) :
    MemLp (broadMoment a β b P g i) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,moment a (if i=0 then 1 else 0),moment a (if i=1 then 1 else 0),packet β b P]
  have hfc : ∀ j, Continuous (f j) := by
    intro j
    fin_cases j
    · exact hc
    · exact moment_continuous _ _
    · exact moment_continuous _ _
    · change Continuous (packet β b P)
      unfold packet KFCausalNeutralLinePackets.entire
      fun_prop
  have hfm : ∀ j, MemLp (f j) 2 volume := by
    intro j
    fin_cases j
    · exact hg
    · exact moment_memLp _ ha _
    · exact moment_memLp _ ha _
    · exact packet_memLp β hβ b P
  have hm := KFCausalChargeGaussianProducts.block_product_memLp 4 f hfc hfm
  apply hm.ae_eq
  filter_upwards [] with v
  fin_cases i <;> simp [f,Fin.prod_univ_succ,broadMoment,spectator,moment] <;> ring

#print axioms narrowMoment_eq
#print axioms narrowMoment_memLp
#print axioms narrowMoment_integrable
#print axioms narrowMoment_fourier
#print axioms broadMoment_memLp
end
end UnifiedTheory.Audit.KFCausalNarrowGaussianMoments
