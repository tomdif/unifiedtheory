/- Quadratic position moments in the actual narrow Fourier tensor factors.
Exact transforms and L1/L2 integrability supply second momentum outputs. -/
import UnifiedTheory.Audit.KFCausalNarrowFourierPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNarrowGaussianSecondMoments
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalGaussianQuadraticFourier (moment moment_continuous moment_memLp second_moment_fourier)
open KFCausalReciprocalGaussianFourier (product)
open KFCausalNarrowFourierPackets (spectator)
open KFCausalNeutralLinePackets (packet packet_memLp)

def narrowSquare (a : ℝ) (i : Fin 2) : Block 2 → ℂ :=
  KFCausalPairedQuadraticFourier.product a (if i=0 then 2 else 0) (if i=1 then 2 else 0)

theorem narrowSquare_eq (a : ℝ) (i : Fin 2) (u : Block 2) :
    narrowSquare a i u = (u i:ℂ)^2*product a a u := by
  fin_cases i <;> simp [narrowSquare,KFCausalPairedQuadraticFourier.product,moment,product] <;> ring

theorem narrowSquare_memLp (a : ℝ) (ha : 0 < a) (i : Fin 2) : MemLp (narrowSquare a i) 2 volume :=
  KFCausalPairedQuadraticFourier.product_memLp a ha _ _

theorem narrowSquare_integrable (a : ℝ) (ha : 0 < a) (i : Fin 2) : Integrable (narrowSquare a i) :=
  KFCausalPairedQuadraticFourier.product_integrable a ha _ _

theorem narrowSquare_fourier (a : ℝ) (ha : 0 < a) (i : Fin 2) (u : Block 2) :
    (𝓕 (narrowSquare a i)) u = (1/(2*(a:ℂ))-(Real.pi:ℂ)^2*(u i:ℂ)^2/(a:ℂ)^2)*(𝓕 (product a a)) u := by
  have h0 : moment a 0 = KFCausalGaussianSliceDomain.gaussian (a:ℂ) := by
    funext x
    simp [moment]
  fin_cases i
  · change (𝓕 (KFCausalPairedQuadraticFourier.product a 2 0)) u =
      (1/(2*(a:ℂ))-(Real.pi:ℂ)^2*(u 0:ℂ)^2/(a:ℂ)^2)*(𝓕 (product a a)) u
    unfold KFCausalPairedQuadraticFourier.product product
    rw [KFCausalPairedQuadraticFourier.two_fourier,KFCausalPairedQuadraticFourier.two_fourier,
      second_moment_fourier a ha,h0]
    ring
  · change (𝓕 (KFCausalPairedQuadraticFourier.product a 0 2)) u =
      (1/(2*(a:ℂ))-(Real.pi:ℂ)^2*(u 1:ℂ)^2/(a:ℂ)^2)*(𝓕 (product a a)) u
    unfold KFCausalPairedQuadraticFourier.product product
    rw [KFCausalPairedQuadraticFourier.two_fourier,KFCausalPairedQuadraticFourier.two_fourier,
      second_moment_fourier a ha,h0]
    ring

def broadSquare (a β : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (i : Fin 2) (v : Block 4) : ℂ :=
  (v i.castSucc.succ:ℂ)^2*spectator a β b P g v

theorem broadSquare_memLp (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) (hc : Continuous g) (hg : MemLp g 2 volume) (i : Fin 2) :
    MemLp (broadSquare a β b P g i) 2 volume := by
  let f : Fin 4 → ℝ → ℂ := ![g,moment a (if i=0 then 2 else 0),moment a (if i=1 then 2 else 0),packet β b P]
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
  fin_cases i <;> simp [f,Fin.prod_univ_succ,broadSquare,spectator,moment] <;> ring

#print axioms narrowSquare_eq
#print axioms narrowSquare_memLp
#print axioms narrowSquare_integrable
#print axioms narrowSquare_fourier
#print axioms broadSquare_memLp
end
end UnifiedTheory.Audit.KFCausalNarrowGaussianSecondMoments
