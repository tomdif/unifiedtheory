/- Bounded analytic continuation of the actual radial neutral-position
test after clock straightening and partial Fourier transform. The added
momentum heat factor is contractive throughout the strip, so the existing
localized-phase estimate is retained. Real-slice equality is proved for
the physical operator on all L2 vectors; exponential-domain transport is
not asserted by this multiplier theorem. -/
import UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block split)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped mix)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)
open UnifiedTheory.Audit.KFCausalClockFloorPairedStraightening (clockInverse dilation)
open UnifiedTheory.Audit.KFCausalClockFloorMixedChart (mixedMap)
open UnifiedTheory.Audit.KFCausalClockFloorMixedRadial (clockMixed radial_transformed)
open UnifiedTheory.Audit.KFCausalClockFloorMixedSymbols (radial_symbol)
open UnifiedTheory.Audit.KFCausalClockFloorMixedHeatStrip (heatFactor heatFactor_real heatFactor_analytic heatFactor_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionStripPhase (localized localized_analytic localized_bound phase_real)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action symbol)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (momentumScale)
open UnifiedTheory.Audit.KFCausalComplexClockChart (targetStrip)
open UnifiedTheory.Audit.KFCausalComplexClockInverse
open UnifiedTheory.Audit.KFCausalClockInverseStripBounds

def grouped (s r : ℝ) : Grouped := (![0,0,scale*s,scale*s],r)

theorem grouped_mix (s r : ℝ) : mix (grouped s r).1 = 2*scale*s := by
  simp [grouped,mix]
  ring

theorem grouped_mix_square (s r : ℝ) : (mix (grouped s r).1)^2 = 2*s^2 := by
  rw [grouped_mix]
  calc
    _ = 4*scale^2*s^2 := by ring
    _ = _ := by rw [scale_square]; ring

theorem localized_real (δ v t s r : ℝ) : localized δ v (t:ℂ) (grouped s r) =
    (Real.exp (-2*δ*Real.exp t*s^2):ℂ)*
      scalar (v*(r+4*scale*(Real.exp (t/2)-1)*s)) := by
  rw [localized,phase_real]
  simp only [← Complex.ofReal_pow,← Complex.ofReal_exp,← Complex.ofReal_neg,← Complex.ofReal_mul]
  change (Real.exp (-δ*Real.exp t*(mix (grouped s r).1)^2):ℂ)*
    scalar (v*(r+2*(Real.exp (t/2)-1)*mix (grouped s r).1)) = _
  rw [grouped_mix_square,grouped_mix]
  congr 1
  · congr 2
    ring
  · congr 1
    ring

def factor (δ v p s r : ℝ) (z : ℂ) : ℂ :=
  heatFactor δ p z*localized δ v z (grouped s r)

theorem factor_analytic (δ v p s r : ℝ) (z : ℂ) : AnalyticAt ℂ (factor δ v p s r) z :=
  (heatFactor_analytic δ p z).mul (localized_analytic δ v (grouped s r) z)

theorem factor_real (δ v p s r t : ℝ) : factor δ v p s r (t:ℂ) =
    (Real.exp (-2*δ*(Real.exp (-t)*p^2+Real.exp t*s^2)):ℂ)*
      scalar (v*(r+4*scale*(Real.exp (t/2)-1)*s)) := by
  rw [factor,heatFactor_real,localized_real,← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  congr 2
  congr 1
  ring

def multiplier (ε h δ v : ℝ) (q : ℂ) (x : Block 2 × Block 4) : ℂ :=
  factor δ v (momentumScale h*x.1 1) (x.2 2) (x.2 3) (complexInverse ε q)

theorem multiplier_analytic (ε h δ v : ℝ) (hε : 0 < ε) (q : ℂ) (hq : q ∈ targetStrip ε)
    (x : Block 2 × Block 4) : AnalyticAt ℂ (fun q => multiplier ε h δ v q x) q :=
  (factor_analytic δ v _ _ _ _).comp (complexInverse_analytic ε hε q hq)

theorem multiplier_bound (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (q : ℂ)
    (hq : |q.im| ≤ Real.pi*ε/3) (x : Block 2 × Block 4) :
    ‖multiplier ε h δ v q x‖ ≤ Real.exp (v^2*q.im^2/(2*δ*ε^2)) := by
  rw [multiplier,factor,norm_mul]
  have hh := heatFactor_bound δ (momentumScale h*x.1 1) hδ.le _
    (inverse_im_third_strip ε hε q hq)
  have hl := KFCausalNeutralPositionStripPhase.multiplier_bound ε δ v hε hδ q hq
    (grouped (x.2 2) (x.2 3))
  exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans (by simpa only [one_mul] using hl)

theorem multiplier_real (ε h δ v : ℝ) (hε : 0 < ε) (x : Block 2 × Block 4) :
    multiplier ε h δ v (x.2 0:ℂ) x = symbol h δ v ((split 2 4).symm (mixedMap ε hε x)) := by
  rw [multiplier,complexInverse_real ε hε,factor_real,radial_symbol]
  rfl

theorem radial_transformed_analytic (ε h δ v : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (f : Hilbert) :
    clockMixed ε hε (action h δ v hδ f) =ᵐ[volume] fun x =>
      multiplier ε h δ v (x.2 0:ℂ) x*(clockMixed ε hε f) x := by
  simpa only [multiplier_real ε h δ v hε] using radial_transformed ε hε h δ v hδ f

#print axioms grouped_mix
#print axioms grouped_mix_square
#print axioms localized_real
#print axioms factor_analytic
#print axioms factor_real
#print axioms multiplier_analytic
#print axioms multiplier_bound
#print axioms multiplier_real
#print axioms radial_transformed_analytic

end
end UnifiedTheory.Audit.KFCausalClockFloorMixedRadialStrip
