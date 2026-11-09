/- The actual rational radial cutoff preserves the full natural ordered
clock exponential and both ordered matter graphs. Its shifted output is
bounded and accretive. No growing-form stability or operator core is
assumed or asserted by these natural-domain transport identities. -/
import UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaStrip
import UnifiedTheory.Audit.KFCausalMixedStripFieldGraph
import UnifiedTheory.Audit.KFCausalClockMixedClockGraph
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOrderedTransport
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalEuclideanConfiguration (Space)
open KFCausalEuclideanClockSplit (TailSpace)
open KFCausalEuclideanProductCoordinates (Block split split_preserves_volume)
open KFCausalPairedModeCoordinates (scale modeIsometry mode_preserves_volume)
open KFCausalClockFloorRadialYosidaSymbol (action)
open KFCausalClockFloorRadialYosidaStrip
open KFCausalClockFloorMixedRadial (clockMixed)
open KFCausalClockFloorDefectCoordinates (straightening)
open KFCausalMixedStripExponentialGraph (unitary unitary_straightening_coe)
open KFCausalClockFloorBoundedInverse (inverseL ordered_graph_iff)
open KFCausalClockMixedClockGraph (inverseL_clockMixed_coe)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open KFCausalClockFloorTrialMatter (matterFactor)
open KFCausalClockFloorExponential (longitudinalExponential)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalPhysicalField (physicalField)
open KFCausalTransverseFieldSquare (fieldSquare)
open KFCausalOrderedOperatorComposition (composition_graph)

def mixedTail (z : TailSpace) : Block 2 × Block 4 :=
  (WithLp.toLp 2 ![scale*(z 0-z 1),scale*(z 2-z 3)],
    WithLp.toLp 2 ![0,scale*(z 0+z 1),scale*(z 2+z 3),z 4])

def family (ε h N : ℝ) (q : ℂ) (z : TailSpace) : ℂ :=
  multiplier ε h N q (mixedTail z)

theorem family_analytic (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (z : TailSpace) (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/6) :
    AnalyticAt ℂ (fun q => family ε h N q z) q :=
  multiplier_analytic ε hε h N hN q hq _

theorem family_line_continuous (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) :
    Continuous (fun z : ℝ × TailSpace => family ε h N ((z.1:ℂ)+(y:ℂ)*Complex.I) z.2) := by
  have ht : Continuous mixedTail := by
    unfold mixedTail
    apply Continuous.prodMk
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp <;> fun_prop
  have hc : Continuous (fun z : ℝ × TailSpace => (z.1,mixedTail z.2)) :=
    continuous_fst.prodMk (ht.comp continuous_snd)
  change Continuous (fun z : ℝ × TailSpace =>
    multiplier ε h N ((z.1:ℂ)+(y:ℂ)*Complex.I) (mixedTail z.2))
  have hf := (multiplier_line_continuous ε hε h N hN y hy).comp hc
  simpa only [Function.comp_apply] using hf

theorem family_bound (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/6) (z : TailSpace) : ‖family ε h N q z‖ ≤ N :=
  multiplier_norm ε hε h N hN q hq _

theorem family_re (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (q : ℂ) (hq : |q.im| ≤ Real.pi*ε/6) (z : TailSpace) : 0 ≤ (family ε h N q z).re :=
  multiplier_re ε hε h N hN q hq _

theorem family_symbol (ε h N y : ℝ) (x : Space) :
    KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y x =
      multiplier ε h N ((x 0:ℂ)+(y:ℂ)*Complex.I) (split 2 4 (modeIsometry x)) := rfl

def shifted (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) : Hilbert →L[ℂ] Hilbert :=
  KFCausalMixedStripExponentialGraph.action ε hε (family ε h N) (Real.pi*ε/6) N
    (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy

theorem shifted_zero (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (h0 : |(0:ℝ)| ≤ Real.pi*ε/6) (f : Hilbert) :
    shifted ε hε h N hN 0 h0 f=action ε hε h N hN f := by
  apply (unitary ε hε).injective
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [KFCausalMixedStripExponentialGraph.action_coe ε hε
      (family ε h N) (Real.pi*ε/6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) 0 h0 f,
    unitary_straightening_coe ε hε f,
    unitary_straightening_coe ε hε (action ε hε h N hN f),
    ((split_preserves_volume 2 4).quasiMeasurePreserving.comp
      mode_preserves_volume.quasiMeasurePreserving).ae (action_transformed ε hε h N hN f)]
    with x hn hf hp hr
  change (straightening ε hε (unitary ε hε (shifted ε hε h N hN 0 h0 f))) x=_ at hn
  rw [hn,hp,hf,family_symbol]
  simp only [Complex.ofReal_zero,zero_mul,add_zero]
  exact hr.symm

theorem shifted_norm (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) (f : Hilbert) :
    ‖shifted ε hε h N hN y hy f‖ ≤ N*‖f‖ :=
  KFCausalMixedStripExponentialGraph.action_norm ε hε
    (family ε h N) (Real.pi*ε/6) N
    (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy N
    (fun x => family_bound ε hε h N hN _ (by simpa using hy) _) f

private theorem multiplier_accretive {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (m : X → ℂ) (f g : Lp ℂ 2 μ) (hm : ∀ x, 0 ≤ (m x).re)
    (hg : g =ᵐ[μ] fun x => m x*f x) : 0 ≤ (inner ℂ f g).re := by
  have he := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re ∂μ)=(∫ x, inner ℂ (f x) (g x) ∂μ).re at he
  rw [L2.inner_def,← he]
  apply integral_nonneg_of_ae
  filter_upwards [hg] with x hx
  rw [hx]
  change 0 ≤ (inner ℂ (f x) (m x • f x)).re
  rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
  change 0 ≤ (m x*((‖f x‖:ℝ):ℂ)^2).re
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact mul_nonneg (hm x) (sq_nonneg _)

theorem shifted_accretive (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (y : ℝ) (hy : |y| ≤ Real.pi*ε/6) (f : Hilbert) :
    0 ≤ (inner ℂ f (shifted ε hε h N hN y hy f)).re := by
  have he := multiplier_accretive
    (KFCausalStripFamilyExponentialGraph.symbol (family ε h N) y)
    (straightening ε hε (unitary ε hε f))
    (straightening ε hε (unitary ε hε (shifted ε hε h N hN y hy f)))
    (fun x => family_re ε hε h N hN _ (by simpa using hy) _)
    (KFCausalMixedStripExponentialGraph.action_coe ε hε (family ε h N) (Real.pi*ε/6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN) y hy f)
  simpa only [LinearIsometryEquiv.inner_map_map] using he

theorem inverse_commute (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N) (f : Hilbert) :
    inverseL ε hε (action ε hε h N hN f)=action ε hε h N hN (inverseL ε hε f) := by
  apply (clockMixed ε hε).injective
  apply Lp.ext
  filter_upwards [inverseL_clockMixed_coe ε hε (action ε hε h N hN f),
    action_transformed ε hε h N hN f,action_transformed ε hε h N hN (inverseL ε hε f),
    inverseL_clockMixed_coe ε hε f] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  ring

theorem shift_bound (ε h : ℝ) (hb : |h| ≤ Real.pi*ε/3) : |-h/2| ≤ Real.pi*ε/6 := by
  rw [abs_div,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

theorem ordered_graph_action (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g) ∈
      (orderedExponential ε hε h).graph := by
  rw [ordered_graph_iff] at hfg ⊢
  have h0 : |(0:ℝ)| ≤ Real.pi*ε/6 := by rw [abs_zero]; positivity
  have hg := KFCausalMixedStripExponentialGraph.graph_action ε hε
    (family ε h N) (Real.pi*ε/6) N (family_line_continuous ε hε h N hN) hN.le
    (family_bound ε hε h N hN) (family_analytic ε hε h N hN) h h0
    (shift_bound ε h hb) (inverseL ε hε f) g hfg
  change (shifted ε hε h N hN 0 h0 (inverseL ε hε f),
    shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g) ∈ _ at hg
  rw [shifted_zero,← inverse_commute] at hg
  exact hg

theorem ordered_domain_action (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (f : Hilbert) (hf : f ∈ (orderedExponential ε hε h).domain) :
    action ε hε h N hN f ∈ (orderedExponential ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (ordered_graph_action ε hε h N hN hb f _
    ((orderedExponential ε hε h).mem_graph ⟨f,hf⟩))

theorem linear_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (physicalField pointField)).graph) :
    (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g) ∈
      (matterFactor ε hε h (physicalField pointField)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨shifted ε hε h N hN (-h/2) (shift_bound ε h hb) u,
    ordered_graph_action ε hε h N hN hb f u hu,
    KFCausalMixedStripFieldGraph.field_graph_action ε hε (family ε h N) (Real.pi*ε/6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN)
      (-h/2) (shift_bound ε h hb) u g hg⟩

theorem quadratic_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h N : ℝ) (hN : 0 < N)
    (hb : |h| ≤ Real.pi*ε/3) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (fieldSquare pointField)).graph) :
    (action ε hε h N hN f,shifted ε hε h N hN (-h/2) (shift_bound ε h hb) g) ∈
      (matterFactor ε hε h (fieldSquare pointField)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨shifted ε hε h N hN (-h/2) (shift_bound ε h hb) u,
    ordered_graph_action ε hε h N hN hb f u hu,
    KFCausalMixedStripFieldGraph.square_graph_action ε hε (family ε h N) (Real.pi*ε/6) N
      (family_line_continuous ε hε h N hN) hN.le (family_bound ε hε h N hN)
      (-h/2) (shift_bound ε h hb) u g hg⟩

#print axioms family_analytic
#print axioms family_line_continuous
#print axioms family_bound
#print axioms family_re
#print axioms family_symbol
#print axioms shifted_zero
#print axioms shifted_norm
#print axioms shifted_accretive
#print axioms inverse_commute
#print axioms shift_bound
#print axioms ordered_graph_action
#print axioms ordered_domain_action
#print axioms linear_matter_graph_action
#print axioms quadratic_matter_graph_action
end
end UnifiedTheory.Audit.KFCausalClockFloorRadialYosidaOrderedTransport
