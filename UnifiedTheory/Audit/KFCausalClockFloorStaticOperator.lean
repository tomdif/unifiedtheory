/- The maximal static sigma multiplier is exactly the square of the
proved static root operator, with the actual composition domains retained.
Its pairing is the original static-root energy pairing. Identification
with the closure of the original static output is a separate attachment. -/
import UnifiedTheory.Audit.KFCausalClockFloorStaticMultiplierForm

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorStaticOperator
noncomputable section
open MeasureTheory
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeTransverseSplit (dualPhysical)
open KFCausalClockFloorStaticMultiplierForm
open KFCausalUnitaryRealMultiplier
open KFCausalRealMultiplierSelfAdjoint

def operator (ε : ℝ) (hε : 0 < ε) (h : ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  realPullback dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable

theorem selfAdjoint (ε : ℝ) (hε : 0 < ε) (h : ℝ) :
    IsSelfAdjoint (operator ε hε h) :=
  realPullback_selfAdjoint dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable

theorem domain_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f : Hilbert) :
    f ∈ (operator ε hε h).domain ↔
      MemLp (fun x => (symbol ε h x : ℂ)*(dualPhysical f) x) 2 :=
  realPullback_domain dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable f

theorem graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert) :
    (f,g) ∈ (operator ε hε h).graph ↔
      dualPhysical g =ᵐ[volume] fun x => (symbol ε h x : ℂ)*(dualPhysical f) x :=
  realPullback_graph dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable f g

private theorem root_memLp (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (operator ε hε h).graph) :
    MemLp (fun x => (rootSymbol ε h x : ℂ)*(dualPhysical f) x) 2 := by
  have hm := ((Lp.memLp (dualPhysical f)).norm.add (Lp.memLp (dualPhysical g)).norm)
  have hc := (Complex.continuous_ofReal.comp (symbol_continuous ε hε h).sqrt).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable (dualPhysical f))
  apply hm.of_le hc
  filter_upwards [(graph_iff ε hε h f g).mp hfg] with x hx
  have hs : rootSymbol ε h x ≤ 1+symbol ε h x := by
    have hpos := (symbol_positive ε hε h x).le
    have hs0 : 0 ≤ rootSymbol ε h x := Real.sqrt_nonneg _
    have he := rootSymbol_square ε hε h x
    nlinarith [sq_nonneg (rootSymbol ε h x-1)]
  change ‖(rootSymbol ε h x : ℂ) * (dualPhysical f) x‖ ≤ ‖‖(dualPhysical f) x‖ + ‖(dualPhysical g) x‖‖
  rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),hx]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (symbol_positive ε hε h x)]
  change |rootSymbol ε h x| * ‖(dualPhysical f) x‖ ≤ _
  rw [abs_of_nonneg (show 0 ≤ rootSymbol ε h x from Real.sqrt_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg ((dualPhysical f) x))]

theorem root_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : (operator ε hε h).domain) : (f : Hilbert) ∈ (rootOperator ε hε h).domain :=
  (realPullback_domain dualPhysical (rootSymbol ε h)
    ((symbol_continuous ε hε h).sqrt.measurable) f).mpr
      (root_memLp ε hε h f _ ((operator ε hε h).mem_graph f))

private theorem root_square_cast (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (x : KFCausalEuclideanProductCoordinates.Joint 5 1) :
    (rootSymbol ε h x : ℂ)^2=(symbol ε h x : ℂ) := by
  exact_mod_cast rootSymbol_square ε hε h x

theorem square_graph_iff (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert) :
    (f,g) ∈ (operator ε hε h).graph ↔ ∃ y : Hilbert,
      (f,y) ∈ (rootOperator ε hε h).graph ∧ (y,g) ∈ (rootOperator ε hε h).graph := by
  constructor
  · intro hfg
    have hf : f ∈ (rootOperator ε hε h).domain :=
      (realPullback_domain dualPhysical (rootSymbol ε h)
        ((symbol_continuous ε hε h).sqrt.measurable) f).mpr (root_memLp ε hε h f g hfg)
    let y := rootOperator ε hε h ⟨f,hf⟩
    have hy : (f,y) ∈ (rootOperator ε hε h).graph := (rootOperator ε hε h).mem_graph ⟨f,hf⟩
    refine ⟨y,hy,?_⟩
    apply (realPullback_graph dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) y g).mpr
    filter_upwards [(graph_iff ε hε h f g).mp hfg,
      (realPullback_graph dualPhysical (rootSymbol ε h)
        ((symbol_continuous ε hε h).sqrt.measurable) f y).mp hy] with x hx hyx
    rw [hx,hyx,← mul_assoc,← pow_two,root_square_cast ε hε h x]
  · rintro ⟨y,hy,hg⟩
    apply (graph_iff ε hε h f g).mpr
    filter_upwards [(realPullback_graph dualPhysical (rootSymbol ε h)
        ((symbol_continuous ε hε h).sqrt.measurable) f y).mp hy,
      (realPullback_graph dualPhysical (rootSymbol ε h)
        ((symbol_continuous ε hε h).sqrt.measurable) y g).mp hg] with x hyx hgx
    rw [hgx,hyx,← mul_assoc,← pow_two,root_square_cast ε hε h x]

theorem root_pairing (ε : ℝ) (hε : 0 < ε) (h : ℝ)
    (f : (operator ε hε h).domain) (v : (rootOperator ε hε h).domain) :
    inner ℂ (rootOperator ε hε h v)
      (rootOperator ε hε h ⟨(f:Hilbert),root_domain ε hε h f⟩) =
        inner ℂ (v:Hilbert) (operator ε hε h f) := by
  rw [← dualPhysical.inner_map_map,← dualPhysical.inner_map_map (v:Hilbert),
    L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [realPullback_coe dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) v,
    realPullback_coe dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) ⟨(f:Hilbert),root_domain ε hε h f⟩,
    realPullback_coe dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable f]
      with x hv hf ht
  change inner ℂ ((dualPhysical (realPullback dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) v)) x)
    ((dualPhysical (realPullback dualPhysical (rootSymbol ε h)
      ((symbol_continuous ε hε h).sqrt.measurable) ⟨(f:Hilbert),root_domain ε hε h f⟩)) x) =
      inner ℂ ((dualPhysical (v:Hilbert)) x) ((dualPhysical
        (realPullback dualPhysical (symbol ε h) (symbol_continuous ε hε h).measurable f)) x)
  rw [hv,hf,ht]
  change inner ℂ ((rootSymbol ε h x:ℂ) • (dualPhysical (v:Hilbert)) x)
      ((rootSymbol ε h x:ℂ) • (dualPhysical (f:Hilbert)) x) =
    inner ℂ ((dualPhysical (v:Hilbert)) x) ((symbol ε h x:ℂ) • (dualPhysical (f:Hilbert)) x)
  rw [inner_smul_left,inner_smul_right,inner_smul_right,Complex.conj_ofReal]
  rw [← mul_assoc,← pow_two,root_square_cast ε hε h x]

#print axioms selfAdjoint
#print axioms domain_iff
#print axioms graph_iff
#print axioms root_domain
#print axioms square_graph_iff
#print axioms root_pairing
end
end UnifiedTheory.Audit.KFCausalClockFloorStaticOperator
