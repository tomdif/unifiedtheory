/- The maximal Fourier momentum is the strong generator of translations
in an arbitrary Euclidean direction. Bounded operators commuting with the
translations therefore preserve its entire natural graph. -/
import UnifiedTheory.Audit.KFCausalFourierTranslation
import UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
import UnifiedTheory.Audit.KFCausalLpDerivativeRepresentative
import UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
open UnifiedTheory.Audit.KFCausalUnitaryMomentumSelfAdjoint
open UnifiedTheory.Audit.KFCausalUnitaryMomentumEvolution
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier
open UnifiedTheory.Audit.KFCausalRealMultiplierSelfAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem translation_initial (f : Hilbert (E := E)) : translation (0:E) f = f := by
  apply Lp.ext
  simpa only [add_zero] using translation_coe (0:E) f

theorem translation_compose (v w : E) (f : Hilbert (E := E)) :
    translation w (translation v f) = translation (v+w) f := by
  apply Lp.ext
  filter_upwards [translation_coe w (translation v f),translation_coe (v+w) f,
    (shift_preserves_volume w).quasiMeasurePreserving.ae (translation_coe v f)] with x hx hy hz
  rw [hx,hy]
  change (translation v f) (x+w) = _ at hz
  rw [hz]
  congr 1
  change x+w+v=x+(v+w)
  abel

theorem translation_continuous (v : E) (f : Hilbert (E := E)) :
    Continuous (fun t : ℝ => translation (t • v) f) := by
  have hc : Continuous (fun t : ℝ => (Homeomorph.addRight (t • v) : C(E,E))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : ℝ × E => z.2+z.1 • v)
    fun_prop
  exact (continuous_const : Continuous (fun _ : ℝ => f)).compMeasurePreservingLp
    hc (fun t => measurePreserving_add_right volume (t • v)) (by norm_num : (2:ENNReal) ≠ ⊤)

def directionalGroup (v : E) : StrongUnitaryGroup (Hilbert (E := E)) where
  action t := translation (t • v)
  initial f := by simpa only [zero_smul] using translation_initial f
  compose t u f := by simpa only [add_smul] using translation_compose (t • v) (u • v) f
  continuous_orbit := translation_continuous v

def multiplier (hbar : ℝ) (v k : E) : ℝ := 2*Real.pi*hbar*inner ℝ k v

omit [FiniteDimensional ℝ E] in
theorem multiplier_measurable (hbar : ℝ) (v : E) : Measurable (multiplier hbar v) := by
  unfold multiplier
  fun_prop

def spectralMomentum (hbar : ℝ) (v : E) : Hilbert (E := E) →ₗ.[ℂ] Hilbert (E := E) :=
  realPullback (Lp.fourierTransformₗᵢ E ℂ) (multiplier hbar v) (multiplier_measurable hbar v)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_eq (t : ℝ) (v k : E) :
    phase (t • v) k = Complex.exp ((2*Real.pi*t*inner ℝ k v:ℝ)*Complex.I) := by
  simp only [phase,real_inner_smul_left,real_inner_comm v k,Real.fourierChar_apply]
  congr 1
  push_cast
  ring

theorem fourier_translation_coe (v : E) (t : ℝ) (f : Hilbert (E := E)) :
    (Lp.fourierTransformₗᵢ E ℂ) (translation (t • v) f) =ᵐ[volume]
      fun k => Complex.exp ((2*Real.pi*t*inner ℝ k v:ℝ)*Complex.I)*((Lp.fourierTransformₗᵢ E ℂ) f) k := by
  rw [fourier_translation]
  filter_upwards [phaseAction_coe (t • v) ((Lp.fourierTransformₗᵢ E ℂ) f)] with k hk
  rw [hk,phase_eq]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_derivative (v k : E) (z : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((2*Real.pi*t*inner ℝ k v:ℝ)*Complex.I)*z)
      ((2*Real.pi*inner ℝ k v:ℝ)*Complex.I*z) 0 := by
  have hd := (((hasDerivAt_id (0:ℝ)).const_mul (2*Real.pi)).mul_const (inner ℝ k v)).ofReal_comp.mul_const Complex.I
  simpa only [id_eq,mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul,mul_one] using hd.cexp.mul_const z

theorem generator_fourier_coe (hbar : ℝ) (hn : hbar ≠ 0) (v : E)
    (f : (momentum (directionalGroup v) hbar).domain) :
    (Lp.fourierTransformₗᵢ E ℂ) (momentum (directionalGroup v) hbar f) =ᵐ[volume]
      fun k => (multiplier hbar v k:ℂ)*((Lp.fourierTransformₗᵢ E ℂ) (f:Hilbert)) k := by
  have hd := momentum_orbit_derivative (directionalGroup v) hbar hn f 0
  simp only [StrongUnitaryGroup.initial] at hd
  have hF := (((Lp.fourierTransformₗᵢ E ℂ) : Hilbert (E := E) →L[ℂ] Hilbert (E := E)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun t => (Lp.fourierTransformₗᵢ E ℂ) (translation (t • v) (f:Hilbert)))
    ((Lp.fourierTransformₗᵢ E ℂ) ((Complex.I/(hbar:ℂ)) • momentum (directionalGroup v) hbar f)) 0 at hF
  rw [map_smul] at hF
  have hrep := KFCausalLpDerivativeRepresentative.derivative_representative _ _ _ _
    (fun t => fourier_translation_coe v t f) hF (fun k => phase_derivative v k ((Lp.fourierTransformₗᵢ E ℂ) (f:Hilbert) k))
  filter_upwards [hrep,Lp.coeFn_smul (Complex.I/(hbar:ℂ))
    ((Lp.fourierTransformₗᵢ E ℂ) (momentum (directionalGroup v) hbar f))] with k hk hs
  rw [hs] at hk
  simp only [Pi.smul_apply,smul_eq_mul] at hk
  have he := congrArg (fun z : ℂ => (-Complex.I*(hbar:ℂ))*z) hk
  dsimp only at he
  have hi : (-Complex.I*(hbar:ℂ))*(Complex.I/(hbar:ℂ)) = 1 := by rw [mul_comm,inverse_coefficient hbar hn]
  rw [← mul_assoc,hi,one_mul] at he
  rw [he]
  unfold multiplier
  push_cast
  ring_nf
  norm_num [Complex.I_sq]

theorem spectralMomentum_eq_generator (hbar : ℝ) (hn : hbar ≠ 0) (v : E) :
    spectralMomentum hbar v = momentum (directionalGroup v) hbar := by
  have hle : momentum (directionalGroup v) hbar ≤ spectralMomentum hbar v := by
    apply LinearPMap.le_graph_iff.mp
    rintro ⟨f,g⟩ hfg
    obtain ⟨u,hu,hg⟩ := (LinearPMap.mem_graph_iff _).mp hfg
    apply (realPullback_graph _ _ _ f g).mpr
    simpa only [hu,hg] using generator_fourier_coe hbar hn v u
  have hm := momentum_selfAdjoint (directionalGroup v) hbar hn
  have hformal : (momentum (directionalGroup v) hbar).IsFormalAdjoint (spectralMomentum hbar v) := by
    intro f g
    rw [← (Lp.fourierTransformₗᵢ E ℂ).inner_map_map (momentum (directionalGroup v) hbar f) (g:Hilbert),
      ← (Lp.fourierTransformₗᵢ E ℂ).inner_map_map (f:Hilbert) (spectralMomentum hbar v g),L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [generator_fourier_coe hbar hn v f,
      realPullback_coe (Lp.fourierTransformₗᵢ E ℂ) (multiplier hbar v) (multiplier_measurable hbar v) g] with k hf hg
    change ((Lp.fourierTransformₗᵢ E ℂ) (spectralMomentum hbar v g)) k = _ at hg
    rw [hf,hg]
    change inner ℂ ((multiplier hbar v k:ℂ) • ((Lp.fourierTransformₗᵢ E ℂ) (f:Hilbert)) k)
      (((Lp.fourierTransformₗᵢ E ℂ) (g:Hilbert)) k) =
        inner ℂ (((Lp.fourierTransformₗᵢ E ℂ) (f:Hilbert)) k)
          ((multiplier hbar v k:ℂ) • ((Lp.fourierTransformₗᵢ E ℂ) (g:Hilbert)) k)
    simp [mul_assoc,mul_left_comm]
  have ha := hformal.le_adjoint (momentum_dense (directionalGroup v) hbar)
  rw [LinearPMap.isSelfAdjoint_def.mp hm] at ha
  exact le_antisymm ha hle

theorem spectralMomentum_graph_derivative (hbar : ℝ) (hn : hbar ≠ 0) (v : E) (f g : Hilbert (E := E)) :
    (f,g) ∈ (spectralMomentum hbar v).graph ↔
      HasDerivAt (fun t : ℝ => translation (t • v) f) ((Complex.I/(hbar:ℂ)) • g) 0 := by
  rw [spectralMomentum_eq_generator hbar hn v]
  exact momentum_graph_iff (directionalGroup v) hbar hn f g

theorem bounded_commutation (hbar : ℝ) (hn : hbar ≠ 0) (v : E)
    (B : Hilbert (E := E) →L[ℂ] Hilbert (E := E))
    (hB : ∀ (t : ℝ) f, B (translation (t • v) f) = translation (t • v) (B f))
    (f g : Hilbert (E := E)) (hfg : (f,g) ∈ (spectralMomentum hbar v).graph) :
    (B f,B g) ∈ (spectralMomentum hbar v).graph := by
  apply (spectralMomentum_graph_derivative hbar hn v _ _).mpr
  have hd := (B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative hbar hn v f g).mp hfg)
  change HasDerivAt (fun t : ℝ => B (translation (t • v) f)) (B ((Complex.I/(hbar:ℂ)) • g)) 0 at hd
  simpa only [Function.comp_def,hB,map_smul] using hd

#print axioms translation_initial
#print axioms translation_compose
#print axioms translation_continuous
#print axioms multiplier_measurable
#print axioms phase_eq
#print axioms fourier_translation_coe
#print axioms phase_derivative
#print axioms generator_fourier_coe
#print axioms spectralMomentum_eq_generator
#print axioms spectralMomentum_graph_derivative
#print axioms bounded_commutation

end
end UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
