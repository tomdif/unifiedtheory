/-
  Audit/KFCausalCSpecRecoveredStageBDG4DOperator.lean

  Concrete 4D BDG operator profile input for the recovered-stage BDG bridge.

  The volume-sector theorem `bdg_4d_operator_reduced` is stated for a real
  high-density parameter.  This file packages its hypothesis stack as
  `BDG4DOperatorProfileData`, proves the real profile limit, and samples it
  into the `BDGProfileSequenceAsymptotics` interface used by recovered CSpec
  stages.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecRecoveredStageBDGProfile
import UnifiedTheory.Audit.KFCausalMinkowski4DOperator

set_option autoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

open MeasureTheory Real Set Filter Topology
open scoped BigOperators
open UnifiedTheory.Audit.KFCausalMinkowski4DMoments
open UnifiedTheory.Audit.KFCausalMinkowski4DOperator

/-- The analytic/geometric hypothesis stack required by the reduced 4D BDG
operator theorem, bundled so it can be sampled into the CSpec recovery
interface. -/
structure BDG4DOperatorProfileData where
  uSupport : ℝ
  vSupport : ℝ
  profileBound : ℝ
  profileDerivBound : ℝ
  mixedBound : ℝ
  mixedUDerivBound : ℝ
  mixedVDerivBound : ℝ
  coneBound : ℝ
  huSupport_pos : 0 < uSupport
  hvSupport_pos : 0 < vSupport
  mbar : ℝ → ℝ → ℝ
  profile : ℝ → ℝ → ℝ
  profileU : ℝ → ℝ → ℝ
  profileUV : ℝ → ℝ → ℝ
  profileUVU : ℝ → ℝ → ℝ
  profileUVV : ℝ → ℝ → ℝ
  profileUU : ℝ → ℝ
  profileVV : ℝ → ℝ
  profile_def :
    ∀ u v, profile u v = mbar (-(u + v) / 2) ((v - u) / 2)
  even_mbar : ∀ t r, mbar t (-r) = mbar t r
  profile_cont : Continuous (Function.uncurry profile)
  profileU_cont : Continuous (Function.uncurry profileU)
  profileUV_cont : Continuous (Function.uncurry profileUV)
  profile_deriv_u :
    ∀ v u, HasDerivAt (fun u' => profile u' v) (profileU u v) u
  profileU_deriv_v :
    ∀ u v, HasDerivAt (fun v' => profileU u v') (profileUV u v) v
  profileUV_deriv_u :
    ∀ v u, HasDerivAt (fun u' => profileUV u' v) (profileUVU u v) u
  profileUV_deriv_v :
    ∀ u v, HasDerivAt (fun v' => profileUV u v') (profileUVV u v) v
  profile_bound : ∀ u v, |profile u v| ≤ profileBound
  profileU_bound : ∀ u v, |profileU u v| ≤ profileDerivBound
  profileUV_bound : ∀ u v, |profileUV u v| ≤ mixedBound
  profileUVU_bound : ∀ u v, |profileUVU u v| ≤ mixedUDerivBound
  profileUVV_bound : ∀ u v, |profileUVV u v| ≤ mixedVDerivBound
  hCcone : ∀ (a : ℝ), 0 < a → ∀ u v,
    |a * (v - u)^2 * f4D (a * u^2 * v^2) * profile u v| ≤ coneBound * a
  profile_support_u : ∀ u v, uSupport ≤ u → profile u v = 0
  profile_support_v : ∀ u v, vSupport ≤ v → profile u v = 0
  profileU_support_u : ∀ u v, uSupport ≤ u → profileU u v = 0
  profileU_support_v : ∀ u v, vSupport ≤ v → profileU u v = 0
  profileUV_support_u : ∀ u v, uSupport ≤ u → profileUV u v = 0
  profileUV_support_v : ∀ u v, vSupport ≤ v → profileUV u v = 0
  profileVV_deriv : ∀ u, HasDerivAt profileVV (profileUVV u 0) u
  profileUU_deriv : ∀ v, HasDerivAt profileUU (profileUVU 0 v) v
  profileUVV_axis_cont : Continuous (fun u => profileUVV u 0)
  profileUVU_axis_cont : Continuous (fun v => profileUVU 0 v)
  profileVV_support : ∀ u, uSupport ≤ u → profileVV u = 0
  profileUU_support : ∀ v, vSupport ≤ v → profileUU v = 0

namespace BDG4DOperatorProfileData

/-- The real-parameter reduced 4D BDG operator profile mean. -/
noncomputable def mean (D : BDG4DOperatorProfileData) : ℝ → ℝ :=
  fun a => Real.sqrt a *
    ((16 * a * ∫ t in Iio (0 : ℝ), ∫ r in Ioo (0 : ℝ) (-t),
      r^2 * f4D (a * (t^2 - r^2)^2) * D.mbar t r) -
        (1 / 6) * D.profile 0 0)

/-- The point-jet target of the reduced 4D BDG operator profile. -/
noncomputable def target (D : BDG4DOperatorProfileData) : ℝ :=
  Real.sqrt π / 24 * (D.profileUU 0 + D.profileVV 0) -
    Real.sqrt π / 6 * D.profileUV 0 0

/-- The existing reduced 4D operator theorem, repackaged as a profile limit. -/
theorem tendsto (D : BDG4DOperatorProfileData) :
    Tendsto (mean D) atTop (𝓝 (target D)) := by
  change
    Tendsto
      (fun a => Real.sqrt a *
        ((16 * a * ∫ t in Iio (0 : ℝ), ∫ r in Ioo (0 : ℝ) (-t),
          r^2 * f4D (a * (t^2 - r^2)^2) * D.mbar t r) -
            (1 / 6) * D.profile 0 0))
      atTop
      (𝓝 (Real.sqrt π / 24 * (D.profileUU 0 + D.profileVV 0) -
        Real.sqrt π / 6 * D.profileUV 0 0))
  exact
    bdg_4d_operator_reduced
      D.uSupport D.vSupport D.profileBound D.profileDerivBound
      D.mixedBound D.mixedUDerivBound D.mixedVDerivBound D.coneBound
      D.huSupport_pos D.hvSupport_pos
      D.mbar D.profile D.profileU D.profileUV D.profileUVU D.profileUVV
      D.profileUU D.profileVV
      D.profile_def D.even_mbar
      D.profile_cont D.profileU_cont D.profileUV_cont
      D.profile_deriv_u D.profileU_deriv_v
      D.profileUV_deriv_u D.profileUV_deriv_v
      D.profile_bound D.profileU_bound D.profileUV_bound
      D.profileUVU_bound D.profileUVV_bound D.hCcone
      D.profile_support_u D.profile_support_v
      D.profileU_support_u D.profileU_support_v
      D.profileUV_support_u D.profileUV_support_v
      D.profileVV_deriv D.profileUU_deriv
      D.profileUVV_axis_cont D.profileUVU_axis_cont
      D.profileVV_support D.profileUU_support

/-- Sampling the real 4D operator profile along any recovered-stage density
sequence tending to infinity preserves the BDG profile limit. -/
theorem sampled_tendsto
    (D : BDG4DOperatorProfileData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop) :
    Tendsto (fun n => mean D (density n)) atTop (𝓝 (target D)) :=
  D.tendsto.comp hdensity

/-- The reduced 4D operator profile as a one-channel
`BDGProfileSequenceAsymptotics` object.  This is the concrete profile input
that the recovered-stage bridge can consume. -/
noncomputable def sequenceAsymptotics
    (D : BDG4DOperatorProfileData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ) :
    BDGProfileSequenceAsymptotics Unit where
  layers := Finset.univ
  density := density
  layerMean := fun _ n => mean D (density n)
  profileMean := fun _ => mean D
  layerConstant := fun _ => 0
  layerSecond := fun _ => 1
  curvatureCoeff := 0
  phiAtPoint := phiAtPoint
  boxPhi := target D
  curvaturePhi := curvaturePhi
  density_tendsto_atTop := hdensity
  profile_tendsto := by
    intro i _hi
    cases i
    simpa [target]
      using D.tendsto
  layerMean_eventually_eq_profile := by
    intro i
    filter_upwards with n
    rfl

/-- The concrete one-channel 4D operator profile supplies the sequence-level
layer asymptotics required by the recovered-stage BDG interface. -/
theorem sequenceAsymptotics_layer_asymptotics
    (D : BDG4DOperatorProfileData)
    (density : ℕ → ℝ)
    (hdensity : Tendsto density atTop atTop)
    (phiAtPoint curvaturePhi : ℝ) :
    ∀ i ∈ (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layers,
      Tendsto
        ((D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerMean i)
        atTop
        (𝓝
          ((D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerConstant i *
              (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).phiAtPoint +
            (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layerSecond i *
              ((D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).boxPhi +
                (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).curvatureCoeff *
                  (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).curvaturePhi))) :=
  (D.sequenceAsymptotics density hdensity phiAtPoint curvaturePhi).layer_asymptotics

#print axioms BDG4DOperatorProfileData.tendsto
#print axioms BDG4DOperatorProfileData.sampled_tendsto
#print axioms BDG4DOperatorProfileData.sequenceAsymptotics
#print axioms BDG4DOperatorProfileData.sequenceAsymptotics_layer_asymptotics

end BDG4DOperatorProfileData

end UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
