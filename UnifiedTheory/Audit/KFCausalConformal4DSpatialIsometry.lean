import UnifiedTheory.Audit.KFCausalConformal4DChronology
import UnifiedTheory.Audit.KFCausalConformal4DCoordinateVolume
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Spatial linear isometries lift to actual coordinate maps fixing time.
They preserve the conformal metric, actual curve-defined chronology, and
Lebesgue measure. No spherical-symmetry identity is assumed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalConformal4DSpatialIsometry
noncomputable section
open Set MeasureTheory WithLp
open scoped ContDiff
open KFCausalConformal4DDiamondBenchmark
open KFCausalConformal4DDiamondMeasure (spatialRadius)
open KFCausalConformal4DBoostedMoments (lorentzSquare)
open KFCausalConformal4DTimelikeTangents
open KFCausalConformal4DChronology

abbrev Euclidean := EuclideanSpace ℝ (Fin 3)

def spatialPart (p : Point) : Euclidean := toLp 2 (fun i : Fin 3 => p i.succ)

def lift (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) : Point :=
  Fin.cons (p 0) (ofLp (e (spatialPart p)))

theorem lift_time (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) : lift e p 0 = p 0 := rfl

theorem spatialPart_lift (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    spatialPart (lift e p) = e (spatialPart p) := by
  ext i
  rfl

private theorem spatialPart_add (p q : Point) : spatialPart (p + q) = spatialPart p + spatialPart q := by
  ext i
  rfl

private theorem spatialPart_smul (a : ℝ) (p : Point) : spatialPart (a • p) = a • spatialPart p := by
  ext i
  rfl

private theorem lift_inverse (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    lift e.symm (lift e p) = p := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change e.symm (spatialPart (lift e p)) j = p j.succ
    rw [spatialPart_lift, e.symm_apply_apply]
    rfl

def liftEquiv (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) : Point ≃L[ℝ] Point :=
  (show Point ≃ₗ[ℝ] Point from
    { toFun := lift e
      invFun := lift e.symm
      left_inv := lift_inverse e
      right_inv := lift_inverse e.symm
      map_add' := fun p q => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · change e (spatialPart (p + q)) j = (e (spatialPart p) + e (spatialPart q)) j
          rw [spatialPart_add, map_add]
      map_smul' := fun a p => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · change e (spatialPart (a • p)) j = (a • e (spatialPart p)) j
          rw [spatialPart_smul, map_smul] }).toContinuousLinearEquiv

theorem liftEquiv_apply (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    liftEquiv e p = lift e p := rfl

theorem spatialPart_norm (p : Point) : ‖spatialPart p‖ = spatialRadius p := by
  rw [EuclideanSpace.norm_eq]
  simp [spatialPart, spatialRadius, Fin.sum_univ_three, Real.norm_eq_abs]

theorem lift_radius (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    spatialRadius (lift e p) = spatialRadius p := by
  rw [← spatialPart_norm, spatialPart_lift, e.norm_map, spatialPart_norm]

private theorem radius_sq (p : Point) : spatialRadius p ^ 2 = p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem lift_lorentz (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (p : Point) :
    lorentzSquare (lift e p) = lorentzSquare p := by
  have hr := congrArg (fun r : ℝ => r ^ 2) (lift_radius e p)
  dsimp only at hr
  rw [radius_sq, radius_sq] at hr
  unfold lorentzSquare
  rw [lift_time]
  linarith

theorem lift_omega (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) (att spatial : ℝ) (p : Point) :
    omega att spatial (lift e p) = omega att spatial p := by
  have hr := congrArg (fun r : ℝ => r ^ 2) (lift_radius e p)
  dsimp only at hr
  rw [radius_sq, radius_sq] at hr
  unfold omega
  rw [lift_time, hr]

theorem lift_future_tangent (e : Euclidean ≃ₗᵢ[ℝ] Euclidean)
    (att spatial : ℝ) (p v : Point) :
    futureTangent att spatial (lift e p) (lift e v) ↔ futureTangent att spatial p v := by
  simp only [futureTangent, lift_time, metric_square, lift_omega, lift_lorentz]

private def splitEuclidean : Point ≃ᵐ ℝ × Euclidean :=
  KFCausalConformal4DCoordinateVolume.timeSplit.trans
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))

private theorem split_preserving : MeasurePreserving splitEuclidean := by
  exact ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 3))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)

theorem lift_measurePreserving (e : Euclidean ≃ₗᵢ[ℝ] Euclidean) :
    MeasurePreserving (lift e) := by
  have he : lift e = splitEuclidean.symm ∘ Prod.map id e ∘ splitEuclidean := by
    funext p
    ext i
    fin_cases i <;> rfl
  rw [he]
  exact split_preserving.symm.comp
    (((MeasurePreserving.id volume).prod e.measurePreserving).comp split_preserving)

private theorem chronological_lift (e : Euclidean ≃ₗᵢ[ℝ] Euclidean)
    (att spatial : ℝ) (p q : Point) (h : chronologicalIn att spatial univ p q) :
    chronologicalIn att spatial univ (lift e p) (lift e q) := by
  obtain ⟨γ, hγ, h0, h1, hv⟩ := h
  let L := liftEquiv e
  refine ⟨L ∘ γ, L.contDiff.comp hγ, ?_, ?_, ?_⟩
  · change L (γ 0) = lift e p
    rw [h0]
    rfl
  · change L (γ 1) = lift e q
    rw [h1]
    rfl
  · intro s hs
    refine ⟨mem_univ _, ?_⟩
    have hd := (L : Point →L[ℝ] Point).hasFDerivAt.comp_hasDerivAt s
      ((hγ.differentiable (by norm_num)).differentiableAt.hasDerivAt)
    change HasDerivAt (L ∘ γ) (L (deriv γ s)) s at hd
    rw [hd.deriv]
    exact (lift_future_tangent e att spatial (γ s) (deriv γ s)).mpr (hv s hs).2

theorem chronological_lift_iff (e : Euclidean ≃ₗᵢ[ℝ] Euclidean)
    (att spatial : ℝ) (p q : Point) :
    chronologicalIn att spatial univ (lift e p) (lift e q) ↔
      chronologicalIn att spatial univ p q := by
  refine ⟨?_, chronological_lift e att spatial p q⟩
  intro h
  simpa only [lift_inverse] using chronological_lift e.symm att spatial _ _ h

theorem chronological_diamond_image (e : Euclidean ≃ₗᵢ[ℝ] Euclidean)
    (att spatial : ℝ) (p q : Point) :
    lift e '' chronologicalDiamondIn att spatial univ p q =
      chronologicalDiamondIn att spatial univ (lift e p) (lift e q) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(chronological_lift_iff e att spatial p z).mpr hz.1,
      (chronological_lift_iff e att spatial z q).mpr hz.2⟩
  · intro hx
    obtain ⟨z, rfl⟩ := (liftEquiv e).surjective x
    exact ⟨z, ⟨(chronological_lift_iff e att spatial p z).mp hx.1,
      (chronological_lift_iff e att spatial z q).mp hx.2⟩, rfl⟩

#print axioms lift_time
#print axioms spatialPart_lift
#print axioms liftEquiv_apply
#print axioms spatialPart_norm
#print axioms lift_radius
#print axioms lift_lorentz
#print axioms lift_omega
#print axioms lift_future_tangent
#print axioms lift_measurePreserving
#print axioms chronological_lift_iff
#print axioms chronological_diamond_image
end
end UnifiedTheory.Audit.KFCausalConformal4DSpatialIsometry
