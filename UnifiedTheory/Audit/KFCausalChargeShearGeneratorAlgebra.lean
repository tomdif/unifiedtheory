/- The actual charge-conjugated shear vector fields form a five-parameter
matrix algebra after the existing frequency normalization. The neutral
shear terms are retained. The commutator convention here is A*B-B*A for
linear coordinate maps, not an assertion about unbounded quantum graphs. -/
import UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalChargeShearGeneratorAlgebra
noncomputable section
open UnifiedTheory.Audit.KFCausalChargeShearJointFlow (Space)
open UnifiedTheory.Audit.KFCausalChargeShearRotatedVelocity (velocity rotatedVelocity)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow (dilate dilationEquiv)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (scale scale_square)

abbrev Coefficients := Fin 5 → ℝ

/-- Slots are diagonal shear, symmetric mixing, rotation, and two neutral shears. -/
def generator (a : Coefficients) : Space →ₗ[ℝ] Space where
  toFun x := WithLp.toLp 2 fun
    | .inl i => ![-a 0*x (.inl 0)/2+(a 1/2-a 2)*x (.inr 1),
      -a 0*x (.inl 1)/2+(a 1/2-a 2)*x (.inr 2)] i
    | .inr i => ![0,(a 1/2+a 2)*x (.inl 0)+a 0*x (.inr 1)/2,
      (a 1/2+a 2)*x (.inl 1)+a 0*x (.inr 2)/2,
      2*scale*(a 3*x (.inl 1)+a 4*x (.inr 2))] i
  map_add' x y := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring

def bracket (a b : Coefficients) : Coefficients :=
  ![2*(a 2*b 1-a 1*b 2),
    2*(a 0*b 2-a 2*b 0),
    (a 0*b 1-a 1*b 0)/2,
    (a 0*b 3-a 3*b 0)/2-a 2*b 4+a 4*b 2-(a 1*b 4-a 4*b 1)/2,
    -(a 0*b 4-a 4*b 0)/2+a 2*b 3-a 3*b 2-(a 1*b 3-a 3*b 1)/2]

theorem generator_commutator (a b : Coefficients) :
    (generator a).comp (generator b)-(generator b).comp (generator a) = generator (bracket a b) := by
  ext x i
  rcases i with i | i <;> fin_cases i <;> simp [generator,bracket] <;> ring

def unit (i : Fin 2 ⊕ Fin 4) : Space := WithLp.toLp 2 (Pi.single i 1)

theorem generator_eq_zero_iff (a : Coefficients) : generator a = 0 ↔ a = 0 := by
  constructor
  · intro he
    have h0 := congrArg (fun L : Space →ₗ[ℝ] Space => L (unit (.inl 0)) (.inl 0)) he
    have h1 := congrArg (fun L : Space →ₗ[ℝ] Space => L (unit (.inl 0)) (.inr 1)) he
    have h2 := congrArg (fun L : Space →ₗ[ℝ] Space => L (unit (.inr 1)) (.inl 0)) he
    have h3 := congrArg (fun L : Space →ₗ[ℝ] Space => L (unit (.inl 1)) (.inr 3)) he
    have h4 := congrArg (fun L : Space →ₗ[ℝ] Space => L (unit (.inr 2)) (.inr 3)) he
    simp [generator,unit] at h0 h1 h2 h3 h4
    have hs : scale ≠ 0 := by nlinarith [scale_square]
    have h3' : a 3 = 0 := h3.resolve_left hs
    have h4' : a 4 = 0 := h4.resolve_left hs
    funext i
    fin_cases i
    · exact h0
    · change a 1 = 0; linarith
    · change a 2 = 0; linarith
    · exact h3'
    · exact h4'
  · rintro rfl
    ext x i
    rcases i with i | i <;> fin_cases i <;> simp [generator]

theorem generator_add (a b : Coefficients) : generator (a+b) = generator a+generator b := by
  ext x i
  rcases i with i | i <;> fin_cases i <;> simp [generator] <;> ring

theorem generator_smul (r : ℝ) (a : Coefficients) : generator (r • a) = r • generator a := by
  ext x i
  rcases i with i | i <;> fin_cases i <;> simp [generator] <;> ring

theorem actual_shear (x : Space) : velocity x = generator ![1,0,0,0,1] x := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [velocity,generator]

def orbitCoefficients (θ : ℝ) : Coefficients :=
  ![Real.cos θ^2-Real.sin θ^2,-2*Real.sin θ*Real.cos θ,0,-Real.sin θ,Real.cos θ]

theorem actual_rotated_normalized (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Space) :
    dilate c (rotatedVelocity c hc θ x) = generator (orbitCoefficients θ) (dilate c x) := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [dilate,rotatedVelocity,velocity,generator,orbitCoefficients,
      KFCausalNormalizedChargeFlow.flow_apply,KFCausalPairedRotation.rotate] <;>
    field_simp <;> ring

theorem actual_commutator_normalized (c : ℝ) (hc : c ≠ 0) (θ φ : ℝ) (x : Space) :
    dilate c (rotatedVelocity c hc θ (rotatedVelocity c hc φ x)-
      rotatedVelocity c hc φ (rotatedVelocity c hc θ x)) =
      generator (bracket (orbitCoefficients θ) (orbitCoefficients φ)) (dilate c x) := by
  have hd (u v : Space) : dilate c (u-v) = dilate c u-dilate c v :=
    (dilationEquiv c hc).map_sub u v
  rw [hd,actual_rotated_normalized,actual_rotated_normalized,
    actual_rotated_normalized,actual_rotated_normalized]
  exact congrArg (fun L : Space →ₗ[ℝ] Space => L (dilate c x))
    (generator_commutator (orbitCoefficients θ) (orbitCoefficients φ))

theorem actual_commutator_witness (c : ℝ) (hc : c ≠ 0) :
    (rotatedVelocity c hc 0 (rotatedVelocity c hc (Real.pi/4) (unit (.inl 0)))-
      rotatedVelocity c hc (Real.pi/4) (rotatedVelocity c hc 0 (unit (.inl 0)))) (.inr 1) = -c/2 := by
  have he := congrArg (fun x : Space => x (.inr 1))
    (actual_commutator_normalized c hc 0 (Real.pi/4) (unit (.inl 0)))
  change _ = _ at he
  simp [dilate,generator,bracket,orbitCoefficients,unit,
    Real.sin_pi_div_four,Real.cos_pi_div_four] at he
  calc
    _ = -(2*(Real.sqrt 2/2)*(Real.sqrt 2/2))/2*c := he
    _ = -c/2 := by
      ring_nf
      rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring

theorem actual_rotated_noncommuting (c : ℝ) (hc : c ≠ 0) :
    (fun x => rotatedVelocity c hc 0 (rotatedVelocity c hc (Real.pi/4) x)) ≠
      (fun x => rotatedVelocity c hc (Real.pi/4) (rotatedVelocity c hc 0 x)) := by
  intro he
  have h := actual_commutator_witness c hc
  have hx := congrArg (fun f : Space → Space => f (unit (.inl 0))) he
  dsimp only at hx
  rw [hx,sub_self] at h
  change 0 = -c/2 at h
  exact hc (by linarith)

theorem neutral_ideal (a b : Coefficients) (h0 : b 0 = 0) (h1 : b 1 = 0) (h2 : b 2 = 0) :
    bracket a b 0 = 0 ∧ bracket a b 1 = 0 ∧ bracket a b 2 = 0 := by
  simp [bracket,h0,h1,h2]

theorem neutral_commute (a b : Coefficients)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) (ha2 : a 2 = 0)
    (hb0 : b 0 = 0) (hb1 : b 1 = 0) (hb2 : b 2 = 0) : bracket a b = 0 := by
  funext i
  fin_cases i <;> simp [bracket,ha0,ha1,ha2,hb0,hb1,hb2]

theorem rotated_generators_recover :
    orbitCoefficients 0+orbitCoefficients Real.pi = 2 • ![1,0,0,0,0] ∧
    orbitCoefficients 0-orbitCoefficients Real.pi = 2 • ![0,0,0,0,1] ∧
    orbitCoefficients (-(Real.pi/2))-orbitCoefficients (Real.pi/2) = 2 • ![0,0,0,1,0] ∧
    orbitCoefficients (Real.pi/4)+orbitCoefficients (Real.pi/4+Real.pi) = -2 • ![0,1,0,0,0] := by
  refine ⟨?_,?_,?_,?_⟩ <;> funext i <;> fin_cases i <;>
    simp [orbitCoefficients,Real.sin_add,Real.cos_add]
  all_goals nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

theorem diagonal_mix_bracket : bracket ![1,0,0,0,0] ![0,1,0,0,0] = (1/2:ℝ) • ![0,0,1,0,0] := by
  funext i
  fin_cases i <;> dsimp [bracket] <;> norm_num

#print axioms generator_commutator
#print axioms generator_eq_zero_iff
#print axioms generator_add
#print axioms generator_smul
#print axioms actual_shear
#print axioms actual_rotated_normalized
#print axioms actual_commutator_normalized
#print axioms actual_commutator_witness
#print axioms actual_rotated_noncommuting
#print axioms neutral_ideal
#print axioms neutral_commute
#print axioms rotated_generators_recover
#print axioms diagonal_mix_bracket
end
end UnifiedTheory.Audit.KFCausalChargeShearGeneratorAlgebra
