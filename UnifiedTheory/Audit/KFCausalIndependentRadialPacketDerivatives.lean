/- Width derivatives of the actual two-width charge profile. The radial
insertions here are linked to that profile; no independent jet data occur. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialPackets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialPacketDerivatives
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalIndependentRadialPacketProfiles (chargeProfile chargeQuadratic chargeQuadratic_coordinates)

def leftRadius (c : ℝ) (x : Joint 2 4) : ℝ := c^2*(x (.inl 0))^2+(x (.inr 1))^2
def rightRadius (c : ℝ) (x : Joint 2 4) : ℝ := c^2*(x (.inl 1))^2+(x (.inr 2))^2

theorem radii_nonnegative (c : ℝ) (x : Joint 2 4) : 0 ≤ leftRadius c x ∧ 0 ≤ rightRadius c x := by
  constructor <;> dsimp [leftRadius,rightRadius] <;> positivity

def momentProfile (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (m n : ℕ) (x : Joint 2 4) : ℂ :=
  (leftRadius c x:ℂ)^m*(rightRadius c x:ℂ)^n*chargeProfile α β wL wR c b P g x

private theorem profile_derivative (α β c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (l r : ℝ → ℝ) (u v : ℝ) (x : Joint 2 4)
    (hd : HasDerivAt (fun t => chargeQuadratic (l t) (r t) c x) v u) :
    HasDerivAt (fun t => chargeProfile α β (l t) (r t) c b P g x)
      (-(α:ℂ)*(v:ℂ)*chargeProfile α β (l u) (r u) c b P g x) u := by
  have he := ((hd.ofReal_comp.const_mul (-(α:ℂ))).cexp.const_mul
    ((Real.pi/α:ℝ)*g (x (.inr 0)))).mul_const (KFCausalNeutralLinePackets.packet β b P (x (.inr 3)))
  convert he using 1
  simp only [chargeProfile]
  ring

theorem left_derivative (α β wL wR c : ℝ) (hw : wL ≠ 0) (b : ℂ)
    (P : Polynomial ℂ) (g : ℝ → ℂ) (m n : ℕ) (x : Joint 2 4) :
    HasDerivAt (fun w => momentProfile α β w wR c b P g m n x)
      ((α/wL^2:ℝ)*momentProfile α β wL wR c b P g (m+1) n x) wL := by
  have hd : HasDerivAt (fun w => chargeQuadratic w wR c x) (-leftRadius c x/wL^2) wL := by
    simp only [chargeQuadratic_coordinates,one_div]
    change HasDerivAt (fun w => w⁻¹*leftRadius c x+wR*rightRadius c x) _ _
    convert (((hasDerivAt_id wL).inv hw).mul_const (leftRadius c x)).add_const
      (wR*rightRadius c x) using 1
    simp
    ring
  have he := (profile_derivative α β c b P g id (fun _ => wR) wL _ x hd).const_mul
    ((leftRadius c x:ℂ)^m*(rightRadius c x:ℂ)^n)
  convert he using 1
  simp only [momentProfile,id_eq,pow_succ]
  push_cast
  ring

theorem right_derivative (α β wL wR c : ℝ) (b : ℂ)
    (P : Polynomial ℂ) (g : ℝ → ℂ) (m n : ℕ) (x : Joint 2 4) :
    HasDerivAt (fun w => momentProfile α β wL w c b P g m n x)
      (-(α:ℂ)*momentProfile α β wL wR c b P g m (n+1) x) wR := by
  have hd : HasDerivAt (fun w => chargeQuadratic wL w c x) (rightRadius c x) wR := by
    simp only [chargeQuadratic_coordinates]
    change HasDerivAt (fun w => (1/wL)*leftRadius c x+w*rightRadius c x) _ _
    convert ((hasDerivAt_id wR).mul_const (rightRadius c x)).const_add ((1/wL)*leftRadius c x) using 1
    simp
  have he := (profile_derivative α β c b P g (fun _ => wL) id wR _ x hd).const_mul
    ((leftRadius c x:ℂ)^m*(rightRadius c x:ℂ)^n)
  convert he using 1
  simp only [momentProfile,id_eq,pow_succ]
  ring

theorem momentProfile_zero (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ) :
    momentProfile α β wL wR c b P g 0 0=chargeProfile α β wL wR c b P g := by
  funext x
  simp only [momentProfile,pow_zero,mul_one,one_mul]

#print axioms radii_nonnegative
#print axioms left_derivative
#print axioms right_derivative
#print axioms momentProfile_zero
end
end UnifiedTheory.Audit.KFCausalIndependentRadialPacketDerivatives
