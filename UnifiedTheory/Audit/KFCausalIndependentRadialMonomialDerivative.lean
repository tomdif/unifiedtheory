/- Exact derivative closure of the actual charged-coordinate monomial
profiles. The neutral derivative is the original packet step polynomial. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialCoordinateMoments
import UnifiedTheory.Audit.KFCausalIndependentRadialKineticProfiles
import UnifiedTheory.Audit.KFCausalFiniteMonomialDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMonomialDerivative
noncomputable section
open KFCausalEuclideanProductCoordinates (Joint)
open KFCausalIndependentRadialCoordinateMoments (coordinate monomial profile)
open KFCausalIndependentRadialKineticProfiles (position coefficient neutral firstProfile profile_first_derivative)
open KFCausalSymmetricMomentumCoordinates (symmetricVector symmetricBlock rightVector)
open KFCausalPairedModeCoordinates (scale)
open KFCausalFiniteMonomialDerivative (lower raise)
open KFCausalNeutralLinePackets (step)

def positionIndex (i : Fin 2) : Fin 4 := ![2,3] i

theorem coordinate_translate (c : ℝ) (i : Fin 2) (x : Joint 2 4) (t : ℝ) :
    (fun j => (coordinate c (x+t • symmetricVector i) j:ℂ))=
      Function.update (fun j => (coordinate c x j:ℂ)) (positionIndex i)
        ((coordinate c x (positionIndex i):ℂ)+2*(scale:ℂ)*(t:ℂ)) := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [coordinate,positionIndex,symmetricVector,symmetricBlock,rightVector] <;> ring

theorem monomial_derivative (c : ℝ) (n : Fin 4 → ℕ) (i : Fin 2) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => monomial c n (x+t • symmetricVector i))
      (2*(scale:ℂ)*(n (positionIndex i):ℂ)*monomial c (lower n (positionIndex i)) x) 0 := by
  change HasDerivAt (fun t : ℝ => KFCausalFiniteMonomialDerivative.monomial n
      (fun j => (coordinate c (x+t • symmetricVector i) j:ℂ))) _ _
  simp only [coordinate_translate]
  exact KFCausalFiniteMonomialDerivative.affine_derivative n
    (fun j => (coordinate c x j:ℂ)) (positionIndex i) (2*(scale:ℂ))

theorem profile_raise (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (n : Fin 4 → ℕ) (j : Fin 4) (x : Joint 2 4) :
    profile α β wL wR c b P g (raise n j) x=(coordinate c x j:ℂ)*profile α β wL wR c b P g n x := by
  have he := KFCausalFiniteMonomialDerivative.raising n (fun j => (coordinate c x j:ℂ)) j
  change monomial c (raise n j) x=(coordinate c x j:ℂ)*monomial c n x at he
  simp only [profile,he,mul_assoc]

theorem profile_derivative (α β wL wR c : ℝ) (b : ℂ) (P : Polynomial ℂ) (g : ℝ → ℂ)
    (n : Fin 4 → ℕ) (i : Fin 2) (x : Joint 2 4) :
    HasDerivAt (fun t : ℝ => profile α β wL wR c b P g n (x+t • symmetricVector i))
      ((2*(scale:ℂ)*(n (positionIndex i):ℂ))*profile α β wL wR c b P g (lower n (positionIndex i)) x+
        coefficient α wL wR i*profile α β wL wR c b P g (raise n (positionIndex i)) x+
        (neutral i:ℂ)*profile α β wL wR c b (step β b P) g n x) 0 := by
  have hp : coordinate c x (positionIndex i)=position i x := by fin_cases i <;> rfl
  have he := (monomial_derivative c n i x).mul (profile_first_derivative α β wL wR c b P g i x)
  convert he using 1
  rw [profile_raise,hp]
  simp only [profile,firstProfile,zero_smul,add_zero]
  ring

#print axioms coordinate_translate
#print axioms monomial_derivative
#print axioms profile_raise
#print axioms profile_derivative
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMonomialDerivative
