/- Positive finite excitation for the auxiliary Bose Hamiltonian follows
from the nontrivial original one-particle space and the actual form inverse. -/
import UnifiedTheory.Audit.KFCausalPositiveFormSpectralPoint
import UnifiedTheory.Audit.KFCausalBosonicIntervalResolvent
import UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBosonicFiniteExcitation
noncomputable section
open UnifiedTheory.Clay.YangMills.SpectralGap

section DirectSum
variable {ι : Type*} {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, CompleteSpace (E i)]
open KFCausalHilbertDirectSumHamiltonian
local instance : DecidableEq ι := Classical.decEq _

def coordinate (i : ι) : lp E 2 →L[ℂ] E i :=
  LinearMap.mkContinuous
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num) x i)

def coordinateResolvent (A : ∀ i, E i →ₗ.[ℂ] E i) (lam : ℝ)
    (R : ResolventWitness (operator A) lam) (i : ι) : ResolventWitness (A i) lam where
  inverse := (coordinate i).comp
    (R.inverse.comp (lp.singleContinuousLinearMap ℂ E 2 i))
  right_inverse y := by
    have he := (graph_iff A _ _).mp (R.right_inverse (lp.single 2 i y)) i
    simpa only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
      lp.single_apply_self] using he
  left_inverse x := by
    obtain ⟨u, hu, hv⟩ := (operator A).mem_graph_iff.mp (single_graph A i x)
    dsimp only at hu hv
    have he := R.left_inverse u
    rw [hu, hv, ← lp.single_smul, ← lp.single_sub] at he
    have hc := congrArg (fun z : lp E 2 => z i) he
    simpa only [lp.single_apply_self] using hc

theorem finite_excitation_of_coordinate (A : ∀ i, E i →ₗ.[ℂ] E i) (i : ι)
    (hi : FiniteExcitation (A i)) : FiniteExcitation (operator A) := by
  obtain ⟨lam, hlam, hnot⟩ := hi
  refine ⟨lam, hlam, ?_⟩
  rintro ⟨R⟩
  exact hnot ⟨coordinateResolvent A lam R i⟩
end DirectSum

open KFCausalClosedGraphForm KFCausalTensorSumEnergyFloor KFCausalBosonicFock

variable {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem finite_excitation [Nontrivial H] (D : Data H K) (delta : ℝ)
    (hdelta : 0 < delta) (hD : LowerBound D delta) : FiniteExcitation (fullHamiltonian D) := by
  letI : Nontrivial (sector D 1).State :=
    (KFCausalBosonicSectorOneParticle.identification D).symm.injective.nontrivial
  apply finite_excitation_of_coordinate (sectorHamiltonian D) 1
  exact KFCausalPositiveFormSpectralPoint.finite_excitation (sector D 1).form delta hdelta
    (KFCausalBosonicIntervalResolvent.positive_sector_lower D delta hdelta.le hD 0)

theorem spectral_requirements [Nontrivial H] (D : Data H K) (delta : ℝ)
    (hdelta : 0 < delta) (hD : LowerBound D delta) :
    SpectralRequirements (fullHamiltonian D) (vacuum D) delta :=
  KFCausalBosonicIntervalResolvent.spectral_requirements_of_finite_excitation D delta hdelta hD
    (finite_excitation D delta hdelta hD)

end
end UnifiedTheory.Audit.KFCausalBosonicFiniteExcitation
