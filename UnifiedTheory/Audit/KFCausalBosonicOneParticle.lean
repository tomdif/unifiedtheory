/- The complete one-particle space sits isometrically in the occupation Fock
space, using a Hilbert basis whose existence is proved by Mathlib. This does
not assume that the Hamiltonian has an eigenbasis. -/
import UnifiedTheory.Audit.KFCausalBosonicFieldClosure

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalBosonicOneParticle
noncomputable section
open KFCausalBosonicOccupationSpace
open scoped ENNReal
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq _

def mode (i : ι) : ℂ →ₗᵢ[ℂ] Fock ι where
  toLinearMap := (lp.singleContinuousLinearMap ℂ (fun _ : Occupation ι => ℂ)
    2 (Finsupp.single i 1)).toLinearMap
  norm_map' c := lp.norm_single (E := fun _ : Occupation ι => ℂ)
    (by norm_num : (0 : ℝ≥0∞) < 2) _ c

theorem modes_orthogonal : OrthogonalFamily ℂ (fun _ : ι => ℂ) mode := by
  intro i j hij c d
  have hn : (Finsupp.single i 1 : Occupation ι) ≠ Finsupp.single j 1 := by
    intro he
    have ha := congrArg (fun n : Occupation ι => n i) he
    simp [hij] at ha
  change inner ℂ (lp.single 2 (Finsupp.single i 1) c)
    (lp.single 2 (Finsupp.single j 1) d : Fock ι) = 0
  simp [lp.inner_single_left, lp.single_apply, hn]

def modeSum : lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] Fock ι := modes_orthogonal.linearIsometry

theorem modeSum_single (i : ι) (c : ℂ) :
    modeSum (lp.single 2 i c) = lp.single 2 (Finsupp.single i 1) c :=
  modes_orthogonal.linearIsometry_apply_single c

theorem mode_vacuum_orthogonal (i : ι) (c : ℂ) :
    inner ℂ (vacuum (ι := ι)) (mode i c) = 0 := by
  have hn : (Finsupp.single i 1 : Occupation ι) ≠ 0 := by simp
  change inner ℂ (lp.single 2 0 1) (lp.single 2 (Finsupp.single i 1) c : Fock ι) = 0
  simp [lp.inner_single_left, lp.single_apply, hn]

theorem modeSum_vacuum_orthogonal (f : lp (fun _ : ι => ℂ) 2) :
    inner ℂ (vacuum (ι := ι)) (modeSum f) = 0 := by
  have he := (modes_orthogonal.hasSum_linearIsometry f).map
    (innerSL ℂ vacuum) (innerSL ℂ vacuum).continuous
  change HasSum (fun i => inner ℂ vacuum (mode i (f i)))
    (inner ℂ vacuum (modeSum f)) at he
  have hz : HasSum (fun _ : ι => (0 : ℂ)) (inner ℂ vacuum (modeSum f)) := by
    simpa only [mode_vacuum_orthogonal] using he
  exact hz.unique hasSum_zero

variable (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

def basedOneParticle (b : HilbertBasis ι ℂ X) : X →ₗᵢ[ℂ] Fock ι :=
  modeSum.comp b.repr.toLinearIsometry

theorem basedOneParticle_basis (b : HilbertBasis ι ℂ X) (i : ι) :
    basedOneParticle X b (b i) = embed (KFCausalBosonicCCR.field i vacuumCore) := by
  change modeSum (b.repr (b i)) = _
  rw [b.repr_self, modeSum_single, KFCausalBosonicCCR.field_vacuum, embed_single]

/-- A prescribed unit vector can be a mode without being an energy eigenvector. -/
theorem exists_basis_with_vector (z : X) (hz : ‖z‖ = 1) :
    ∃ (w : Set X) (b : HilbertBasis w ℂ X) (i : w), b i = z := by
  have ho : Orthonormal ℂ ((↑) : ({z} : Set X) → X) := by
    constructor
    · intro i
      simpa only [Set.mem_singleton_iff.mp i.property] using hz
    · intro i j hij
      exact False.elim (hij (Subtype.ext
        ((Set.mem_singleton_iff.mp i.property).trans (Set.mem_singleton_iff.mp j.property).symm)))
  obtain ⟨w, b, hw, hb⟩ := ho.exists_hilbertBasis_extension
  let i : w := ⟨z, hw (Set.mem_singleton z)⟩
  exact ⟨w, b, i, congrFun hb i⟩

def modeSet : Set X := Classical.choose (exists_hilbertBasis (𝕜 := ℂ) (E := X))
def modeBasis : HilbertBasis (modeSet X) ℂ X :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis (𝕜 := ℂ) (E := X)))

abbrev BosonicSpace := Fock (modeSet X)

def oneParticle : X →ₗᵢ[ℂ] BosonicSpace X :=
  modeSum.comp (modeBasis X).repr.toLinearIsometry

theorem oneParticle_norm (x : X) : ‖oneParticle X x‖ = ‖x‖ :=
  (oneParticle X).norm_map x

theorem oneParticle_injective : Function.Injective (oneParticle X) :=
  (oneParticle X).injective

theorem oneParticle_vacuum_orthogonal (x : X) :
    inner ℂ (vacuum (ι := modeSet X)) (oneParticle X x) = 0 :=
  modeSum_vacuum_orthogonal ((modeBasis X).repr x)

end
end UnifiedTheory.Audit.KFCausalBosonicOneParticle
