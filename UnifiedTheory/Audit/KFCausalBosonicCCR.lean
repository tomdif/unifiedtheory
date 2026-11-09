/- Canonical commutation and adjoint relations on the dense occupation core.
The identities concern the actual normalized ladder maps on the constructed
Hilbert space. They do not assume a representation of the CCR. -/
import UnifiedTheory.Audit.KFCausalBosonicOccupationSpace

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalBosonicCCR
noncomputable section
open KFCausalBosonicOccupationSpace
variable {ι : Type*}
local instance : DecidableEq ι := Classical.decEq _

theorem basis_inner (n m : Occupation ι) (c d : ℂ) :
    inner ℂ (embed (Finsupp.single n c)) (embed (Finsupp.single m d)) =
      if n = m then starRingEnd ℂ c * d else 0 := by
  classical
  by_cases h : n = m
  · subst m
    simp [lp.inner_single_left, RCLike.inner_apply, mul_comm]
  · simp [lp.inner_single_left, lp.single_apply, h, Ne.symm h]

theorem lower_raise_other (i j : ι) (hij : i ≠ j) (n : Occupation ι) :
    lower j (raise i n) = raise i (lower j n) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [lower, raise, hij]
  · by_cases hkj : k = j
    · subst k
      simp [lower, raise, Ne.symm hij]
    · simp [lower, raise, hki, hkj]

theorem different_mode_ccr (i j : ι) (hij : i ≠ j) (u : Core ι) :
    annihilation j (creation i u) = creation i (annihilation j u) := by
  have hm : (annihilation j).comp (creation i) = (creation i).comp (annihilation j) := by
    apply Finsupp.lhom_ext
    intro n c
    simp only [LinearMap.comp_apply, creation_single, annihilation_single,
      lower_raise_other i j hij]
    have hr : raise i n j = n j := by simp [raise, Ne.symm hij]
    have hl : lower j n i = n i := by simp [lower, hij]
    rw [hr, hl]
    congr 1
    ring
  exact congrArg (fun T : Core ι →ₗ[ℂ] Core ι => T u) hm

theorem canonical_commutation (i j : ι) (u : Core ι) :
    annihilation j (creation i u) - creation i (annihilation j u) =
      if i = j then u else 0 := by
  by_cases hij : i = j
  · subst j
    simp [same_mode_ccr]
  · rw [different_mode_ccr i j hij, sub_self, if_neg hij]

private theorem creation_annihilation_basis (i : ι) (n m : Occupation ι) (c d : ℂ) :
    inner ℂ (embed (creation i (Finsupp.single n c))) (embed (Finsupp.single m d)) =
      inner ℂ (embed (Finsupp.single n c)) (embed (annihilation i (Finsupp.single m d))) := by
  rw [creation_single, annihilation_single, basis_inner, basis_inner]
  by_cases hm : m i = 0
  · have hne : raise i n ≠ m := by
      intro he
      have hx := congrArg (fun v : Occupation ι => v i) he
      simp [raise, hm] at hx
    simp [hm, hne]
  · have he : raise i n = m ↔ n = lower i m := by
      constructor
      · intro h
        rw [← h, lower_raise]
      · intro h
        rw [h, raise_lower i m hm]
    by_cases hn : n = lower i m
    · have hx : n i + 1 = m i := by
        rw [hn]
        simp [lower]
        omega
      rw [if_pos (he.mpr hn), if_pos hn, hx]
      simp [amplitude, map_mul]
      ring
    · have hnr : raise i n ≠ m := fun hh => hn (he.mp hh)
      simp [hnr, hn]

theorem creation_annihilation_adjoint (i : ι) (u v : Core ι) :
    inner ℂ (embed (creation i u)) (embed v) =
      inner ℂ (embed u) (embed (annihilation i v)) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, inner_add_left, hu, hw]
  | single n c =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v w hv hw => simp only [map_add, inner_add_right, hv, hw]
      | single m d => exact creation_annihilation_basis i n m c d

def field (i : ι) : Core ι →ₗ[ℂ] Core ι := creation i + annihilation i

theorem field_symmetric (i : ι) (u v : Core ι) :
    inner ℂ (embed (field i u)) (embed v) = inner ℂ (embed u) (embed (field i v)) := by
  have hc := creation_annihilation_adjoint i u v
  have ha := congrArg (starRingEnd ℂ) (creation_annihilation_adjoint i v u)
  simp only [inner_conj_symm] at ha
  simp only [field, LinearMap.add_apply, map_add, inner_add_left, inner_add_right]
  rw [hc, ← ha]
  ac_rfl

theorem field_vacuum (i : ι) :
    field i vacuumCore = Finsupp.single (Finsupp.single i 1) 1 := by
  simp [field]

theorem field_vacuum_nonzero (i : ι) : embed (field i vacuumCore) ≠ 0 := by
  rw [field_vacuum]
  intro hz
  have he : Finsupp.single (Finsupp.single i 1) (1 : ℂ) = 0 :=
    embed_injective (by simpa only [map_zero] using hz)
  simpa using he

end
end UnifiedTheory.Audit.KFCausalBosonicCCR
