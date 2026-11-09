/- Polynomial growth in the transverse variables, uniform in the clock.
Such multipliers preserve L2 for profiles with all radial moments. -/
import UnifiedTheory.Audit.KFCausalGaussianAllRadiusMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalRadialMultipliers
noncomputable section
open MeasureTheory
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalShearRadius (radius radius_positive radius_one_le coordinate_abs_le)

def Controlled (f : Configuration → ℂ) : Prop :=
  Continuous f ∧ ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C*(radius x.2)^n

theorem controlled_const (c : ℂ) : Controlled (fun _ => c) :=
  ⟨continuous_const,0,‖c‖,norm_nonneg c,fun _ => by simp⟩

theorem controlled_clock (b : ℝ → ℂ) (hb : Continuous b) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ s, ‖b s‖ ≤ C) : Controlled (fun x => b x.1) :=
  ⟨hb.comp continuous_fst,0,C,hC,fun x => by simpa using hbound x.1⟩

theorem controlled_coordinate (i : Fin 5) : Controlled (fun x => (x.2 i:ℂ)) := by
  refine ⟨by fun_prop,1,1,by norm_num,?_⟩
  intro x
  simpa only [one_mul,pow_one,Complex.norm_real,Real.norm_eq_abs] using coordinate_abs_le x.2 i

theorem controlled_add (f g : Configuration → ℂ) (hf : Controlled f) (hg : Controlled g) :
    Controlled (fun x => f x+g x) := by
  rcases hf with ⟨hfc,n,C,hC,hf⟩
  rcases hg with ⟨hgc,m,D,hD,hg⟩
  refine ⟨hfc.add hgc,n+m,C+D,add_nonneg hC hD,?_⟩
  intro x
  have hn := pow_le_pow_right₀ (radius_one_le x.2) (Nat.le_add_right n m)
  have hm := pow_le_pow_right₀ (radius_one_le x.2) (Nat.le_add_left m n)
  have h1 := mul_le_mul_of_nonneg_left hn hC
  have h2 := mul_le_mul_of_nonneg_left hm hD
  calc
    ‖f x+g x‖ ≤ ‖f x‖+‖g x‖ := norm_add_le _ _
    _ ≤ (C+D)*radius x.2^(n+m) := by nlinarith [hf x,hg x]

theorem controlled_mul (f g : Configuration → ℂ) (hf : Controlled f) (hg : Controlled g) :
    Controlled (fun x => f x*g x) := by
  rcases hf with ⟨hfc,n,C,hC,hf⟩
  rcases hg with ⟨hgc,m,D,hD,hg⟩
  refine ⟨hfc.mul hgc,n+m,C*D,mul_nonneg hC hD,?_⟩
  intro x
  rw [norm_mul,pow_add]
  have hb := mul_le_mul (hf x) (hg x) (norm_nonneg _)
    (mul_nonneg hC (pow_nonneg (radius_positive x.2).le n))
  nlinarith only [hb]

theorem controlled_neg (f : Configuration → ℂ) (hf : Controlled f) : Controlled (fun x => -f x) := by
  simpa only [neg_one_mul] using controlled_mul _ f (controlled_const (-1)) hf

theorem controlled_sub (f g : Configuration → ℂ) (hf : Controlled f) (hg : Controlled g) :
    Controlled (fun x => f x-g x) := by
  simpa only [sub_eq_add_neg] using controlled_add f _ hf (controlled_neg g hg)

theorem controlled_pow (f : Configuration → ℂ) (hf : Controlled f) (n : ℕ) :
    Controlled (fun x => f x^n) := by
  induction n with
  | zero => simpa using controlled_const 1
  | succ n ih => simpa only [pow_succ] using controlled_mul _ f ih hf

theorem controlled_sum {ι : Type*} (s : Finset ι) (f : ι → Configuration → ℂ)
    (hf : ∀ i ∈ s, Controlled (f i)) : Controlled (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using controlled_const 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact controlled_add _ _ (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem controlled_memLp (f F : Configuration → ℂ) (hf : Controlled f)
    (hF : ∀ n : ℕ, MemLp (fun x => ((radius x.2^n:ℝ):ℂ)*F x) 2 volume) :
    MemLp (fun x => f x*F x) 2 volume := by
  rcases hf with ⟨hc,n,C,hC,hb⟩
  have hm : MemLp F 2 volume := by simpa using hF 0
  apply ((hF n).const_mul (C:ℂ)).of_le (hc.aestronglyMeasurable.mul hm.aestronglyMeasurable)
  filter_upwards [] with x
  have he := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (F x))
  simpa only [Pi.mul_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
    abs_of_nonneg (pow_nonneg (radius_positive x.2).le n),mul_assoc] using he

#print axioms controlled_const
#print axioms controlled_clock
#print axioms controlled_coordinate
#print axioms controlled_add
#print axioms controlled_mul
#print axioms controlled_neg
#print axioms controlled_sub
#print axioms controlled_pow
#print axioms controlled_sum
#print axioms controlled_memLp
end
end UnifiedTheory.Audit.KFCausalRadialMultipliers
