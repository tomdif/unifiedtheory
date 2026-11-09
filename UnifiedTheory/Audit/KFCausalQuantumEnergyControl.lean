/- A capacity-independent energy-growth factor for the actual nonautonomous
finite dynamics. This controls energy from initial energy; it does not
silently identify energy with occupation number or prove a continuum limit. -/
import UnifiedTheory.Audit.KFCausalExponentialClockDynamics
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalQuantumEnergyControl
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {n : Type*} [Fintype n]
local notation "M" => Matrix n n ℂ

def expectation (v : n → ℂ) (A : M) : ℝ := (star v ⬝ᵥ (A*ᵥv)).re

def expectationMap (v : n → ℂ) : M →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := expectation v
      map_add' := by intro A B; simp [expectation,add_mulVec,dotProduct_add]
      map_smul' := by intro r A; simp [expectation,smul_mulVec,dotProduct_smul] }

@[simp] theorem expectationMap_apply (v : n → ℂ) (A : M) : expectationMap v A=expectation v A := rfl

theorem expectation_add (v : n → ℂ) (A B : M) : expectation v (A+B)=expectation v A+expectation v B :=
  (expectationMap v).map_add A B

theorem expectation_smul (v : n → ℂ) (r : ℝ) (A : M) : expectation v (r • A)=r*expectation v A :=
  (expectationMap v).map_smul r A

theorem expectation_nonneg (v : n → ℂ) (A : M) (hA : A.PosSemidef) : 0 ≤ expectation v A :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg v)).1

theorem expectation_conjugate (v : n → ℂ) (A U : M) :
    expectation v (Uᴴ*A*U)=expectation (U*ᵥv) A := by
  simp only [expectation,star_mulVec,dotProduct_mulVec,vecMul_vecMul]

variable [DecidableEq n]

/-- The two Schrödinger terms cancel; only the explicit time derivative
of the Hamiltonian remains. No unequal-time commutation is assumed. -/
theorem transported_hamiltonian_derivative (H U : ℝ → M) (omega t : ℝ) (D : M)
    (hH : (H t).IsHermitian) (hdH : HasDerivAt H D t)
    (hU : HasDerivAt U ((-Complex.I*(omega : ℂ)) • (H t*U t)) t) :
    HasDerivAt (fun s => (U s)ᴴ*H s*U s) ((U t)ᴴ*D*U t) t := by
  have hd := (hU.star.mul hdH).mul hU
  convert hd using 1
  simp only [Pi.mul_apply,star_eq_conjTranspose,conjTranspose_smul,conjTranspose_mul,
    hH.eq,Complex.star_def,map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg,
    add_mul,smul_mul_assoc,mul_smul_comm,mul_assoc]
  module

def hamiltonian (K V : M) (t : ℝ) : M := K+Real.exp (2*t) • V
def energy (K V : M) (U : ℝ → M) (v : n → ℂ) (t : ℝ) : ℝ :=
  expectation v ((U t)ᴴ*hamiltonian K V t*U t)

omit [Fintype n] [DecidableEq n] in
theorem hamiltonian_positive (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef) (t : ℝ) :
    (hamiltonian K V t).PosSemidef := hK.add (hV.smul (Real.exp_pos _).le)

theorem hamiltonian_derivative (K V : M) (t : ℝ) :
    HasDerivAt (hamiltonian K V) ((2*Real.exp (2*t)) • V) t := by
  have hd := ((((hasDerivAt_id t).const_mul 2).exp).smul_const V).const_add K
  convert hd using 1
  simp only [id_eq,mul_one]
  rw [mul_comm]

theorem energy_derivative (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef)
    (U : ℝ → M) (omega : ℝ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (hamiltonian K V t*U t)) t)
    (v : n → ℂ) (t : ℝ) :
    HasDerivAt (energy K V U v)
      (2*Real.exp (2*t)*expectation v ((U t)ᴴ*V*U t)) t := by
  have hd := transported_hamiltonian_derivative (hamiltonian K V) U omega t _
    (hamiltonian_positive K V hK hV t).isHermitian (hamiltonian_derivative K V t) (hU t)
  have he := (expectationMap v).hasFDerivAt.comp_hasDerivAt t hd
  simpa only [Function.comp_def,energy,mul_smul_comm,smul_mul_assoc,
    expectationMap_apply,expectation_smul] using he

theorem energy_decomposition (K V : M) (U : ℝ → M) (v : n → ℂ) (t : ℝ) :
    energy K V U v t=expectation v ((U t)ᴴ*K*U t)+
      Real.exp (2*t)*expectation v ((U t)ᴴ*V*U t) := by
  simp only [energy,hamiltonian,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,
    expectation_add,expectation_smul]

theorem energy_source_bounds (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef)
    (U : ℝ → M) (v : n → ℂ) (t : ℝ) :
    0 ≤ 2*Real.exp (2*t)*expectation v ((U t)ᴴ*V*U t) ∧
    2*Real.exp (2*t)*expectation v ((U t)ᴴ*V*U t) ≤ 2*energy K V U v t := by
  have hk := expectation_nonneg v _ (hK.conjTranspose_mul_mul_same (U t))
  have hv := expectation_nonneg v _ (hV.conjTranspose_mul_mul_same (U t))
  constructor
  · positivity
  · rw [energy_decomposition]; linarith

theorem energy_monotone (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef)
    (U : ℝ → M) (omega : ℝ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (hamiltonian K V t*U t)) t)
    (v : n → ℂ) : Monotone (energy K V U v) := by
  apply monotone_of_deriv_nonneg (fun t => (energy_derivative K V hK hV U omega hU v t).differentiableAt)
  intro t
  rw [(energy_derivative K V hK hV U omega hU v t).deriv]
  exact (energy_source_bounds K V hK hV U v t).1

theorem rescaled_energy_antitone (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef)
    (U : ℝ → M) (omega : ℝ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (hamiltonian K V t*U t)) t)
    (v : n → ℂ) : Antitone (fun t => Real.exp (-2*t)*energy K V U v t) := by
  have hd (t : ℝ) := (((hasDerivAt_id t).const_mul (-2)).exp).mul
    (energy_derivative K V hK hV U omega hU v t)
  apply antitone_of_deriv_nonpos (fun t => (hd t).differentiableAt)
  intro t
  rw [(hd t).deriv]
  dsimp
  have hb := (energy_source_bounds K V hK hV U v t).2
  have he := Real.exp_pos (-2*t)
  nlinarith

/-- The growth factor contains no dimension, capacity, spectral norm or
occupation bound. Initial energy still has to be bounded for a family
of regulators. This estimate alone does not control occupation moments. -/
theorem energy_growth_bound (K V : M) (hK : K.PosSemidef) (hV : V.PosSemidef)
    (U : ℝ → M) (omega : ℝ)
    (hU : ∀ t, HasDerivAt U ((-Complex.I*(omega : ℂ)) • (hamiltonian K V t*U t)) t)
    (v : n → ℂ) (s t : ℝ) (hst : s ≤ t) :
    energy K V U v s ≤ energy K V U v t ∧
      energy K V U v t ≤ Real.exp (2*(t-s))*energy K V U v s := by
  refine ⟨energy_monotone K V hK hV U omega hU v hst,?_⟩
  have hh := mul_le_mul_of_nonneg_left
    (rescaled_energy_antitone K V hK hV U omega hU v hst) (Real.exp_pos (2*t)).le
  have ht : Real.exp (2*t)*Real.exp (-2*t)=1 := by rw [← Real.exp_add]; simp
  rw [← mul_assoc,ht,one_mul,← mul_assoc,← Real.exp_add] at hh
  convert hh using 1
  congr 2
  ring

#print axioms expectation_conjugate
#print axioms transported_hamiltonian_derivative
#print axioms energy_derivative
#print axioms energy_source_bounds
#print axioms energy_monotone
#print axioms rescaled_energy_antitone
#print axioms energy_growth_bound

end
end UnifiedTheory.Audit.KFCausalQuantumEnergyControl
