/- Joint L2 limits of the actual slice Fourier profile and its normalized
clock derivative, for the full correlated clustered family. This proves
integrability and norm convergence of the explicit representatives; the
unitary partial Fourier and pure-clock operator graph bridges remain separate. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Data

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Limit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredPhysicalClockLimit (amplitudes)
open KFCausalCorrelatedClusteredJointFourierDecomposition
open KFCausalCorrelatedClusteredJointFourierL2Data
open KFCausalShiftedNarrowWeightedProfiles
open KFCausalShiftedNarrowJointGaussian (narrow spectator)
open KFCausalCorrelatedClusteredPotentialFourierClock

theorem sum_representatives {m : ℕ} (u : Fin m → Hilbert) (F : Fin m → Configuration → ℂ)
    (hF : ∀ i, u i =ᵐ[volume] F i) :
    (∑ i, u i : Hilbert) =ᵐ[volume] fun x => ∑ i, F i x := by
  filter_upwards [KFCausalFiniteLpRepresentatives.sum_coe volume Finset.univ u,
    ae_all_iff.mpr hF] with x hx hf
  rw [hx]
  exact Finset.sum_congr rfl (fun i _ => hf i)

variable {m : ℕ} (f : Family m) (α β ε y z : ℝ) (a p : Fin m → ℝ) (k : ℕ)
local notation "c" => amplitudes ε y a p
local notation "d" => momentAmplitude ε y a p
local notation "U" => inputPart f α ε y z k
local notation "V" => regularPart f α β ε y z p k
local notation "W" => chargedPart f α ε y z k

def inputLimitFunction (x : Configuration) : ℂ :=
  ∑ i, moment α β ε y (f.source i) (fun s => c s i) (U i) (f.degree i) x

def clockLimitFunction (x : Configuration) : ℂ :=
  ∑ i, (moment α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) x+
    limitJet α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) x-
    (2*(a i:ℂ))*moment α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) x)

variable (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3) (hz : |z| ≤ Real.pi*ε/3)

include hα hε hy in
theorem input_limit_identification (x : Configuration) :
    fourierLimit f α β ε y z a p k x.1 (narrow x) (spectator x) =
      inputLimitFunction f α β ε y z a p k x := by
  have hl := tendsto_finset_sum Finset.univ (fun i _ =>
    weighted_tendsto α β ε y (f.source i) (fun s => c s i) (U i) (f.degree i) x)
  have he : ∀ᶠ δ in 𝓝[>] (0:ℝ),
      (∑ i, weighted α β ε y (f.source i) (fun s => c s i) (U i) (f.degree i) δ x) =
        fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (input_decomposition f α β ε y z a p k hα hε hy δ hδ x).symm
  exact tendsto_nhds_unique
    (fourierProfile_tendsto f α β ε y z a p k hα hε hy x.1 (narrow x) (spectator x))
    (hl.congr' he)

include hα hε hy hz in
theorem clock_limit_identification (x : Configuration) :
    clockLimitExpression f α β ε y z a p k x.1 (narrow x) (spectator x) =
      clockLimitFunction f α β ε y z a p k x := by
  have hl := tendsto_finset_sum Finset.univ (fun i _ =>
    ((weighted_tendsto α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) x).add
      (weightedJet_tendsto α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) x)).sub
        ((weighted_tendsto α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) x).const_mul (2*(a i:ℂ))))
  apply tendsto_nhds_unique
    (clockExpression_tendsto f α β ε y z a p k hα hε hy x.1 (narrow x) (spectator x))
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (clock_decomposition f α β ε y z a p k hα hε hy hz δ hδ x).symm

variable (ha : ∀ i, 0 < a i)

def finiteInput (δ : ℝ) : Hilbert := ∑ i, inputVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ
def limitingInput : Hilbert := ∑ i, inputLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i

def finiteClockTerm (i : Fin m) (δ : ℝ) : Hilbert :=
  regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ+
    chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ-
      (2*(a i:ℂ)) • momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ

def limitingClockTerm (i : Fin m) : Hilbert :=
  regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i+
    chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i-
      (2*(a i:ℂ)) • momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i

def finiteClock (δ : ℝ) : Hilbert := ∑ i, finiteClockTerm f α β ε y z a p k hα hβ hw hε hy hz ha i δ
def limitingClock : Hilbert := ∑ i, limitingClockTerm f α β ε y z a p k hα hβ hw hε hy hz ha i

theorem finiteClockTerm_coe (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    finiteClockTerm f α β ε y z a p k hα hβ hw hε hy hz ha i δ =ᵐ[volume] fun x =>
      weighted α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) δ x+
        weightedJet α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) δ x-
          (2*(a i:ℂ))*weighted α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) δ x := by
  filter_upwards [Lp.coeFn_sub
    (regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ+chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ)
    ((2*(a i:ℂ)) • momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ),
    Lp.coeFn_add (regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ) (chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ),
    Lp.coeFn_smul (2*(a i:ℂ)) (momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ),
    regularVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i δ hδ, chargedVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i δ hδ,
    momentVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i δ hδ] with x hs hadd hsm hreg hcharge hmoment
  change ((regularVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ+chargedVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ)-
    (2*(a i:ℂ)) • momentVector f α β ε y z a p k hα hβ hw hε hy hz ha i δ) x = _
  simp only [hs,Pi.sub_apply,hadd,Pi.add_apply,hsm,Pi.smul_apply,smul_eq_mul,hreg,hcharge,hmoment]

theorem limitingClockTerm_coe (i : Fin m) :
    limitingClockTerm f α β ε y z a p k hα hβ hw hε hy hz ha i =ᵐ[volume] fun x =>
      moment α β ε y (f.source i) (fun s => c s i) (V i) (f.degree i) x+
        limitJet α β ε y (f.source i) (fun s => c s i) (W i) (f.degree i) x-
          (2*(a i:ℂ))*moment α β ε y (f.source i) (fun s => d s i) (U i) (f.degree i) x := by
  filter_upwards [Lp.coeFn_sub
    (regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i+chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)
    ((2*(a i:ℂ)) • momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i),
    Lp.coeFn_add (regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i) (chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i),
    Lp.coeFn_smul (2*(a i:ℂ)) (momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i),
    regularLimitVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i, chargedLimitVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i,
    momentLimitVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i] with x hs hadd hsm hreg hcharge hmoment
  change ((regularLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i+chargedLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i)-
    (2*(a i:ℂ)) • momentLimitVector f α β ε y z a p k hα hβ hw hε hy hz ha i) x = _
  simp only [hs,Pi.sub_apply,hadd,Pi.add_apply,hsm,Pi.smul_apply,smul_eq_mul,hreg,hcharge,hmoment]

theorem finiteInput_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ =ᵐ[volume] fun x =>
      fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
  have hs := sum_representatives _ _ (fun i => inputVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i δ hδ)
  exact hs.trans (Eventually.of_forall (fun x =>
    (input_decomposition f α β ε y z a p k hα hε hy δ hδ x).symm))

theorem limitingInput_coe :
    limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha =ᵐ[volume] fun x =>
      fourierLimit f α β ε y z a p k x.1 (narrow x) (spectator x) := by
  have hs := sum_representatives _ _ (fun i => inputLimitVector_coe f α β ε y z a p k hα hβ hw hε hy hz ha i)
  exact hs.trans (Eventually.of_forall (fun x =>
    (input_limit_identification f α β ε y z a p k hα hε hy x).symm))

theorem finiteClock_coe (δ : ℝ) (hδ : 0 < δ) :
    finiteClock f α β ε y z a p k hα hβ hw hε hy hz ha δ =ᵐ[volume] fun x =>
      clockExpression f α β ε y z a p k δ x.1 (narrow x) (spectator x) := by
  have hs := sum_representatives _ _ (fun i => finiteClockTerm_coe f α β ε y z a p k hα hβ hw hε hy hz ha i δ hδ)
  exact hs.trans (Eventually.of_forall (fun x =>
    (clock_decomposition f α β ε y z a p k hα hε hy hz δ hδ x).symm))

theorem limitingClock_coe :
    limitingClock f α β ε y z a p k hα hβ hw hε hy hz ha =ᵐ[volume] fun x =>
      clockLimitExpression f α β ε y z a p k x.1 (narrow x) (spectator x) := by
  have hs := sum_representatives _ _ (fun i => limitingClockTerm_coe f α β ε y z a p k hα hβ hw hε hy hz ha i)
  exact hs.trans (Eventually.of_forall (fun x =>
    (clock_limit_identification f α β ε y z a p k hα hε hy hz x).symm))

theorem finiteInput_tendsto :
    Tendsto (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha) (𝓝[>] 0) (𝓝 (limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha)) :=
  tendsto_finset_sum Finset.univ (fun i _ => inputVector_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha i)

theorem finiteClock_tendsto :
    Tendsto (finiteClock f α β ε y z a p k hα hβ hw hε hy hz ha) (𝓝[>] 0) (𝓝 (limitingClock f α β ε y z a p k hα hβ hw hε hy hz ha)) :=
  tendsto_finset_sum Finset.univ (fun i _ =>
    ((regularVector_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha i).add (chargedVector_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha i)).sub
      (tendsto_const_nhds.smul (momentVector_tendsto f α β ε y z a p k hα hβ hw hε hy hz ha i)))

include hα hβ hw hε hy hz ha

theorem finiteInput_memLp (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun x : Configuration => fourierProfile f α β ε y z a p k δ x.1 (narrow x) (spectator x)) 2 volume :=
  (Lp.memLp (finiteInput f α β ε y z a p k hα hβ hw hε hy hz ha δ)).ae_eq (finiteInput_coe f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ)

theorem finiteClock_memLp (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun x : Configuration => clockExpression f α β ε y z a p k δ x.1 (narrow x) (spectator x)) 2 volume :=
  (Lp.memLp (finiteClock f α β ε y z a p k hα hβ hw hε hy hz ha δ)).ae_eq (finiteClock_coe f α β ε y z a p k hα hβ hw hε hy hz ha δ hδ)

theorem limitingInput_memLp :
    MemLp (fun x : Configuration => fourierLimit f α β ε y z a p k x.1 (narrow x) (spectator x)) 2 volume :=
  (Lp.memLp (limitingInput f α β ε y z a p k hα hβ hw hε hy hz ha)).ae_eq (limitingInput_coe f α β ε y z a p k hα hβ hw hε hy hz ha)

theorem limitingClock_memLp :
    MemLp (fun x : Configuration => clockLimitExpression f α β ε y z a p k x.1 (narrow x) (spectator x)) 2 volume :=
  (Lp.memLp (limitingClock f α β ε y z a p k hα hβ hw hε hy hz ha)).ae_eq (limitingClock_coe f α β ε y z a p k hα hβ hw hε hy hz ha)

#print axioms sum_representatives
#print axioms input_limit_identification
#print axioms clock_limit_identification
#print axioms finiteClockTerm_coe
#print axioms limitingClockTerm_coe
#print axioms finiteInput_coe
#print axioms limitingInput_coe
#print axioms finiteClock_coe
#print axioms limitingClock_coe
#print axioms finiteInput_tendsto
#print axioms finiteClock_tendsto
#print axioms finiteInput_memLp
#print axioms finiteClock_memLp
#print axioms limitingInput_memLp
#print axioms limitingClock_memLp
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredJointFourierL2Limit
