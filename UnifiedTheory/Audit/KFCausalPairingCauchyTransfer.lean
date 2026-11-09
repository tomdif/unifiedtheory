/- Vanishing physical norm errors preserve the Cauchy property of scalar
weak pairings. -/
import UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalPairingCauchyTransfer
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem pairing_cauchy_of_norm_error {u v : ℕ → H}
    (he : Tendsto (fun n => ‖u n-v n‖) atTop (𝓝 0)) (y : H)
    (hc : CauchySeq (fun n => inner ℂ (u n) y)) :
    CauchySeq (fun n => inner ℂ (v n) y) := by
  obtain ⟨l,hl⟩ := cauchySeq_tendsto_of_complete hc
  have hd : Tendsto (fun n => u n-v n) atTop (𝓝 (0:H)) := tendsto_zero_iff_norm_tendsto_zero.mpr he
  have hi := hl.sub (hd.inner (𝕜 := ℂ) (tendsto_const_nhds (x := y)))
  simpa only [inner_sub_left,sub_sub_cancel] using hi.cauchySeq

#print axioms pairing_cauchy_of_norm_error

end UnifiedTheory.Audit.KFCausalPairingCauchyTransfer
