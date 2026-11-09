/- Arbitrary-Order Thirteen-Factor Multi-Power `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` and
Thirteen-Parameter `(a, b, d, e, c, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)` Yosida Composition
Defect Calculus on `Dom(A^n)` and `Dom(A^{n+1})` Across All Five Clock-Floor Hamiltonians `T`, `P`, `G`,
`S(t)`, and `H(t)`. -/
import UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwelveFactorMultiPowerYosidaComposition

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderThirteenFactorMultiPowerYosidaComposition

noncomputable section

open scoped Topology InnerProduct BigOperators
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorRadialYosidaReference (wide_bound)
open KFCausalPositiveResolventBounds (Resolves)
open KFCausalClockFloorStaticResolventRadialCommutator
  (staticOperator_positive staticResolvent staticResolvent_resolves staticResolvent_left_inverse)
open KFCausalClockFloorHigherPowerOperatorCores
  (operatorPowerDomain operatorPowerDomain_le_of_le
   staticPowerDomain potentialPowerDomain growingPowerDomain
   residualPowerDomain hamiltonianPowerDomain)
open KFCausalClockFloorHigherPowerYosidaGraphConvergence
  (iteratedIdentityPower iteratedIdentityPower_sub
   iteratedIdentityPower_norm_le iteratedIdentityPower_domain_rate_bound)
open KFCausalClockFloorHigherPowerArbitraryOrderGraphConvergence
  (totalOperator totalOperator_of_mem_domain
   iteratedOperatorPower iteratedOperatorPower_succ_apply
   iteratedOperatorPower_mem_domain_of_mem_succ
   iteratedIdentityPower_maps_operatorPowerDomain_to_self
   iteratedOperatorPower_iteratedIdentityPower_comm
   kthPowerGraphNormSq
   kthPowerGraphNormSq_iteratedIdentityPower_contraction)
open KFCausalClockFloorArbitraryOrderTwoParameterYosidaCauchyRate
  (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
   sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ)
open UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderTwelveFactorMultiPowerYosidaComposition
  (iteratedIdentityPower_twelveFactor_comp_mem_comm_and_contraction
   iteratedOperatorPower_iteratedIdentityPower_twelveFactor_defect_rate_on_succ
   kthPowerGraphNormSq_iteratedIdentityPower_twelveFactor_defect_bound_on_succ)

section AbstractThirteenFactorMultiPowerYosida

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Thirteen-factor multi-power `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida smoother
for `R` at spectral parameters `(a, b, d, e, c, f_param, g_param, h_param, i_param, j_param, k_param, l_param, m_param)`. -/
abbrev thirteenFactorMultiPowerYosida
    (R : ℝ → H →L[ℂ] H) (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) (x : H) : H :=
  iteratedIdentityPower (R a) a r
    (iteratedIdentityPower (R b) b s
      (iteratedIdentityPower (R d) d q
        (iteratedIdentityPower (R e) e p
          (iteratedIdentityPower (R c) c l
            (iteratedIdentityPower (R f_param) f_param u
              (iteratedIdentityPower (R g_param) g_param v_pow
                (iteratedIdentityPower (R h_param) h_param w_pow
                  (iteratedIdentityPower (R i_param) i_param z_pow
                    (iteratedIdentityPower (R j_param) j_param y_pow
                      (iteratedIdentityPower (R k_param) k_param x_pow
                        (iteratedIdentityPower (R l_param) l_param d_pow
                          (iteratedIdentityPower (R m_param) m_param c_pow x))))))))))))

/-- `operatorPowerDomain A n` invariance, commutation with `iteratedOperatorPower A n`,
and `kthPowerGraphNormSq A n` contractivity for the thirteen-factor Yosida smoother
`thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x`. -/
theorem iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (hr : ∀ v, 0 < v → Resolves A (R v) v)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ v, 0 < v → ∀ z : A.domain, R v (A z + v • (z : H)) = (z : H))
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A n) :
    thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
      r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x ∈ operatorPowerDomain A n ∧
    iteratedOperatorPower A n
      (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) =
      thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow (iteratedOperatorPower A n x) ∧
    kthPowerGraphNormSq A n
      (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq A n x := by
  unfold thirteenFactorMultiPowerYosida
  have hbdecfghijklm := iteratedIdentityPower_twelveFactor_comp_mem_comm_and_contraction
    A R b d e c f_param g_param h_param i_param j_param k_param l_param m_param hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
    n s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx
  have habdecfghijklm :
      iteratedIdentityPower (R a) a r
        (iteratedIdentityPower (R b) b s
          (iteratedIdentityPower (R d) d q
            (iteratedIdentityPower (R e) e p
              (iteratedIdentityPower (R c) c l
                (iteratedIdentityPower (R f_param) f_param u
                  (iteratedIdentityPower (R g_param) g_param v_pow
                    (iteratedIdentityPower (R h_param) h_param w_pow
                      (iteratedIdentityPower (R i_param) i_param z_pow
                        (iteratedIdentityPower (R j_param) j_param y_pow
                          (iteratedIdentityPower (R k_param) k_param x_pow
                            (iteratedIdentityPower (R l_param) l_param d_pow
                              (iteratedIdentityPower (R m_param) m_param c_pow x)))))))))))) ∈
        operatorPowerDomain A n :=
    iteratedIdentityPower_maps_operatorPowerDomain_to_self A (R a) a (hr a ha) (hl a ha) n r hbdecfghijklm.1
  have hca :=
    iteratedOperatorPower_iteratedIdentityPower_comm A (R a) a (hr a ha) (hl a ha) n r hbdecfghijklm.1
  have hcontr_a := kthPowerGraphNormSq_iteratedIdentityPower_contraction
    A (R a) a ha (hr a ha) hp (hl a ha) n r hbdecfghijklm.1
  exact ⟨habdecfghijklm, by rw [hca, hbdecfghijklm.2.1], hcontr_a.trans hbdecfghijklm.2.2⟩

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida composition
defect rate bound on `operatorPowerDomain A (n + 1)`. -/
theorem iteratedOperatorPower_iteratedIdentityPower_thirteenFactor_defect_rate_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (hr : ∀ v, 0 < v → Resolves A (R v) v)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ v, 0 < v → ∀ z : A.domain, R v (A z + v • (z : H)) = (z : H))
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    ‖iteratedOperatorPower A n
      (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x)‖ ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) *
        ‖iteratedOperatorPower A (n + 1) x‖ := by
  have hxn : x ∈ operatorPowerDomain A n :=
    operatorPowerDomain_le_of_le A (Nat.le_succ n) hx
  have h13 := iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction
    A R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
    n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxn
  have h12_succ := iteratedIdentityPower_twelveFactor_comp_mem_comm_and_contraction
    A R b d e c f_param g_param h_param i_param j_param k_param l_param m_param hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
    (n + 1) s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx
  have h12_n := iteratedIdentityPower_twelveFactor_comp_mem_comm_and_contraction
    A R b d e c f_param g_param h_param i_param j_param k_param l_param m_param hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
    n s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxn
  let z := iteratedIdentityPower (R b) b s
    (iteratedIdentityPower (R d) d q
      (iteratedIdentityPower (R e) e p
        (iteratedIdentityPower (R c) c l
          (iteratedIdentityPower (R f_param) f_param u
            (iteratedIdentityPower (R g_param) g_param v_pow
              (iteratedIdentityPower (R h_param) h_param w_pow
                (iteratedIdentityPower (R i_param) i_param z_pow
                  (iteratedIdentityPower (R j_param) j_param y_pow
                    (iteratedIdentityPower (R k_param) k_param x_pow
                      (iteratedIdentityPower (R l_param) l_param d_pow
                        (iteratedIdentityPower (R m_param) m_param c_pow x)))))))))))
  change ‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - x)‖ ≤ _
  have hsplit :
      iteratedIdentityPower (R a) a r z - x =
        (iteratedIdentityPower (R a) a r z - z) + (z - x) := by abel
  have hsub1 := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n h13.1 h12_n.1).2
  have hadd := (iteratedOperatorPower_add_and_sub_of_mem_operatorPowerDomain
    A n ((operatorPowerDomain A n).sub_mem h13.1 h12_n.1)
      ((operatorPowerDomain A n).sub_mem h12_n.1 hxn)).1
  rw [hsplit, hadd]
  have htri := norm_add_le
    (iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z))
    (iteratedOperatorPower A n (z - x))
  have hbd12 := iteratedOperatorPower_iteratedIdentityPower_twelveFactor_defect_rate_on_succ
    A R b d e c f_param g_param h_param i_param j_param k_param l_param m_param hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
    n s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx
  have hz_dom : iteratedOperatorPower A n z ∈ A.domain :=
    iteratedOperatorPower_mem_domain_of_mem_succ A n h12_succ.1
  have hca_z := iteratedOperatorPower_iteratedIdentityPower_comm
    A (R a) a (hr a ha) (hl a ha) n r h12_n.1
  have hba := iteratedIdentityPower_domain_rate_bound
    A (R a) a ha (hr a ha) hp (hl a ha) r ⟨iteratedOperatorPower A n z, hz_dom⟩
  have hAz :
      ‖A ⟨iteratedOperatorPower A n z, hz_dom⟩‖ ≤ ‖iteratedOperatorPower A (n + 1) x‖ := by
    have hsucc_z :
        A ⟨iteratedOperatorPower A n z, hz_dom⟩ = iteratedOperatorPower A (n + 1) z := by
      rw [iteratedOperatorPower_succ_apply, totalOperator_of_mem_domain A hz_dom]
    rw [hsucc_z, h12_succ.2.1]
    have hcb := iteratedIdentityPower_norm_le A (R b) b hb (hr b hb) hp s
      (iteratedIdentityPower (R d) d q
        (iteratedIdentityPower (R e) e p
          (iteratedIdentityPower (R c) c l
            (iteratedIdentityPower (R f_param) f_param u
              (iteratedIdentityPower (R g_param) g_param v_pow
                (iteratedIdentityPower (R h_param) h_param w_pow
                  (iteratedIdentityPower (R i_param) i_param z_pow
                    (iteratedIdentityPower (R j_param) j_param y_pow
                      (iteratedIdentityPower (R k_param) k_param x_pow
                        (iteratedIdentityPower (R l_param) l_param d_pow
                          (iteratedIdentityPower (R m_param) m_param c_pow
                            (iteratedOperatorPower A (n + 1) x))))))))))))
    have hcd := iteratedIdentityPower_norm_le A (R d) d hd (hr d hd) hp q
      (iteratedIdentityPower (R e) e p
        (iteratedIdentityPower (R c) c l
          (iteratedIdentityPower (R f_param) f_param u
            (iteratedIdentityPower (R g_param) g_param v_pow
              (iteratedIdentityPower (R h_param) h_param w_pow
                (iteratedIdentityPower (R i_param) i_param z_pow
                  (iteratedIdentityPower (R j_param) j_param y_pow
                    (iteratedIdentityPower (R k_param) k_param x_pow
                      (iteratedIdentityPower (R l_param) l_param d_pow
                        (iteratedIdentityPower (R m_param) m_param c_pow
                          (iteratedOperatorPower A (n + 1) x)))))))))))
    have hce := iteratedIdentityPower_norm_le A (R e) e he (hr e he) hp p
      (iteratedIdentityPower (R c) c l
        (iteratedIdentityPower (R f_param) f_param u
          (iteratedIdentityPower (R g_param) g_param v_pow
            (iteratedIdentityPower (R h_param) h_param w_pow
              (iteratedIdentityPower (R i_param) i_param z_pow
                (iteratedIdentityPower (R j_param) j_param y_pow
                  (iteratedIdentityPower (R k_param) k_param x_pow
                    (iteratedIdentityPower (R l_param) l_param d_pow
                      (iteratedIdentityPower (R m_param) m_param c_pow
                        (iteratedOperatorPower A (n + 1) x))))))))))
    have hcc := iteratedIdentityPower_norm_le A (R c) c hc (hr c hc) hp l
      (iteratedIdentityPower (R f_param) f_param u
        (iteratedIdentityPower (R g_param) g_param v_pow
          (iteratedIdentityPower (R h_param) h_param w_pow
            (iteratedIdentityPower (R i_param) i_param z_pow
              (iteratedIdentityPower (R j_param) j_param y_pow
                (iteratedIdentityPower (R k_param) k_param x_pow
                  (iteratedIdentityPower (R l_param) l_param d_pow
                    (iteratedIdentityPower (R m_param) m_param c_pow
                      (iteratedOperatorPower A (n + 1) x)))))))))
    have hcf := iteratedIdentityPower_norm_le A (R f_param) f_param hf_p (hr f_param hf_p) hp u
      (iteratedIdentityPower (R g_param) g_param v_pow
        (iteratedIdentityPower (R h_param) h_param w_pow
          (iteratedIdentityPower (R i_param) i_param z_pow
            (iteratedIdentityPower (R j_param) j_param y_pow
              (iteratedIdentityPower (R k_param) k_param x_pow
                (iteratedIdentityPower (R l_param) l_param d_pow
                  (iteratedIdentityPower (R m_param) m_param c_pow
                    (iteratedOperatorPower A (n + 1) x))))))))
    have hcg := iteratedIdentityPower_norm_le A (R g_param) g_param hg_p (hr g_param hg_p) hp v_pow
      (iteratedIdentityPower (R h_param) h_param w_pow
        (iteratedIdentityPower (R i_param) i_param z_pow
          (iteratedIdentityPower (R j_param) j_param y_pow
            (iteratedIdentityPower (R k_param) k_param x_pow
              (iteratedIdentityPower (R l_param) l_param d_pow
                (iteratedIdentityPower (R m_param) m_param c_pow
                  (iteratedOperatorPower A (n + 1) x)))))))
    have hch := iteratedIdentityPower_norm_le A (R h_param) h_param hh_p (hr h_param hh_p) hp w_pow
      (iteratedIdentityPower (R i_param) i_param z_pow
        (iteratedIdentityPower (R j_param) j_param y_pow
          (iteratedIdentityPower (R k_param) k_param x_pow
            (iteratedIdentityPower (R l_param) l_param d_pow
              (iteratedIdentityPower (R m_param) m_param c_pow
                (iteratedOperatorPower A (n + 1) x))))))
    have hci := iteratedIdentityPower_norm_le A (R i_param) i_param hi_p (hr i_param hi_p) hp z_pow
      (iteratedIdentityPower (R j_param) j_param y_pow
        (iteratedIdentityPower (R k_param) k_param x_pow
          (iteratedIdentityPower (R l_param) l_param d_pow
            (iteratedIdentityPower (R m_param) m_param c_pow
              (iteratedOperatorPower A (n + 1) x)))))
    have hcj := iteratedIdentityPower_norm_le A (R j_param) j_param hj_p (hr j_param hj_p) hp y_pow
      (iteratedIdentityPower (R k_param) k_param x_pow
        (iteratedIdentityPower (R l_param) l_param d_pow
          (iteratedIdentityPower (R m_param) m_param c_pow
            (iteratedOperatorPower A (n + 1) x))))
    have hck := iteratedIdentityPower_norm_le A (R k_param) k_param hk_p (hr k_param hk_p) hp x_pow
      (iteratedIdentityPower (R l_param) l_param d_pow
        (iteratedIdentityPower (R m_param) m_param c_pow
          (iteratedOperatorPower A (n + 1) x)))
    have hcl := iteratedIdentityPower_norm_le A (R l_param) l_param hl_p (hr l_param hl_p) hp d_pow
      (iteratedIdentityPower (R m_param) m_param c_pow
        (iteratedOperatorPower A (n + 1) x))
    have hcm := iteratedIdentityPower_norm_le A (R m_param) m_param hm_p (hr m_param hm_p) hp c_pow
      (iteratedOperatorPower A (n + 1) x)
    exact hcb.trans (hcd.trans (hce.trans (hcc.trans (hcf.trans (hcg.trans (hch.trans (hci.trans (hcj.trans (hck.trans (hcl.trans hcm))))))))))
  have hba' :
      ‖iteratedIdentityPower (R a) a r (iteratedOperatorPower A n z) -
          iteratedOperatorPower A n z‖ ≤
        ((r : ℝ) * a⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ := by
    have hr_nn : 0 ≤ (r : ℝ) * a⁻¹ :=
      mul_nonneg (Nat.cast_nonneg r) (inv_nonneg.mpr (le_of_lt ha))
    exact hba.trans (mul_le_mul_of_nonneg_left hAz hr_nn)
  calc
    ‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z) +
        iteratedOperatorPower A n (z - x)‖
      ≤ ‖iteratedOperatorPower A n (iteratedIdentityPower (R a) a r z - z)‖ +
          ‖iteratedOperatorPower A n (z - x)‖ := htri
    _ = ‖iteratedIdentityPower (R a) a r (iteratedOperatorPower A n z) -
            iteratedOperatorPower A n z‖ +
          ‖iteratedOperatorPower A n (z - x)‖ := by rw [hsub1, hca_z]
    _ ≤ ((r : ℝ) * a⁻¹) * ‖iteratedOperatorPower A (n + 1) x‖ +
          ((s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ + (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ +
            (u : ℝ) * f_param⁻¹ + (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ +
            (z_pow : ℝ) * i_param⁻¹ + (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ +
            (d_pow : ℝ) * l_param⁻¹ + (c_pow : ℝ) * m_param⁻¹) *
            ‖iteratedOperatorPower A (n + 1) x‖ :=
        add_le_add hba' hbd12
    _ = ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
          (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
          (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
          (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
          (c_pow : ℝ) * m_param⁻¹) *
          ‖iteratedOperatorPower A (n + 1) x‖ := by ring

/-- Squared `n`-th order graph-norm thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)`
Yosida composition defect bound on `operatorPowerDomain A (n + 1)`. -/
theorem kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ
    (A : H →ₗ.[ℂ] H) (R : ℝ → H →L[ℂ] H) (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (hr : ∀ v, 0 < v → Resolves A (R v) v)
    (hp : ∀ z : A.domain, 0 ≤ (inner ℂ (A z) (z : H)).re)
    (hl : ∀ v, 0 < v → ∀ z : A.domain, R v (A z + v • (z : H)) = (z : H))
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : H} (hx : x ∈ operatorPowerDomain A (n + 1)) :
    kthPowerGraphNormSq A n
      (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
         r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq A (n + 1) x := by
  let rate := (r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
    (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
    (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
    (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
    (c_pow : ℝ) * m_param⁻¹
  have h1 :
      kthPowerGraphNormSq A n
        (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
          r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      rate ^ 2 *
        (∑ j ∈ Finset.range (n + 1), ‖iteratedOperatorPower A (j + 1) x‖ ^ 2) := by
    unfold kthPowerGraphNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hxj : x ∈ operatorPowerDomain A (j + 1) :=
      operatorPowerDomain_le_of_le A (Nat.succ_le_succ hjn) hx
    have hbd := iteratedOperatorPower_iteratedIdentityPower_thirteenFactor_defect_rate_on_succ
      A R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p hr hp hl
      j r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxj
    have hsq :
        ‖iteratedOperatorPower A j
          (thirteenFactorMultiPowerYosida R a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
            r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x)‖ ^ 2 ≤
        (rate * ‖iteratedOperatorPower A (j + 1) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hbd 2
    linarith [mul_pow rate ‖iteratedOperatorPower A (j + 1) x‖ 2]
  have h2 := mul_le_mul_of_nonneg_left
    (sum_succ_iteratedOperatorPower_sq_le_kthPowerGraphNormSq_succ A n x)
    (sq_nonneg rate)
  exact h1.trans h2

end AbstractThirteenFactorMultiPowerYosida

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
  (hb : |h| ≤ Real.pi * ε / 3) (m g k : ℝ)

local notation "hw" => wide_bound ε hε h hb
local notation "T" => KFCausalClockFloorStaticOperator.operator ε hε h
local notation "PD" => KFCausalClockFloorPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "P" => KFCausalClockFloorPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "SD" => KFCausalClockFloorStaticPotentialHamiltonian.formData ε hε h hh hw m g k
local notation "S" => KFCausalClockFloorStaticPotentialHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hw m g k
local notation "RT" => staticResolvent ε hε h hb hh
local notation "RP" => KFCausalClockFloorPotentialClockResolvent.resolvent ε hε h hh hw m g k
local notation "RG" => KFCausalClockFloorGrowingYosida.resolvent ε hε h hh hw m g k
local notation "RS" => KFCausalClockFloorResidualClockCore.resolvent ε hε h hh hw m g k
local notation "RH" => KFCausalClockFloorHamiltonianClockCore.resolvent ε hε h hh hw m g k

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida contraction
and defect bound on `staticPowerDomain ε hε h (n + 1)` for `T`. -/
theorem static_arbitraryOrder_thirteenFactor_yosida_package
    (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : Hilbert}
    (hx : x ∈ staticPowerDomain ε hε h (n + 1)) :
    kthPowerGraphNormSq T (n + 1)
      (thirteenFactorMultiPowerYosida RT a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq T (n + 1) x ∧
    kthPowerGraphNormSq T n
      (thirteenFactorMultiPowerYosida RT a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq T (n + 1) x :=
  ⟨(iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction T RT a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) (n + 1) r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ T RT a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (staticResolvent_resolves ε hε h hb hh)
     (staticOperator_positive ε hε h)
     (staticResolvent_left_inverse ε hε h hb hh) n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx⟩

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida contraction
and defect bound on `potentialPowerDomain ε hε h hh hb m g k (n + 1)` for `P`. -/
theorem potential_arbitraryOrder_thirteenFactor_yosida_package
    (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : Hilbert}
    (hx : x ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq P (n + 1)
      (thirteenFactorMultiPowerYosida RP a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq P (n + 1) x ∧
    kthPowerGraphNormSq P n
      (thirteenFactorMultiPowerYosida RP a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq P (n + 1) x :=
  ⟨(iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction P RP a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k)
     (n + 1) r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ P RP a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorPotentialClockResolvent.resolves ε hε h hh hw m g k)
     (KFCausalClosedGraphForm.hamiltonian_positive PD)
     (KFCausalClockFloorPotentialClockApproximation.left_inverse ε hε h hh hw m g k) n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx⟩

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida contraction
and defect bound on `growingPowerDomain ε hε h hh hb m g k (n + 1)` for `G`. -/
theorem growing_arbitraryOrder_thirteenFactor_yosida_package
    (a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : Hilbert}
    (hx : x ∈ growingPowerDomain ε hε h hh hb m g k (n + 1)) :
    kthPowerGraphNormSq G (n + 1)
      (thirteenFactorMultiPowerYosida RG a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq G (n + 1) x ∧
    kthPowerGraphNormSq G n
      (thirteenFactorMultiPowerYosida RG a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq G (n + 1) x :=
  ⟨(iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction G RG a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k)
     (n + 1) r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ G RG a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorGrowingYosida.resolves ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingHamiltonian.hamiltonian_positive ε hε h hh hw m g k)
     (KFCausalClockFloorGrowingYosida.left_inverse ε hε h hh hw m g k) n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx⟩

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida contraction
and defect bound on `residualPowerDomain ε hε h hh hb m g k t (n + 1)` for `S t`. -/
theorem residual_arbitraryOrder_thirteenFactor_yosida_package
    (t a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : Hilbert}
    (hx : x ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (S t) (n + 1)
      (thirteenFactorMultiPowerYosida (RS t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq (S t) (n + 1) x ∧
    kthPowerGraphNormSq (S t) n
      (thirteenFactorMultiPowerYosida (RS t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq (S t) (n + 1) x :=
  ⟨(iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction (S t) (RS t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ (S t) (RS t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorResidualClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClosedGraphForm.hamiltonian_positive (SD t))
     (KFCausalClockFloorResidualClockCore.left_inverse ε hε h hh hw m g k t) n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx⟩

/-- Thirteen-factor multi-order `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)` Yosida contraction
and defect bound on `hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)` for `H t`. -/
theorem hamiltonian_arbitraryOrder_thirteenFactor_yosida_package
    (t a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {x : Hilbert}
    (hx : x ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    kthPowerGraphNormSq (H t) (n + 1)
      (thirteenFactorMultiPowerYosida (RH t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x) ≤
      kthPowerGraphNormSq (H t) (n + 1) x ∧
    kthPowerGraphNormSq (H t) n
      (thirteenFactorMultiPowerYosida (RH t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow x - x) ≤
      ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
        (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
        (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
        (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
        (c_pow : ℝ) * m_param⁻¹) ^ 2 *
        kthPowerGraphNormSq (H t) (n + 1) x :=
  ⟨(iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction (H t) (RH t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t)
     (n + 1) r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx).2.2,
   kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ (H t) (RH t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
     ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p
     (KFCausalClockFloorHamiltonianClockCore.resolves ε hε h hh hw m g k t)
     (KFCausalClockFloorAveragedHamiltonian.hamiltonian_positive ε hε h hh hw m g k t)
     (KFCausalClockFloorHamiltonianClockCore.left_inverse ε hε h hh hw m g k t) n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hx⟩

/-- Master Five-Operator Arbitrary-Order Thirteen-Factor Multi-Power `(r, s, q, p, l, u, v_pow, w_pow, z_pow, y_pow, x_pow, d_pow, c_pow)`
Yosida Composition Defect Synthesis across `T`, `P`, `G`, `S(t)`, and `H(t)`. -/
theorem arbitraryOrder_thirteenFactor_multiPower_yosida_master_synthesis
    (t a b d e c f_param g_param h_param i_param j_param k_param l_param m_param : ℝ)
    (ha : 0 < a) (hb_pos : 0 < b) (hd : 0 < d) (he : 0 < e) (hc : 0 < c)
    (hf_p : 0 < f_param) (hg_p : 0 < g_param) (hh_p : 0 < h_param)
    (hi_p : 0 < i_param) (hj_p : 0 < j_param) (hk_p : 0 < k_param) (hl_p : 0 < l_param) (hm_p : 0 < m_param)
    (n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow : ℕ) {xT xP xG xS xH : Hilbert}
    (hxT : xT ∈ staticPowerDomain ε hε h (n + 1))
    (hxP : xP ∈ potentialPowerDomain ε hε h hh hb m g k (n + 1))
    (hxG : xG ∈ growingPowerDomain ε hε h hh hb m g k (n + 1))
    (hxS : xS ∈ residualPowerDomain ε hε h hh hb m g k t (n + 1))
    (hxH : xH ∈ hamiltonianPowerDomain ε hε h hh hb m g k t (n + 1)) :
    let rateSq := ((r : ℝ) * a⁻¹ + (s : ℝ) * b⁻¹ + (q : ℝ) * d⁻¹ +
      (p : ℝ) * e⁻¹ + (l : ℝ) * c⁻¹ + (u : ℝ) * f_param⁻¹ +
      (v_pow : ℝ) * g_param⁻¹ + (w_pow : ℝ) * h_param⁻¹ + (z_pow : ℝ) * i_param⁻¹ +
      (y_pow : ℝ) * j_param⁻¹ + (x_pow : ℝ) * k_param⁻¹ + (d_pow : ℝ) * l_param⁻¹ +
      (c_pow : ℝ) * m_param⁻¹) ^ 2
    kthPowerGraphNormSq T n
      (thirteenFactorMultiPowerYosida RT a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow xT - xT) ≤
      rateSq * kthPowerGraphNormSq T (n + 1) xT ∧
    kthPowerGraphNormSq P n
      (thirteenFactorMultiPowerYosida RP a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow xP - xP) ≤
      rateSq * kthPowerGraphNormSq P (n + 1) xP ∧
    kthPowerGraphNormSq G n
      (thirteenFactorMultiPowerYosida RG a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow xG - xG) ≤
      rateSq * kthPowerGraphNormSq G (n + 1) xG ∧
    kthPowerGraphNormSq (S t) n
      (thirteenFactorMultiPowerYosida (RS t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow xS - xS) ≤
      rateSq * kthPowerGraphNormSq (S t) (n + 1) xS ∧
    kthPowerGraphNormSq (H t) n
      (thirteenFactorMultiPowerYosida (RH t) a b d e c f_param g_param h_param i_param j_param k_param l_param m_param
        r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow xH - xH) ≤
      rateSq * kthPowerGraphNormSq (H t) (n + 1) xH :=
  ⟨(static_arbitraryOrder_thirteenFactor_yosida_package ε hε h hh hb a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxT).2,
   (potential_arbitraryOrder_thirteenFactor_yosida_package ε hε h hh hb m g k a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxP).2,
   (growing_arbitraryOrder_thirteenFactor_yosida_package ε hε h hh hb m g k a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxG).2,
   (residual_arbitraryOrder_thirteenFactor_yosida_package ε hε h hh hb m g k t a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxS).2,
   (hamiltonian_arbitraryOrder_thirteenFactor_yosida_package ε hε h hh hb m g k t a b d e c f_param g_param h_param i_param j_param k_param l_param m_param ha hb_pos hd he hc hf_p hg_p hh_p hi_p hj_p hk_p hl_p hm_p n r s q p l u v_pow w_pow z_pow y_pow x_pow d_pow c_pow hxH).2⟩

#print axioms iteratedIdentityPower_thirteenFactor_comp_mem_comm_and_contraction
#print axioms iteratedOperatorPower_iteratedIdentityPower_thirteenFactor_defect_rate_on_succ
#print axioms kthPowerGraphNormSq_iteratedIdentityPower_thirteenFactor_defect_bound_on_succ
#print axioms static_arbitraryOrder_thirteenFactor_yosida_package
#print axioms potential_arbitraryOrder_thirteenFactor_yosida_package
#print axioms growing_arbitraryOrder_thirteenFactor_yosida_package
#print axioms residual_arbitraryOrder_thirteenFactor_yosida_package
#print axioms hamiltonian_arbitraryOrder_thirteenFactor_yosida_package
#print axioms arbitraryOrder_thirteenFactor_multiPower_yosida_master_synthesis

end

end UnifiedTheory.Audit.KFCausalClockFloorArbitraryOrderThirteenFactorMultiPowerYosidaComposition
