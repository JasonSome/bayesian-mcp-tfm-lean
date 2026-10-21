import FCAppendix.Affine.Hybrid.Native02.SourceFamily
import FCAppendix.Affine.Hybrid.Native02.NativeSourceIC
import FCAppendix.Affine.Hybrid.Native02.ReferenceMenus

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.Distributional

namespace SourceFamily
variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

theorem price_tendsto : Tendsto S.price atTop (nhds p.lam) :=
  S.price_limit

theorem finite_exposure_mem (k : ℕ) (b : ℝ) (hb : b ∈ Icc p.L p.U) :
    exposure p.xi (S.price k) b ∈ Icc (0:ℝ) 1 :=
  p.finite_reference_exposure_mem (A.joint (S.M k)) b hb

theorem limiting_exposure_mem (_S : SourceFamily p A) (b : ℝ) (hb : b ∈ Icc p.L p.U) :
    exposure p.xi p.lam b ∈ Icc (0:ℝ) 1 :=
  p.source_reference_exposure_mem A b hb

theorem eventually_boxed_menus_at_price (W : ℝ) (hW : 0 ≤ W) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ k : ℕ in atTop, ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.bid ∈ Icc p.L p.U → ∀ v : ℝ, |v| ≤ W →
      (act.routeCount=2 → |(problem (S.game k) i).payoff v act-
        broadcastReference p.eta p.xi p.z v (S.price k) act.bid| < eps) ∧
      (act.routeCount=1 → |(problem (S.game k) i).payoff v act-
        singletonReference p.xi p.z v (S.price k) act.bid| < eps) := by
  have hm := FullContext.eventually_original_game_boxed_menus
    p.s p.a p.h p.rho p.z p.xi p.eta p.d p.L p.U p.R W
    p.s_pos p.a_pos p.h_pos p.mass p.z_nonneg p.z_lt_one p.xi_pos p.xi_lt_one
    p.eta_pos.le p.eta_lt_one.le p.d_nonneg p.L_pos p.L_lt_U.le p.upper_floor hW
    p.low_receipt p.rho_lower p.rho_upper p.qbar_pos p.qbar_lt_one
    p.box_lower p.box_upper p.capacity p.capacity_limit eps heps
  filter_upwards [S.N_tendsto.eventually hm] with k hk
  intro i act hb v hv
  obtain ⟨hfull, hgap, hrow⟩ := S.context_facts k
  have ht := hk (S.lowLaw k) (S.activeLaw k)
    (S.lowLaw_singletons k) (S.lowLaw_supported k) (S.activeLaw_supported k)
    (S.baseGame k) rfl rfl rfl hfull hgap hrow i act hb v hv
  rw [S.game_eq_closed k]
  simpa only [price, PrimitiveInput.h0, PrimitiveInput.qbar, C, M,
    broadcastReference, singletonReference] using ht

theorem eventually_boxed_menus (W : ℝ) (hW : 0 ≤ W) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ k : ℕ in atTop, ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.bid ∈ Icc p.L p.U → ∀ v : ℝ, |v| ≤ W →
      (act.routeCount=2 → |(problem (S.game k) i).payoff v act-
        broadcastReference p.eta p.xi p.z v p.lam act.bid| < eps) ∧
      (act.routeCount=1 → |(problem (S.game k) i).payoff v act-
        singletonReference p.xi p.z v p.lam act.bid| < eps) := by
  let K₂ := broadcastExposureModulus p.eta W p.U/(p.xi*p.L)
  let K₁ := (W+p.U)/(p.xi*p.L)
  let K := K₂+K₁+1
  have hK₂ : 0 ≤ K₂ := div_nonneg
    (broadcastExposureModulus_nonneg hW p.U_pos.le) (mul_pos p.xi_pos p.L_pos).le
  have hK₁ : 0 ≤ K₁ := div_nonneg (add_nonneg hW p.U_pos.le)
    (mul_pos p.xi_pos p.L_pos).le
  have hK : 0 < K := by dsimp only [K]; linarith
  have hsmall : ∀ᶠ k : ℕ in atTop, K*|S.price k-p.lam| < eps/2 := by
    have ht : Tendsto (fun k => K*|S.price k-p.lam|) atTop (nhds 0) := by
      simpa only [sub_self, abs_zero, mul_zero] using
        ((S.price_tendsto.sub_const p.lam).abs).const_mul K
    exact ht.eventually (Iio_mem_nhds (half_pos heps))
  filter_upwards [S.eventually_boxed_menus_at_price W hW (eps/2) (half_pos heps), hsmall]
    with k hk hsmallk
  intro i act hb v hv
  have hB : |broadcastReference p.eta p.xi p.z v (S.price k) act.bid-
      broadcastReference p.eta p.xi p.z v p.lam act.bid| < eps/2 := by
    apply (broadcastReference_price_bound p.xi_pos p.L_pos p.z_nonneg p.z_lt_one.le
      hb hv (S.finite_exposure_mem k act.bid hb) (S.limiting_exposure_mem act.bid hb)).trans_lt
    change K₂*|S.price k-p.lam| < eps/2
    exact (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith : K₂ ≤ K)
      (abs_nonneg _)).trans_lt hsmallk
  have hS : |singletonReference p.xi p.z v (S.price k) act.bid-
      singletonReference p.xi p.z v p.lam act.bid| < eps/2 := by
    apply (singletonReference_price_bound p.xi_pos p.L_pos p.z_nonneg p.z_lt_one.le hb hv).trans_lt
    change K₁*|S.price k-p.lam| < eps/2
    exact (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith : K₁ ≤ K)
      (abs_nonneg _)).trans_lt hsmallk
  constructor
  · intro hk2
    calc
      _ ≤ |(problem (S.game k) i).payoff v act-
          broadcastReference p.eta p.xi p.z v (S.price k) act.bid|+
          |broadcastReference p.eta p.xi p.z v (S.price k) act.bid-
            broadcastReference p.eta p.xi p.z v p.lam act.bid| := abs_sub_le _ _ _
      _ < eps/2+eps/2 := add_lt_add ((hk i act hb v hv).1 hk2) hB
      _ = eps := by ring
  · intro hk1
    calc
      _ ≤ |(problem (S.game k) i).payoff v act-
          singletonReference p.xi p.z v (S.price k) act.bid|+
          |singletonReference p.xi p.z v (S.price k) act.bid-
            singletonReference p.xi p.z v p.lam act.bid| := abs_sub_le _ _ _
      _ < eps/2+eps/2 := add_lt_add ((hk i act hb v hv).2 hk1) hS
      _ = eps := by ring

theorem boxed_incumbent_IC (k : ℕ) :
    ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)),
      ∀ (i : Fin (S.M k)) (act : JointAction 2), act.bid ∈ Icc p.L p.U → act.routeCount=2 →
        (problem (S.game k) i).payoff x.1 act ≤ (problem (S.game k) i).payoff x.1 x.2 := by
  have hIC : ∀ᵐ x ∂(S.PA k : Measure (ℝ × JointAction 2)), ∀ b : ℝ, b ∈ Icc p.L p.U →
      FullContext.physicalSourceUtility (S.N k) (S.C k) p.xi p.z p.L p.U
        p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
        (S.lowLaw k) (S.activeLaw k) x.1 b ≤
      FullContext.physicalSourceUtility (S.N k) (S.C k) p.xi p.z p.L p.U
        p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
        (S.lowLaw k) (S.activeLaw k) x.1 x.2.bid := by
    change ∀ᵐ x ∂((A.joint (S.M k)).1 : Measure (p.Value × p.Bid)).map
      (fun t => (t.1.1, activeBroadcast p.L_pos.le t.2)), _
    apply (measurableEmbedding_activeJointPoint p.L_pos.le).ae_map_iff.mpr
    filter_upwards [A.numeric_IC (S.M k) (S.market_ge k)] with t ht
    intro b hb
    simpa only [S.M_sub_one k, C, lowLaw, activeLaw, activeBroadcast] using
      ht (⟨b,hb⟩ : p.Bid)
  have heta : p.eta = 1-2*p.xi := by dsimp only [PrimitiveInput.xi]; ring
  have hA : (S.baseGame k).A = Schedule.affine 2 (1-2*p.xi) (by linarith [p.xi_half])
      (by linarith [p.xi_pos]) := by
    simpa only [←heta] using
      (show (S.baseGame k).A = Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le from rfl)
  obtain ⟨hfull, hgap, hrow⟩ := S.context_facts k
  exact FullContext.native_source_boxed_IC_ae p.xi_pos p.xi_half.le p.z (S.baseGame k)
    hA rfl rfl p.d_nonneg p.L_pos p.low_receipt p.upper_floor hfull hgap
    p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass (S.lowLaw k) (S.activeLaw k)
    (S.lowLaw_singletons k) (S.activeLaw_singletons k) (S.lowLaw_supported k) (S.activeLaw_supported k)
    hrow (S.PA k) ((S.PA_support k).mono (fun _ hx => hx.2)) hIC

theorem eventually_boxed_count_masses (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ k : ℕ in atTop, ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.bid ∈ Icc p.L p.U → act.routeCount=2 →
      let q := exposure p.xi (S.price k) act.bid
      ∃ (hq0 : 0 ≤ q) (hq1 : q ≤ 1), ∀ r : Fin 3,
        |((problem (S.game k) i).outcome act).mass r-
          (activeLimitLaw p.z q p.z_nonneg p.z_lt_one.le hq0 hq1).mass r| < eps := by
  have hm := FullContext.eventually_original_game_boxed_count_masses
    p.s p.a p.h p.rho p.z p.xi p.eta p.d p.L p.U p.R
    p.s_pos p.a_pos p.h_pos p.mass p.z_nonneg p.z_lt_one p.xi_pos p.xi_lt_one
    p.eta_pos p.eta_lt_one.le p.d_nonneg p.L_pos p.L_lt_U.le p.upper_floor
    p.low_receipt p.rho_lower p.rho_upper p.qbar_pos p.qbar_lt_one
    p.box_lower p.box_upper p.capacity p.capacity_limit eps heps
  filter_upwards [S.N_tendsto.eventually hm] with k hk
  intro i act hb hk2
  obtain ⟨hfull, hgap, hrow⟩ := S.context_facts k
  rw [S.game_eq_closed k]
  simpa only [price, PrimitiveInput.h0, PrimitiveInput.qbar, C, M] using
    hk (S.lowLaw k) (S.activeLaw k)
      (S.lowLaw_singletons k) (S.lowLaw_supported k) (S.activeLaw_supported k)
      (S.baseGame k) rfl rfl rfl hfull hgap hrow i act hb hk2

theorem rawActiveCountLimit :
    ∀ eps > 0, ∀ᶠ k : ℕ in atTop, ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.bid ∈ Icc p.L p.U → act.routeCount=2 → ∀ r : Fin 3,
        |((problem (S.game k) i).outcome act).mass r-
          activeMass p.z (exposure p.xi p.lam act.bid) r| < eps := by
  apply uniform_native_count_limit_of_price S.game p.xi p.L p.U p.z p.lam S.price
    p.xi_pos p.L_pos p.z_nonneg p.z_lt_one.le S.price_limit
    (fun k b hb => S.finite_exposure_mem k b hb)
    (fun b hb => S.limiting_exposure_mem b hb)
  intro eps heps
  filter_upwards [S.eventually_boxed_count_masses eps heps] with k hk
  intro i act hb hroute r
  obtain ⟨hq0, hq1, hmass⟩ := hk i act hb hroute
  simpa only [activeLimitLaw_mass] using hmass r

end SourceFamily
end FCAppendix.Affine.Hybrid.Native02
