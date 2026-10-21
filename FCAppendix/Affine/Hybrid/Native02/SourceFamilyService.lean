import FCAppendix.Affine.Hybrid.Native02.SourceFamily
import FCAppendix.Affine.Hybrid.Native02.LowService
import FCAppendix.Affine.Hybrid.Native02.OriginalGraph

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.RankEnvelope

namespace SourceFamily
variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

theorem vhi_lt_t : p.vhi< S.t := p.upper_separated S.t S.t_mem
theorem d_lt_vlo (_S : SourceFamily p A) : p.d< p.vlo := (p.d_lt_L.trans p.L_lt_U).trans p.value_surplus
theorem d_lt_t : p.d< S.t := (S.d_lt_vlo.trans_le p.value_order).trans S.vhi_lt_t
theorem active_value_bound (v : ℝ) (hv : v∈ p.activeSupport) : 0< v ∧ |v|≤ S.H := by
  have hb:=p.active_band hv
  have hp:=p.vlo_pos.trans_le hb.1
  refine ⟨hp,?_⟩
  rw [abs_of_pos hp]
  exact (hb.2.trans S.vhi_lt_t.le).trans (S.upperSupport_bounds S.t_mem).2
theorem active_band_value_bound (v : ℝ) (hv : v∈ Icc p.vlo p.vhi) : 0< v ∧ |v|≤ S.H := by
  have hp:=p.vlo_pos.trans_le hv.1
  refine ⟨hp,?_⟩
  rw [abs_of_pos hp]
  exact (hv.2.trans S.vhi_lt_t.le).trans (S.upperSupport_bounds S.t_mem).2
theorem upper_value_bound (v : ℝ) (hv : v∈ p.upperSupport) : 0< v ∧ |v|≤ S.H := by
  have hb:=S.upperSupport_bounds hv
  have hp:=S.t_pos.trans_le hb.1
  exact ⟨hp,by rw [abs_of_pos hp];exact hb.2⟩

def posterior (k : ℕ) : PosteriorSystem (S.game k) :=
  nativeC5Posterior (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
    p.d p.L p.U p.R p.z (S.lowLaw k) (S.P_shape k)

theorem proposer_all_lists_seeds (k : ℕ) : ∀ j X,FeasibleObservedList j X→∀ s,
    Finite.Optimal (S.C k)
      (beliefReceipts (S.game k).A (posteriorCountBelief (S.game k) (S.posterior k) j X) X)
      ((S.game k).policy j X s).val :=
  nativeC5ProposersOptimal (S.M k) (S.C k) (S.P k) p.eta p.eta_pos.le p.eta_lt_one
    p.d p.L p.U p.R p.z p.R_pos (S.lowLaw k) (S.P_shape k)

theorem proposer_on_path (k : ℕ) : ∀ j,ProposerRationalOnPath (S.game k) j :=
  posterior_rationalOnPath (S.game k) (S.posterior k)
    (fun j X hX=> ae_of_all _ (S.proposer_all_lists_seeds k j X hX))

theorem affine_receipt_floor (k r : ℕ) (hr : 0< r) (hr2 : r≤2) :
    p.kappa*(r:ℝ)≤(S.game k).A.charge r := by
  have hA : (S.game k).A=Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le := rfl
  rcases show r=1 ∨ r=2 by omega with h|h
  · subst r
    simpa only [hA,Schedule.affine,successIndicator,Nat.cast_one,mul_one,one_ne_zero,if_false,
      sub_self,mul_zero,add_zero] using p.kappa_le_one
  · subst r
    rw [hA]
    norm_num [Schedule.affine,successIndicator,PrimitiveInput.kappa,PrimitiveInput.xi]
    linarith

theorem low_service_tail (k : ℕ) : ∀ j,
    alphaGt (S.game k) j (p.d/p.kappa)=p.a+p.h/2 := by
  apply original_low_service_tail (S.game k) p.s p.a p.h p.d p.kappa
    p.a_pos.le p.h_pos.le p.d_nonneg p.kappa_pos p.kappa_le_one
    (S.PL k) (S.PA k) (S.PH k) (S.joint_original_components k)
  · exact (S.PL_support k).mono (fun _ hx=> hx.2.1.2)
  · exact S.PA_kappa_support k
  · filter_upwards [S.PH_support k] with x hx
    refine ⟨?_,hx.2⟩
    have hLR : p.L≤ x.2.bid := (p.L_lt_U.trans p.upper_floor).le.trans hx.1
    exact p.low_receipt.trans_le (mul_le_mul_of_nonneg_left hLR p.kappa_pos.le)

theorem exists_low_service_error :
    ∃e : ℕ→ℝ,(∀ k,0≤ e k) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ᶠk in atTop,∀ i : Fin (S.M k),∀ a : JointAction 2,a.bid≤ p.d→
        ((problem (S.game k) i).outcome a).success≤ e k := by
  have hcap : Tendsto (fun k=>(S.C k:ℝ)/((S.N k:ℝ)+1))
      atTop (𝓝 p.rho) := by
    simpa only [M,Nat.cast_add,Nat.cast_one] using S.capacity_limit
  apply eventually_uniform_low_service S.game S.N_tendsto
    (fun k=>(S.valid k).2.2.le) p.kappa p.d (p.a+p.h/2) p.rho
    p.kappa_pos p.rho_upper hcap S.proposerRational S.affine_receipt_floor
  intro k j
  exact (S.low_service_tail k j).ge

theorem eventually_low_payoff_small (W : ℝ) (_hW : 0≤ W) (eps : ℝ) (heps : 0< eps) :
    ∀ᶠk in atTop,∀ i : Fin (S.M k),∀ v∈ Icc (0:ℝ) W,∀ a : JointAction 2,
      a.bid≤ p.d→(problem (S.game k) i).payoff v a< eps := by
  obtain ⟨e,he0,he,hraw⟩:=S.exists_low_service_error
  have hsmall : ∀ᶠk in atTop,W*e k< eps := by
    have ht : Tendsto (fun k => W*e k) atTop (𝓝 0) := by
      simpa only [mul_zero] using he.const_mul W
    exact ht.eventually (Iio_mem_nhds heps)
  filter_upwards [hraw,hsmall] with k hk hs
  intro i v hv a ha
  exact (low_raw_payoff_bound (S.game k) rfl i v W (e k) hv.1 hv.2 (he0 k) a
    (hk i a ha)).trans_lt hs

theorem actual_load_limit : Tendsto (fun k=> finiteLoad (S.game k)) atTop (𝓝 (2*p.rho)) := by
  apply original_population_load_tendsto S.game p.s p.a p.h p.d p.rho
    p.a_pos.le p.h_pos.le p.d_pos p.rho_upper S.PL S.PA S.PH S.joint_original_components
  · intro k
    exact (S.PL_support k).mono (fun _ hx=> hx.2.1.2)
  · intro k
    exact (S.PA_support k).mono (fun _ hx=>⟨p.d_lt_L.trans_le hx.2.1.1,hx.2.2⟩)
  · intro k
    exact (S.PH_support k).mono (fun _ hx=>
      ⟨(p.d_lt_L.trans (p.L_lt_U.trans p.upper_floor)).trans_le hx.1,hx.2⟩)
  · exact S.M_tendsto
  · exact S.capacity_limit
  · exact S.proposer_on_path

theorem original_band_support (k : ℕ) :
    ∀ᵐx ∂(S.game k).F⊗ₘ(S.game k).σ,
      OriginalBandSupport p.d p.vlo p.vhi S.t p.L p.U p.R x := by
  apply original_joint_band_support (S.game k) p.s p.a p.h p.d p.vlo p.vhi S.t p.L p.U p.R
    S.d_lt_vlo p.value_order S.vhi_lt_t (S.PL k) (S.PA k) (S.PH k)
    (S.joint_original_components k)
  · exact (S.PL_support k).mono (fun _ hx=>⟨hx.1.2,hx.2.1.2,hx.2.2⟩)
  · exact S.PA_support k
  · exact (S.PH_spec k).2.2.1.mono (fun _ hx=>⟨hx.1.1,hx.2.2⟩)

theorem original_supported_graph : ∀ eps>0,∀ᶠk in atTop,
    ∀ᵐx ∂(S.game k).F⊗ₘ(S.game k).σ,
      x.1∈ Icc p.vlo p.vhi→|x.2.bid-A.targetReal x.1|< eps := by
  intro eps heps
  filter_upwards [S.M_tendsto.eventually (A.supported_graph eps heps)] with k hk
  apply original_joint_supported_graph p A (S.game k) (A.joint (S.M k))
    (S.PL k) (S.PH k) (S.joint_original_components k)
  · exact (S.PL_support k).mono (fun _ hx=> hx.1.2)
  · exact (S.PH_spec k).2.2.1.mono (fun _ hx=> S.vhi_lt_t.trans_le hx.1.1)
  · exact hk

theorem upper_raw_count_floor (k : ℕ) (i : Fin (S.M k)) (a : JointAction 2)
    (ha : p.R≤ a.bid) (hk : a.routeCount=1) :
    S.upperRank k S.t≤((problem (S.game k) i).outcome a).success :=
  (S.upperPackage k).singleton_count i a hk ha

theorem upperBid_floor (k : ℕ) (v : ℝ) (hv : S.t≤ v) : p.R≤ S.upperBid k v := by
  exact (S.upperBid_bounds k v hv).1

end SourceFamily
end FCAppendix.Affine.Hybrid.Native02
