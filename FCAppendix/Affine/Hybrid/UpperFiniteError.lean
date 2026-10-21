import FCAppendix.Existence.UpperEnvelope
import FCAppendix.Existence.SingletonLimits

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open Existence.RankEnvelope

theorem bounded_envelope_error_le {q : ℝ→ℝ} (hq : Monotone q) (hcont : Continuous q)
    (t R H : ℝ) (htH : t ≤ H) (hH : ∀x,H ≤ x→q x=1) :
    error q t R ≤ (H-R)*(1-q t) := by
  have hf : Continuous (fun x=>1-q x):=continuous_const.sub hcont
  have hz : (fun x=>1-q x)=ᵐ[volume.restrict (Ioi H)] (fun _=>0):=by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx
    rw [hH x hx.le,sub_self]
  have hi : IntegrableOn (fun x=>1-q x) (Ioi H):=
    (integrable_zero _ _ (volume.restrict (Ioi H))).congr hz.symm
  have hs : (∫x in Ioi H,1-q x)=0:=by rw [integral_congr_ae hz,integral_zero]
  have he:=intervalIntegral.integral_interval_add_Ioi'
    (hf.intervalIntegrable (μ:=volume) (a:=t) (b:=H)) hi
  rw [hs,add_zero] at he
  have hb:=(integral_bounds hq htH).1
  have heq : (∫x in t..H,1-q x)=(H-t)-(∫x in t..H,q x):=by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hcont.intervalIntegrable (μ:=volume) (a:=t) (b:=H)),intervalIntegral.integral_const]
    simp only [smul_eq_mul,mul_one]
  rw [error,←he,heq]
  nlinarith

theorem bounded_rank_error_le (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1) (hmass : mu.real univ ≤ 1)
    (t R H : ℝ) (htH : t ≤ H) (hsupport : ∀ᵐv ∂mu,v ≤ H) :
    error (rank mu (r+1) c 2) t R ≤ (H-R)*(1-rank mu (r+1) c 2 t) := by
  exact bounded_envelope_error_le (rank_monotone mu hc hcr (by norm_num) hmass)
    (continuous_rank mu _ _ _) t R H htH
    (fun x hx=>rank_eq_one_above_support mu _ _ _ hc hsupport hx)

theorem rank_floor_tendsto_one (mu : Measure ℝ) [IsFiniteMeasure mu]
    (hmass : mu.real univ ≤ 1) (N C : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (hC : ∀k,C k ≤ N k+1) (rho t : ℝ)
    (hc : Tendsto (fun k=>(C k:ℝ)/((N k:ℝ)+1)) atTop (𝓝 rho))
    (hgap : contactTail mu 2 t<rho) :
    Tendsto (fun k=>rank mu (N k) (C k) 2 t) atTop (𝓝 1) := by
  have hp:=contactTail_bounds mu (by norm_num : 2 ≤ (2:ℕ)) hmass t
  have hh:=Bayes.binomBelow_tendsto_one_of_subcritical N C (fun _=>contactTail mu 2 t)
    hN hC (fun _=>hp.1) (fun _=>hp.2.le) tendsto_const_nhds
    (capacity_rival_density N C hN hc) hgap
  apply hh.congr'
  apply Eventually.of_forall
  intro k
  change Bayes.binomBelow (N k) (contactTail mu 2 t) (C k)=rankSuccess (N k) (C k) (contactTail mu 2 t)
  rw [rankSuccess_eq_prob _ _ ⟨hp.1,hp.2.le⟩,Bayes.binomBelow_eq_prob _ _ (hC k) _ hp.1 hp.2.le]

theorem upper_error_tendsto_zero (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hmass : mu.real univ ≤ 1) (N C : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    (hC0 : ∀k,1 ≤ C k) (hC : ∀k,C k ≤ N k) (rho t R H : ℝ)
    (hRt : R ≤ t) (htH : t ≤ H) (hsupport : ∀ᵐv ∂mu,v ≤ H)
    (hc : Tendsto (fun k=>(C k:ℝ)/((N k:ℝ)+1)) atTop (𝓝 rho))
    (hgap : contactTail mu 2 t<rho) :
    Tendsto (fun k=>error (rank mu (N k) (C k) 2) t R) atTop (𝓝 0) := by
  have hq:=rank_floor_tendsto_one mu hmass N C hN (fun k=>(hC k).trans (Nat.le_succ _)) rho t hc hgap
  have hb : Tendsto (fun k=>(H-R)*(1-rank mu (N k) (C k) 2 t)) atTop (𝓝 0):=by
    simpa only [sub_self,mul_zero] using ((tendsto_const_nhds (x:=(1:ℝ))).sub hq).const_mul (H-R)
  apply squeeze_zero' (Eventually.of_forall (fun k=>error_nonneg hRt
    (fun x=>(rank_bounds mu (N k) (C k) (by norm_num) hmass x).2))) ?_ hb
  filter_upwards [hN.eventually_ge_atTop 1] with k hk
  have he : N k-1+1=N k:=by omega
  have hh:=bounded_rank_error_le mu (N k-1) (C k) (hC0 k) (by rw [he];exact hC k)
    hmass t R H htH hsupport
  simpa only [he] using hh

theorem eventually_upper_hidden_guard {E delta : ℕ→ℝ} (hE : Tendsto E atTop (𝓝 0))
    (hdelta : Tendsto delta atTop (𝓝 0)) {η R : ℝ} (hη : 0<η) (hR : 0<R) :
    ∀ᶠk in atTop,E k<η*R*(1-2*delta k) := by
  have hl : Tendsto (fun k=>η*R*(1-2*delta k)-E k) atTop (𝓝 (η*R)):=by
    simpa only [mul_zero,sub_zero,mul_one] using
      (((tendsto_const_nhds (x:=(1:ℝ))).sub (hdelta.const_mul 2)).const_mul (η*R)).sub hE
  filter_upwards [hl.eventually (eventually_gt_nhds (mul_pos hη hR))] with k hk
  linarith

end FCAppendix.Affine.Hybrid
