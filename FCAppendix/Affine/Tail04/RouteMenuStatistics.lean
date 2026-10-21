import FCAppendix.Affine.Tail04.RawRouteCounts
import FCAppendix.Affine.Tail04.CanonicalFailure
import FCAppendix.Affine.Tail04.GlobalLowerRoutes

noncomputable section
namespace FCAppendix.Affine.Tail04.RouteMenuStatistics
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open MenuError UnusedFocalCountError SourceMenuIdentity GlobalLower
open scoped BigOperators

def statistic (η v b : ℝ) (k : Fin 3) (r : Fin 3) : ℝ :=
  if k=0 then 0 else if k=1 then (v-b)*(r.val:ℝ)/2 else affineStatistic η v b r

lemma singleton_expect (K : CountLaw 2) (η v b : ℝ) :
    K.expect (statistic η v b 1)=(v-b)*K.load/2 := by
  change K.expect (fun r : Fin 3 => (v-b)*(r.val:ℝ)/2) = (v-b)*K.load/2
  rw [show (fun r : Fin 3=>(v-b)*(r.val:ℝ)/2)=
    (fun r : Fin 3=>(v-b)*((r.val:ℝ)/2)) by funext r;ring,
    FiniteLaw.expect_const_mul,show (fun r : Fin 3=>(r.val:ℝ)/2)=
      (fun r : Fin 3=>(r.val:ℝ)*(1/2)) by funext r;ring,FiniteLaw.expect_mul_const]
  dsimp only [CountLaw.load]
  ring

theorem native_payoff {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
    (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)
    (i : Fin m) (v b : ℝ) (hb : 0≤ b) (k : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb k)=
      ((problem Γ i).outcome (RawRoutes.action b hb 2)).expect (statistic η v b k) := by
  have hp:=RawRoutes.all_route_payoffs Γ i b hb η hη0 hη1 hA hg v
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) k
  · change (problem Γ i).payoff v (RawRoutes.action b hb 0)=
      ((problem Γ i).outcome (RawRoutes.action b hb 2)).expect (fun _=>0)
    rw [hp.1,FiniteLaw.expect_const]
  · change (problem Γ i).payoff v (RawRoutes.action b hb 1)=
      ((problem Γ i).outcome (RawRoutes.action b hb 2)).expect (statistic η v b 1)
    rw [hp.2.1,singleton_expect]
    have hL:=load_eq_mean Γ (by norm_num : 0<2) i (RawRoutes.action b hb 2)
    change _=2*meanAcceptProb Γ i b at hL
    rw [hL]
    ring
  · change (problem Γ i).payoff v (RawRoutes.action b hb 2)=
      ((problem Γ i).outcome (RawRoutes.action b hb 2)).expect (affineStatistic η v b)
    rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg,affineStatistic_expect]
    dsimp only [RawRoutes.action]
    ring

lemma oscillation_bound {η v b B : ℝ} (hη0 : 0≤ η) (hη1 : η≤1)
    (hv : 0≤ v) (hb : b∈Icc (0:ℝ) B) (k : Fin 3) :
    MenuError.oscillation (statistic η v b k)≤ v+2*B := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))) k
  · change MenuError.oscillation (fun _ : Fin 3=>(0:ℝ))≤_
    simp only [MenuError.oscillation,sub_self,abs_zero,max_self]
    linarith [hb.1,hb.2]
  · change MenuError.oscillation (statistic η v b 1)≤_
    have ha : |v-b|≤ v+b := (abs_sub v b).trans (by rw [abs_of_nonneg hv,abs_of_nonneg hb.1])
    have hstep0 : statistic η v b 1 1-statistic η v b 1 0=(v-b)/2 := by
      norm_num [statistic]
    have hstep1 : statistic η v b 1 2-statistic η v b 1 1=(v-b)/2 := by
      norm_num [statistic]
      ring
    rw [MenuError.oscillation,hstep0,hstep1,max_self,abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith [hb.1,hb.2]
  · change MenuError.oscillation (affineStatistic η v b)≤_
    exact (oscillation_affineStatistic hη0 hη1 hv hb.1).trans (by linarith [hb.1,hb.2])

lemma canonical_singleton (ξ lam v b : ℝ) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 1)=
      (v-b)*canonicalProbability ξ lam b := by
  rw [canonicalCount_expect]
  norm_num [coinMoment,statistic]
  ring

lemma canonical_broadcast (ξ lam v b : ℝ) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 2)=
      Hybrid.independentTwo (1-2*ξ) v b (canonicalProbability ξ lam b) := by
  change (canonicalCount ξ lam b).expect (affineStatistic (1-2*ξ) v b)=_
  rw [canonicalCount_expect]
  let q:=canonicalProbability ξ lam b
  change (1-q)*(1-q)*0+(q*(1-q)+(1-q)*q)*(v-b)+
    q*q*(v-(1+(1-2*ξ))*b)=Hybrid.independentTwo (1-2*ξ) v b q
  unfold Hybrid.independentTwo
  ring

lemma canonical_exposure {ξ B lam b : ℝ} (hξ : 0< ξ) (hξ1 : ξ<1)
    (hB : 0< B) (hb : b∈Icc (0:ℝ) B) (hlam : (1-ξ)*B≤ lam) (hlamb : lam< b) :
    canonicalProbability ξ lam b=(1-lam/b)/ξ ∧
      b=lam/(1-ξ*canonicalProbability ξ lam b) := by
  have hk : 0<1-ξ := by linarith
  have hlam0 : 0< lam := (mul_pos hk hB).trans_le hlam
  have hb0 : 0< b := hlam0.trans hlamb
  have hq0 : 0≤(1-lam/b)/ξ := div_nonneg
    (sub_nonneg.mpr ((div_le_one hb0).mpr hlamb.le)) hξ.le
  have hq1 : (1-lam/b)/ξ≤1 := (div_le_one hξ).mpr (by
    have hh:=mul_le_mul_of_nonneg_left hb.2 hk.le
    have hl : 1-ξ≤ lam/b := (le_div_iff₀ hb0).mpr (hh.trans hlam)
    linarith)
  have he : canonicalProbability ξ lam b=(1-lam/b)/ξ := by
    unfold canonicalProbability
    have hfrac : (b-lam)/(ξ*b)=(1-lam/b)/ξ := by field_simp [hξ.ne',hb0.ne']
    rw [hfrac,probabilityClip_eq ⟨hq0,hq1⟩]
  refine ⟨he,?_⟩
  have hd : 0<1-ξ*canonicalProbability ξ lam b := by
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hq1 hξ.le]
  apply (eq_div_iff hd.ne').mpr
  rw [he]
  field_simp [hξ.ne',hb0.ne']
  ring

lemma canonical_as_menu {ξ B lam b v : ℝ} (hξ : 0< ξ) (hξ1 : ξ<1)
    (hB : 0< B) (hb : b∈Icc (0:ℝ) B) (hlam : (1-ξ)*B≤ lam) (hlamb : lam< b) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 1)=
      Hybrid.one ξ 0 v lam (canonicalProbability ξ lam b) ∧
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 2)=
      Hybrid.two ξ 0 v lam (canonicalProbability ξ lam b) := by
  have he:=canonical_exposure hξ hξ1 hB hb hlam hlamb
  have hq:=(canonicalProbability_mem ξ lam b)
  have hd : 0<1-ξ*canonicalProbability ξ lam b := by nlinarith [hξ.le,hq.2]
  have hprice : b*(1-ξ*canonicalProbability ξ lam b)=lam := by
    conv_lhs => lhs; rw [he.2]
    exact div_mul_cancel₀ _ hd.ne'
  constructor
  · rw [canonical_singleton]
    unfold Hybrid.one
    rw [←he.2]
    ring
  · rw [canonical_broadcast]
    unfold Hybrid.independentTwo Hybrid.two
    have hpq := congrArg (fun x : ℝ=>2*canonicalProbability ξ lam b*x) hprice
    nlinarith [hpq]

lemma canonical_payoff_zero {ξ lam b : ℝ} (hξ : 0< ξ) (hb : 0≤ b) (hlam : b≤ lam)
    (v : ℝ) (k : Fin 3) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b k)=0 := by
  rw [canonicalCount_expect,canonical_zero hξ hb hlam]
  fin_cases k <;> norm_num [coinMoment,statistic,affineStatistic]

theorem canonical_one_at_partial {ξ B lam b : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2)
    (hB : 1≤ B) (hb : b∈Icc (0:ℝ) B) (hlam : (1-ξ)*B≤ lam) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) 2 b 1)≤1 := by
  by_cases h : b≤ lam
  · rw [canonical_payoff_zero hξ hb.1 h 2 1]
    norm_num
  · have he:=canonical_as_menu (v:=2) hξ (by linarith : ξ<1) (by linarith : 0< B) hb hlam (lt_of_not_ge h)
    rw [he.1]
    have hq:=canonicalProbability_mem ξ lam b
    have hk : 0≤1-ξ := by linarith
    exact canonical_one_at_two ξ lam _ hξ.le hξh hq.1 hq.2
      (by nlinarith [mul_le_mul_of_nonneg_left hB hk])

theorem canonical_two_all_prices {ξ B lam lo b v : ℝ} (hξ : 0< ξ) (hξ1 : ξ<1)
    (hB : 0< B) (hb : b∈Icc (0:ℝ) B) (hlam : (1-ξ)*B≤ lam) (hlo : lo≤ lam) (hv : 0< v) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 2)≤ v-(2*lo-lo^2/v) := by
  by_cases h : b≤ lam
  · rw [canonical_payoff_zero hξ hb.1 h v 2]
    have he : v-(2*lo-lo^2/v)=(v-lo)^2/v := by field_simp [hv.ne'];ring
    rw [he]
    positivity
  · rw [(canonical_as_menu hξ hξ1 hB hb hlam (lt_of_not_ge h)).2]
    exact canonical_two_lower_multiplier_bound ξ lam lo _ v hv
      (canonicalProbability_mem ξ lam b).1 hlo

theorem canonical_one_large {ξ B lam lo b v : ℝ} (hξ : 0< ξ) (hξ1 : ξ<1)
    (hB : 0< B) (hb : b∈Icc (0:ℝ) B) (hlam : (1-ξ)*B≤ lam)
    (hlo : 0≤ lo) (hlolam : lo≤ lam) (hv : lo/(1-ξ)^2≤ v) :
    (canonicalCount ξ lam b).expect (statistic (1-2*ξ) v b 1)≤ v-lo/(1-ξ) := by
  have hk : 0<1-ξ := by linarith
  have hbase : lo/(1-ξ)≤ lo/(1-ξ)^2 :=
    div_le_div_of_nonneg_left hlo (sq_pos_of_pos hk) (by nlinarith [hξ.le])
  by_cases h : b≤ lam
  · rw [canonical_payoff_zero hξ hb.1 h v 1]
    linarith
  · rw [(canonical_as_menu hξ hξ1 hB hb hlam (lt_of_not_ge h)).1]
    have hq:=canonicalProbability_mem ξ lam b
    have hd : 0<1-ξ*canonicalProbability ξ lam b := by nlinarith [hq.2]
    have hm : Hybrid.one ξ 0 v lam (canonicalProbability ξ lam b)≤
        Hybrid.one ξ 0 v lo (canonicalProbability ξ lam b) := by
      unfold Hybrid.one
      simp only [zero_div,zero_add,sub_zero,one_mul]
      exact mul_le_mul_of_nonneg_left
        (sub_le_sub_left (div_le_div_of_nonneg_right hlolam hd.le) v) hq.1
    exact hm.trans (canonical_one_large_value ξ lo _ v hξ.le hξ1 hlo hq.1 hq.2 hv)

end FCAppendix.Affine.Tail04.RouteMenuStatistics
