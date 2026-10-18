import FCAppendix.Exclusive.NarrowGlobalHighSample

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory Filter
open Existence

lemma raw_radius_wide (scaleLo width : ℝ) (hlo : 0 < scaleLo) (hw : 0 < width) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ scale b : ℝ, scaleLo ≤ scale →
      |b-scale| < radius → b ∈ Icc (scale*Real.exp (-width)) (scale*Real.exp width) := by
  let r := min (1-Real.exp (-width)) (Real.exp width-1)
  have hr : 0 < r := lt_min (by linarith [Real.exp_lt_one_iff.mpr (by linarith : -width<0)])
    (sub_pos.mpr (Real.one_lt_exp_iff.mpr hw))
  refine ⟨scaleLo*r/2,by positivity,?_⟩
  intro scale b hs hb
  have hloR : scaleLo*r/2 ≤ scale*(1-Real.exp (-width)) := by
    have hm := mul_le_mul hs (min_le_left (1-Real.exp (-width)) (Real.exp width-1)) hr.le (hlo.le.trans hs)
    nlinarith only [hm,mul_nonneg hlo.le hr.le]
  have hhiR : scaleLo*r/2 ≤ scale*(Real.exp width-1) := by
    have hm := mul_le_mul hs (min_le_right (1-Real.exp (-width)) (Real.exp width-1)) hr.le (hlo.le.trans hs)
    nlinarith only [hm,mul_nonneg hlo.le hr.le]
  have ha := abs_lt.mp hb
  constructor <;> nlinarith only [hloR,hhiR,ha.1,ha.2]

theorem exists_high_market_parameters
    (d : ℕ) (hd : 1 ≤ d) (h : unitInterval) (rho width scaleLo cap : ℝ)
    (hh : 0 < (h:ℝ)) (hrho : 0 < rho) (hrh : rho < (h:ℝ)) (hw : 0 < width)
    (hlo : 0 < scaleLo)
    (hscales : ∀ a : UserTariff, a.Allowed →
      referenceCentralBid d a (rho/(h:ℝ)) ∈ Icc scaleLo cap) :
    ∃ delta eps eta radius gap : ℝ, ∃ M0 : ℕ,
      0 < delta ∧ delta ≤ width ∧ 0 < eps ∧ eps ≤ 1/2 ∧ 0 < eta ∧ 0 < radius ∧ 0 < gap ∧ 0 < M0 ∧
      (∀ scale b : ℝ, scaleLo ≤ scale → |b-scale| < radius →
        b ∈ Icc (scale*Real.exp (-width)) (scale*Real.exp width)) ∧
      ∀ (m c : ℕ), M0 ≤ m+1 → |(c:ℝ)/((m:ℝ)+1)-rho| < eta →
      ∀ {V : Type*} [MeasurableSpace V] (nu : Measure V) [IsProbabilityMeasure nu] (beta : V → ℝ), Measurable beta →
      (∀ v, beta v ∈ Icc (-delta) delta) → ∀ a : UserTariff, a.Allowed →
      ∀ G : Schedule (d+1), ∀ g v : ℝ, g ∈ Icc (0:ℝ) eps → v ∈ Icc (1-eps) (1+eps) →
      let scale := referenceCentralBid d a (rho/(h:ℝ))
      let payoff := fun k b => ∫ omega, LowType.binomialPayoff a G k g v b
        (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) ∂iidRivalLaw m h nu
      gap ≤ payoff (d+1) scale ∧ ∀ k : ℕ, k ≤ d+1 → ∀ b : ℝ, 0 ≤ b →
        (k=d+1 → b ∉ Icc (scale*Real.exp (-width)) (scale*Real.exp width)) →
        payoff k b+gap ≤ payoff (d+1) scale := by
  let p0 := rho/(h:ℝ)
  have hp0 : 0 < p0 := div_pos hrho hh
  have hp1 : p0 < 1 := (div_lt_one hh).mpr hrh
  have hq : 0 < (1-p0)^d := pow_pos (sub_pos.mpr hp1) d
  have hcap : 0 < cap := hlo.trans_le ((hscales .unique trivial).1.trans (hscales .unique trivial).2)
  let lower := scaleLo*(1-p0)^d/2
  let upper := cap*(1-p0)^d+lower
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hprices (a : UserTariff) (ha : a.Allowed) : normalizedPrice d a p0 ∈ Icc lower upper := by
    have hs : referenceCentralBid d a p0 ∈ Icc scaleLo cap := hscales a ha
    have hp := referenceCentralBid_price d a p0 hp1
    have hL := mul_le_mul_of_nonneg_right hs.1 hq.le
    have hU := mul_le_mul_of_nonneg_right hs.2 hq.le
    rw [hp] at hL hU
    have hbase : 0 ≤ scaleLo*(1-p0)^d := mul_nonneg hlo.le hq.le
    dsimp [lower,upper]
    constructor <;> nlinarith only [hL,hU,hbase]
  obtain ⟨radius,hrad,hwide⟩ := raw_radius_wide scaleLo width hlo hw
  obtain ⟨gg,pg,vg,bg,_cut,hgg,hpg,hvg,hbg,_hcut,hglobal⟩ :=
    exists_uniform_high_global_guard d hd p0 radius lower upper hp0 hp1 hrad hlower hprices
  obtain ⟨gu,hgu,huref⟩ := exists_uniform_reference_utility_margin d hd p0 hp0 hp1
  let margin := min gg gu
  have hmarg : 0 < margin := lt_min hgg hgu
  obtain ⟨pc,hpc,hcentral⟩ := integral_central_payoff_lower (d+1) (by omega)
    lower upper cap (margin/8) hlower (by positivity)
  let priceTolerance := min pg (min pc lower)
  have hpt : 0 < priceTolerance := lt_min hpg (lt_min hpc hlower)
  let K : ℝ := 1+(cap+1)*(d+1:ℕ)
  have hK : 0 < K := by dsimp [K]; positivity
  let badTolerance := min bg (margin/(4*K))
  have hbt : 0 < badTolerance := lt_min hbg (by positivity)
  let valueBudget := min vg (min (margin/8) 1)
  have hvb : 0 < valueBudget := lt_min hvg (lt_min (by positivity) zero_lt_one)
  let eps := min (1/2) (valueBudget/((d+1:ℕ)+1:ℝ))
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have hepsHalf : eps ≤ 1/2 := min_le_left _ _
  have hepsBudget : eps*((d+1:ℕ)+1:ℝ) ≤ valueBudget :=
    (le_div_iff₀ (by positivity : (0:ℝ)<((d+1:ℕ)+1:ℝ))).mp (min_le_right _ _)
  obtain ⟨dp,ep,Mp,hdp,hep,hMp,hprice⟩ := sampled_price_neighborhood d hd (h:ℝ) rho cap
    priceTolerance hh hrho hrh hcap hpt
  let delta := min dp width
  let eta := min ep (rho/2)
  have hdelta : 0 < delta := lt_min hdp hw
  have heta : 0 < eta := lt_min hep (by positivity)
  obtain ⟨Mc,hcount⟩ := exists_count_bad_probability_bound_all_types h heta hbt
  let M0 := max (Mp+1) (Mc+1)+1
  have hM0 : 0 < M0 := by dsimp [M0]; omega
  refine ⟨delta,eps,eta,radius,margin/4,M0,hdelta,min_le_right _ _,heps,hepsHalf,heta,hrad,
    by positivity,hM0,hwide,?_⟩
  intro m c hm hcapacity V _ nu _ beta hbmeas hbeta a ha G g v hg hv
  let scale := referenceCentralBid d a p0
  let mu := iidRivalLaw m h nu
  let E : Set (RivalProfile m V) :=
    {omega | |(1+(activeCount omega:ℝ))/((m:ℝ)+1)-(h:ℝ)| < eta}
  let payoff := fun k b => ∫ omega, LowType.binomialPayoff a G k g v b
    (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) ∂mu
  have hMpRow : Mp ≤ m+1 := by have := le_max_left (Mp+1) (Mc+1); dsimp [M0] at hm; omega
  have hMcRow : Mc ≤ m := by have := le_max_right (Mp+1) (Mc+1); dsimp [M0] at hm; omega
  have hc : 0 < c := by
    by_contra hn
    have hz : c=0 := by omega
    rw [hz,Nat.cast_zero,zero_div,zero_sub,abs_neg,abs_of_pos hrho] at hcapacity
    have he : eta ≤ rho/2 := min_le_right _ _
    linarith only [hcapacity,he,hrho]
  have hs : referenceCentralBid d a p0 ∈ Icc scaleLo cap := hscales a ha
  have hspos : 0 < scale := hlo.trans_le hs.1
  have hbetaP : ∀ v, beta v ∈ Icc (-dp) dp := fun v =>
    ⟨(by have := (hbeta v).1; have := (min_le_left dp width); linarith),
     (hbeta v).2.trans (min_le_left _ _)⟩
  have countMeas : Measurable (fun omega : RivalProfile m V => (activeCount omega:ℝ)) :=
    (measurable_of_countable ((↑) : ℕ → ℝ)).comp (measurable_activeCount_sample m)
  have hE : MeasurableSet E := measurableSet_lt
    (((measurable_const.add countMeas).div_const _).sub_const (h:ℝ)).abs measurable_const
  have hbad : mu.real Eᶜ < badTolerance := by
    have hh := hcount V m hMcRow nu
    simpa only [E,compl_setOf,not_lt,mu] using hh
  have hPriceGood (b : ℝ) (omega : RivalProfile m V) (ho : omega ∈ E) :
      sampledPrice d hd c scale beta b omega ∈ Icc lower upper ∧
      |sampledPrice d hd c scale beta b omega-normalizedPrice d a p0| < priceTolerance := by
    have ht := (hprice m c hMpRow scale hspos hs.2 beta hbetaP b omega
      (ho.trans_le (min_le_left _ _)) (hcapacity.trans_le (min_le_left _ _))).2
    rw [referenceCentralBid_price d a p0 hp1] at ht
    have hL := mul_le_mul_of_nonneg_right hs.1 hq.le
    have hU := mul_le_mul_of_nonneg_right hs.2 hq.le
    rw [referenceCentralBid_price d a p0 hp1] at hL hU
    have hptL : priceTolerance ≤ lower := (min_le_right _ _).trans (min_le_right _ _)
    have htAbs := abs_lt.mp ht
    refine ⟨⟨?_,?_⟩,ht⟩ <;> dsimp [lower,upper] at * <;> linarith only [hL,hU,hptL,htAbs.1,htAbs.2]
  have hvalue : |v-1|+g*(d+1:ℕ) ≤ valueBudget := by
    have hva : |v-1| ≤ eps := abs_le.mpr ⟨by linarith only [hv.1],by linarith only [hv.2]⟩
    have hbase := mul_le_mul_of_nonneg_right hg.2 (Nat.cast_nonneg (d+1))
    nlinarith only [hva,hbase,hepsBudget]
  have hv0 : 0 ≤ v := by linarith only [hv.1,hepsHalf]
  have hv2 : v ≤ 2 := by linarith only [hv.2,hepsHalf]
  have hg1 : g ≤ 1 := by linarith only [hg.2,hepsHalf]
  have hcentralBound : referenceUtility d a (normalizedPrice d a p0) 1 p0 ≤
      payoff (d+1) scale+margin/2 := by
    have hc := hcentral mu E hE a ha G g v hg.1 hv0 scale ⟨hspos.le,hs.2⟩
      _ (hprices a ha) _ (measurable_sampledPrice d hd c hc scale beta hbmeas scale)
      (sampledPrice_nonneg d hd c scale beta scale)
      (fun omega ho => ⟨(hPriceGood scale omega ho).1,((hPriceGood scale omega ho).2).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))⟩)
    rw [pricedPayoff_central_eq_reference d hd a ha p0 hp0.le hp1] at hc
    have hval : |v-1|+g*(d+1:ℕ) ≤ margin/8 := hvalue.trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hcoef : 1+(cap+g)*(d+1:ℕ) ≤ K := by
      dsimp [K]
      nlinarith only [mul_le_mul_of_nonneg_right hg1 (Nat.cast_nonneg (d+1))]
    have hprob := (le_div_iff₀ (show (0:ℝ)<4*K by positivity)).mp
      (hbad.le.trans (min_le_right _ _))
    have hcost := mul_le_mul_of_nonneg_right hcoef (measureReal_nonneg (μ := mu) (s := Eᶜ))
    change referenceUtility d a (normalizedPrice d a p0) 1 p0 ≤
      payoff (d+1) scale+margin/8+|v-1|+g*(d+1:ℕ)+(1+(cap+g)*(d+1:ℕ))*mu.real Eᶜ at hc
    nlinarith only [hc,hval,hprob,hcost]
  have hU : margin ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0 :=
    (min_le_right _ _).trans (huref a ha)
  change margin/4 ≤ payoff (d+1) scale ∧ _
  refine ⟨by linarith only [hcentralBound,hU,hmarg.le],?_⟩
  intro k hk b hb houtside
  have hradBid : k=d+1 → radius ≤ |b-referenceCentralBid d a p0| := by
    intro he
    apply le_of_not_gt
    intro hclose
    exact houtside he (hwide scale b hs.1 hclose)
  have hdev := hglobal mu E hE a ha G g v hg.1 hv0 hv2 (hvalue.trans (min_le_left _ _))
    k hk b hb hradBid _ (measurable_sampledPrice d hd c hc scale beta hbmeas b)
    (sampledPrice_nonneg d hd c scale beta b)
    (fun omega ho => ⟨(hPriceGood b omega ho).1,((hPriceGood b omega ho).2).trans_le (min_le_left _ _)⟩)
    (hbad.le.trans (min_le_left _ _))
  have hmg : margin ≤ gg := min_le_left _ _
  change payoff k b+gg ≤ referenceUtility d a (normalizedPrice d a p0) 1 p0 at hdev
  linarith only [hdev,hcentralBound,hmg,hmarg.le]

end FCAppendix.Exclusive.Narrow.Global
