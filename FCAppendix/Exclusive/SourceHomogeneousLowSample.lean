import FCAppendix.Exclusive.SourceStationaryLow
import FCAppendix.Exclusive.NarrowExistenceNativeSampled

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter
open Exclusive.Narrow.Existence Exclusive.Narrow.Global ExclusiveSource

theorem exists_sampled_low_parameters (d : ℕ) (hd : 1 ≤ d)
    (h : unitInterval) (rho scaleLo cap : ℝ)
    (hh : 0 < (h : ℝ)) (hrho : 0 < rho) (hrh : rho < (h : ℝ))
    (hscaleLo : 0 < scaleLo) (hcap : 0 < cap)
    (K : LowMarketConstants (d+1) scaleLo ((1-rho/(h : ℝ))^d)) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ delta ≤ K.deltaCap ∧ 0 < eta ∧
      ∀ (m c : ℕ), M0 ≤ m → 0 < c → |(c:ℝ)/((m:ℝ)+1)-rho| < eta →
      ∀ {V : Type*} [MeasurableSpace V] (nu : Measure V) [IsProbabilityMeasure nu]
      (beta : V → ℝ), Measurable beta → (∀ u, beta u ∈ Icc (-delta) delta) →
      ∀ scale ∈ Icc scaleLo cap, ∀ a : UserTariff, a.Allowed →
      ∀ G : Schedule (d+1), ∀ g v : ℝ, 0 ≤ g → v-g ≤ K.lowUpper →
      ∀ k : ℕ, 1 ≤ k → k ≤ d+1 → ∀ b ≥ scale*K.t,
      (∫ omega, LowType.binomialPayoff a G k g v b
        (activeDemand (d+1) b (sampledPrice d hd c scale beta b omega)) ∂iidRivalLaw m h nu) < 0 := by
  let q := (1-rho/(h : ℝ))^d
  have htol := K.tolerance_pos
  have hq : 0 < q := by
    have hq0 : 0 < 1-rho/(h : ℝ) := by
      have := (div_lt_one hh).mpr hrh
      linarith
    exact pow_pos hq0 _
  let pmin := demand (d+1) K.t (q+K.tolerance/scaleLo)
  let D := pmin*(min (scaleLo*K.t) (scaleLo*q-K.tolerance)-K.lowUpper)
  have hpmin : 0 < pmin := (demand_pos_iff (d+1) (by omega) K.t_pos
    (by positivity : 0 ≤ q+K.tolerance/scaleLo)).mpr K.separation
  have hD : 0 < D := mul_pos hpmin (sub_pos.mpr K.low_margin)
  have hprob : 0 < D/(K.lowUpper+D) := div_pos hD (by linarith [K.low_pos])
  obtain ⟨dp,eta,Mp,hdp,heta,_hMp,hprice⟩ := sampled_price_neighborhood d hd (h:ℝ) rho
    cap K.tolerance hh hrho hrh hcap K.tolerance_pos
  let delta := min dp K.deltaCap
  have hdelta : 0 < delta := lt_min hdp K.width_pos
  obtain ⟨Mc,hcount⟩ := exists_count_bad_probability_bound_all_types h heta hprob
  refine ⟨delta,eta,max Mp Mc,hdelta,min_le_right _ _,heta,?_⟩
  intro m c hm hc hC V _ nu _ beta hmeas hband scale hs a ha G g v hg hv k hk hkn b hb
  have hscale : 0 < scale := hscaleLo.trans_le hs.1
  have hupper : 0 < scale*q+K.tolerance := by positivity
  have hfloor : scaleLo*q-K.tolerance ≤ scale*q-K.tolerance := by
    have := mul_le_mul_of_nonneg_right hs.1 hq.le
    linarith
  have hlower : 0 < scale*q-K.tolerance :=
    ((K.low_pos.trans K.low_margin).trans_le (min_le_right _ _)).trans_le hfloor
  have hcut : scale*q+K.tolerance < scale*K.t := by
    have hm := mul_lt_mul_of_pos_left K.separation hscaleLo
    have he : scaleLo*(q+K.tolerance/scaleLo)=scaleLo*q+K.tolerance := by field_simp
    rw [he] at hm
    have hh := mul_le_mul_of_nonneg_right hs.1
      (sub_pos.mpr ((lt_add_of_pos_right q (div_pos K.tolerance_pos hscaleLo)).trans K.separation)).le
    nlinarith
  have hmin : min (scaleLo*K.t) (scaleLo*q-K.tolerance) ≤
      min (scale*K.t) (scale*q-K.tolerance) :=
    min_le_min (mul_le_mul_of_nonneg_right hs.1 K.t_pos.le) hfloor
  let ps := demand (d+1) (scale*K.t) (scale*q+K.tolerance)
  let Ds := ps*(min (scale*K.t) (scale*q-K.tolerance)-K.lowUpper)
  have hpm : pmin ≤ ps := scaled_good_marginal_lower (by omega) hscaleLo hs.1
    K.t_pos K.tolerance_pos.le hupper.le (le_refl _) (le_refl _)
  have hDs : D ≤ Ds := mul_le_mul hpm (by linarith [K.low_margin])
    (by linarith [K.low_margin]) (demand_nonneg _ _ _)
  have hDs0 : 0 < Ds := hD.trans_le hDs
  have hbudget : D/(K.lowUpper+D) ≤ Ds/(K.lowUpper+Ds) := by
    apply (div_le_div_iff₀ (by linarith [K.low_pos]) (by linarith [K.low_pos])).mpr
    nlinarith [mul_nonneg K.low_pos.le (sub_nonneg.mpr hDs)]
  let E := goodCount (V := V) m (h:ℝ) eta
  have hE : MeasurableSet E := by
    exact ((measurable_of_countable (fun N : ℕ => |(1+(N:ℝ))/((m:ℝ)+1)-(h:ℝ)|)).comp
      (measurable_activeCount_sample m)) measurableSet_Iio
  have hbad : (iidRivalLaw m h nu).real Eᶜ < Ds/(K.lowUpper+Ds) := by
    have hh := hcount V m ((le_max_right Mp Mc).trans hm) nu
    have he : Eᶜ={omega | eta ≤ |(1+(activeCount omega:ℝ))/((m:ℝ)+1)-(h:ℝ)|} := by
      ext omega
      simp [E,goodCount,not_lt]
    rw [he]
    exact hh.trans_le hbudget
  have hbandp : ∀ u, beta u ∈ Icc (-dp) dp := fun u =>
    ⟨(neg_le_neg (min_le_left dp K.deltaCap)).trans (hband u).1,
      (hband u).2.trans (min_le_left dp K.deltaCap)⟩
  have hpriceE : ∀ omega ∈ E, sampledPrice d hd c scale beta b omega ∈
      Icc (scale*q-K.tolerance) (scale*q+K.tolerance) := by
    intro omega ho
    have hh := hprice m c (by have := (le_max_left Mp Mc).trans hm; omega) scale hscale hs.2
      beta hbandp b omega ho hC
    have ht := abs_lt.mp hh.2
    exact ⟨by linarith,by linarith⟩
  have hb0 : 0 < b := (mul_pos hscale K.t_pos).trans_le hb
  simp only [activeDemand,if_pos hb0]
  apply LowType.large_bid_deviation_negative (iidRivalLaw m h nu) E hE (d+1) (by omega)
    a ha G k hk hkn hg hlower (by linarith [K.tolerance_pos]) hcut hb K.low_pos.le hv
    (K.low_margin.trans_le hmin) (sampledPrice d hd c scale beta b)
    (measurable_sampledPrice d hd c hc scale beta hmeas b)
    (sampledPrice_nonneg d hd c scale beta b) hpriceE
  exact hbad

end FCAppendix.Bayes.ExclusiveConstruction
