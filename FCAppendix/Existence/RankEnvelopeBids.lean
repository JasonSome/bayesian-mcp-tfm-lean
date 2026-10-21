import FCAppendix.Existence.RankEnvelopeIntegral
import FCAppendix.Existence.RankEnvelopeProbability

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set Filter Topology

def bidRank (mu : Measure ℝ) (r c n : ℕ) (b : ℝ → ℝ) (y : ℝ) : ℝ :=
  rankSuccess r c ((mu.map b).real (Ioi y)/(n:ℝ))

theorem bid_rank_tail_at_report (mu : Measure ℝ) [IsFiniteMeasure mu]
    {b : ℝ → ℝ} (hb : Measurable b) {t x : ℝ} (htx : t ≤ x)
    (hmono : MonotoneOn b (Ici t)) (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    [NullSingletonClass (mu.map b)] :
    (mu.map b).real (Ioi (b x))=mu.real (Ioi x) := by
  rw [map_measureReal_apply hb measurableSet_Ioi]
  have hatom : mu {v | b v=b x}=0 := by
    have hz := measure_singleton (μ:=mu.map b) (b x)
    rw [Measure.map_apply hb (measurableSet_singleton _)] at hz
    exact hz
  have hne : ∀ᵐ v ∂mu, b v ≠ b x := by
    exact measure_eq_zero_iff_ae_notMem.mp hatom
  apply measureReal_congr
  filter_upwards [hsupport,hne] with v hv hnv
  change (b x<b v)=(x<v)
  apply propext
  constructor
  · intro hbid
    by_contra hbad
    exact (not_le_of_gt hbid) (hmono hv htx (le_of_not_gt hbad))
  · intro hxv
    exact lt_of_le_of_ne (hmono htx hv hxv.le) (Ne.symm hnv)

theorem bidRank_at_report (mu : Measure ℝ) [IsFiniteMeasure mu]
    {b : ℝ → ℝ} (hb : Measurable b) {t x : ℝ} (htx : t ≤ x)
    (hmono : MonotoneOn b (Ici t)) (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    [NullSingletonClass (mu.map b)] (r c n : ℕ) :
    bidRank mu r c n b (b x)=rank mu r c n x := by
  rw [bidRank,bid_rank_tail_at_report mu hb htx hmono hsupport]
  rfl

theorem rank_atomless_bid (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {t R : ℝ} (hRt : R<t) (hsupport : ∀ᵐ v ∂mu, t ≤ v) :
    NullSingletonClass (mu.map (bid (rank mu (r+1) c n) t R)) := by
  apply atomless_bid_of_rank_strict (rank_monotone mu hc hcr hn hmass)
    (continuous_rank mu _ _ _) (rank_pos mu _ _ hc hn hmass) hRt mu hsupport
  intro x v _htx hxv hmassInterval
  exact rank_strict_of_mass mu hc hcr hn hmass hxv hmassInterval

theorem all_one_route_bids_IC (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {t R : ℝ} (hRt : R<t) (hsupport : ∀ᵐ v ∂mu, t ≤ v) (v y : ℝ) (hy : R ≤ y) :
    (v-y)*bidRank mu (r+1) c n (bid (rank mu (r+1) c n) t R) y ≤
      utility (rank mu (r+1) c n) t R v := by
  let q := rank mu (r+1) c n
  let b := bid q t R
  have hqmono : Monotone q := rank_monotone mu hc hcr hn hmass
  have hqpos : ∀ x, 0 < q x := rank_pos mu _ _ hc hn hmass
  have hqcont : Continuous q := continuous_rank mu _ _ _
  have hb : Continuous b := continuous_bid hqcont (fun x => (hqpos x).ne') t R
  have hbmono : MonotoneOn b (Ici t) := bid_monotoneOn hqmono hRt.le (hqpos t)
  letI : NullSingletonClass (mu.map b) := rank_atomless_bid mu hc hcr hn hmass hRt hsupport
  by_cases hrange : ∃ x : ℝ, t ≤ x ∧ y<b x
  · obtain ⟨x,htx,hyx⟩ := hrange
    obtain ⟨z,hz,hbz⟩ := intermediate_value_Icc htx hb.continuousOn
      (show y ∈ Icc (b t) (b x) from ⟨by simpa only [b,bid_at_floor q t R (hqpos t).ne'] using hy,hyx.le⟩)
    have htail := bidRank_at_report mu hb.measurable hz.1 hbmono hsupport (r+1) c n
    rw [hbz] at htail
    change (v-y)*bidRank mu (r+1) c n b y ≤ utility q t R v
    rw [htail,← hbz]
    exact one_route_IC hqmono t R z v (hqpos z).ne'
  · have hupper : ∀ x, t ≤ x → b x ≤ y := by
      intro x htx
      exact le_of_not_gt (fun hx => hrange ⟨x,htx,hx⟩)
    have hzero : (mu.map b) (Ioi y)=0 := by
      rw [Measure.map_apply hb.measurable measurableSet_Ioi]
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hsupport] with x hx hbad
      exact not_lt_of_ge (hupper x hx) hbad
    have htail : bidRank mu (r+1) c n b y=1 := by
      simp only [bidRank,Measure.real,hzero,ENNReal.toReal_zero,zero_div,rankSuccess_zero _ _ hc]
    have hbounds : ∀ᶠ x : ℝ in atTop, (v-y)*q x ≤ utility q t R v := by
      filter_upwards [eventually_ge_atTop t] with x hx
      have hrep := one_route_IC hqmono t R x v (hqpos x).ne'
      have hprice := mul_le_mul_of_nonneg_right (sub_le_sub_left (hupper x hx) v) (hqpos x).le
      exact hprice.trans hrep
    have hlim := (rank_tendsto_one mu (r+1) c n hc).const_mul (v-y)
    change (v-y)*bidRank mu (r+1) c n b y ≤ utility q t R v
    rw [htail,mul_one]
    have hres := le_of_tendsto hlim hbounds
    simpa only [mul_one] using hres

theorem bidRank_floor_lower (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {t R : ℝ} (hRt : R<t) (hsupport : ∀ᵐ v ∂mu, t ≤ v) {y : ℝ} (hy : R ≤ y) :
    rank mu (r+1) c n t ≤ bidRank mu (r+1) c n (bid (rank mu (r+1) c n) t R) y := by
  let q := rank mu (r+1) c n
  let b := bid q t R
  have hqmono : Monotone q := rank_monotone mu hc hcr hn hmass
  have hqpos : ∀ x, 0 < q x := rank_pos mu _ _ hc hn hmass
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _) (fun x => (hqpos x).ne') t R
  letI : NullSingletonClass (mu.map b) := rank_atomless_bid mu hc hcr hn hmass hRt hsupport
  have htail := bidRank_at_report mu hb.measurable le_rfl
    (bid_monotoneOn hqmono hRt.le (hqpos t)) hsupport (r+1) c n
  have hmassb : (mu.map b).real univ ≤ 1 := by
    rw [map_measureReal_apply hb.measurable MeasurableSet.univ]
    simpa only [preimage_univ] using hmass
  have hm := rank_monotone (mu.map b) hc hcr hn hmassb
    (show b t ≤ y by simpa only [b,bid_at_floor q t R (hqpos t).ne'] using hy)
  change bidRank mu (r+1) c n b (b t) ≤ bidRank mu (r+1) c n b y at hm
  rw [htail] at hm
  exact hm

theorem floor_contract_dominates_below (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {t R : ℝ} (hRt : R<t) (hsupport : ∀ᵐ x ∂mu, t ≤ x) (v y : ℝ)
    (hvt : v ≤ t) (hy : R ≤ y) :
    (v-y)*bidRank mu (r+1) c n (bid (rank mu (r+1) c n) t R) y ≤
      (v-R)*rank mu (r+1) c n t := by
  have hi := all_one_route_bids_IC mu hc hcr hn hmass hRt hsupport t y hy
  rw [utility_at_floor] at hi
  have hq := bidRank_floor_lower mu hc hcr hn hmass hRt hsupport hy
  have hm := mul_le_mul_of_nonpos_left hq (sub_nonpos.mpr hvt)
  nlinarith

theorem rank_eq_one_above_support (mu : Measure ℝ) [IsFiniteMeasure mu]
    (r c n : ℕ) (hc : 1 ≤ c) {H : ℝ} (hsupport : ∀ᵐ x ∂mu, x ≤ H)
    {v : ℝ} (hHv : H ≤ v) : rank mu r c n v=1 := by
  have hz : mu (Ioi v)=0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hsupport] with x hx hbad
    exact not_lt_of_ge (hx.trans hHv) hbad
  simp only [rank,contactTail,Measure.real,hz,ENNReal.toReal_zero,zero_div,rankSuccess_zero r c hc]

theorem rank_deficit_integrable_of_bounded (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c n : ℕ) (hc : 1 ≤ c) (t : ℝ) {H : ℝ} (hsupport : ∀ᵐ x ∂mu, x ≤ H) :
    IntegrableOn (fun x => 1-rank mu r c n x) (Ioi t) := by
  let f := fun x => 1-rank mu r c n x
  have hcont : Continuous f := continuous_const.sub (continuous_rank mu r c n)
  have hi := (hcont.integrableOn_Icc (μ:=volume) (a:=t) (b:=H)).integrable_indicator measurableSet_Icc
  apply hi.restrict.congr
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx
  by_cases hxH : x ≤ H
  · rw [indicator_of_mem (show x ∈ Icc t H from ⟨hx.le,hxH⟩)]
  · have hq := rank_eq_one_above_support mu r c n hc hsupport (le_of_not_ge hxH)
    rw [indicator_of_notMem (show x ∉ Icc t H from fun hh => hxH hh.2)]
    rw [hq,sub_self]

end FCAppendix.Existence.RankEnvelope
