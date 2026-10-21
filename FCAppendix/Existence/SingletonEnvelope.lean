import FCAppendix.Existence.RankEnvelopeBids

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set Filter Topology

theorem zero_utility_lower {q : ℝ → ℝ} (hq : Monotone q) {w : ℝ} (hw : 0 ≤ w) :
    w*q 0 ≤ utility q 0 0 w := by
  have hh := (integral_bounds hq hw).1
  simpa only [utility,sub_self,zero_mul,zero_add,sub_zero] using hh

theorem zero_utility_pos {q : ℝ → ℝ} (hq : Monotone q) (hq0 : 0<q 0)
    {w : ℝ} (hw : 0<w) : 0 < utility q 0 0 w :=
  (mul_pos hw hq0).trans_le (zero_utility_lower hq hw.le)

theorem zero_bid_strict_of_rank {q : ℝ → ℝ} (hq : Monotone q) (hqpos : ∀ x, 0<q x)
    {x v : ℝ} (hx : 0<x) (hxv : x ≤ v) (hqstrict : q x<q v) :
    bid q 0 0 x < bid q 0 0 v := by
  have hp := div_pos (mul_pos (zero_utility_pos hq (hqpos 0) hx) (sub_pos.mpr hqstrict))
    (mul_pos (hqpos x) (hqpos v))
  have hb := bid_increase_bound hq le_rfl (hqpos 0) hx.le hxv
  linarith

theorem zero_bid_atomless (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0<v) :
    NullSingletonClass (mu.map (bid (rank mu (r+1) c n) 0 0)) := by
  let q := rank mu (r+1) c n
  let b := bid q 0 0
  have hqmono : Monotone q := rank_monotone mu hc hcr hn hmass
  have hqpos : ∀ x, 0<q x := rank_pos mu _ _ hc hn hmass
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _) (fun x => (hqpos x).ne') 0 0
  constructor
  intro z
  rw [Measure.map_apply hb.measurable (measurableSet_singleton z)]
  let E := fun j : ℕ => Ici (1/((j:ℝ)+1)) ∩ {x | b x=z}
  have hnull (j : ℕ) : mu (E j)=0 := by
    apply Ample.RankMeasureTools.closed_set_null_of_interval_null mu (fun x => measure_singleton x)
      (isClosed_Ici.inter (isClosed_eq hb continuous_const))
    intro x hx v hv hxv
    have hx0 : 0<x := (by positivity : (0:ℝ)<1/((j:ℝ)+1)).trans_le hx.1
    by_cases he : x=v
    · rw [he,Ioc_self,measure_empty]
    · by_contra hmassInterval
      have hqstrict := rank_strict_of_mass mu hc hcr hn hmass (lt_of_le_of_ne hxv he) hmassInterval
      have hstrict := zero_bid_strict_of_rank hqmono hqpos hx0 hxv hqstrict
      change b x<b v at hstrict
      rw [hx.2,hv.2] at hstrict
      exact lt_irrefl _ hstrict
  apply le_antisymm _ bot_le
  calc
    _ ≤ mu (⋃ j, E j) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with x hx hz
      obtain ⟨j,hj⟩ := exists_nat_one_div_lt hx
      exact mem_iUnion.mpr ⟨j,hj.le,hz⟩
    _ = 0 := measure_iUnion_null hnull

theorem zero_bid_positive_ae (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0<v) :
    ∀ᵐ v ∂mu, 0 < bid (rank mu (r+1) c n) 0 0 v := by
  let q := rank mu (r+1) c n
  let b := bid q 0 0
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _)
    (fun x => (rank_pos mu _ _ hc hn hmass x).ne') 0 0
  letI : NullSingletonClass (mu.map b) := zero_bid_atomless mu hc hcr hn hmass hsupport
  have hz : mu {v | b v=0}=0 := by
    have hh := measure_singleton (μ:=mu.map b) 0
    rwa [Measure.map_apply hb.measurable (measurableSet_singleton _)] at hh
  filter_upwards [hsupport,measure_eq_zero_iff_ae_notMem.mp hz] with v hv hne
  have hnonneg := floor_le_bid (rank_monotone mu hc hcr hn hmass) le_rfl
    (rank_pos mu _ _ hc hn hmass 0) hv.le
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

theorem zero_all_one_route_bids_IC (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ x ∂mu, 0<x) (v y : ℝ) (hy : 0 ≤ y) :
    (v-y)*bidRank mu (r+1) c n (bid (rank mu (r+1) c n) 0 0) y ≤
      utility (rank mu (r+1) c n) 0 0 v := by
  let q := rank mu (r+1) c n
  let b := bid q 0 0
  have hqmono : Monotone q := rank_monotone mu hc hcr hn hmass
  have hqpos : ∀ x, 0<q x := rank_pos mu _ _ hc hn hmass
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _) (fun x => (hqpos x).ne') 0 0
  have hbmono : MonotoneOn b (Ici 0) := bid_monotoneOn hqmono le_rfl (hqpos 0)
  letI : NullSingletonClass (mu.map b) := zero_bid_atomless mu hc hcr hn hmass hsupport
  have hs0 : ∀ᵐ x ∂mu, (0:ℝ) ≤ x := hsupport.mono fun _ hx => hx.le
  by_cases hrange : ∃ x : ℝ, 0 ≤ x ∧ y<b x
  · obtain ⟨x,htx,hyx⟩ := hrange
    obtain ⟨z,hz,hbz⟩ := intermediate_value_Icc htx hb.continuousOn
      (show y ∈ Icc (b 0) (b x) from ⟨by simpa only [b,bid_at_floor q 0 0 (hqpos 0).ne'] using hy,hyx.le⟩)
    have htail := bidRank_at_report mu hb.measurable hz.1 hbmono hs0 (r+1) c n
    rw [hbz] at htail
    change (v-y)*bidRank mu (r+1) c n b y ≤ utility q 0 0 v
    rw [htail,← hbz]
    exact one_route_IC hqmono 0 0 z v (hqpos z).ne'
  · have hupper : ∀ x, 0 ≤ x → b x ≤ y := by
      intro x htx
      exact le_of_not_gt (fun hx => hrange ⟨x,htx,hx⟩)
    have hzero : (mu.map b) (Ioi y)=0 := by
      rw [Measure.map_apply hb.measurable measurableSet_Ioi,measure_eq_zero_iff_ae_notMem]
      filter_upwards [hs0] with x hx hbad
      exact not_lt_of_ge (hupper x hx) hbad
    have htail : bidRank mu (r+1) c n b y=1 := by
      simp only [bidRank,Measure.real,hzero,ENNReal.toReal_zero,zero_div,rankSuccess_zero _ _ hc]
    have hbounds : ∀ᶠ x : ℝ in atTop, (v-y)*q x ≤ utility q 0 0 v := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      have hrep := one_route_IC hqmono 0 0 x v (hqpos x).ne'
      exact (mul_le_mul_of_nonneg_right (sub_le_sub_left (hupper x hx) v) (hqpos x).le).trans hrep
    have hres := le_of_tendsto ((rank_tendsto_one mu (r+1) c n hc).const_mul (v-y)) hbounds
    change (v-y)*bidRank mu (r+1) c n b y ≤ utility q 0 0 v
    simpa only [htail,mul_one] using hres

theorem zero_bid_uniform_bound {q : ℝ → ℝ} (hq : Monotone q) (hpos : ∀ x, 0<q x)
    (hq1 : ∀ x, q x ≤ 1) {w H : ℝ} (hw : 0 ≤ w) (hwH : w ≤ H) :
    0 ≤ bid q 0 0 w ∧ bid q 0 0 w ≤ H*(1-q 0) := by
  refine ⟨floor_le_bid hq le_rfl (hpos 0) hw,?_⟩
  have hU := zero_utility_lower hq hw
  have hmul := mul_le_mul_of_nonneg_left (hq1 w) (mul_nonneg hw (hpos 0).le)
  have hdiv : w*q 0 ≤ utility q 0 0 w/q w := by
    rw [le_div_iff₀ (hpos w)]
    nlinarith
  have hH := mul_le_mul_of_nonneg_right hwH (sub_nonneg.mpr (hq1 0))
  dsimp only [bid]
  nlinarith

def singletonBid (mu : Measure ℝ) (r c n : ℕ) (w : ℝ) : ℝ :=
  max (bid (rank mu (r+1) c n) 0 0 w) 0

theorem singletonBid_nonneg (mu : Measure ℝ) (r c n : ℕ) (w : ℝ) :
    0 ≤ singletonBid mu r c n w := le_max_right _ _

theorem continuous_singletonBid (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1) :
    Continuous (singletonBid mu r c n) :=
  (continuous_bid (continuous_rank mu _ _ _)
    (fun x => (rank_pos mu _ _ hc hn hmass x).ne') 0 0).max continuous_const

theorem singletonBid_eq (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) : singletonBid mu r c n w=bid (rank mu (r+1) c n) 0 0 w :=
  max_eq_left (floor_le_bid (rank_monotone mu hc hcr hn hmass) le_rfl
    (rank_pos mu _ _ hc hn hmass 0) hw)

theorem singletonBid_law (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0<v) :
    mu.map (singletonBid mu r c n)=mu.map (bid (rank mu (r+1) c n) 0 0) :=
  Measure.map_congr (hsupport.mono fun _ hv => singletonBid_eq mu hc hcr hn hmass hv.le)

theorem singletonBid_atomless (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0<v) : NullSingletonClass (mu.map (singletonBid mu r c n)) := by
  rw [singletonBid_law mu hc hcr hn hmass hsupport]
  exact zero_bid_atomless mu hc hcr hn hmass hsupport

theorem singletonBid_positive_ae (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ v ∂mu, 0<v) : ∀ᵐ v ∂mu, 0<singletonBid mu r c n v := by
  filter_upwards [hsupport,zero_bid_positive_ae mu hc hcr hn hmass hsupport] with v hv hpos
  rwa [singletonBid_eq mu hc hcr hn hmass hv.le]

theorem singletonBid_payoff (mu : Measure ℝ) [IsFiniteMeasure mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    {w : ℝ} (hw : 0 ≤ w) :
    (w-singletonBid mu r c n w)*rank mu (r+1) c n w=utility (rank mu (r+1) c n) 0 0 w := by
  rw [singletonBid_eq mu hc hcr hn hmass hw,report_payoff 0 0 w w
    (rank_pos mu _ _ hc hn hmass w).ne']
  simp only [sub_self,zero_mul,add_zero]

theorem singletonBid_all_bids_IC (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    {r c n : ℕ} (hc : 1 ≤ c) (hcr : c ≤ r+1) (hn : 2 ≤ n) (hmass : mu.real univ ≤ 1)
    (hsupport : ∀ᵐ x ∂mu, 0<x) (v y : ℝ) (hy : 0 ≤ y) :
    (v-y)*bidRank mu (r+1) c n (singletonBid mu r c n) y ≤ utility (rank mu (r+1) c n) 0 0 v := by
  change (v-y)*rankSuccess (r+1) c ((mu.map (singletonBid mu r c n)).real (Ioi y)/(n:ℝ)) ≤ _
  rw [singletonBid_law mu hc hcr hn hmass hsupport]
  exact zero_all_one_route_bids_IC mu hc hcr hn hmass hsupport v y hy

end FCAppendix.Existence.RankEnvelope
