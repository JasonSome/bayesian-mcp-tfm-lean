import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.UpperNativeRoutes
import FCAppendix.Finite.SingletonDeviation
import FCAppendix.Finite.RankConcentration

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open Existence.RankEnvelope

theorem exists_original_upper_joint
    (FH : ProbabilityMeasure ℝ) [NullSingletonClass (FH : Measure ℝ)]
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (m c : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), t ≤ v) :
    let mu := ENNReal.ofReal h • (FH : Measure ℝ)
    let q := rank mu (m - 1) c 2
    let b := bid q t R
    Continuous b ∧
    (∀ v, t ≤ v → R ≤ b v ∧ b v ≤ v) ∧
    ∃ hb : Measurable b, ∃ PH : ProbabilityMeasure (ℝ × JointAction 2),
      PH = Hybrid.upperJoint FH b hb ∧
      (PH : Measure (ℝ × JointAction 2)).map Prod.fst = (FH : Measure ℝ) ∧
      (PH : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
        (FH : Measure ℝ).map b ∧
      (∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid ∧ x.2.routeCount = 1) ∧
      (∀ y : ℝ, (PH : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0) := by
  dsimp only
  let mu := ENNReal.ofReal h • (FH : Measure ℝ)
  letI : IsFiniteMeasure mu := by
    constructor
    simp only [mu, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  letI : NullSingletonClass mu :=
    ⟨fun y => by simp only [mu, Measure.smul_apply, smul_eq_mul,
      measure_singleton, mul_zero]⟩
  let q := rank mu (m - 1) c 2
  let b := bid q t R
  have hmass : mu.real univ ≤ 1 := by
    simpa only [mu, Measure.real, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one, ENNReal.toReal_ofReal hh.le] using hh1
  have he : m - 2 + 1 = m - 1 := by omega
  have hqmono : Monotone q := by
    simpa only [q, he] using
      (rank_monotone mu (r := m - 2) hc (by omega) (by norm_num) hmass)
  have hqpos : ∀ v, 0 < q v :=
    fun v => rank_pos mu (m - 1) c hc (by norm_num) hmass v
  have hqcont : Continuous q := continuous_rank mu _ _ _
  have hb : Continuous b := continuous_bid hqcont (fun v => (hqpos v).ne') t R
  have hmu : ∀ᵐ v ∂mu, t ≤ v := Measure.ae_smul_measure hsupport _
  letI : NullSingletonClass (mu.map b) := by
    simpa only [b, q, he] using
      (rank_atomless_bid mu (r := m - 2) hc (by omega) (by norm_num)
        hmass hRt hmu)
  have hfloorAll : ∀ v, t ≤ v → R ≤ b v ∧ b v ≤ v := by
    intro v hv
    exact ⟨floor_le_bid hqmono hRt.le (hqpos t) hv,
      bid_le_value hqmono hRt.le (hqpos t) hv⟩
  have hfloor : ∀ᵐ v ∂(FH : Measure ℝ), R ≤ b v :=
    hsupport.mono (fun v hv => (hfloorAll v hv).1)
  have hpos : ∀ᵐ v ∂(FH : Measure ℝ), 0 ≤ b v :=
    hfloor.mono (fun _ hv => hR.le.trans hv)
  letI : NullSingletonClass ((FH : Measure ℝ).map b) := by
    constructor
    intro y
    have hz : (mu.map b) {y} = 0 := measure_singleton y
    rw [Measure.map_smul, Measure.smul_apply, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr hh)
  refine ⟨hb, hfloorAll, hb.measurable, Hybrid.upperJoint FH b hb.measurable, ?_,
    Hybrid.upperJoint_value_marginal FH b hb.measurable,
    Hybrid.upperJoint_bid_marginal FH b hb.measurable hpos,
    Hybrid.upperJoint_support FH b hb.measurable R hfloor,
    Hybrid.upperJoint_atomless FH b hb.measurable hpos⟩
  rfl

section Native
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_upper_mean_of_policy_rank
    (Gamma : FiniteGame m 2 c Seed) (mu : Measure ℝ)
    (b : ℝ → ℝ) (R : ℝ) (hcm : c ≤ m)
    (hrank : ∀ (i : Fin m) (j : Fin 2) (y : ℝ), R ≤ y →
      ∀ᵐ omega ∂backgroundLaw Gamma,
        Accepts Gamma i y j omega ↔ rivals i (aboveAt j y) omega < c)
    (htail : ∀ (j : Fin 2) (y : ℝ), R ≤ y →
      alphaGt Gamma j y = (mu.map b).real (Ioi y) / 2)
    (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    meanAcceptProb Gamma i y = bidRank mu (m - 1) c 2 b y := by
  have hp : ∀ j : Fin 2, acceptProb Gamma i y j =
      binomBelow (m - 1) (alphaGt Gamma j y) c := by
    intro j
    rw [alphaGt, ← prob_rivals_lt Gamma i _ (measurableSet_aboveAt j y) c]
    apply measureReal_congr
    exact (hrank i j y hy).mono (fun _ hh => propext hh)
  have ha : alphaGt Gamma 0 y ∈ Icc (0 : ℝ) 1 := by
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  have he : meanAcceptProb Gamma i y =
      binomBelow (m - 1) (alphaGt Gamma 0 y) c := by
    unfold meanAcceptProb
    simp_rw [hp, alphaGt_eq Gamma _ 0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [he, bidRank]
  change binomBelow (m-1) (alphaGt Gamma 0 y) c=
    rankSuccess (m-1) c ((Measure.map b mu).real (Ioi y)/2)
  rw [← htail 0 y hy,
    rankSuccess_eq_prob _ _ ha,
    binomBelow_eq_prob _ _ (by omega) _ ha.1 ha.2]

theorem native_zero_route_payoff
    (Gamma : FiniteGame m 2 c Seed) (i : Fin m)
    (act : JointAction 2) (hk : act.routeCount = 0) (v : ℝ) :
    (problem Gamma i).payoff v act = 0 := by
  let law := (problem Gamma i).outcome act
  have hl : law.load = 0 := by
    have h := load_le_routeCount_mul_success Gamma i act
    rw [hk, Nat.cast_zero, zero_mul] at h
    exact le_antisymm h law.load_nonneg
  have hs : law.success = 0 := (law.zero_success_iff_zero_load).2 hl
  have hA : law.charge Gamma.A = 0 := by
    exact le_antisymm (by simpa only [hl] using law.charge_le_load Gamma.A)
      (law.charge_nonneg Gamma.A)
  have hG : law.charge Gamma.G = 0 := by
    exact le_antisymm (by simpa only [hl] using law.charge_le_load Gamma.G)
      (law.charge_nonneg Gamma.G)
  change law.utility v act.bid Gamma.g Gamma.A Gamma.G = 0
  simp only [CountLaw.utility_eq, hs, hA, hG, mul_zero, sub_self]

theorem native_original_upper_attainment
    (Gamma : FiniteGame m 2 c Seed) (hg : Gamma.g = 0)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (hmass : mu.real univ ≤ 1) (t R : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hmean : ∀ (i : Fin m) (y : ℝ), R ≤ y →
      meanAcceptProb Gamma i y =
        bidRank mu (m - 1) c 2 (bid (rank mu (m - 1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hv : t ≤ v) :
    (problem Gamma i).payoff v
      (Hybrid.upperAction (bid (rank mu (m - 1) c 2) t R) v) =
      utility (rank mu (m - 1) c 2) t R v := by
  let q := rank mu (m - 1) c 2
  let b := bid q t R
  have he : m - 2 + 1 = m - 1 := by omega
  have hqmono : Monotone q := by
    simpa only [q, he] using
      (rank_monotone mu (r := m - 2) hc (by omega) (by norm_num) hmass)
  have hqpos : ∀ x, 0 < q x := fun x => rank_pos mu _ _ hc (by norm_num) hmass x
  have hb : Continuous b := continuous_bid (continuous_rank mu _ _ _)
    (fun x => (hqpos x).ne') t R
  have hfloor : R ≤ b v := floor_le_bid hqmono hRt.le (hqpos t) hv
  have hact : (Hybrid.upperAction b v).bid = b v := max_eq_left (hR.le.trans hfloor)
  letI : NullSingletonClass (mu.map b) := by
    simpa only [b, q, he] using
      (rank_atomless_bid mu (r := m - 2) hc (by omega) (by norm_num)
        hmass hRt hsupport)
  rw [singleton_payoff Gamma (by norm_num) i _ rfl v, hg, sub_zero, hact,
    hmean i (b v) hfloor,
    bidRank_at_report mu hb.measurable hv
      (bid_monotoneOn hqmono hRt.le (hqpos t)) hsupport]
  rw [report_payoff t R v v (hqpos v).ne']
  simp only [sub_self, zero_mul, add_zero]
  rfl

theorem native_original_upper_hidden_excluded
    (Gamma : FiniteGame m 2 c Seed) (eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1) (hg : Gamma.g = 0)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (hmass : mu.real univ ≤ 1) (t R : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hint : IntegrableOn (fun x => 1 - rank mu (m - 1) c 2 x) (Ioi t))
    (hguard : error (rank mu (m - 1) c 2) t R <
      eta * R * (1 - 2 * (1 - rank mu (m - 1) c 2 t)))
    (hmean : ∀ (i : Fin m) (y : ℝ), R ≤ y →
      meanAcceptProb Gamma i y =
        bidRank mu (m - 1) c 2 (bid (rank mu (m - 1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hv : t ≤ v)
    (act : JointAction 2) (hk : act.routeCount = 2) (hbid : R ≤ act.bid) :
    (problem Gamma i).payoff v act < utility (rank mu (m - 1) c 2) t R v := by
  have he : m - 2 + 1 = m - 1 := by omega
  have hqmono : Monotone (rank mu (m - 1) c 2) := by
    simpa only [he] using
      (rank_monotone mu (r := m - 2) hc (by omega) (by norm_num) hmass)
  have hqt : 0 < rank mu (m - 1) c 2 t :=
    rank_pos mu _ _ hc (by norm_num) hmass t
  have hfloor : rank mu (m - 1) c 2 t ≤ meanAcceptProb Gamma i act.bid := by
    rw [hmean i act.bid hbid]
    simpa only [he] using
      (bidRank_floor_lower mu (r := m - 2) hc (by omega) (by norm_num)
        hmass hRt hsupport hbid)
  exact Hybrid.native_hidden_upper_excluded Gamma heta0 heta1 hA hg
    hqmono (fun x => (rank_bounds mu _ _ (by norm_num) hmass x).2)
    hR hRt hqt hint hguard hv i act hk hbid (by linarith)

theorem native_hidden_upper_below_floor
    (Gamma : FiniteGame m 2 c Seed) (eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1) (hg : Gamma.g = 0)
    (q : ℝ → ℝ) (hq1 : ∀ x, q x ≤ 1)
    (t R delta v : ℝ) (hR : 0 < R) (hRt : R < t)
    (hRv : R ≤ v) (hvt : v ≤ t)
    (hguard : error q t R < eta * R * (1 - 2 * delta))
    (i : Fin m) (act : JointAction 2) (hk : act.routeCount = 2)
    (hbid : R ≤ act.bid) (hmean : 1 - delta ≤ meanAcceptProb Gamma i act.bid) :
    (problem Gamma i).payoff v act < (v - R) * q t := by
  let law := (problem Gamma i).outcome act
  have hE := error_nonneg hRt.le hq1
  have hprod : 0 < eta * R * (1 - 2 * delta) := hE.trans_lt hguard
  have hdelta : 0 ≤ 1 - 2 * delta := by
    by_contra hh
    have hh' := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg heta0 hR.le) (le_of_not_ge hh)
    linarith
  have hD : 1 - 2 * delta ≤ law.duplicates :=
    Hybrid.native_broadcast_duplicates_lower Gamma i act hk delta hmean
  have hcost := mul_le_mul_of_nonneg_left hD
    (mul_nonneg heta0 (hR.le.trans hbid))
  have hfloor := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbid heta0) hdelta
  have hS : (v - act.bid) * law.success ≤ v - R := by
    by_cases hbv : act.bid ≤ v
    · have hh := mul_le_mul_of_nonneg_left law.success_le_one (sub_nonneg.mpr hbv)
      nlinarith
    · have hh := mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_not_ge hbv)) law.success_nonneg
      linarith
  have hEfloor : (t - R) * (1 - q t) ≤ error q t R := by
    dsimp only [error]
    exact le_add_of_nonneg_right (integral_nonneg fun x => sub_nonneg.mpr (hq1 x))
  have hEvalue := mul_le_mul_of_nonneg_right (sub_le_sub_right hvt R)
    (sub_nonneg.mpr (hq1 t))
  change law.utility v act.bid Gamma.g Gamma.A Gamma.G < _
  rw [hA, hg, affine_zero_base_utility]
  nlinarith

theorem native_original_upper_all_actions
    (Gamma : FiniteGame m 2 c Seed) (eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1) (hg : Gamma.g = 0)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (hmass : mu.real univ ≤ 1) (t R sigma : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hint : IntegrableOn (fun x => 1 - rank mu (m - 1) c 2 x) (Ioi t))
    (hguard : error (rank mu (m - 1) c 2) t R <
      eta * R * (1 - 2 * (1 - rank mu (m - 1) c 2 t)))
    (hmean : ∀ (i : Fin m) (y : ℝ), R ≤ y →
      meanAcceptProb Gamma i y =
        bidRank mu (m - 1) c 2 (bid (rank mu (m - 1) c 2) t R) y)
    (hsigma : sigma < rank mu (m - 1) c 2 t)
    (hboundary : ∀ (i : Fin m) (act : JointAction 2), act.bid < R →
      (problem Gamma i).payoff t act ≤ (t - R) * rank mu (m - 1) c 2 t)
    (hslopes : ∀ (i : Fin m) (act : JointAction 2), act.bid < R →
      ((problem Gamma i).outcome act).success ≤ sigma)
    (i : Fin m) (v : ℝ) (hv : t ≤ v) :
    (problem Gamma i).BestResponse v
      (Hybrid.upperAction (bid (rank mu (m - 1) c 2) t R) v) := by
  let q := rank mu (m - 1) c 2
  have he : m - 2 + 1 = m - 1 := by omega
  have hqmono : Monotone q := by
    simpa only [q, he] using
      (rank_monotone mu (r := m - 2) hc (by omega) (by norm_num) hmass)
  have hqt : 0 < q t := rank_pos mu _ _ hc (by norm_num) hmass t
  intro act
  rw [native_original_upper_attainment Gamma hg mu hm hc hcm hmass t R hR hRt
    hsupport hmean i v hv]
  by_cases hbid : R ≤ act.bid
  · have hk : act.routeCount = 0 ∨ act.routeCount = 1 ∨ act.routeCount = 2 := by
      have hh := act.routeCount_le
      omega
    rcases hk with hk | hk | hk
    · rw [native_zero_route_payoff Gamma i act hk v]
      exact utility_nonneg hqmono hRt.le hqt.le hv
    · rw [singleton_payoff Gamma (by norm_num) i act hk v, hg, sub_zero,
        hmean i act.bid hbid]
      simpa only [he] using
        (all_one_route_bids_IC mu (r := m - 2) hc (by omega) (by norm_num)
          hmass hRt hsupport v act.bid hbid)
    · exact (native_original_upper_hidden_excluded Gamma eta heta0 heta1 hA hg mu
        hm hc hcm hmass t R hR hRt hsupport hint hguard hmean i v hv act hk hbid).le
  · have hb := hboundary i act (lt_of_not_ge hbid)
    have hs := hslopes i act (lt_of_not_ge hbid)
    have hu := supporting_line hqmono t R t v
    rw [utility_at_floor] at hu
    have hvs := mul_le_mul_of_nonneg_left (hs.trans hsigma.le) (sub_nonneg.mpr hv)
    rw [(problem Gamma i).payoff_affine t v act]
    linarith

theorem lower_bestResponse_from_floor_comparison
    (Gamma : FiniteGame m 2 c Seed) (eta : ℝ)
    (heta0 : 0≤ eta) (heta1 : eta≤1)
    (hA : Gamma.A=Schedule.affine 2 eta heta0 heta1) (hg : Gamma.g=0)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2≤ m) (hc : 1≤ c) (hcm : c< m) (hmass : mu.real univ≤1)
    (t R : ℝ) (hR : 0< R) (hRt : R< t) (hsupport : ∀ᵐ v ∂mu,t≤ v)
    (hguard : error (rank mu (m-1) c 2) t R<
      eta*R*(1-2*(1-rank mu (m-1) c 2 t)))
    (hmean : ∀ (i : Fin m) (y : ℝ),R≤ y → meanAcceptProb Gamma i y=
      bidRank mu (m-1) c 2 (bid (rank mu (m-1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hvt : v≤ t) (act : JointAction 2)
    (hrestricted : ∀ alt : JointAction 2,alt.bid< R →
      (problem Gamma i).payoff v alt≤(problem Gamma i).payoff v act)
    (hfloorPay : (v-R)*rank mu (m-1) c 2 t≤(problem Gamma i).payoff v act) :
    (problem Gamma i).BestResponse v act := by
  have he : m-2+1=m-1 := by omega
  have hnonneg : 0≤(problem Gamma i).payoff v act := by
    simpa only [Interim.Problem.payoff_abstain] using hrestricted (Interim.abstain 2) hR
  intro alt
  by_cases hb : alt.bid< R
  · exact hrestricted alt hb
  have hbid : R≤ alt.bid := le_of_not_gt hb
  by_cases hvR : v≤ R
  · have hu := affine_above_value_nonpositive ((problem Gamma i).outcome alt)
      heta0 heta1 alt.bid_nonneg (hvR.trans hbid) Gamma.G
    change ((problem Gamma i).outcome alt).utility v alt.bid Gamma.g Gamma.A Gamma.G≤_
    rw [hA,hg]
    exact hu.trans hnonneg
  have hRv : R≤ v := (lt_of_not_ge hvR).le
  have hk : alt.routeCount=0 ∨ alt.routeCount=1 ∨ alt.routeCount=2 := by
    have := alt.routeCount_le
    omega
  rcases hk with hk | hk | hk
  · rw [native_zero_route_payoff Gamma i alt hk v]
    exact hnonneg
  · have hp : (problem Gamma i).payoff v alt≤(v-R)*rank mu (m-1) c 2 t := by
      rw [singleton_payoff Gamma (by norm_num) i alt hk v,hg,sub_zero,hmean i alt.bid hbid]
      simpa only [he] using floor_contract_dominates_below mu (r:=m-2) hc (by omega)
        (by norm_num) hmass hRt hsupport v alt.bid hvt hbid
    exact hp.trans hfloorPay
  · have hfloor : rank mu (m-1) c 2 t≤ meanAcceptProb Gamma i alt.bid := by
      rw [hmean i alt.bid hbid]
      simpa only [he] using bidRank_floor_lower mu (r:=m-2) hc (by omega)
        (by norm_num) hmass hRt hsupport hbid
    exact (native_hidden_upper_below_floor Gamma eta heta0 heta1 hA hg
      (rank mu (m-1) c 2) (fun x => (rank_bounds mu _ _ (by norm_num) hmass x).2)
      t R (1-rank mu (m-1) c 2 t) v hR hRt hRv hvt hguard i alt hk hbid
      (by linarith)).le.trans hfloorPay

theorem lower_bestResponse_after_upper_completion
    (Gamma : FiniteGame m 2 c Seed) (eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hA : Gamma.A = Schedule.affine 2 eta heta0 heta1) (hg : Gamma.g = 0)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (hmass : mu.real univ ≤ 1) (t R : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hguard : error (rank mu (m - 1) c 2) t R <
      eta * R * (1 - 2 * (1 - rank mu (m - 1) c 2 t)))
    (hmean : ∀ (i : Fin m) (y : ℝ), R ≤ y →
      meanAcceptProb Gamma i y =
        bidRank mu (m - 1) c 2 (bid (rank mu (m - 1) c 2) t R) y)
    (i : Fin m) (v : ℝ) (hvt : v ≤ t)
    (act a0 : JointAction 2) (ha0 : a0.bid < R)
    (hboundary : (problem Gamma i).payoff t a0 =
      (t - R) * rank mu (m - 1) c 2 t)
    (hslope : ((problem Gamma i).outcome a0).success ≤ rank mu (m - 1) c 2 t)
    (hrestricted : ∀ alt : JointAction 2, alt.bid < R →
      (problem Gamma i).payoff v alt ≤ (problem Gamma i).payoff v act) :
    (problem Gamma i).BestResponse v act := by
  have he : m - 2 + 1 = m - 1 := by omega
  have hnonneg : 0 ≤ (problem Gamma i).payoff v act := by
    have hh := hrestricted (Interim.abstain 2) hR
    simpa only [Interim.Problem.payoff_abstain] using hh
  have hfloorPay : (v - R) * rank mu (m - 1) c 2 t ≤
      (problem Gamma i).payoff v act := by
    have hh := hrestricted a0 ha0
    rw [(problem Gamma i).payoff_affine t v a0, hboundary] at hh
    have hh' := mul_le_mul_of_nonpos_left hslope (sub_nonpos.mpr hvt)
    nlinarith
  intro alt
  by_cases hb : alt.bid < R
  · exact hrestricted alt hb
  have hbid : R ≤ alt.bid := le_of_not_gt hb
  by_cases hvR : v ≤ R
  · have hu := affine_above_value_nonpositive ((problem Gamma i).outcome alt)
      heta0 heta1 alt.bid_nonneg (hvR.trans hbid) Gamma.G
    change ((problem Gamma i).outcome alt).utility v alt.bid Gamma.g Gamma.A Gamma.G ≤ _
    rw [hA, hg]
    exact hu.trans hnonneg
  have hRv : R ≤ v := (lt_of_not_ge hvR).le
  have hk : alt.routeCount = 0 ∨ alt.routeCount = 1 ∨ alt.routeCount = 2 := by
    have hh := alt.routeCount_le
    omega
  rcases hk with hk | hk | hk
  · rw [native_zero_route_payoff Gamma i alt hk v]
    exact hnonneg
  · have hp : (problem Gamma i).payoff v alt ≤
        (v - R) * rank mu (m - 1) c 2 t := by
      rw [singleton_payoff Gamma (by norm_num) i alt hk v, hg, sub_zero,
        hmean i alt.bid hbid]
      simpa only [he] using
        (floor_contract_dominates_below mu (r := m - 2) hc (by omega) (by norm_num)
          hmass hRt hsupport v alt.bid hvt hbid)
    exact hp.trans hfloorPay
  · have hfloor : rank mu (m - 1) c 2 t ≤ meanAcceptProb Gamma i alt.bid := by
      rw [hmean i alt.bid hbid]
      simpa only [he] using
        (bidRank_floor_lower mu (r := m - 2) hc (by omega) (by norm_num)
          hmass hRt hsupport hbid)
    have hp := native_hidden_upper_below_floor Gamma eta heta0 heta1 hA hg
      (rank mu (m - 1) c 2) (fun x => (rank_bounds mu _ _ (by norm_num) hmass x).2)
      t R (1 - rank mu (m - 1) c 2 t) v hR hRt hRv hvt hguard i alt hk hbid
      (by linarith)
    exact hp.le.trans hfloorPay

end Native
end FCAppendix.Affine.Tail04
