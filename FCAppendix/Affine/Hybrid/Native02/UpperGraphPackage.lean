import FCAppendix.Affine.Hybrid.Native02.ClosedUpperTransport
import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.NativeLowIncentives

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open Existence.RankEnvelope

section GraphConstruction
variable (FH : ProbabilityMeasure ℝ) [NullSingletonClass (FH : Measure ℝ)]
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (m c : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (t R H : ℝ) (hR : 0 < R) (hRt : R < t)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), v ∈ Icc t H)
local notation "mu" => ENNReal.ofReal h • (FH : Measure ℝ)
local notation "q" => rank mu (m-1) c 2
local notation "b" => bid q t R

local instance graphUpperFinite : IsFiniteMeasure mu := by
  constructor
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.ofReal_lt_top

local instance graphUpperNull : NullSingletonClass mu :=
  ⟨fun y => by simp only [Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]⟩

include hh hh1 hm hc hcm hR hRt hsupport in
theorem actualUpperEnvelope :
    UpperEnvelopeProperties mu (m-2) c q b (utility q t R) t R (error q t R) := by
  have hmass : (mu).real univ ≤ 1 := weighted_upper_mass_le_one h hh.le hh1 FH
  have hs : ∀ᵐ v ∂mu, v ∈ Icc t H := Measure.ae_smul_measure hsupport _
  have he : m-2+1 = m-1 := by omega
  simpa only [he] using upper_envelope_bounded mu (m-2) c hc (by omega) hmass t R H hR hRt hs

include hh hh1 hm hc hcm hR hRt hsupport in
theorem actualUpperBid_measurable : Measurable b :=
  (actualUpperEnvelope FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport).continuous_bid.measurable

def actualUpperJoint : ProbabilityMeasure (ℝ × JointAction 2) :=
  upperJoint FH b (actualUpperBid_measurable FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport)

lemma upperJoint_graph (B : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    ∀ᵐ x ∂(upperJoint B f hf : Measure (ℝ × JointAction 2)), x.2 = upperAction f x.1 := by
  have hh : ∀ᵐ x ∂(upperJoint B f hf : Measure (ℝ × JointAction 2)),
      x.2.bid = max (f x.1) 0 ∧ x.2.routeCount = 1 := by
    apply (ae_map_iff (measurable_id.prodMk (measurable_upperAction f hf)).aemeasurable
      ((measurableSet_eq_fun ((measurable_bid 2).comp measurable_snd)
        ((hf.comp measurable_fst).max measurable_const)).inter
        (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))).mpr
    exact ae_of_all _ (fun _ => ⟨rfl,rfl⟩)
  filter_upwards [hh] with x hx
  have hext (a a' : JointAction 2) (hb : a.bid=a'.bid) (hk : a.routeCount=a'.routeCount) : a=a' := by
    cases a
    cases a'
    simp_all
  exact hext _ _ hx.1 hx.2

theorem actualUpperJoint_spec :
    let PH := actualUpperJoint FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
    (PH : Measure (ℝ × JointAction 2)).map Prod.fst = (FH : Measure ℝ) ∧
    (PH : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) = (FH : Measure ℝ).map b ∧
    (∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),
      x.1 ∈ Icc t H ∧ x.2 = upperAction b x.1 ∧ R ≤ x.2.bid ∧ x.2.routeCount = 1) ∧
    (∀ y : ℝ, (PH : Measure (ℝ × JointAction 2)) {x | x.2.bid=y} = 0) := by
  let hp := actualUpperEnvelope FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
  let hb := actualUpperBid_measurable FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
  have hfloor : ∀ᵐ v ∂(FH : Measure ℝ), R ≤ b v :=
    hsupport.mono (fun v hv => (hp.bid_bounds v hv.1).1)
  have hpos : ∀ᵐ v ∂(FH : Measure ℝ), 0 ≤ b v := hfloor.mono (fun _ hv => hR.le.trans hv)
  letI : NullSingletonClass ((FH : Measure ℝ).map b) := by
    constructor
    intro y
    have hz := hp.atomless.measure_singleton y
    change ((mu).map b) {y} = 0 at hz
    rw [Measure.map_smul, Measure.smul_apply, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr hh)
  have hvalue : ∀ᵐ x ∂(upperJoint FH b hb : Measure (ℝ × JointAction 2)), x.1 ∈ Icc t H := by
    apply (ae_map_iff (measurable_id.prodMk (measurable_upperAction b hb)).aemeasurable
      (measurable_fst measurableSet_Icc)).mpr
    exact hsupport
  refine ⟨upperJoint_value_marginal FH b hb, upperJoint_bid_marginal FH b hb hpos, ?_,
    upperJoint_atomless FH b hb hpos⟩
  filter_upwards [hvalue, upperJoint_graph FH b hb, upperJoint_support FH b hb R hfloor]
    with x hv hg hs
  exact ⟨hv,hg,hs⟩

end GraphConstruction

structure NativeUpperPackage {m c : ℕ} (Γ : FiniteGame m 2 c unitInterval)
    (PH : ProbabilityMeasure (ℝ × JointAction 2)) (q b : ℝ → ℝ) (t R H : ℝ) : Prop where
  joint_shape : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),
    x.1 ∈ Icc t H ∧ x.2 = upperAction b x.1 ∧ R ≤ x.2.bid ∧ x.2.routeCount = 1
  attainment : ∀ (i : Fin m) (v : ℝ), t ≤ v →
    (problem Γ i).payoff v (upperAction b v) = utility q t R v
  utility_floor : ∀ (i : Fin m) (v : ℝ), t ≤ v →
    v-R-error q t R ≤ (problem Γ i).payoff v (upperAction b v)
  one_route : ∀ (i : Fin m) (v : ℝ) (act : JointAction 2),
    act.routeCount=1 → R ≤ act.bid → (problem Γ i).payoff v act ≤ utility q t R v
  two_routes : ∀ (i : Fin m) (v : ℝ), t ≤ v → ∀ act : JointAction 2,
    act.routeCount=2 → R ≤ act.bid → (problem Γ i).payoff v act < utility q t R v
  singleton_count : ∀ (i : Fin m) (act : JointAction 2), act.routeCount=1 → R ≤ act.bid →
    q t ≤ ((problem Γ i).outcome act).success
  joint_upper_IC : ∀ i : Fin m, ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)),
    ∀ act : JointAction 2, R ≤ act.bid → (problem Γ i).payoff x.1 act ≤ (problem Γ i).payoff x.1 x.2

theorem closed_actual_upper_package
    (m c : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ c) (hcm : c < m)
    (U s a h : ℝ) (hU : 0 ≤ U) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hh : 0 < h) (hh1 : h ≤ 1) (hsum : s+a+h=1)
    (PL PA : ProbabilityMeasure (ℝ × JointAction 2))
    (FH : ProbabilityMeasure ℝ) [NullSingletonClass (FH : Measure ℝ)]
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), x.2.bid ≤ U)
    (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta < 1)
    (t R H : ℝ) (hR : 0 < R) (hRt : R < t) (hUR : U < R)
    (hsupport : ∀ᵐ v ∂(FH : Measure ℝ), v ∈ Icc t H)
    (C : ContextPolicy m c unitInterval)
    (hguard : error (rank (ENNReal.ofReal h • (FH : Measure ℝ)) (m-1) c 2) t R <
      eta*R*(1-2*(1-rank (ENNReal.ofReal h • (FH : Measure ℝ)) (m-1) c 2 t))) :
    let mu := ENNReal.ofReal h • (FH : Measure ℝ)
    let q := rank mu (m-1) c 2
    let b := bid q t R
    let PH := actualUpperJoint FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
    let P := populationLaw s a h hs ha hh.le hsum PL PA PH
    let Γ := ClosedPolicy.nativeGame C (PopulationGame.game m c P eta heta0 heta1 U) R
    NativeUpperPackage Γ PH q b t R H := by
  let mu := ENNReal.ofReal h • (FH : Measure ℝ)
  let q := rank mu (m-1) c 2
  let b := bid q t R
  let PH := actualUpperJoint FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
  let P := populationLaw s a h hs ha hh.le hsum PL PA PH
  let Γ := ClosedPolicy.nativeGame C (PopulationGame.game m c P eta heta0 heta1 U) R
  obtain ⟨hvalue,hbid,hshape,hnull⟩ :=
    actualUpperJoint_spec FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
  have hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), x.2.routeCount=1 :=
    hshape.mono (fun _ hx => hx.2.2.2)
  have hsup := hsupport.mono (fun _ hv => hv.1)
  have hatt (i : Fin m) (v : ℝ) (hv : t ≤ v) :
      (problem Γ i).payoff v (upperAction b v) = utility q t R v :=
    closed_upper_constructed_attainment m c U s a h hU C hs ha hh.le hh1 hsum
      PL PA PH FH hL hA hH hnull b hbid eta heta0 heta1 hm hc hcm t R hR hRt hUR hsup rfl i v hv
  have hone (i : Fin m) (v : ℝ) (act : JointAction 2) (hk : act.routeCount=1)
      (hact : R ≤ act.bid) : (problem Γ i).payoff v act ≤ utility q t R v :=
    closed_upper_one_route_bound m c U s a h hU C hs ha hh.le hh1 hsum
      PL PA PH FH hL hA hH hnull b hbid eta heta0 heta1 hm hc hcm
      t R H hR hRt hUR hsupport rfl i v act hk hact
  have htwo (i : Fin m) (v : ℝ) (hv : t ≤ v) (act : JointAction 2)
      (hk : act.routeCount=2) (hact : R ≤ act.bid) : (problem Γ i).payoff v act < utility q t R v :=
    closed_upper_hidden_constructed_excluded m c U s a h hU C hs ha hh.le hh1 hsum
      PL PA PH FH hL hA hH hnull b hbid eta heta0 heta1 hm hc hcm
      t R H hR hRt hUR hsupport rfl hguard i v hv act hk hact
  have hcount (i : Fin m) (act : JointAction 2) (hk : act.routeCount=1)
      (hact : R ≤ act.bid) : q t ≤ ((problem Γ i).outcome act).success := by
    have hl := load_le_routeCount_mul_success Γ i act
    have he : ((problem Γ i).outcome act).load = ((problem Γ i).outcome act).success := by
      simp only [hk, Nat.cast_one, one_mul] at hl
      exact le_antisymm hl ((problem Γ i).outcome act).success_le_load
    rw [← he, load_eq_mean Γ (by norm_num : 0 < 2) i act, hk, Nat.cast_one, one_mul]
    exact closed_upper_mean_floor_lower m c U s a h hU C hs ha hh.le hh1 hsum
      PL PA PH FH hL hA hH hnull b hbid eta heta0 heta1 hm hc hcm
      t R hRt hUR hsup rfl i act.bid hact
  let hp := actualUpperEnvelope FH h hh hh1 m c hm hc hcm t R H hR hRt hsupport
  have huf (i : Fin m) (v : ℝ) (hv : t ≤ v) :
      v-R-error q t R ≤ (problem Γ i).payoff v (upperAction b v) := by
    rw [hatt i v hv]
    exact (hp.error_bounds v hv).1
  have hpositive (v : ℝ) (hv : t ≤ v) : 0 < utility q t R v := by
    letI : IsFiniteMeasure mu := by
      constructor
      simp only [mu, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      exact ENNReal.ofReal_lt_top
    letI : NullSingletonClass mu :=
      ⟨fun y => by simp only [mu, Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]⟩
    have hmass : (mu).real univ ≤ 1 := weighted_upper_mass_le_one h hh.le hh1 FH
    have hmEq : m-2+1=m-1 := by omega
    have hmono : Monotone q := by
      simpa only [hmEq] using rank_monotone mu (r := m-2) hc (by omega)
        (by norm_num : 2 ≤ (2 : ℕ)) hmass
    exact utility_pos hmono hRt (rank_pos mu _ _ hc (by norm_num) hmass t) hv
  refine ⟨hshape,hatt,huf,hone,htwo,hcount,?_⟩
  intro i
  filter_upwards [hshape] with x hx act hact
  rw [hx.2.1, hatt i x.1 hx.1.1]
  by_cases hk0 : act.routeCount=0
  · exact (NativeLowIncentives.payoff_nonpos_of_zero_routes Γ i x.1 act hk0).trans
      (hpositive x.1 hx.1.1).le
  · by_cases hk1 : act.routeCount=1
    · exact hone i x.1 act hk1 hact
    · have hk2 : act.routeCount=2 := by have := act.routeCount_le; omega
      exact (htwo i x.1 hx.1.1 act hk2 hact).le

end FCAppendix.Affine.Hybrid.Native02
