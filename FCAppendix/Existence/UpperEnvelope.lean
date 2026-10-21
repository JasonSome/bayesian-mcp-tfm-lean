import FCAppendix.Existence.RankEnvelopeBids
import FCAppendix.Existence.RankEnvelopeRoutes

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set

structure UpperEnvelopeProperties (mu : Measure ℝ) (r c : ℕ)
    (q b U : ℝ → ℝ) (t R E : ℝ) : Prop where
  continuous_rank : Continuous q
  continuous_bid : Continuous b
  matching : U t=(t-R)*q t
  floor : b t=R
  bid_bounds : ∀ v, t ≤ v → R ≤ b v ∧ b v ≤ v
  atomless : NullSingletonClass (mu.map b)
  one_route : ∀ v y, R ≤ y → (v-y)*bidRank mu (r+1) c 2 b y ≤ U v
  error_nonnegative : 0 ≤ E
  error_bounds : ∀ v, t ≤ v → v-R-E ≤ U v ∧ R ≤ b v ∧ b v ≤ R+E/q t
  boundary_above : ∀ v s L, s<q t → t<v → L ≤ U t+(v-t)*s → L<U v
  boundary_below : ∀ v s L y, s<q t → v<t → U t+(v-t)*s ≤ L → R ≤ y →
    (v-y)*bidRank mu (r+1) c 2 b y<L
  hidden_above : ∀ eta (h0 : 0 ≤ eta) (h1 : eta ≤ 1) delta,
    E<eta*R*(1-2*delta) → ∀ v b', t ≤ v → R ≤ b' →
    ∀ law : FiniteLaw (Bool × Bool),
    1-delta ≤ law.prob (fun z => z.1=true) → 1-delta ≤ law.prob (fun z => z.2=true) →
    ∀ G : Schedule 2, (twoContactLaw law).utility v b' 0 (Schedule.affine 2 eta h0 h1) G < U v
  hidden_below : ∀ eta (h0 : 0 ≤ eta) (h1 : eta ≤ 1) delta,
    E<eta*R*(1-2*delta) → ∀ v b', R ≤ v → v ≤ t → R ≤ b' →
    ∀ law : FiniteLaw (Bool × Bool),
    1-delta ≤ law.prob (fun z => z.1=true) → 1-delta ≤ law.prob (fun z => z.2=true) →
    ∀ G : Schedule 2, (twoContactLaw law).utility v b' 0 (Schedule.affine 2 eta h0 h1) G < (v-R)*q t
  hidden_below_value : ∀ eta (h0 : 0 ≤ eta) (h1 : eta ≤ 1) delta,
    E<eta*R*(1-2*delta) → ∀ v b', v ≤ R → R ≤ b' →
    ∀ law : FiniteLaw (Bool × Bool),
    1-delta ≤ law.prob (fun z => z.1=true) → 1-delta ≤ law.prob (fun z => z.2=true) →
    ∀ G : Schedule 2, (twoContactLaw law).utility v b' 0 (Schedule.affine 2 eta h0 h1) G < 0

theorem upper_envelope (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1) (hmass : mu.real univ ≤ 1)
    (t R : ℝ) (hR : 0<R) (hRt : R<t) (hsupport : ∀ᵐ v ∂mu, t ≤ v)
    (hint : IntegrableOn (fun x => 1-rank mu (r+1) c 2 x) (Ioi t)) :
    UpperEnvelopeProperties mu r c (rank mu (r+1) c 2)
      (bid (rank mu (r+1) c 2) t R) (utility (rank mu (r+1) c 2) t R)
      t R (error (rank mu (r+1) c 2) t R) := by
  let q := rank mu (r+1) c 2
  have hn : 2 ≤ (2:ℕ) := le_rfl
  have hqmono : Monotone q := rank_monotone mu hc hcr hn hmass
  have hqcont : Continuous q := continuous_rank mu _ _ _
  have hqpos : ∀ v, 0 < q v := rank_pos mu _ _ hc hn hmass
  have hq1 : ∀ v, q v ≤ 1 := fun v => (rank_bounds mu _ _ hn hmass v).2
  refine {
    continuous_rank := hqcont
    continuous_bid := continuous_bid hqcont (fun x => (hqpos x).ne') t R
    matching := utility_at_floor q t R
    floor := bid_at_floor q t R (hqpos t).ne'
    bid_bounds := fun v hv => ⟨floor_le_bid hqmono hRt.le (hqpos t) hv,
      bid_le_value hqmono hRt.le (hqpos t) hv⟩
    atomless := rank_atomless_bid mu hc hcr hn hmass hRt hsupport
    one_route := fun v y hy => all_one_route_bids_IC mu hc hcr hn hmass hRt hsupport v y hy
    error_nonnegative := error_nonneg hRt.le hq1
    error_bounds := ?_
    boundary_above := ?_
    boundary_below := ?_
    hidden_above := ?_
    hidden_below := ?_
    hidden_below_value := ?_ }
  · intro v hv
    exact ⟨utility_error_bound hqmono hv hq1 hint,bid_error_bound hqmono hRt.le (hqpos t) hv hq1 hint⟩
  · intro v s L hs htv hL
    exact upper_beats_lower_above hqmono hs htv hL
  · intro v s L y hs hvt hL hy
    exact (floor_contract_dominates_below mu hc hcr hn hmass hRt hsupport v y hvt.le hy).trans_lt
      (lower_beats_floor_below hs hvt hL)
  · intro eta h0 h1 delta hguard v b' hv hb law hl hr G
    exact hidden_two_route_excluded hqmono hq1 hR hRt (hqpos t) hint h0 h1 hguard hv hb law hl hr G
  · intro eta h0 h1 delta hguard v b' hv hvt hb law hl hr G
    exact hidden_two_route_below_floor hq1 hR hRt hv hvt h0 h1 hguard hb law hl hr G
  · intro eta h0 h1 delta hguard v b' hv hb law hl hr G
    exact hidden_two_route_below_value hq1 hR hRt hv h0 h1 hguard hb law hl hr G

theorem upper_envelope_bounded (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (r c : ℕ) (hc : 1 ≤ c) (hcr : c ≤ r+1) (hmass : mu.real univ ≤ 1)
    (t R H : ℝ) (hR : 0<R) (hRt : R<t) (hsupport : ∀ᵐ v ∂mu, v ∈ Icc t H) :
    UpperEnvelopeProperties mu r c (rank mu (r+1) c 2)
      (bid (rank mu (r+1) c 2) t R) (utility (rank mu (r+1) c 2) t R)
      t R (error (rank mu (r+1) c 2) t R) :=
  upper_envelope mu r c hc hcr hmass t R hR hRt (hsupport.mono fun _ hv => hv.1)
    (rank_deficit_integrable_of_bounded mu (r+1) c 2 hc t (hsupport.mono fun _ hv => hv.2))

end FCAppendix.Existence.RankEnvelope
