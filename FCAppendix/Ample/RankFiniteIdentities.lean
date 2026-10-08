import FCAppendix.Ample.RankLimitProperties
import FCAppendix.Ample.SlackAccounting

noncomputable section
namespace FCAppendix.Ample.BidStratum
open MeasureTheory Set Filter Topology
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {bid : Ω → ℝ} (E : BidStratum μ bid) (hb : Measurable bid)

theorem rankMeasure_tail_at_rank (b : ℝ) :
    (E.rankMeasure hb).real (Ioi (E.rank b)) = E.tail b := by
  rw [E.rankMeasure_eq_volume hb, measureReal_restrict_apply measurableSet_Ioi]
  have he : Ioi (E.rank b) ∩ Ioc (0 : ℝ) E.mass = Ioc (E.rank b) E.mass := by
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    exact ⟨fun hu => ⟨hu.1, hu.2.2⟩,
      fun hu => ⟨hu.1, (E.rank_nonneg b).trans_lt hu.1, hu.2⟩⟩
  rw [he, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (E.rank_le_mass b))]
  unfold rank
  ring

include hb in

theorem rank_threshold_ae (b : ℝ) :
    ∀ᵐ x ∂μ, x ∈ E.carrier →
      (b < bid x ↔ E.rank b < E.rank (bid x)) := by
  classical
  let T : Set Ω := E.carrier ∩ {x | b < bid x}
  let R : Set Ω := E.carrier ∩ {x | E.rank b < E.rank (bid x)}
  have hR : MeasurableSet R := E.measurable_carrier.inter
    (measurableSet_lt measurable_const ((E.continuous_rank hb).measurable.comp hb))
  have hsub : R ⊆ T := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hxb
    exact hx.2.not_ge (E.rank_monotone (le_of_not_gt hxb))
  have hmass : μ.real R = E.tail b := by
    rw [← E.rankMeasure_tail_at_rank hb b, E.rankMeasure_apply hb _ measurableSet_Ioi]
    rfl
  have hz : μ (T \ R) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
    rw [measureReal_sdiff hsub hR, hmass]
    change E.tail b - E.tail b = 0
    ring
  have hae : ∀ᵐ x ∂μ, x ∉ T \ R := by
    rw [ae_iff]
    simp only [not_not]
    exact hz
  filter_upwards [hae] with x hx hE
  constructor
  · intro hxb
    have hxR : x ∈ R := by
      by_contra hnot
      exact hx ⟨⟨hE, hxb⟩, hnot⟩
    exact hxR.2
  · intro hr
    exact (hsub ⟨hE, hr⟩).2

end FCAppendix.Ample.BidStratum

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem visibleClassMass_eq_rank_tail (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) {b : ℝ} (hb : 0 ≤ b)
    {j : ℕ} (hj : 1 ≤ j) :
    visibleClassMass Γ b j =
      (rankClassLaw Γ j).real (Ioi (ascendingBidRank Γ b)) := by
  rw [← positiveRouteTail_class_eq Γ b hb hj,
    rankClassLaw_real_apply Γ j _ measurableSet_Ioi]
  have ha := (positiveBidStratum Γ hatom (fun _ => True)).rank_threshold_ae
    ((measurable_bid n).comp measurable_snd) b
  apply measureReal_congr
  filter_upwards [ha] with x hx
  apply propext
  change (0 < x.2.bid ∧ 0 < x.2.routeCount ∧ x.2.routeCount = j ∧ b < x.2.bid) ↔
    (0 < x.2.bid ∧ x.2.routeCount = j ∧ ascendingBidRank Γ b < ascendingBidRank Γ x.2.bid)
  constructor
  · rintro ⟨hbid, hk, hkj, hbx⟩
    refine ⟨hbid, hkj, ?_⟩
    simpa only [ascendingBidRank_eq_stratum Γ hatom] using
      (hx ⟨hbid, hk, trivial⟩).mp hbx
  · rintro ⟨hbid, hkj, hr⟩
    have hk : 0 < x.2.routeCount := by omega
    refine ⟨hbid, hk, hkj, ?_⟩
    apply (hx ⟨hbid, hk, trivial⟩).mpr
    simpa only [ascendingBidRank_eq_stratum Γ hatom] using hr

theorem visibleClassMass_le_rank_cut (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) {b u : ℝ} (hb : 0 ≤ b)
    (hu : u ≤ ascendingBidRank Γ b) {j : ℕ} (hj : 1 ≤ j) :
    visibleClassMass Γ b j ≤ (rankClassLaw Γ j).real (Ioi u) := by
  rw [visibleClassMass_eq_rank_tail Γ hatom hb hj]
  exact measureReal_mono (Ioi_subset_Ioi hu)

theorem rivalMGF_mono_weights {n k : ℕ} (hk : k ≤ n)
    {p q : ℕ → ℝ} (hpq : ∀ j ∈ Finset.Icc 1 n, p j ≤ q j)
    {θ : ℝ} (hθ : 0 ≤ θ) : rivalMGF n k p θ ≤ rivalMGF n k q θ := by
  unfold rivalMGF
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (hpq j hj)
    (contactGain_nonneg n k j hk (Finset.mem_Icc.mp hj).2 hθ)

theorem rank_actualFailure_eq_identity (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid) :
    actualFailure Γ a = 1 - ((problem Γ i).outcome a).success := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact (actualFailure_eq_congestProb Γ (Nat.succ_pos N) hA hatom hj a hb).trans
    (by simpa only [Nat.succ_sub_one] using
      (ppi_failure_eq_congestProb Γ hA hatom hj i a hb).symm)

theorem actual_failure_rank_chernoff (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (a : JointAction n) (hb : 0 < a.bid) {u θ : ℝ}
    (hu : u ≤ ascendingBidRank Γ a.bid) (hθ : 0 ≤ θ) :
    actualFailure Γ a ≤ exp (-θ * (a.routeCount : ℝ) * c) *
      (rivalMGF n a.routeCount (fun j => (rankClassLaw Γ j).real (Ioi u)) θ) ^ (m-1) := by
  rw [actualFailure_eq_congestProb Γ hm hA hatom hj a hb]
  have hc := congestProb_le_chernoff (N := m-1) (c := c) a.routeCount_le (visibleClassMass_valid Γ a.bid) hθ
  have hexp : -(θ * ((a.routeCount : ℝ) * c)) = -θ * (a.routeCount : ℝ) * c := by ring
  rw [hexp] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  apply pow_le_pow_left₀
  · exact (zero_lt_one.trans_le
      (one_le_rivalMGF a.routeCount_le (visibleClassMass_valid Γ a.bid).nonneg hθ)).le
  · exact rivalMGF_mono_weights a.routeCount_le
      (fun j hj => visibleClassMass_le_rank_cut Γ hatom hb.le hu
        (Finset.mem_Icc.mp hj).1) hθ

theorem rank_failure_chernoff_all_identities (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid) {u θ : ℝ}
    (hu : u ≤ ascendingBidRank Γ a.bid) (hθ : 0 ≤ θ) :
    1 - ((problem Γ i).outcome a).success ≤ exp (-θ * (a.routeCount : ℝ) * c) *
      (rivalMGF n a.routeCount (fun j => (rankClassLaw Γ j).real (Ioi u)) θ) ^ (m-1) := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  rw [← rank_actualFailure_eq_identity Γ hm hA hatom hj i a hb]
  exact actual_failure_rank_chernoff Γ hm hA hatom hj a hb hu hθ

theorem RankLimit.moving_tail {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)
    {u : ℝ} {ut : ℕ → ℝ} (hut : ∀ᶠ t in atTop, ut t ∈ Icc 0 h)
    (hlim : Tendsto ut atTop (𝓝 u)) {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    Tendsto (fun t => (rankClassLaw (Γ t) j).real (Ioi (ut t))) atTop
      (𝓝 (rankTail nu h u j)) := by
  have hdiff : Tendsto (fun t => (rankClassLaw (Γ t) j).real (Ioi (ut t)) -
      rankTail nu h (ut t) j) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((hr.tails ε hε).and hut)
    refine ⟨N, fun t ht => ?_⟩
    simpa only [Real.dist_eq, sub_zero] using (hN t ht).1 j hj (ut t) (hN t ht).2
  have hcont := (hr.continuous_tail hj).continuousAt.tendsto.comp hlim
  convert hdiff.add hcont using 1 <;> simp

theorem RankLimit.visible_weights_tendsto {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t)) (b : ℕ → ℝ)
    (hb : ∀ᶠ t in atTop, 0 ≤ b t)
    (hpart : ∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = h)
    {u : ℝ} (hu : Tendsto (fun t => ascendingBidRank (Γ t) (b t)) atTop (𝓝 u)) :
    ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun t => visibleClassMass (Γ t) (b t) j) atTop
        (𝓝 (rankTail nu h u j)) := by
  intro j hj
  have hs : ∀ᶠ t in atTop, ascendingBidRank (Γ t) (b t) ∈ Icc 0 h := by
    filter_upwards [hpart] with t ht
    exact ⟨ascendingBidRank_nonneg _ _,
      (ascendingBidRank_le_participation _ _).trans_eq ht⟩
  apply (hr.moving_tail hs hu hj).congr'
  filter_upwards [hb] with t ht
  exact (visibleClassMass_eq_rank_tail (Γ t) (hatom t) ht
    (Finset.mem_Icc.mp hj).1).symm

end FCAppendix.Bayes
