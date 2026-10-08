import FCAppendix.Ample.RankCutSelection
import FCAppendix.Ample.RankConditionalLaw
import FCAppendix.Ample.RankChernoffComparison
import FCAppendix.Ample.RankProbabilitySubsequence

noncomputable section
namespace FCAppendix.Bayes.RankLimit
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools Ample.DownstreamNormalizationCore

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem failure_small_of_good_cuts
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hFg : F.real (Ioi g) = h) (hh : 0 < h)
    (hpart : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      (0 < x.2.bid ∧ 0 < x.2.routeCount) ↔ (Γ t).g < x.1)
    {D : ℕ → ℝ} (hD : ∀ᶠ t in atTop, 0 < D t)
    (P : ℕ → ℝ → Prop)
    (hP : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ u ∂nu k, P k u)
    (hcutBound : ∀ k ∈ Finset.Icc 1 n, ∀ u : ℝ, 0 < u → u ≤ h → P k u →
      ∀ ε > 0, ∀ᶠ t in atTop, ∀ a : JointAction n,
        0 < a.bid → a.routeCount = k → u ≤ ascendingBidRank (Γ t) a.bid →
        actualFailure (Γ t) a / D t ≤ ε) :
    ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / D t) := by
  classical
  intro ε hε η hη
  let S : Finset ℕ := Finset.Icc 1 n
  let δ : ℝ := h*η/(4*((S.card:ℝ)+1))
  have hden : 0 < 4*((S.card:ℝ)+1) :=
    mul_pos (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) S.card; linarith)
  have hδ : 0 < δ := div_pos (mul_pos hh hη) hden
  have hδeq : δ*(4*((S.card:ℝ)+1)) = h*η := by
    exact div_mul_cancel₀ _ hden.ne'
  have hscalar : (S.card:ℝ)*(2*δ) + h*η/4 < h*η := by
    have hnn : 0 ≤ (S.card:ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    nlinarith
  have hchoose (k : ℕ) : ∃ u : ℝ,
      k ∈ S → 0 < pi k → 0 < u ∧ u ≤ h ∧ P k u ∧ (nu k).real (Iic u) < δ := by
    by_cases hk : k ∈ S
    · by_cases hpk : 0 < pi k
      · letI := hr.finite hk
        have hm : 0 < (nu k).real univ := by rwa [hr.mass k hk]
        obtain ⟨u, hu0, huh, huP, hum⟩ := exists_good_lower_cut
          (nu k) (hr.atomless hk) (hr.supported hk) hm (hP k hk) hδ
        exact ⟨u, fun _ _ => ⟨hu0, huh, huP, hum⟩⟩
      · exact ⟨0, fun _ hp => (hpk hp).elim⟩
    · exact ⟨0, fun hk' _ => (hk hk').elim⟩
  choose cut hcut using hchoose
  let E : ℕ → ℕ → Set (ℝ × JointAction n) := fun t k =>
    if 0 < pi k then
      {x | 0 < x.2.bid ∧ x.2.routeCount = k ∧ ascendingBidRank (Γ t) x.2.bid ≤ cut k}
    else {x | 0 < x.2.bid ∧ x.2.routeCount = k}
  have hEroute (t k : ℕ) (x : ℝ × JointAction n) (hx : x ∈ E t k) :
      x.2.routeCount = k := by
    by_cases hp : 0 < pi k
    · exact (show 0 < x.2.bid ∧ x.2.routeCount = k ∧
        ascendingBidRank (Γ t) x.2.bid ≤ cut k from by simpa only [E, if_pos hp, Set.mem_setOf_eq] using hx).2.1
    · exact (show 0 < x.2.bid ∧ x.2.routeCount = k from
        by simpa only [E, if_neg hp, Set.mem_setOf_eq] using hx).2
  have hEmeas (t k : ℕ) : MeasurableSet (E t k) := by
    have hbid : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.bid} :=
      measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)
    have hrout := measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd)
      (measurable_const : Measurable (fun _ : ℝ × JointAction n => k))
    by_cases hp : 0 < pi k
    · simpa only [E, if_pos hp, Function.comp_apply, Set.setOf_and] using hbid.inter
        (hrout.inter (measurableSet_le (measurable_drawRank (Γ t)) measurable_const))
    · simpa only [E, if_neg hp, Function.comp_apply, Set.setOf_and] using hbid.inter hrout
  have hsmallMass (k : ℕ) (hk : k ∈ S) :
      ∀ᶠ t in atTop, ((Γ t).F ⊗ₘ (Γ t).σ).real (E t k) < 2*δ := by
    by_cases hp : 0 < pi k
    · have hc := hcut k hk hp
      have ht := (hr.lower_tail_tendsto hk ⟨hc.1.le, hc.2.1⟩).eventually_lt_const
        (show (nu k).real (Iic (cut k)) < 2*δ by linarith [hc.2.2.2])
      filter_upwards [ht] with t ht
      simpa only [rankClassLaw_real_apply (Γ t) k _ measurableSet_Iic,
        E, if_pos hp, mem_Iic] using ht
    · have hp0 : pi k = 0 := le_antisymm (le_of_not_gt hp)
        (by rw [← hr.mass k hk]; exact measureReal_nonneg)
      have ht := (hr.mass_tendsto hk).eventually_lt_const
        (show pi k < 2*δ by rw [hp0]; linarith)
      filter_upwards [ht] with t ht
      simpa only [rankClassLaw_real_apply (Γ t) k univ MeasurableSet.univ,
        E, if_neg hp, mem_univ, and_true] using ht
  have hsmallFail (k : ℕ) (hk : k ∈ S) : ∀ᶠ t in atTop,
      0 < pi k → ∀ a : JointAction n, 0 < a.bid → a.routeCount = k →
        cut k ≤ ascendingBidRank (Γ t) a.bid → actualFailure (Γ t) a / D t ≤ ε := by
    by_cases hp : 0 < pi k
    · have hc := hcut k hk hp
      exact (hcutBound k hk (cut k) hc.1 hc.2.1 hc.2.2.1 ε hε).mono
        (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ hpos => (hp hpos).elim)
  have hM_all := rank_eventually_finset S _ hsmallMass
  have hF_all := rank_eventually_finset S _ hsmallFail
  obtain ⟨lo, hi, hlo, _hlh, hvalue⟩ := exists_compact_positive_band F g
    (show 0 < h*η/4 from div_pos (mul_pos hh hη) (by norm_num))
  let V : Set (ℝ × JointAction n) := {x | g < x.1 ∧ x.1-g ∉ Icc lo hi}
  have hVmass (t : ℕ) : ((Γ t).F ⊗ₘ (Γ t).σ).real V < h*η/4 := by
    have hvm : MeasurableSet {v : ℝ | g < v ∧ v-g ∉ Icc lo hi} :=
      (measurableSet_lt measurable_const measurable_id).inter
        (((measurable_id.sub_const g) measurableSet_Icc).compl)
    change ((Γ t).F ⊗ₘ (Γ t).σ).real
      {x | x.1 ∈ {v : ℝ | g < v ∧ v-g ∉ Icc lo hi}} < _
    rw [joint_value_probability _ _ hvm, hF t]
    exact hvalue
  filter_upwards [hM_all, hF_all, hpart, hD] with t hm hf hp hDt
  let R : Set (ℝ × JointAction n) := ⋃ k ∈ S, E t k
  have hdis : Set.PairwiseDisjoint (↑S) (E t) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro x hx hy
    exact hij ((hEroute t i x hx).symm.trans (hEroute t j x hy))
  have hRmass : ((Γ t).F ⊗ₘ (Γ t).σ).real R ≤ (S.card:ℝ)*(2*δ) := by
    rw [show R = ⋃ k ∈ S, E t k from rfl,
      measureReal_biUnion_finset hdis (fun k _ => hEmeas t k)]
    calc
      (∑ k ∈ S, ((Γ t).F ⊗ₘ (Γ t).σ).real (E t k)) ≤ ∑ _k ∈ S, 2*δ :=
        Finset.sum_le_sum (fun k hk => (hm k hk).le)
      _ = (S.card:ℝ)*(2*δ) := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hExc : ((Γ t).F ⊗ₘ (Γ t).σ).real (R ∪ V) < h*η := by
    have hU := measureReal_union_le (μ := ((Γ t).F ⊗ₘ (Γ t).σ)) R V
    linarith [hVmass t]
  have hsub : ∀ᵐ x ∂activeDrawLaw (Γ t),
      ε < |actualFailure (Γ t) x.2 / D t| → x ∈ R ∪ V := by
    filter_upwards [rank_activeDrawLaw_ae_of_joint (Γ t) hp,
      rank_activeDrawLaw_positive (Γ t)] with x hx hpv hxBad
    by_cases hcompact : x.1-g ∈ Icc lo hi
    · left
      have hxv : (Γ t).g < x.1 := by rw [hg t]; linarith [hcompact.1]
      have hxpos := hx.mpr hxv
      have hk : x.2.routeCount ∈ S :=
        Finset.mem_Icc.mpr ⟨hxpos.2, x.2.routeCount_le⟩
      by_contra hxR
      have hnot : x ∉ E t x.2.routeCount := by
        intro hE
        exact hxR (mem_iUnion.mpr ⟨x.2.routeCount, mem_iUnion.mpr ⟨hk, hE⟩⟩)
      have hpk : 0 < pi x.2.routeCount := by
        by_contra hpnot
        apply hnot
        simpa only [E, if_neg hpnot, Set.mem_setOf_eq] using (show 0 < x.2.bid ∧ x.2.routeCount = x.2.routeCount from ⟨hxpos.1, rfl⟩)
      have hrank : cut x.2.routeCount ≤ ascendingBidRank (Γ t) x.2.bid := by
        by_contra hnotle
        apply hnot
        simpa only [E, if_pos hpk, Set.mem_setOf_eq] using
          (show 0 < x.2.bid ∧ x.2.routeCount = x.2.routeCount ∧
            ascendingBidRank (Γ t) x.2.bid ≤ cut x.2.routeCount from
              ⟨hxpos.1, rfl, (lt_of_not_ge hnotle).le⟩)
      have hquot := hf x.2.routeCount hk hpk x.2 hxpos.1 rfl hrank
      have hnonneg : 0 ≤ actualFailure (Γ t) x.2 / D t :=
        div_nonneg ((actualMenu (Γ t)).failure_nonneg x.2) hDt.le
      rw [abs_of_nonneg hnonneg] at hxBad
      exact (not_lt_of_ge hquot) hxBad
    · right
      exact ⟨by simpa only [hg t] using hpv, hcompact⟩
  have hactive : (Γ t).F.real (Ioi (Γ t).g) = h := by rw [hF t, hg t, hFg]
  exact rank_conditional_exception_bound (E := R ∪ V) (Γ t) (by rwa [hactive]) hsub hη
    (by simpa only [hactive] using hExc)

end FCAppendix.Bayes.RankLimit
