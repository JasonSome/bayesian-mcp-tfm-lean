import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Positive
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06PureChernoff
import FCAppendix.Affine.Uniform06.FullFamilyConvergence
import FCAppendix.Affine.Uniform06.FullBidGeometry
import FCAppendix.Affine.Uniform06.CanonicalPureTransfer
import FCAppendix.Affine.Uniform07.RateMonotonicity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform07
open LiteralExperiment LiteralPureComponents PureRankCounts

namespace Received05

theorem full_joint_uniform (row : Row) :
    ∀V∈𝓝 (FullJointLaw.law row),∀ᶠm in atTop,∀E : ReadyLaw row m,G row m E∈V := by
  have hp:=SourceEarlyFamily.eventually_source_prefix (G row) (g row) (cm row) row
    (earlyMenu row) (roots row).literal (roots row).rejection
  have hguard : ∀ᶠm in atTop,∀E : ReadyLaw row m,
      (g row m E).radius≤ cutoff row/100 ∧
        LiteralPrefixStieltjes.PrefixConditions (xi row) (g row m E)
          (SourcePrefixConstructor.sortEnd row) := by
    filter_upwards [hp] with m hm E
    exact ⟨(hm E).1,(hm E).2.1⟩
  exact FullFamilyConvergence.source_family_weak_limit (ReadyLaw row)
    (G row) (g row) (cm row) row
    (by unfold SourcePrefixConstructor.sortEnd; have := cutoff_pos row; linarith)
    (value row) (atoms row)
    (SourceEarlyFamily.source_common_used (G row) (g row) (cm row) row
      (earlyMenu row) (atoms row))
    (SourceEarlyFamily.source_early_active (G row) (g row) (cm row) row (earlyMenu row))
    (root_limit row) hguard

theorem ReadyLowerFamily.full_joint_tendsto (F : ReadyLowerFamily) (row : Row)
    (σ : ℕ→ℕ) (hσ : Tendsto σ atTop atTop) :
    Tendsto (fun k=>G row (F.start+σ k) (F.law row (σ k))) atTop
      (𝓝 (FullJointLaw.law row)) := by
  have hm : Tendsto (fun k=>F.start+σ k) atTop atTop :=
    (Physical.tail_population_tendsto F.start).comp hσ
  apply tendsto_def.mpr
  intro V hV
  filter_upwards [hm.eventually (full_joint_uniform row V hV)] with k hk
  exact hk (F.law row (σ k))

end Received05

namespace Received06

theorem full_bid_scaled_cdf (row : Row) {H : ℝ}
    (hH : H∈Icc (0:ℝ) (entry row)) :
    sourceRank (cutoff row) ((FullJointLaw.law row:Measure (ℝ×ℝ)).map Prod.snd) H=H := by
  have ht:=cutoff_pos row
  have hentryt : entry row< cutoff row := by
    have hx : x row<1 := by cases row <;> norm_num [x,xQ]
    unfold entry
    nlinarith
  have hHt : H∈Icc (0:ℝ) (cutoff row):=⟨hH.1,hH.2.trans hentryt.le⟩
  have hbid : FullJointLaw.bid row H=H := by
    simp only [FullJointLaw.bid,if_pos hH.2]
  have he : ∀ᵐv∂LowChernoff.conditionalValueLaw row,
      FullJointLaw.bid row v≤ H ↔ v≤ H := by
    have hv : ∀ᵐv∂LowChernoff.conditionalValueLaw row,v∈Icc (0:ℝ) (cutoff row) := by
      rw [LowChernoff.conditionalValueLaw]
      exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
    filter_upwards [hv] with v hv
    constructor
    · intro hle
      by_contra hn
      have hh:=(FullBidGeometry.strictMonoOn_bid row) hHt hv (lt_of_not_ge hn)
      rw [hbid] at hh
      exact (not_lt_of_ge hle) hh
    · intro hle
      have hh:=(FullBidGeometry.strictMonoOn_bid row).monotoneOn hv hHt hle
      rwa [hbid] at hh
  have hmap : ((FullJointLaw.law row:Measure (ℝ×ℝ)).map Prod.snd) (Iic H)=
      (LowChernoff.conditionalValueLaw row) (Iic H) := by
    change (((LowChernoff.conditionalValueLaw row).map
      (fun v=>(v,FullJointLaw.bid row v))).map Prod.snd) (Iic H)=_
    have hmeas : Measurable (fun v : ℝ=>(v,FullJointLaw.bid row v)) :=
      measurable_id.prodMk (FullJointLaw.measurable_bid row)
    rw [Measure.map_map measurable_snd hmeas]
    change ((LowChernoff.conditionalValueLaw row).map (FullJointLaw.bid row)) (Iic H)=_
    rw [Measure.map_apply (FullJointLaw.measurable_bid row) measurableSet_Iic]
    apply measure_congr
    filter_upwards [he] with v hv
    exact propext hv
  unfold sourceRank Measure.real
  rw [hmap]
  exact EarlyRankCeiling.conditional_value_scaled_cdf row hHt

theorem fixed_subentry_rank_tendsto (row : Row)
    (μ : ℕ→ ProbabilityMeasure (ℝ×ℝ))
    (hμ : Tendsto μ atTop (𝓝 (FullJointLaw.law row)))
    {H : ℝ} (hH : H∈Icc (0:ℝ) (entry row)) :
    Tendsto (fun k=>sourceRank (cutoff row) ((μ k:Measure (ℝ×ℝ)).map Prod.snd) H)
      atTop (𝓝 H) := by
  have hw:=((ProbabilityMeasure.continuous_map continuous_snd).tendsto
    (FullJointLaw.law row)).comp hμ
  have hf : ((FullJointLaw.law row:Measure (ℝ×ℝ)).map Prod.snd) (frontier (Iic H))=0 := by
    rw [frontier_Iic]
    exact FullBidGeometry.full_bid_singleton_null row H
  have hmass:=ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw hf
  have hr:=((ENNReal.tendsto_toReal (measure_ne_top
    (((FullJointLaw.law row:Measure (ℝ×ℝ)).map Prod.snd)) (Iic H))).comp hmass).const_mul
      (cutoff row)
  have hr' : Tendsto
      (fun k=>sourceRank (cutoff row) ((μ k:Measure (ℝ×ℝ)).map Prod.snd) H)
      atTop (𝓝 (sourceRank (cutoff row)
        ((FullJointLaw.law row:Measure (ℝ×ℝ)).map Prod.snd) H)) := hr
  rwa [full_bid_scaled_cdf row hH] at hr'

theorem eventually_subentry_rank_le_entry (row : Row)
    (μ : ℕ→ ProbabilityMeasure (ℝ×ℝ))
    (hμ : Tendsto μ atTop (𝓝 (FullJointLaw.law row)))
    {H : ℝ} (hH0 : 0≤ H) (hH : H< entry row) :
    ∀ᶠk in atTop,∀b≤ H,
      sourceRank (cutoff row) ((μ k:Measure (ℝ×ℝ)).map Prod.snd) b≤ entry row := by
  have hh:=fixed_subentry_rank_tendsto row μ hμ ⟨hH0,hH.le⟩
  filter_upwards [hh.eventually (Iio_mem_nhds hH)] with k hk b hb
  exact (mul_le_mul_of_nonneg_left (measureReal_mono (Iic_subset_Iic.mpr hb))
    (cutoff_pos row).le).trans hk.le

theorem entry_pure_rate_mem (row : Row) :
    pureRate row (x row)∈Ioo (0:ℝ) (9/1000000) := by
  constructor
  · cases row
    · have h:=first_pure_entry
      norm_num only [x,xQ,Rat.cast_div,Rat.cast_ofNat]
      linarith
    · have h:=second_pure_entry
      norm_num only [x,xQ,Rat.cast_div,Rat.cast_ofNat]
      linarith
  · cases row
    · have h:=source_pure_rate_antitone Row.first
        (by norm_num [x,xQ] : (739/1000:ℝ)∈Icc (1/2) (x Row.first))
        (by norm_num [x,xQ] : x Row.first∈Icc (1/2) (x Row.first))
        (by norm_num [x,xQ] : (739/1000:ℝ)≤ x Row.first)
      linarith [first_pure_low]
    · have h:=source_pure_rate_antitone Row.second
        (by norm_num [x,xQ] : (691/1000:ℝ)∈Icc (1/2) (x Row.second))
        (by norm_num [x,xQ] : x Row.second∈Icc (1/2) (x Row.second))
        (by norm_num [x,xQ] : (691/1000:ℝ)≤ x Row.second)
      linarith [second_pure_low]

theorem source_pure_duplicate_le_success (row : Row) (m : ℕ)
    (μ : Measure (ℝ×ℝ)) [IsProbabilityMeasure μ] (b : ℝ) :
    sourcePureDuplicate row m μ b≤ sourcePureSuccess row m μ b := by
  letI : IsProbabilityMeasure (μ.map Prod.snd):=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI:=sourceRivalLaw_probability (cutoff_mem row) (μ.map Prod.snd)
  let P:=Measure.pi (fun _ : Fin (m-1)=>sourceRivalLaw (cutoff row) (μ.map Prod.snd))
  apply integral_mono_ae
    (integrable_rowUnequalPureDuplicate (kappa row) (capacity m) b P)
    (PurePivotalSource.integrable_rowUnequalPureFirst (kappa row) (capacity m) b P)
  exact ae_of_all _ fun ω=>by
    unfold rowUnequalPureDuplicate PurePivotalSource.rowUnequalPureFirst
    split_ifs
    · rfl
    · simp only [PureDuplicateIntervals.rowPureDuplicate,LowBody.pureDuplicate,
        LiteralExperiment.first_eq_indicator]
      split_ifs with hboth hfirst
      · norm_num
      · exact (hfirst (Finset.mem_union.mpr (Or.inl hboth.1))).elim
      · norm_num
      · norm_num

def pureRemainderBound (row : Row) (m : ℕ) : ℝ :=
  (2*entryPureCoefficient row+1)*Real.exp (-pureRate row (x row)*(m:ℝ))

theorem pureRemainderBound_pos (row : Row) (m : ℕ) : 0< pureRemainderBound row m := by
  unfold pureRemainderBound
  have := entryPureCoefficient_positive row
  positivity

theorem source_pure_subentry_bound (row : Row) {m : ℕ} (hm : 4≤ m)
    (μ : Measure (ℝ×ℝ)) [IsProbabilityMeasure μ]
    (hatom : ∀b : ℝ,(μ.map Prod.snd) {b}=0) {b : ℝ} (hb : 0< b)
    (hr : sourceRank (cutoff row) (μ.map Prod.snd) b≤ entry row) :
    sourcePureSuccess row m μ b≤ pureRemainderBound row m ∧
      sourcePureDuplicate row m μ b≤ pureRemainderBound row m := by
  letI : IsProbabilityMeasure (μ.map Prod.snd):=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hr0 : 0≤ sourceRank (cutoff row) (μ.map Prod.snd) b := by
    have ht:=cutoff_pos row
    unfold sourceRank
    positivity
  let p:ℝ:=(1+cutoff row)/2-sourceRank (cutoff row) (μ.map Prod.snd) b
  have hp : p∈Icc (0:ℝ) 1 := by
    have hpar:=(entryPureParameter_mem row).1
    have ht:=(cutoff_mem row).2
    have he : entryPureParameter row=(1+cutoff row)/2-entry row := by
      unfold entryPureParameter pureParameter entry
      ring
    rw [he] at hpar
    dsimp [p]
    norm_num [rho] at hpar
    constructor <;> linarith
  have hentry : entryPureParameter row≤ p := by
    unfold entryPureParameter pureParameter p entry at *
    nlinarith
  have hQ:=original_pure_rank_chernoff row (m:=m) (by omega) hp hentry
  have hS:=PureUnionUpper.source_pure_union_upper row hm (μ.map Prod.snd) hb (hatom b)
    (hr.trans (RankCutoff.Mstar_above_entry row).le)
  have hex : Real.exp (-(9/1000000:ℝ)*m)≤
      Real.exp (-pureRate row (x row)*(m:ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (neg_le_neg (entry_pure_rate_mem row).2.le) (Nat.cast_nonneg m))
  have hs : sourcePureSuccess row m μ b≤ pureRemainderBound row m := by
    change sourcePureSuccess row m μ b≤ 2*Bayes.binomBelow (m-1) p (capacity m)+_ at hS
    unfold pureRemainderBound
    nlinarith
  exact ⟨hs,(source_pure_duplicate_le_success row m μ b).trans hs⟩

end Received06
end FCAppendix.Affine.Uniform07Finishing.Crossover
