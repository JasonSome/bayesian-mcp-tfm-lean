import FCAppendix.Affine.Uniform06.LiteralPrefixContinuity
import FCAppendix.Affine.Uniform06.LiteralWeakRent
import FCAppendix.Affine.Uniform06.EarlyRankCeiling
import FCAppendix.Affine.Uniform06.ClosedSupportIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralRankIC

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralSuccessLower LiteralWeakRent LiteralPrefixContinuity
open PureRankCounts EqualCanonicalRegularity EarlyRankCeiling
open FCAppendix.Affine.Uniform07

theorem source_kappa (i : Row) : kappa i=1-xi i := by
  cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ]

theorem source_eta (i : Row) : eta i=1-2*xi i := by
  linarith [xi_identity i]

theorem physicalFloor_monotone (i : Row) : Monotone (LowChernoff.physicalFloor i) := by
  intro v w hvw
  have ha : max 0 (v-cutoff i/200) ≤ max 0 (w-cutoff i/200) :=
    max_le_max_left _ (sub_le_sub_right hvw _)
  have hb : min (1:ℝ) (max 0 ((v-(entry i+cutoff i/400))/(cutoff i/400))) ≤
      min (1:ℝ) (max 0 ((w-(entry i+cutoff i/400))/(cutoff i/400))) := by
    exact min_le_min_left _ (max_le_max_left _
      (div_le_div_of_nonneg_right (sub_le_sub_right hvw _)
        (div_nonneg (cutoff_pos i).le (by norm_num))))
  unfold LowChernoff.physicalFloor
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hb
    (le_min (by norm_num) (le_max_left _ _)) (by positivity)

def usedSet (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0:ℝ) (cutoff i) ∧ 0 < p.2 ∧
    p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U) ∧
    ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U),
      payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
        payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)}

theorem usedSet_full (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ)
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U))
    (hIC : ∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 U),
      payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
        payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) :
    ∀ᵐ p ∂G, p ∈ usedSet i m G g margin U := by
  have hn : ∀ᵐ p ∂G, p.2 ≠ 0 := by
    apply (ae_map_iff measurable_snd.aemeasurable (measurableSet_singleton (0:ℝ)).compl).mp
    rw [ae_iff]
    simpa using hatom 0
  filter_upwards [same_joint_value_support i G hvalue,hmenu,hIC,hn] with p hv hm hi hn
  have hp0 : 0 ≤ p.2 := (source_floor_bounds i hv.1).1.trans hm.1
  exact ⟨hv,lt_of_le_of_ne hp0 (Ne.symm hn),hm,hi⟩

theorem usedSet_sorted (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ) :
    ∀ p ∈ usedSet i m G g margin U, p.1 < K →
      ∀ q ∈ usedSet i m G g margin U, p.1 < q.1 → p.2 ≤ q.2 := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hmono := actual_prefix_monotone (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    Gb (source_floor_bid_nonnegative i G hfloor) (capacity m) g hg margin
  intro p hp hpK q hq hpq
  have hpB : p.2 ≤ K := (hp.2.2.1.2.trans (min_le_left _ _)).trans hpK.le
  apply used_bid_sorted_on_prefix
    (show 0 ≤ eta i by cases i <;> norm_num [eta,etaQ]) (physicalFloor_monotone i)
    (show Monotone (fun v : ℝ => min v U) from monotone_id.min monotone_const)
    hmono.1 hmono.2 hpq hp.2.2.1 hq.2.2.1 hp.2.1.le hq.2.1.le hpB
    ((Lm_mem_Ioc i hm).1.trans_le
      (source_actual_success_ge_Lm i hm G g hg margin hp.2.1 hpB (hatom p.2)))
    (source_first_duplicate_bounds i m G g margin q.2).2.1
    hp.2.2.2 hq.2.2.2

theorem source_value_level_null (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i) (v : ℝ) :
    G {p | p.1=v}=0 := by
  have hh := congrArg (fun μ : Measure ℝ => μ {v}) hvalue
  rw [Measure.map_apply measurable_fst (measurableSet_singleton _),
    LowChernoff.conditionalValueLaw,Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton _)] at hh
  have hz : volume ({v} ∩ Icc (0:ℝ) (cutoff i))=0 :=
    measure_mono_null inter_subset_left (by simp)
  simpa only [hz,smul_eq_mul,mul_zero,preimage_setOf_eq,mem_singleton_iff] using! hh

theorem source_rank_identity_on_usedSet (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ)
    (hcommon : ∀ᵐ p ∂G, p ∈ usedSet i m G g margin U) :
    ∀ p ∈ usedSet i m G g margin U, p.1 < K →
      sourceRank (cutoff i) (G.map Prod.snd) p.2=p.1 := by
  have hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2 :=
    hcommon.mono fun _ hp => hp.2.2.1.1
  have hsort := usedSet_sorted i hm G hfloor hatom g hg margin U
  intro p hp hpK
  have hbn : ∀ᵐ q ∂G, q.2 ≠ p.2 := by
    rw [ae_iff]
    have hh := hatom p.2
    rw [Measure.map_apply measurable_snd (measurableSet_singleton _)] at hh
    simpa only [preimage_setOf_eq,mem_singleton_iff,not_not] using! hh
  have hvn : ∀ᵐ q ∂G, q.1 ≠ p.1 := by
    rw [ae_iff]
    simpa only [not_not] using source_value_level_null i G hvalue p.1
  have he : (G.map Prod.snd).real (Iic p.2)=(G.map Prod.fst).real (Iic p.1) := by
    rw [map_measureReal_apply measurable_snd measurableSet_Iic,
      map_measureReal_apply measurable_fst measurableSet_Iic]
    apply measureReal_congr
    filter_upwards [hcommon,hbn,hvn] with q hq hqb hqv
    change (q.2 ≤ p.2) = (q.1 ≤ p.1)
    apply propext
    constructor
    · intro hqp
      by_contra hn
      have hpq : p.1 < q.1 := lt_of_not_ge hn
      exact hqb (le_antisymm hqp (hsort p hp hpK q hq hpq))
    · intro hqp
      have hlt : q.1 < p.1 := lt_of_le_of_ne hqp hqv
      exact hsort q hq (hlt.trans hpK) p hp hlt
  unfold sourceRank
  rw [he,hvalue]
  exact conditional_value_scaled_cdf i hp.1

theorem continuous_sourceRank (t : ℝ) (G : Measure ℝ) [IsFiniteMeasure G]
    (hatom : ∀ b : ℝ, G {b}=0) : Continuous (sourceRank t G) := by
  have he : (fun b => G.real (Iic b))=SupportIntervalDomination.cumulative G := by
    funext b
    unfold SupportIntervalDomination.cumulative
    rw [← measureReal_sdiff (subset_univ (Ioi b)) measurableSet_Ioi]
    congr 1
    ext x
    simp
  unfold sourceRank
  change Continuous ((fun _ : ℝ => t)*(fun b => G.real (Iic b)))
  rw [he]
  exact continuous_const.mul (SupportIntervalDomination.continuous_cumulative G hatom)

theorem source_floor_zero {i : Row} {v : ℝ} (hv : v ≤ entry i+cutoff i/400) :
    LowChernoff.physicalFloor i v=0 := by
  have ht : 0 < cutoff i/400 := div_pos (cutoff_pos i) (by norm_num)
  unfold LowChernoff.physicalFloor
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv) ht.le)]
  norm_num

theorem source_distinct_used_bids_strict_success (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : PrefixConditions (xi i) g K)
    (hKfloor : K ≤ entry i+cutoff i/400)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (U : ℝ)
    {p q : ℝ × ℝ} (hp : p ∈ usedSet i m G g margin U)
    (hq : q ∈ usedSet i m G g margin U) (hqK : q.1 < K) (hpq : p.2 < q.2) :
    sourceSuccess i m G g margin p.2 < sourceSuccess i m G g margin q.2 := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hmono := actual_prefix_monotone (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    Gb (source_floor_bid_nonnegative i G hfloor) (capacity m) g hg margin
  have hqB : q.2 ≤ K := (hq.2.2.1.2.trans (min_le_left _ _)).trans hqK.le
  have hpB : p.2 ≤ K := hpq.le.trans hqB
  have hs := hmono.1 ⟨hp.2.1.le,hpB⟩ ⟨hq.2.1.le,hqB⟩ hpq.le
  have hd := hmono.2 ⟨hp.2.1.le,hpB⟩ ⟨hq.2.1.le,hqB⟩ hpq.le
  by_contra hn
  have he : sourceSuccess i m G g margin q.2=sourceSuccess i m G g margin p.2 :=
    le_antisymm (le_of_not_gt hn) hs
  have hpos : 0 < sourceSuccess i m G g margin p.2 :=
    (Lm_mem_Ioc i (show 4 ≤ m from hm)).1.trans_le
      (source_actual_success_ge_Lm i (show 4 ≤ m from hm) G g hg margin hp.2.1 hpB (hatom p.2))
  have hcost := equal_positive_success_strict_cost (v := q.1) (eta_pos i).le hp.2.1.le hpq
    hpos he (source_first_duplicate_bounds i m G g margin p.2).2.1 hd
  have hlegal : p.2 ∈ Icc (LowChernoff.physicalFloor i q.1) (min q.1 U) := by
    rw [source_floor_zero (hqK.le.trans hKfloor)]
    exact ⟨hp.2.1.le,hpq.le.trans hq.2.2.1.2⟩
  exact not_lt_of_ge (hq.2.2.2 p.2 hlegal) hcost

theorem low_bid_values_below_active_start (i : Row)
    (G : Measure (ℝ × ℝ)) (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {K B err : ℝ} (hK : entry i < K) (hgap : B+err < entry i)
    (hactive : ∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ err) :
    ∀ᵐ p ∂G, p.2 ≤ B → p.1 < K := by
  have he : 0 < entry i := mul_pos
    (by cases i <;> norm_num [x,xQ]) (cutoff_pos i)
  have hbe : ActiveGraphComponent.activeBid i (entry i)=entry i := by
    unfold ActiveGraphComponent.activeBid
    rw [source_kappa]
    have hd : (1-xi i)*entry i+xi i*entry i=entry i := by ring
    rw [hd]
    field_simp [he.ne']
  filter_upwards [same_joint_value_support i G hvalue,hactive] with p hp ha hpb
  by_contra hn
  have hKp : K ≤ p.1 := le_of_not_gt hn
  have hm := activeBid_monotone_positive i he (he.trans (hK.trans_le hKp))
    (hK.le.trans hKp)
  rw [hbe] at hm
  have he' := (abs_le.mp (ha ⟨hKp,hp.2⟩)).1
  linarith

end FCAppendix.Affine.Uniform06.LiteralRankIC
