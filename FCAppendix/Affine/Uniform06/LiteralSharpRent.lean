import FCAppendix.Affine.Uniform06.LowSuccessComparison
import FCAppendix.Affine.Uniform06.LiteralPureBid

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralSharpRent

open MeasureTheory Set Filter Topology
open Rank LiteralRankIC LiteralWeakRent LiteralPrefixStieltjes
open LiteralKernelDecomposition LowRankMeasures LowSuccessComparison
open SourcePivotalRates LiteralExperiment PureRankCounts
open FCAppendix.Affine.Uniform07

def rentConstant (i : Row) : ℝ :=
  Real.exp (-(1/(1-cutoff i)))/24

theorem rentConstant_pos (i : Row) : 0 < rentConstant i := by
  unfold rentConstant
  positivity

theorem exists_used_in_value_band (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {C : Set (ℝ × ℝ)} (hC : ∀ᵐ p ∂G, p ∈ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ cutoff i) :
    ∃ p ∈ C, p.1 ∈ Ioo a b := by
  have hsub : Ioo a b ⊆ Icc (0:ℝ) (cutoff i) :=
    fun _ hx => ⟨ha.trans hx.1.le,hx.2.le.trans hb⟩
  have hp : 0 < G {p : ℝ × ℝ | p.1 ∈ Ioo a b} := by
    have he := Measure.map_apply measurable_fst (measurableSet_Ioo (a := a) (b := b)) (μ := G)
    change (G.map Prod.fst) (Ioo a b)=G {p : ℝ × ℝ | p.1 ∈ Ioo a b} at he
    rw [← he,hvalue,LowChernoff.conditionalValueLaw,Measure.smul_apply,
      Measure.restrict_apply measurableSet_Ioo,inter_eq_left.mpr hsub,Real.volume_Ioo]
    have ht := cutoff_pos i
    have hd : 0 < b-a := sub_pos.mpr hab
    exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr (div_pos zero_lt_one ht), ENNReal.ofReal_pos.mpr hd⟩
  obtain ⟨p,hp,hpC⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp.ne'
    (ae_restrict_of_ae hC)
  exact ⟨p,hpC,hp⟩

theorem finite_rank_band_size (i : Row) {m : ℕ} (hm : 0 < m)
    {v w : ℝ} (hw : 0 ≤ w) (hvw : w < v)
    (hband : v-w ≤ min v (1/(m:ℝ))/2) :
    ((m-1:ℕ):ℝ)/(1-(1+cutoff i)/2+w)*(v-w) ≤ 1/(1-cutoff i) := by
  have ht : 0 < 1-cutoff i := sub_pos.mpr (cutoff_lt_one i)
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hN : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  have hg : v-w ≤ (1/(m:ℝ))/2 :=
    hband.trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hnum : ((m-1:ℕ):ℝ)*(v-w) ≤ 1/2 := by
    calc
      ((m-1:ℕ):ℝ)*(v-w) ≤ (m:ℝ)*(v-w) :=
        mul_le_mul_of_nonneg_right hN (sub_nonneg.mpr hvw.le)
      _ ≤ (m:ℝ)*((1/(m:ℝ))/2) := mul_le_mul_of_nonneg_left hg hmR.le
      _ = 1/2 := by field_simp [hmR.ne']
  have hden : (1-cutoff i)/2 ≤ 1-(1+cutoff i)/2+w := by linarith
  have hd : 0 < 1-(1+cutoff i)/2+w := (half_pos ht).trans_le hden
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hh := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 1/(1-cutoff i) by positivity)
  have he : 1/(1-cutoff i)*((1-cutoff i)/2)=(1/2:ℝ) := by
    field_simp [ht.ne']
  rw [he] at hh
  exact hnum.trans hh

theorem eventually_source_sharp_rank_rent (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (K U : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g K → K ≤ entry i+cutoff i/400 → K ≤ RankCutoff.Mstar i →
      extensionEnd i ≤ g.multiplier-g.radius →
      (∀ᵐ p ∂G, p ∈ usedSet i m G g margin U) →
      ∀ p ∈ usedSet i m G g margin U, p.1 < K → p.2 ≤ extensionEnd i →
        rentConstant i*min p.1 (1/(m:ℝ)) ≤ p.1-p.2 := by
  filter_upwards [eventually_source_low_success_comparable i,eventually_ge_atTop (4:ℕ)]
    with m hcomp hm
  intro G hG hvalue hatom g K U margin hg hKfloor hKM hZL hC p hp hpK hpZ
  letI := hG
  let C := usedSet i m G g margin U
  have hfloor : ∀ᵐ q ∂G, LowChernoff.physicalFloor i q.1 ≤ q.2 :=
    hC.mono fun _ hq => hq.2.2.1.1
  have hsort := usedSet_sorted i hm G hfloor hatom g hg margin U
  have hrank := source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin U hC
  have hv : 0 < p.1 := hp.2.1.trans_le (hp.2.2.1.2.trans (min_le_left _ _))
  have hmR : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  let d := min p.1 (1/(m:ℝ))
  have hd : 0 < d := lt_min hv (by positivity)
  have hdv : d ≤ p.1 := min_le_left _ _
  obtain ⟨q,hq,hqband⟩ := exists_used_in_value_band i G hvalue hC
    (show 0 ≤ p.1-d/2 by linarith) (show p.1-d/2 < p.1-d/4 by linarith)
    (show p.1-d/4 ≤ cutoff i by linarith [hp.1.2])
  have hqv : 0 < q.1 := by linarith [hqband.1]
  have hqp : q.1 < p.1 := by linarith [hqband.2]
  have hqK := hqp.trans hpK
  have hqb : q.2 ≤ p.2 := hsort q hq hqK p hp hqp
  have hpB : p.2 ≤ K := (hp.2.2.1.2.trans (min_le_left _ _)).trans hpK.le
  have hgB := LowRankMeasures.PrefixConditions.mono hg hpB
  have hpM : sourceRank (cutoff i) (G.map Prod.snd) p.2 ≤ RankCutoff.Mstar i := by
    rw [hrank p hp hpK]
    exact hpK.le.trans hKM
  have hqM : sourceRank (cutoff i) (G.map Prod.snd) q.2 ≤ RankCutoff.Mstar i := by
    rw [hrank q hq hqK]
    exact hqK.le.trans hKM
  have hSₚ := hcomp G hG hvalue hfloor hatom g p.2 margin hgB
    (hpZ.trans hZL) hpZ p.2 hp.2.1 le_rfl hpM
  have hSᵩ := hcomp G hG hvalue hfloor hatom g p.2 margin hgB
    (hpZ.trans hZL) hpZ q.2 hq.2.1 hqb hqM
  dsimp only at hSₚ hSᵩ
  rw [hrank p hp hpK] at hSₚ
  rw [hrank q hq hqK] at hSᵩ
  have hpFloor : LowChernoff.physicalFloor i p.1=0 := source_floor_zero
    (hpK.le.trans hKfloor)
  have hqFloor : LowChernoff.physicalFloor i q.1=0 := source_floor_zero
    (hqK.le.trans hKfloor)
  have hIR : 0 ≤ payoff (eta i) q.1 q.2 (sourceSuccess i m G g margin q.2)
      (sourceDuplicate i m G g margin q.2) := by
    have hzero := hq.2.2.2 0 (by
      rw [hqFloor]
      exact ⟨le_rfl,hq.2.1.le.trans hq.2.2.1.2⟩)
    have hs0 := (source_first_duplicate_bounds i m G g margin 0).1.1
    have hn := mul_nonneg hqv.le hs0
    dsimp only [payoff] at hzero ⊢
    nlinarith only [hzero,hn]
  have hcross := hp.2.2.2 q.2 (by
    rw [hpFloor]
    exact ⟨hq.2.1.le,hqb.trans hp.2.2.1.2⟩)
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcN : capacity m ≤ (m-1)+1 := by
    have hh := PhysicalRates.capacity_strictly_below_rivals hm
    omega
  have hparam := source_prefix_rank_parameter i hv.le (hpK.le.trans hKM)
  have hwu : (1+cutoff i)/2-q.1 < 1 := by linarith [cutoff_lt_one i]
  have hsize := finite_rank_band_size i (show 0 < m by omega) hqv.le hqp
    (show p.1-q.1 ≤ min p.1 (1/(m:ℝ))/2 by dsimp only [d] at hqband; linarith [hqband.1])
  have hh := quantitative_rent_from_pureRank (m-1) (capacity m) hc hcN
    (show 0 ≤ eta i by cases i <;> norm_num [eta,etaQ]) hp.2.1.le
    (source_first_duplicate_bounds i m G g margin p.2).2.1 hIR hcross hqp
    (source_first_duplicate_bounds i m G g margin p.2).1.1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 3)
    (by convert! hSᵩ.1 using 1; ring) hSₚ.2.1 hparam.1.1 hwu hsize
  have he := Real.exp_pos (-(1/(1-cutoff i)))
  have hgap : d/4 ≤ p.1-q.1 := by linarith [hqband.2]
  have hmul := mul_le_mul_of_nonneg_right hgap he.le
  dsimp only [rentConstant]
  dsimp only [d] at hmul
  nlinarith

end FCAppendix.Affine.Uniform06.LiteralSharpRent
