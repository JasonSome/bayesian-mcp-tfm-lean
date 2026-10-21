import FCAppendix.Affine.Uniform06.PureRankSelector
import FCAppendix.Affine.Uniform06.EqualCanonicalExpected
import FCAppendix.Affine.Uniform06.RankUpperTail

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureDuplicateRare

open MeasureTheory ProbabilityTheory Set Filter
open LowBody PureRankSelector PureDuplicateIntervals PureRankCounts
open FCAppendix.Affine.Uniform07
open scoped BigOperators

section Geometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem high_receipt_bids_covered
    (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0)
    (i : ι) (hi : i ∈ (T.selection κ b).1 ∩ (T.selection κ b).2) :
    Finset.univ.filter (fun j => κ*b i < b j) ⊆
      (T.selection κ b).1 ∪ (T.selection κ b).2 := by
  classical
  intro j hj
  have hhigh := (Finset.mem_filter.mp hj).2
  by_contra hjn
  have hj₀ : j ∉ (T.selection κ b).1 := fun h => hjn (Finset.mem_union_left _ h)
  have hj₁ : j ∉ (T.selection κ b).2 := fun h => hjn (Finset.mem_union_right _ h)
  have hs := Finite.optimal_swap T.residual₀
    (fun j => if j ∈ (T.selection κ b).2 then κ*b j else b j)
    _ (left_revenue_optimal T κ b hz) i j (Finset.mem_inter.mp hi).1 hj₀
  rw [if_pos (Finset.mem_inter.mp hi).2,if_neg hj₁] at hs
  exact not_lt_of_ge hs hhigh

theorem covered_receipt_card_le
    (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0)
    (i : ι) (hi : i ∈ (T.selection κ b).1 ∩ (T.selection κ b).2) :
    (Finset.univ.filter (fun j => κ*b i < b j)).card+1 ≤ T.residual₀+T.residual₁ := by
  have hs := Finset.card_le_card (high_receipt_bids_covered T κ b hz i hi)
  have hc := Finset.card_union_add_card_inter (T.selection κ b).1 (T.selection κ b).2
  have hI : 0 < ((T.selection κ b).1 ∩ (T.selection κ b).2).card :=
    Finset.card_pos.mpr ⟨i,hi⟩
  have hf := T.selection_feasible κ b
  have hleft := hf.1
  have hright := hf.2.2.1
  omega

end Geometry

section Rows
variable {N : ℕ}

theorem row_scaled_high_card {κ b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ < 1)
    (hb : 0 < b) (ω : Fin N → RowRival) :
    (Finset.univ.filter (fun j => κ*rowBids b ω 0 < rowBids b ω j)).card =
      1+lowAboveCount (κ*b) ω := by
  classical
  have hkb : κ*b < b := by nlinarith
  have hkb0 : 0 ≤ κ*b := mul_nonneg hκ hb.le
  rw [Finset.card_filter,Fin.sum_univ_succ]
  simp only [rowBids,Fin.cons_zero,Fin.cons_succ,if_pos hkb]
  rw [lowAboveCount,PiBinomial.count_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω j).1=0
  · simp [lowAboveSet,hj]
  · simp [lowAboveSet,hj,not_lt_of_ge hkb0]

theorem duplicate_requires_many_scaled_low
    (c : ℕ) {κ b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ < 1) (hb : 0 < b)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (hdup : rowPureDuplicate κ c b ω=1) :
    N+2-2*c ≤ lowBelowCount (κ*b) ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hi : (0:Fin (N+1)) ∈ (T.selection κ (rowBids b ω)).1 ∩
      (T.selection κ (rowBids b ω)).2 := by
    by_contra hn
    have hn' : ¬(0 ∈ (T.selection κ (rowBids b ω)).1 ∧
        0 ∈ (T.selection κ (rowBids b ω)).2) := fun h => hn (Finset.mem_inter.mpr h)
    change (if 0 ∈ (T.selection κ (rowBids b ω)).1 ∧
      0 ∈ (T.selection κ (rowBids b ω)).2 then (1:ℝ) else 0)=1 at hdup
    rw [if_neg hn'] at hdup
    norm_num at hdup
  have hhigh := covered_receipt_card_le T κ (rowBids b ω)
    (rowBids_outside c b ω) 0 hi
  rw [row_scaled_high_card hκ hκ1 hb ω] at hhigh
  have hf := T.selection_feasible κ (rowBids b ω)
  have hp₀ : 0 < T.residual₀ :=
    (Finset.card_pos.mpr ⟨0,(Finset.mem_inter.mp hi).1⟩).trans_le hf.1
  have hp₁ : 0 < T.residual₁ :=
    (Finset.card_pos.mpr ⟨0,(Finset.mem_inter.mp hi).2⟩).trans_le hf.2.2.1
  have hz := no_active_count_zero ω hno
  have hsum := classCounts_sum ω
  have hpart := lower_count_partition (κ*b) ω
  change 1+lowAboveCount (κ*b) ω+1 ≤
    min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)+
      min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hhigh
  change 0 < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω) at hp₀
  change 0 < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hp₁
  rw [hz,Nat.sub_zero] at hhigh hp₀ hp₁
  rw [hz] at hsum
  have h₂ := min_le_right (1+classCount 0 ω) (c-classCount 2 ω)
  have h₃ := min_le_right (1+classCount 0 ω) (c-classCount 3 ω)
  omega

end Rows

section DeletedProduct
variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

omit [MeasurableSpace Ω] in
theorem count_delete_le_one (E : Set Ω) (ω : Fin (N+1) → Ω) (i : Fin (N+1)) :
    PiBinomial.count E Finset.univ ω ≤
      1+PiBinomial.count E Finset.univ (fun j => ω (i.succAbove j)) := by
  classical
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum,Fin.sum_univ_succAbove _ i]
  split_ifs <;> omega

theorem deleted_mark_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B E : Set Ω) (hB : MeasurableSet B) (hE : MeasurableSet E)
    (k : ℕ) (i : Fin (N+1)) :
    (Measure.pi fun _ : Fin (N+1) => μ).real
      {ω | ω i ∈ B ∧ k ≤ PiBinomial.count E Finset.univ (fun j => ω (i.succAbove j))} =
        μ.real B*(Measure.pi fun _ : Fin N => μ).real
          {ω | k ≤ PiBinomial.count E Finset.univ ω} := by
  have htail : MeasurableSet {ω : Fin N → Ω | k ≤ PiBinomial.count E Finset.univ ω} :=
    (PiBinomial.measurable_count E hE Finset.univ) measurableSet_Ici
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i
  have hh := congrArg (fun ν : Measure (Ω × (Fin N → Ω)) =>
    ν (B ×ˢ {ω | k ≤ PiBinomial.count E Finset.univ ω})) hp.map_eq
  rw [Measure.map_apply hp.measurable (hB.prod htail),Measure.prod_prod] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_mul] at hr
  exact hr

theorem cluster_and_many_probability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B E : Set Ω) (hB : MeasurableSet B) (hE : MeasurableSet E) (k : ℕ) :
    (Measure.pi fun _ : Fin (N+1) => μ).real
      {ω | (∃ i, ω i ∈ B) ∧ k+1 ≤ PiBinomial.count E Finset.univ ω} ≤
        (N+1:ℕ)*μ.real B*(Measure.pi fun _ : Fin N => μ).real
          {ω | k ≤ PiBinomial.count E Finset.univ ω} := by
  let A := fun i : Fin (N+1) => {ω : Fin (N+1) → Ω |
    ω i ∈ B ∧ k ≤ PiBinomial.count E Finset.univ (fun j => ω (i.succAbove j))}
  have hs : {ω : Fin (N+1) → Ω | (∃ i, ω i ∈ B) ∧
      k+1 ≤ PiBinomial.count E Finset.univ ω} ⊆ ⋃ i, A i := by
    intro ω hω
    obtain ⟨i,hi⟩ := hω.1
    have hh := count_delete_le_one E ω i
    have hcount := hω.2
    exact mem_iUnion.mpr ⟨i,hi,by omega⟩
  calc
    _ ≤ (Measure.pi fun _ : Fin (N+1) => μ).real (⋃ i, A i) := measureReal_mono hs
    _ ≤ ∑ i, (Measure.pi fun _ : Fin (N+1) => μ).real (A i) :=
      measureReal_iUnion_fintype_le A
    _ = _ := by
      simp only [A,deleted_mark_probability μ B E hB hE k,
        Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

end DeletedProduct

section SourceMass

theorem physicalFloor_above_receipt (i : Row) {v : ℝ}
    (hv : RankCutoff.Mstar i < v) :
    (69/100:ℝ)*entry i < LowChernoff.physicalFloor i v := by
  have ht := cutoff_pos i
  have hx : 0 < x i := by cases i <;> norm_num [x,xQ]
  have he : 0 < entry i := mul_pos hx ht
  have hM : RankCutoff.Mstar i=entry i+cutoff i/200 := by
    unfold RankCutoff.Mstar entry
    ring
  have hpos : 0 ≤ v-cutoff i/200 := by rw [hM] at hv; linarith
  have hden : 0 < cutoff i/400 := by positivity
  have hclip : 1 ≤ (v-(entry i+cutoff i/400))/(cutoff i/400) := by
    apply (le_div_iff₀ hden).mpr
    rw [hM] at hv
    linarith
  unfold LowChernoff.physicalFloor
  rw [max_eq_right hpos,max_eq_right (le_trans (by norm_num) hclip),min_eq_left hclip,mul_one]
  rw [hM] at hv
  nlinarith

theorem original_floor_low_rank_bound (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {w : ℝ} (hw : w ≤ (69/100:ℝ)*entry i) :
    sourceRank (cutoff i) (G.map Prod.snd) w ≤ RankCutoff.Mstar i := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hinc : ∀ᵐ p ∂G, p.2 ≤ w → p.1 ≤ RankCutoff.Mstar i := by
    filter_upwards [hfloor] with p hp
    intro hpw
    by_contra hv
    have h := physicalFloor_above_receipt i (lt_of_not_ge hv)
    linarith
  have hm := measure_mono_ae hinc
  have hmR : G.real {p | p.2 ≤ w} ≤ G.real {p | p.1 ≤ RankCutoff.Mstar i} :=
    ENNReal.toReal_mono (measure_ne_top G _) hm
  have hsnd : G.real {p | p.2 ≤ w}=Gb.real (Iic w) := by
    change G.real {p | p.2 ≤ w}=(G.map Prod.snd).real (Iic w)
    rw [map_measureReal_apply measurable_snd measurableSet_Iic]
    rfl
  have hMt : RankCutoff.Mstar i ≤ cutoff i := by
    unfold RankCutoff.Mstar
    have hcoef : x i+1/200 ≤ 1 := by cases i <;> norm_num [x,xQ]
    nlinarith [mul_le_mul_of_nonneg_right hcoef (cutoff_pos i).le]
  have hM0 := (RankCutoff.Mstar_bounds i).1
  have hfst : G.real {p | p.1 ≤ RankCutoff.Mstar i}=RankCutoff.Mstar i/cutoff i := by
    change G.real (Prod.fst ⁻¹' Iic (RankCutoff.Mstar i))=RankCutoff.Mstar i/cutoff i
    rw [← map_measureReal_apply measurable_fst measurableSet_Iic,hvalue,
      LowChernoff.conditionalValueLaw,Measure.real,Measure.smul_apply,smul_eq_mul,
      Measure.restrict_apply measurableSet_Iic]
    have he : Iic (RankCutoff.Mstar i) ∩ Icc (0:ℝ) (cutoff i)=Icc 0 (RankCutoff.Mstar i) := by
      ext x
      simp only [mem_inter_iff,mem_Iic,mem_Icc]
      constructor
      · rintro ⟨h₁,h₂,h₃⟩
        exact ⟨h₂,h₁⟩
      · rintro ⟨h₁,h₂⟩
        exact ⟨h₂,h₁,h₂.trans hMt⟩
    rw [he,Real.volume_Icc,sub_zero,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (one_div_pos.mpr (cutoff_pos i)).le,ENNReal.toReal_ofReal hM0.le]
    ring
  rw [hsnd,hfst] at hmR
  have hh := mul_le_mul_of_nonneg_left hmR (cutoff_pos i).le
  simpa only [sourceRank,Gb,mul_div_cancel₀ _ (cutoff_pos i).ne'] using hh

theorem source_scaled_prefix_receipt (i : Row) {b : ℝ}
    (hb : b ≤ RankCutoff.Mstar i) : kappa i*b ≤ (69/100:ℝ)*entry i := by
  have hκ : 0 ≤ kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have he : kappa i*RankCutoff.Mstar i ≤ (69/100:ℝ)*entry i := by
    unfold RankCutoff.Mstar entry
    have ht := (cutoff_pos i).le
    cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ,x,xQ] at * <;> nlinarith
  exact (mul_le_mul_of_nonneg_left hb hκ).trans he

end SourceMass

theorem source_low_count_upper_remaining
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (hwHi : μ.real E ≤ (17/20000:ℝ))
    (m c N : ℕ) (hcm : 2*c ≤ m) (hNm : N ≤ m) (hkN : m-2*c ≤ N)
    (hcap : (c:ℝ) ≤ (999/2000:ℝ)*m) :
    (Measure.pi fun _ : Fin N => μ).real
      {ω | m-2*c ≤ PiBinomial.count E Finset.univ ω} ≤
        Real.exp (-(9/1000000:ℝ)*m) := by
  have h := RankUpperTail.iid_count_upper_chernoff μ E hE N (m-2*c) hkN
    (show (0:ℝ) ≤ 1/10 by norm_num)
  have hlog := RankUpperTail.source_tilt_log_bound
    (show 0 ≤ μ.real E from measureReal_nonneg) hwHi
  have hcount : ((m-2*c:ℕ):ℝ)=(m:ℝ)-2*c := by
    rw [Nat.cast_sub hcm]
    push_cast
    ring
  have hNmR : (N:ℝ) ≤ m := by exact_mod_cast hNm
  have hK : (m:ℝ)/1000 ≤ (m-2*c:ℕ) := by rw [hcount]; nlinarith
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
  have hn := mul_le_mul_of_nonneg_right hNmR (by norm_num : (0:ℝ) ≤ 901/10000000)
  nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]

end FCAppendix.Affine.Uniform06.PureDuplicateRare
