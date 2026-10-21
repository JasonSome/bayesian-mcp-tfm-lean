import FCAppendix.Affine.Uniform06.PureDuplicateIntervals
import FCAppendix.Affine.Uniform06.PureRankCounts
import FCAppendix.Affine.LowBody.FirstCopyTemplate

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureRankSelector

open MeasureTheory Set Filter LowBody PureDuplicateIntervals PureRankCounts
open scoped BigOperators

section Template
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem left_revenue_optimal (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0) :
    Finite.Optimal T.residual₀
      (fun j => if j ∈ (T.selection κ b).2 then κ*b j else b j)
      (T.selection κ b).1 := by
  classical
  have hf := T.selection_feasible κ b
  refine ⟨hf.1,fun A hA => ?_⟩
  have hm := (T.selection_nash κ b).1 (A ∩ T.support)
    ((Finset.card_le_card Finset.inter_subset_left).trans hA) Finset.inter_subset_right
  unfold CompleteInformation.revenue at hm
  have he : (∑ j ∈ A ∩ T.support, if j ∈ (T.selection κ b).2 then κ*b j else b j) =
      ∑ j ∈ A, if j ∈ (T.selection κ b).2 then κ*b j else b j := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hjn
    have hjs : j ∉ T.support := fun h => hjn (Finset.mem_inter.mpr ⟨hj,h⟩)
    simp only [hz j hjs,mul_zero,ite_self]
  rwa [he] at hm

theorem right_revenue_optimal (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0) :
    Finite.Optimal T.residual₁
      (fun j => if j ∈ (T.selection κ b).1 then κ*b j else b j)
      (T.selection κ b).2 := by
  classical
  have hf := T.selection_feasible κ b
  refine ⟨hf.2.2.1,fun A hA => ?_⟩
  have hm := (T.selection_nash κ b).2 (A ∩ T.support)
    ((Finset.card_le_card Finset.inter_subset_left).trans hA) Finset.inter_subset_right
  unfold CompleteInformation.revenue at hm
  have he : (∑ j ∈ A ∩ T.support, if j ∈ (T.selection κ b).1 then κ*b j else b j) =
      ∑ j ∈ A, if j ∈ (T.selection κ b).1 then κ*b j else b j := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hjn
    have hjs : j ∉ T.support := fun h => hjn (Finset.mem_inter.mpr ⟨hj,h⟩)
    simp only [hz j hjs,mul_zero,ite_self]
  rwa [he] at hm

theorem left_selected_iff_rank_of_right_zero
    (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0)
    (hzero : T.residual₁=0) (i : ι) (hbi : 0 < b i)
    (hne : ∀ j, j ≠ i → b i ≠ b j) :
    i ∈ (T.selection κ b).1 ↔
      (Finset.univ.filter (fun j => b i < b j)).card < T.residual₀ := by
  classical
  have hopt := T.left_optimal_of_right_zero κ b hzero hz
  constructor
  · intro hi
    by_contra hn
    exact Finite.excluded_of_many_better T.residual₀ b _ hopt i (le_of_not_gt hn) hi
  · intro hcount
    apply Finite.included_of_few_competitors T.residual₀ b _ hopt i hbi
    have he : Finset.univ.filter (fun j => j ≠ i ∧ b i ≤ b j) =
        Finset.univ.filter (fun j => b i < b j) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hji,hij⟩
        exact lt_of_le_of_ne hij (hne j hji)
      · intro hij
        exact ⟨fun he => by simp [he] at hij,hij.le⟩
    rwa [he]

theorem higher_bids_subset_selected_union
    (T : PureTemplate ι) {κ : ℝ} (hκ1 : κ ≤ 1) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0)
    (i : ι) (hbi : 0 ≤ b i)
    (hi : i ∈ (T.selection κ b).1 ∪ (T.selection κ b).2) :
    Finset.univ.filter (fun j => b i < b j) ⊆
      (T.selection κ b).1 ∪ (T.selection κ b).2 := by
  classical
  intro j hj
  have hij : b i < b j := (Finset.mem_filter.mp hj).2
  by_contra hjn
  have hj0 : j ∉ (T.selection κ b).1 := fun h => hjn (Finset.mem_union_left _ h)
  have hj1 : j ∉ (T.selection κ b).2 := fun h => hjn (Finset.mem_union_right _ h)
  have hcost : κ*b i ≤ b i := by nlinarith [mul_le_mul_of_nonneg_right hκ1 hbi]
  rcases Finset.mem_union.mp hi with hi0 | hi1
  · have hswap := Finite.optimal_swap T.residual₀
      (fun j => if j ∈ (T.selection κ b).2 then κ*b j else b j)
      _ (left_revenue_optimal T κ b hz) i j hi0 hj0
    rw [if_neg hj1] at hswap
    split_ifs at hswap <;> linarith
  · have hswap := Finite.optimal_swap T.residual₁
      (fun j => if j ∈ (T.selection κ b).1 then κ*b j else b j)
      _ (right_revenue_optimal T κ b hz) i j hi1 hj1
    rw [if_neg hj0] at hswap
    split_ifs at hswap <;> linarith

theorem selected_implies_fewer_high_bids_than_total_residual
    (T : PureTemplate ι) {κ : ℝ} (hκ1 : κ ≤ 1) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0)
    (i : ι) (hbi : 0 ≤ b i)
    (hi : i ∈ (T.selection κ b).1 ∪ (T.selection κ b).2) :
    (Finset.univ.filter (fun j => b i < b j)).card < T.residual₀+T.residual₁ := by
  classical
  let H := Finset.univ.filter (fun j => b i < b j)
  have hn : i ∉ H := by simp [H]
  have hs := higher_bids_subset_selected_union T hκ1 b hz i hbi hi
  have hsub : insert i H ⊆ (T.selection κ b).1 ∪ (T.selection κ b).2 :=
    Finset.insert_subset hi hs
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hn] at hc
  have hu := Finset.card_union_le (T.selection κ b).1 (T.selection κ b).2
  have hf := T.selection_feasible κ b
  have hf0 := hf.1
  have hf1 := hf.2.2.1
  change H.card < T.residual₀+T.residual₁
  omega

end Template

section Row
variable {N : ℕ}

def lowBelowCount (b : ℝ) (ω : Fin N → RowRival) : ℕ :=
  PiBinomial.count (lowCluster (Iic b)) Finset.univ ω

theorem lower_count_partition (b : ℝ) (ω : Fin N → RowRival) :
    lowAboveCount b ω+lowBelowCount b ω=classCount 0 ω := by
  classical
  unfold lowAboveCount lowBelowCount classCount
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hk : (ω j).1=0
  · by_cases hb : b < (ω j).2
    · simp [lowAboveSet,lowCluster,hk,hb,not_le.mpr hb]
    · simp [lowAboveSet,lowCluster,hk,hb,le_of_not_gt hb]
  · simp [lowAboveSet,lowCluster,hk]

theorem classCounts_sum (ω : Fin N → RowRival) :
    classCount 0 ω+classCount 1 ω+classCount 2 ω+classCount 3 ω=N := by
  unfold classCount
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  have he : (∑ j : Fin N, ((if (ω j).1=0 then 1 else 0)+
      (if (ω j).1=1 then 1 else 0)+(if (ω j).1=2 then 1 else 0)+
      (if (ω j).1=3 then 1 else 0))) = ∑ _j : Fin N, (1:ℕ) := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : (ω j).1=0 ∨ (ω j).1=1 ∨ (ω j).1=2 ∨ (ω j).1=3 := by omega
    rcases hj with hj|hj|hj|hj <;> simp [hj]
  rw [he]
  simp

theorem no_active_count_zero (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1) :
    classCount 1 ω=0 := by
  unfold classCount
  simp only [if_neg (hno _),Finset.sum_const_zero]

theorem otherUpper_count (ω : Fin N → RowRival) :
    PiBinomial.count otherUpper Finset.univ ω=classCount 3 ω := by
  rw [PiBinomial.count_eq_sum]
  unfold classCount
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h1 h2 h2 <;> simp_all [otherUpper]

theorem row_high_card {b : ℝ} (hb : 0 ≤ b) (ω : Fin N → RowRival) :
    (Finset.univ.filter (fun j => rowBids b ω 0 < rowBids b ω j)).card =
      lowAboveCount b ω := by
  classical
  rw [Finset.card_filter,Fin.sum_univ_succ]
  simp only [rowBids,Fin.cons_zero,Fin.cons_succ,lt_self_iff_false,if_false,zero_add]
  rw [lowAboveCount,PiBinomial.count_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω j).1=0
  · simp [lowAboveSet,hj]
  · simp [lowAboveSet,hj,not_lt_of_ge hb]

theorem row_ties_excluded {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b) :
    ∀ j : Fin (N+1), j ≠ 0 → rowBids b ω 0 ≠ rowBids b ω j := by
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · intro _
    by_cases hk : (ω k).1=0
    · simpa only [rowBids,Fin.cons_zero,Fin.cons_succ,if_pos hk] using (htie k hk).symm
    · simp only [rowBids,Fin.cons_zero,Fin.cons_succ,if_neg hk]
      exact hb.ne'

theorem pure_left_on_opposite_full_iff_rank
    (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b)
    (hother : c ≤ PiBinomial.count otherUpper Finset.univ ω) :
    (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1 ↔
      PiBinomial.count (higherAtSet b) Finset.univ ω < c := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hother' : c ≤ classCount 3 ω := by rwa [otherUpper_count] at hother
  have hzero : T.residual₁=0 := by
    simp only [T,patternTemplate,rowResidual,classCount_pattern_tags]
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)=0
    omega
  have hiff := left_selected_iff_rank_of_right_zero T κ (rowBids b ω)
    (rowBids_outside c b ω) hzero 0 (by simpa only [rowBids,Fin.cons_zero] using hb)
    (row_ties_excluded hb ω htie)
  rw [row_high_card hb.le ω] at hiff
  change 0 ∈ (T.selection κ (rowBids b ω)).1 ↔ _
  rw [hiff,higherAtCount_eq]
  have hlow := lowAboveCount_le_low b ω
  change lowAboveCount b ω < min (1+classCount 0 (patternRow (fun j => (ω j).1)))
      (c-classCount 1 (patternRow (fun j => (ω j).1))-
        classCount 2 (patternRow (fun j => (ω j).1))) ↔ _
  simp only [classCount_pattern_tags]
  omega

theorem pure_remaining_left_requires_low_below
    (c : ℕ) {κ b : ℝ} (hκ1 : κ ≤ 1) (hb : 0 ≤ b)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (hother : PiBinomial.count otherUpper Finset.univ ω < c)
    (hleft : (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1) :
    N+1-2*c ≤ lowBelowCount b ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hhigh := selected_implies_fewer_high_bids_than_total_residual T hκ1 (rowBids b ω)
    (rowBids_outside c b ω) 0 (by simpa only [rowBids,Fin.cons_zero] using hb)
    (Finset.mem_union_left _ hleft)
  rw [row_high_card hb ω] at hhigh
  have hf := T.selection_feasible κ (rowBids b ω)
  have hpos : 0 < T.residual₀ := (Finset.card_pos.mpr ⟨0,hleft⟩).trans_le hf.1
  have hc1 := no_active_count_zero ω hno
  have hcount := classCounts_sum ω
  have hpart := lower_count_partition b ω
  have hother' : classCount 3 ω < c := by rwa [otherUpper_count] at hother
  change lowAboveCount b ω <
    min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)+
      min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hhigh
  change 0 < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω) at hpos
  rw [hc1,Nat.sub_zero] at hhigh hpos
  rw [hc1] at hcount
  have hown : classCount 2 ω < c := by omega
  have hres0 := min_le_right (1+classCount 0 ω) (c-classCount 2 ω)
  have hres1 := min_le_right (1+classCount 0 ω) (c-classCount 3 ω)
  omega

theorem pure_left_rank_event_sandwich
    (c : ℕ) {κ b : ℝ} (hκ1 : κ ≤ 1) (hb : 0 < b)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b) :
    ((PiBinomial.count (higherAtSet b) Finset.univ ω < c ∧
      c ≤ PiBinomial.count otherUpper Finset.univ ω) →
      (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1) ∧
    ((0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1 →
      PiBinomial.count (higherAtSet b) Finset.univ ω < c ∨
      N+1-2*c ≤ lowBelowCount b ω) := by
  constructor
  · rintro ⟨hX,hY⟩
    exact (pure_left_on_opposite_full_iff_rank c κ hb ω htie hY).mpr hX
  · intro hleft
    by_cases hY : c ≤ PiBinomial.count otherUpper Finset.univ ω
    · exact Or.inl ((pure_left_on_opposite_full_iff_rank c κ hb ω htie hY).mp hleft)
    · exact Or.inr (pure_remaining_left_requires_low_below c hκ1 hb.le ω hno
        (lt_of_not_ge hY) hleft)

end Row
end FCAppendix.Affine.Uniform06.PureRankSelector
