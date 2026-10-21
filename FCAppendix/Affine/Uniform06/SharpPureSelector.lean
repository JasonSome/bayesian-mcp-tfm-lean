import FCAppendix.Affine.Uniform06.PureUnionUpper

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpPureSelector

open MeasureTheory Set Filter LowBody LiteralExperiment
open PureRankSelector PureDuplicateIntervals PureRankCounts PurePivotalSource PureUnionUpper
open scoped BigOperators

section Template
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_iff_total_rank
    (T : PureTemplate ι) {κ : ℝ} (hκ1 : κ ≤ 1) (b : ι → ℝ)
    (hz : ∀ j, j ∉ T.support → b j=0) (i : ι) (hbi : 0 < b i)
    (hsecond : ∀ j, j ≠ i → κ*b j < b i)
    (hne : ∀ j, j ≠ i → b i ≠ b j) :
    i ∈ (T.selection κ b).1 ∪ (T.selection κ b).2 ↔
      (Finset.univ.filter (fun j => b i < b j)).card < T.residual₀+T.residual₁ := by
  classical
  constructor
  · exact selected_implies_fewer_high_bids_than_total_residual T hκ1 b hz i hbi.le
  · intro hcount
    by_contra hi
    let A := (T.selection κ b).1
    let B := (T.selection κ b).2
    have hiA : i ∉ A := fun h => hi (Finset.mem_union_left _ h)
    have hiB : i ∉ B := fun h => hi (Finset.mem_union_right _ h)
    have hiA' : i ∉ (T.selection κ b).1 := hiA
    have hiB' : i ∉ (T.selection κ b).2 := hiB
    have hA := left_revenue_optimal T κ b hz
    have hB := right_revenue_optimal T κ b hz
    have hfillA : A.card=T.residual₀ :=
      Finite.optimal_fills T.residual₀ _ A hA i hiA (by simpa only [if_neg hiB'] using! hbi)
    have hfillB : B.card=T.residual₁ :=
      Finite.optimal_fills T.residual₁ _ B hB i hiB (by simpa only [if_neg hiA'] using! hbi)
    have hswapA (j : ι) (hj : j ∈ A) : b i ≤ if j ∈ B then κ*b j else b j := by
      simpa only [if_neg hiB'] using! Finite.optimal_swap T.residual₀ _ A hA j i hj hiA
    have hswapB (j : ι) (hj : j ∈ B) : b i ≤ if j ∈ A then κ*b j else b j := by
      simpa only [if_neg hiA'] using! Finite.optimal_swap T.residual₁ _ B hB j i hj hiB
    have hdis : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro j hjA hjB
      have hji : j ≠ i := fun he => hiA (he ▸ hjA)
      have hs := hswapA j hjA
      rw [if_pos hjB] at hs
      exact not_lt_of_ge hs (hsecond j hji)
    have hsub : A ∪ B ⊆ Finset.univ.filter (fun j => b i < b j) := by
      intro j hj
      have hji : j ≠ i := fun he => hi (he ▸ hj)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hj with hjA | hjB
      · have hjn : j ∉ B := Finset.disjoint_left.mp hdis hjA
        have hs := hswapA j hjA
        rw [if_neg hjn] at hs
        exact lt_of_le_of_ne hs (hne j hji)
      · have hjn : j ∉ A := fun h => Finset.disjoint_left.mp hdis h hjB
        have hs := hswapB j hjB
        rw [if_neg hjn] at hs
        exact lt_of_le_of_ne hs (hne j hji)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis,hfillA,hfillB] at hcard
    omega

end Template

section Row
variable {N : ℕ}

theorem row_first_iff_total_rank
    (c : ℕ) {κ U b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hb : 0 < b) (hcross : κ*U < b) (ω : Fin N → RowRival)
    (hcap : ∀ j, (ω j).1=0 → (ω j).2 ≤ U)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b) :
    (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1 ∪ (rowPureSelection κ c b ω).2 ↔
      lowAboveCount b ω < rowResidual c 0 ω+rowResidual c 1 ω := by
  have hsecond : ∀ j : Fin (N+1), j ≠ 0 → κ*rowBids b ω j < rowBids b ω 0 := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · intro _
      by_cases hk : (ω k).1=0
      · simpa only [rowBids,Fin.cons_zero,Fin.cons_succ,if_pos hk] using
          (mul_le_mul_of_nonneg_left (hcap k hk) hκ).trans_lt hcross
      · simpa only [rowBids,Fin.cons_zero,Fin.cons_succ,if_neg hk,mul_zero] using hb
  have hh := first_iff_total_rank (patternTemplate c (fun j => (ω j).1)) hκ1
    (rowBids b ω) (rowBids_outside c b ω) 0
    (by simpa only [rowBids,Fin.cons_zero] using hb) hsecond (row_ties_excluded hb ω htie)
  rw [row_high_card hb.le ω] at hh
  exact hh

theorem row_first_count_formula
    (c : ℕ) {κ U b : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hb : 0 < b) (hcross : κ*U < b) (ω : Fin N → RowRival)
    (hcap : ∀ j, (ω j).1=0 → (ω j).2 ≤ U)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b) :
    rowUnequalPureFirst κ c b ω=
      if rowResidual c 0 ω≠rowResidual c 1 ω ∧
        lowAboveCount b ω < rowResidual c 0 ω+rowResidual c 1 ω then 1 else 0 := by
  unfold rowUnequalPureFirst
  rw [first_eq_indicator]
  simp only [row_first_iff_total_rank c hκ hκ1 hb hcross ω hcap htie]
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω <;>
    by_cases hc : lowAboveCount b ω < rowResidual c 0 ω+rowResidual c 1 ω <;> simp [he,hc]

theorem first_acquisition_crosses_ordinary_low
    (c : ℕ) {κ U x y : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hx : 0 < x) (hxy : x < y) (hcross : κ*U < x)
    (ω : Fin N → RowRival)
    (hcap : ∀ j, (ω j).1=0 → (ω j).2 ≤ U)
    (htx : ∀ j, (ω j).1=0 → (ω j).2 ≠ x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2 ≠ y)
    (hxfirst : rowUnequalPureFirst κ c x ω=0)
    (hyfirst : rowUnequalPureFirst κ c y ω=1) :
    ∃ j, (ω j).1=0 ∧ (ω j).2 ∈ Ioc x y := by
  have hxform := row_first_count_formula c hκ hκ1 hx hcross ω hcap htx
  have hyform := row_first_count_formula c hκ hκ1 (hx.trans hxy) (hcross.trans hxy) ω hcap hty
  have hcnt : lowAboveCount y ω < lowAboveCount x ω := by
    rw [hxfirst] at hxform
    rw [hyfirst] at hyform
    have hycond : rowResidual c 0 ω≠rowResidual c 1 ω ∧
        lowAboveCount y ω < rowResidual c 0 ω+rowResidual c 1 ω := by
      by_contra hn
      rw [if_neg hn] at hyform
      norm_num at hyform
    have hxnot : ¬(rowResidual c 0 ω≠rowResidual c 1 ω ∧
        lowAboveCount x ω < rowResidual c 0 ω+rowResidual c 1 ω) := by
      intro hx
      rw [if_pos hx] at hxform
      norm_num at hxform
    exact hycond.2.trans_le (le_of_not_gt fun hx => hxnot ⟨hycond.1,hx⟩)
  by_contra hn
  have he : lowAboveCount x ω=lowAboveCount y ω := by
    unfold lowAboveCount
    rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply propext
    constructor
    · rintro ⟨hk,hb⟩
      refine ⟨hk,?_⟩
      by_contra hy
      exact hn ⟨j,hk,hb,le_of_not_gt hy⟩
    · rintro ⟨hk,hb⟩
      exact ⟨hk,hxy.trans hb⟩
  omega

theorem both_under_first_acquisition_event
    (c : ℕ) {κ U x y : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hx : 0 < x) (hxy : x < y) (hcross : κ*U < x)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (hcap : ∀ j, (ω j).1=0 → (ω j).2 ≤ U)
    (htx : ∀ j, (ω j).1=0 → (ω j).2 ≠ x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2 ≠ y)
    (hleft : classCount 2 ω< c) (hright : classCount 3 ω< c)
    (hxfirst : rowUnequalPureFirst κ c x ω=0)
    (hyfirst : rowUnequalPureFirst κ c y ω=1) :
    (∃ j, ω j ∈ lowCluster (Ioc x y)) ∧ N+1-2*c ≤ lowBelowCount y ω := by
  refine ⟨first_acquisition_crosses_ordinary_low c hκ hκ1 hx hxy hcross
    ω hcap htx hty hxfirst hyfirst,?_⟩
  have hsel : (0:Fin (N+1)) ∈ (rowPureSelection κ c y ω).1 ∪ (rowPureSelection κ c y ω).2 := by
    unfold rowUnequalPureFirst at hyfirst
    split_ifs at hyfirst
    · norm_num at hyfirst
    · rw [first_eq_indicator] at hyfirst
      split_ifs at hyfirst with hs
      · exact hs
      · norm_num at hyfirst
  rcases Finset.mem_union.mp hsel with hL | hR
  · apply pure_remaining_left_requires_low_below c hκ1 (hx.trans hxy).le ω hno ?_ hL
    simpa only [otherUpper_count] using hright
  · exact right_remaining_requires_low_below c hκ1 (hx.trans hxy).le ω hno hleft hR

end Row
end FCAppendix.Affine.Uniform06.SharpPureSelector
