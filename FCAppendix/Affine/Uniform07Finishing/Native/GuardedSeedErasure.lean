import FCAppendix.Affine.Uniform07Finishing.Native.SourceGuards
import FCAppendix.Affine.Uniform07Finishing.Native.WeightedEquivariance
import FCAppendix.Affine.Hybrid.PureRelabel

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

variable {m : ℕ} [Nonempty (Fin m)]

theorem sourcePsi_zero_of_le {d₀ z b : ℝ} (hb : b ≤ z) : sourcePsi d₀ z b = 0 := by
  simp only [sourcePsi, max_eq_left (sub_nonpos.mpr hb), zero_div]

theorem sourcePsi_le_one {d₀ z b : ℝ} (hd : 0 < d₀) : sourcePsi d₀ z b ≤ 1 := by
  unfold sourcePsi
  apply (div_le_one (hd.trans_le (le_add_of_nonneg_right (le_max_left _ _)))).mpr
  linarith

def highBidSet (z : ℝ) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => z < entryBid (L i))

omit [Nonempty (Fin m)] in
theorem sourceRejectionDemand_le_high_card {d₀ : ℝ} (hd : 0 < d₀)
    (z : ℝ) (L : LocalList m) :
    sourceRejectionDemand d₀ z L ≤ ((highBidSet z L).card : ℝ) := by
  rw [sourceRejectionDemand, highBidSet, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : z < entryBid (L i)
  · rw [if_pos hi]
    exact sourcePsi_le_one hd
  · rw [if_neg hi, sourcePsi_zero_of_le (le_of_not_gt hi)]

omit [Nonempty (Fin m)] in
theorem highBidSet_present {z : ℝ} (hz : 0 ≤ z) (L : LocalList m)
    {i : Fin m} (hi : i ∈ highBidSet z L) : L i ≠ none := by
  intro hn
  have hb := (Finset.mem_filter.mp hi).2
  rw [hn] at hb
  change z < 0 at hb
  exact not_lt_of_ge hz hb

omit [Nonempty (Fin m)] in

theorem locally_optimal_rejects_low
    {κ z : ℝ} (_hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hz : 0 ≤ z)
    (L : LocalList m) (d₀ d₁ : ℕ) (S T : Finset (Fin m))
    (hS : LocallyFeasible L d₀ S) (hT : LocallyFeasible L d₁ T)
    (hhigh : d₀+d₁ < (highBidSet z L).card)
    (hopt : ∀ D, LocallyFeasible L d₀ D →
      CompleteInformation.revenue κ (ResidualPotential.bid L) D T ≤
        CompleteInformation.revenue κ (ResidualPotential.bid L) S T)
    (i : Fin m) (hi : entryBid (L i) ≤ z) : i ∉ S := by
  intro his
  have hc : (S ∪ T).card < (highBidSet z L).card :=
    (Finset.card_union_le S T).trans_lt ((Nat.add_le_add hS.1 hT.1).trans_lt hhigh)
  obtain ⟨k,hk,hkout⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hkS : k ∉ S := fun h => hkout (Finset.mem_union_left T h)
  have hkT : k ∉ T := fun h => hkout (Finset.mem_union_right S h)
  have hkerase : k ∉ S.erase i := fun h => hkS (Finset.mem_of_mem_erase h)
  have hD : LocallyFeasible L d₀ (insert k (S.erase i)) := by
    constructor
    · rw [Finset.card_insert_of_notMem hkerase, Finset.card_erase_of_mem his]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i,his⟩
      have hScard := hS.1
      omega
    · intro l hl
      rcases Finset.mem_insert.mp hl with h | h
      · subst l
        exact highBidSet_present hz L hk
      · exact hS.2 l (Finset.mem_of_mem_erase h)
  have hh := hopt _ hD
  let r : Fin m → ℝ := fun l => if l ∈ T then κ*ResidualPotential.bid L l else ResidualPotential.bid L l
  change (∑l∈insert k (S.erase i),r l) ≤ ∑l∈S,r l at hh
  rw [Finset.sum_insert hkerase] at hh
  have hsum := Finset.sum_erase_add S r his
  have hri : r i ≤ z := by
    have hbi : ResidualPotential.bid L i ≤ z := max_le hi hz
    by_cases hit : i ∈ T
    · change (if i ∈ T then κ*ResidualPotential.bid L i else ResidualPotential.bid L i) ≤ z
      rw [if_pos hit]
      exact (mul_le_of_le_one_left (le_max_right _ _) hκ1).trans hbi
    · simpa only [r, if_neg hit] using hbi
  have hrk : z < r k := by
    have hb := (Finset.mem_filter.mp hk).2
    change z < (if k ∈ T then κ*ResidualPotential.bid L k else ResidualPotential.bid L k)
    rw [if_neg hkT]
    exact hb.trans_le (le_max_left _ _)
  linarith

theorem residual_selection_max {κ : ℝ} (hκ : 0 ≤ κ)
    (L : LocalList m) (d₀ d₁ : ℕ) (P : ResidualPotential.Pair m)
    (hP : ResidualPotential.Feasible L d₀ d₁ P) :
    CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 ≤
      CompleteInformation.potential κ (ResidualPotential.bid L)
        (ResidualPotential.selection κ L d₀ d₁).1
        (ResidualPotential.selection κ L d₀ d₁).2 := by
  have hf := ResidualPotential.selection_feasible κ hκ L d₀ d₁
  have hh := FiniteSelector.select_max (ResidualPotential.objective κ L d₀ d₁) P
  change ResidualPotential.objective κ L d₀ d₁ P ≤
    ResidualPotential.objective κ L d₀ d₁ (ResidualPotential.selection κ L d₀ d₁) at hh
  simpa only [ResidualPotential.objective, if_pos hP, if_pos hf] using hh

omit [Nonempty (Fin m)] in

theorem residual_selection_rejects_low
    {κ z : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hz : 0 ≤ z)
    (L : LocalList m) (d₀ d₁ : ℕ)
    (hhigh : d₀+d₁ < (highBidSet z L).card)
    (i : Fin m) (hi : entryBid (L i) ≤ z) :
    i ∉ (ResidualPotential.selection κ L d₀ d₁).1 ∧
      i ∉ (ResidualPotential.selection κ L d₀ d₁).2 := by
  have hf := ResidualPotential.selection_feasible κ hκ L d₀ d₁
  have hn := ResidualPotential.selection_nash κ hκ L d₀ d₁
  exact ⟨locally_optimal_rejects_low hκ hκ1 hz L d₀ d₁ _ _ hf.1 hf.2 hhigh hn.1 i hi,
    locally_optimal_rejects_low hκ hκ1 hz L d₁ d₀ _ _ hf.2 hf.1
      (by simpa only [Nat.add_comm] using hhigh) hn.2 i hi⟩

omit [Nonempty (Fin m)] in
theorem sourceGuardAlpha_pure_rejects_seed
    {ξ Λ a r U d₀ z t width ε zs : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hd₀ : 0 < d₀) (hz : 0 ≤ z)
    (hzs : zs ≤ z) (c : ℕ) (hm : 0 < m) (hε : 0 < ε)
    (X : StrictNative.ClassifiedContext m)
    (hα : 0 < (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X : ℝ))
    (i : Fin m) (hi : entryBid (X.1 i) ≤ zs) :
    i ∉ (purePair ξ c X).1 ∧ i ∉ (purePair ξ c X).2 := by
  have hg := sourceGuardAlpha_outer c hm hε X hα 3
  change ε*(m : ℝ) < sourceRejectionDemand d₀ z X.1 -
    (budget c 0 X : ℝ) - (budget c 1 X : ℝ) at hg
  have heps : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have hbound := sourceRejectionDemand_le_high_card hd₀ z X.1
  have hcard : budget c 0 X+budget c 1 X < (highBidSet z X.1).card := by
    have hh : ((budget c 0 X+budget c 1 X : ℕ) : ℝ) <
        ((highBidSet z X.1).card : ℝ) := by push_cast; linarith
    exact_mod_cast hh
  exact residual_selection_rejects_low (by linarith : 0 ≤ 1-ξ)
    (by linarith : 1-ξ ≤ 1) hz X.1 _ _ hcard i (hi.trans hzs)

omit [Nonempty (Fin m)] in
theorem highBidSet_seed_change {zs z : ℝ} (hzs : zs ≤ z)
    (L L' : LocalList m)
    (hbid : ∀ i, (entryBid (L i) ≤ zs ∧ entryBid (L' i) ≤ zs) ∨ L i = L' i) :
    highBidSet z L = highBidSet z L' := by
  ext i
  simp only [highBidSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hbid i with hl | he
  · exact iff_of_false (not_lt.mpr (hl.1.trans hzs)) (not_lt.mpr (hl.2.trans hzs))
  · rw [he]

omit [Nonempty (Fin m)] in
theorem feasible_seed_change (L L' : LocalList m) (d₀ d₁ : ℕ)
    (hpres : ∀ i, L i ≠ none ↔ L' i ≠ none) (P : ResidualPotential.Pair m) :
    ResidualPotential.Feasible L d₀ d₁ P ↔ ResidualPotential.Feasible L' d₀ d₁ P := by
  simp only [ResidualPotential.Feasible, LocallyFeasible, hpres]

omit [Nonempty (Fin m)] in
theorem potential_eq_of_selected_bids_eq (κ : ℝ) (L L' : LocalList m)
    (P : ResidualPotential.Pair m)
    (hbid : ∀ i, i ∈ P.1 ∪ P.2 → L i = L' i) :
    CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 =
      CompleteInformation.potential κ (ResidualPotential.bid L') P.1 P.2 := by
  unfold CompleteInformation.potential
  congr 1
  · exact Finset.sum_congr rfl (fun i hi => congrArg (fun b => max (entryBid b) 0) (hbid i hi))
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun b => max (entryBid b) 0)
      (hbid i (Finset.mem_union_left _ (Finset.mem_inter.mp hi).1))

theorem residual_selection_focalCopy_seed_change
    {κ zs z : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (hz : 0 ≤ z) (hzs : zs ≤ z)
    (L L' : LocalList m) (d₀ d₁ : ℕ)
    (hpres : ∀ i, L i ≠ none ↔ L' i ≠ none)
    (hbid : ∀ i, (entryBid (L i) ≤ zs ∧ entryBid (L' i) ≤ zs) ∨ L i = L' i)
    (hhigh : d₀+d₁ < (highBidSet z L).card) (i : Fin m)
    (hgeneric : ∀ P Q : ResidualPotential.Pair m,
      ResidualPotential.Feasible L d₀ d₁ P → ResidualPotential.Feasible L d₀ d₁ Q →
      CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 =
        CompleteInformation.potential κ (ResidualPotential.bid L) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    focalCopy (ResidualPotential.selection κ L d₀ d₁) i =
      focalCopy (ResidualPotential.selection κ L' d₀ d₁) i := by
  let P := ResidualPotential.selection κ L d₀ d₁
  let Q := ResidualPotential.selection κ L' d₀ d₁
  have hp := ResidualPotential.selection_feasible κ hκ L d₀ d₁
  have hq' := ResidualPotential.selection_feasible κ hκ L' d₀ d₁
  have hp' : ResidualPotential.Feasible L' d₀ d₁ P :=
    (feasible_seed_change L L' d₀ d₁ hpres P).mp hp
  have hq : ResidualPotential.Feasible L d₀ d₁ Q :=
    (feasible_seed_change L L' d₀ d₁ hpres Q).mpr hq'
  have hhigh' : d₀+d₁ < (highBidSet z L').card := by
    rwa [← highBidSet_seed_change hzs L L' hbid]
  have hPbid : ∀ k, k ∈ P.1 ∪ P.2 → L k = L' k := by
    intro k hk
    rcases hbid k with hl | he
    · have hn := residual_selection_rejects_low hκ hκ1 hz L d₀ d₁ hhigh k (hl.1.trans hzs)
      exact False.elim ((Finset.mem_union.mp hk).elim hn.1 hn.2)
    · exact he
  have hQbid : ∀ k, k ∈ Q.1 ∪ Q.2 → L k = L' k := by
    intro k hk
    rcases hbid k with hl | he
    · have hn := residual_selection_rejects_low hκ hκ1 hz L' d₀ d₁ hhigh' k (hl.2.trans hzs)
      exact False.elim ((Finset.mem_union.mp hk).elim hn.1 hn.2)
    · exact he
  have heP := potential_eq_of_selected_bids_eq κ L L' P hPbid
  have heQ := potential_eq_of_selected_bids_eq κ L L' Q hQbid
  have hPQ := residual_selection_max hκ L' d₀ d₁ P hp'
  have hQP := residual_selection_max hκ L d₀ d₁ Q hq
  change CompleteInformation.potential κ (ResidualPotential.bid L') P.1 P.2 ≤
    CompleteInformation.potential κ (ResidualPotential.bid L') Q.1 Q.2 at hPQ
  rw [← heP, ← heQ] at hPQ
  exact hgeneric P Q hp hq (le_antisymm hPQ hQP)

omit [Nonempty (Fin m)] in

theorem clipped_marginal_seed_change
    {ξ B z zs : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (hguard : (1-ξ)*B ≤ z) (hzs : zs ≤ z)
    (L L' : LocalList m) (E : Finset (Fin m)) (d : ℕ)
    (hB : ∀ i, entryBid (L i) ≤ B) (hB' : ∀ i, entryBid (L' i) ≤ B)
    (hB0 : 0 ≤ B)
    (hbid : ∀ i, (entryBid (L i) ≤ zs ∧ entryBid (L' i) ≤ zs) ∨ L i = L' i)
    (hroot : (∑i,ClippedResidual.exposure ξ z (listBids (remainder L E) i)) = (d : ℝ)) :
    EqualCapacity.positiveMarginal ξ d (listBids (remainder L E)) =
      EqualCapacity.positiveMarginal ξ d (listBids (remainder L' E)) := by
  have he (i : Fin m) : ClippedResidual.exposure ξ z (listBids (remainder L E) i) =
      ClippedResidual.exposure ξ z (listBids (remainder L' E) i) := by
    rw [remainder_bid, remainder_bid]
    by_cases hi : i ∈ E
    · rw [if_pos hi, if_pos hi]
    · rw [if_neg hi, if_neg hi, listBids_eq_entry, listBids_eq_entry]
      rcases hbid i with hl | he
      · rw [ClippedResidual.exposure_zero (hl.1.trans hzs),
          ClippedResidual.exposure_zero (hl.2.trans hzs)]
      · rw [he]
  have hr' : (∑i,ClippedResidual.exposure ξ z (listBids (remainder L' E) i)) = (d : ℝ) := by
    simpa only [← he] using hroot
  have hb : ∀ i, listBids (remainder L E) i ≤ B := by
    intro i
    rw [remainder_bid]
    split_ifs
    · exact hB0
    · simpa only [listBids_eq_entry] using hB i
  have hb' : ∀ i, listBids (remainder L' E) i ≤ B := by
    intro i
    rw [remainder_bid]
    split_ifs
    · exact hB0
    · simpa only [listBids_eq_entry] using hB' i
  rw [canonical_eq_clipped_at_root _ d hξ hξ1 hz hguard hb hroot,
    canonical_eq_clipped_at_root _ d hξ hξ1 hz hguard hb' hr']
  exact funext he

theorem literal_sourcePlan_clipped_root (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (μseed : Measure ℝ)
    (X : StrictNative.ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (E : Finset (Fin m))
    (hE : sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.cutoff row/2) c μseed
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X = some E) :
    ∃ y ∈ Icc (Λ-Early.nativeRadius row) (Λ+Early.nativeRadius row),
      ClippedResidual.remainingDemand (Uniform07.xi row) (fun k => entryBid (X.1 k)) E y =
        (commonBudget c X : ℝ) ∧
      EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
        (listBids (remainder X.1 E)) =
          ClippedResidual.smallMarginal (Uniform07.xi row) y (fun k => entryBid (X.1 k)) E := by
  let α : StrictNative.ClassifiedContext m → unitInterval := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
    zG (Uniform07.cutoff row) width ε c
  have hα : 0 < (α X : ℝ) := sourcePlan_some_alpha_pos _ _ _ _ _ c μseed α X E hE
  have ho := sourceGuardAlpha_outer c hm hε X hα
  have hlo := ho 0
  have hhi := ho 1
  simp only [sourceSlacks, Matrix.cons_val_zero, Matrix.cons_val_one] at hlo hhi
  have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have ha : 0 < Early.nativeRadius row := (Early.native_sampling_margin_guards row).1
  have hκ : Uniform07.kappa row = 1-Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.kappa, Uniform07.kappaQ, Uniform07.xi, Uniform07.xiQ]
  have hξ1 : Uniform07.xi row < 1 := by
    cases row <;> norm_num [Uniform07.xi, Uniform07.xiQ, Uniform07.etaQ]
  have hl0 : 0 < Λ-Early.nativeRadius row :=
    (mul_pos (by rw [hκ]; linarith) hR).trans hguard
  have hdn : 0 < commonBudget c X := by
    have hn : 0 ≤ sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 :=
      Finset.sum_nonneg (fun k _ => ClippedResidual.exposure_nonneg
        (Uniform07.xi_pos row) (by linarith))
    have hh : (0 : ℝ) < commonBudget c X := by linarith
    exact_mod_cast hh
  obtain ⟨hcard,hmarg⟩ := sourcePlan_exclusive_margin row hΛ c μseed α X E hE
  have hl : (commonBudget c X : ℝ)+(E.card : ℝ)+ε*m <
      ∑k,ClippedResidual.exposure (Uniform07.xi row) (Λ-Early.nativeRadius row)
        (entryBid (X.1 k)) := by
    rw [hcard]
    change _ < sourceDemand (Uniform07.xi row) (Λ-Early.nativeRadius row) X.1
    linarith
  have hh : (∑k,ClippedResidual.exposure (Uniform07.xi row) (Λ+Early.nativeRadius row)
      (entryBid (X.1 k))) < (commonBudget c X : ℝ)-ε*m := by
    change sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 < _
    linarith
  exact (source_U4_passes_native_test X.1 hX (budget c 0 X) (budget c 1 X) E
    (Uniform07.xi_pos row) hξ1 hR hl0 (by linarith) (by rwa [← hκ]) hbid hdn hs
    hcard hl hh (fun k hk => by linarith [hmarg k hk])).2

theorem literal_sourcePlan_clipped_seed_change (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (μseed : Measure ℝ)
    (X : StrictNative.ClassifiedContext m) (L' : LocalList m)
    (hX : NonnegativeList X.1)
    (hbid : ∀ k, entryBid (X.1 k) ≤ R) (hbid' : ∀ k, entryBid (L' k) ≤ R)
    (hchange : ∀ k,
      (entryBid (X.1 k) ≤ Uniform07.cutoff row/2 ∧ entryBid (L' k) ≤ Uniform07.cutoff row/2) ∨
        X.1 k = L' k)
    (E : Finset (Fin m))
    (hE : sourcePlan (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.cutoff row/2) c μseed
      (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c) X = some E) :
    EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
      (listBids (remainder X.1 E)) =
        EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
          (listBids (remainder L' E)) := by
  obtain ⟨y,hy,hr,he⟩ := literal_sourcePlan_clipped_root row hΛ hR hguard hm hε c μseed X hX hbid E hE
  have hlow := ((Early.native_sampling_margin_guards row).2 Λ hΛ).1
  have h52 : (52/100 : ℝ)*Uniform07.cutoff row < Λ-Early.nativeRadius row :=
    (le_max_right _ _).trans_lt hlow
  have ht := Uniform07.cutoff_pos row
  have hy0 : 0 < y := by linarith [hy.1]
  have hseed : Uniform07.cutoff row/2 ≤ y := by linarith [hy.1]
  have hκ : Uniform07.kappa row = 1-Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.kappa, Uniform07.kappaQ, Uniform07.xi, Uniform07.xiQ]
  have hξ1 : Uniform07.xi row < 1 := by
    cases row <;> norm_num [Uniform07.xi, Uniform07.xiQ, Uniform07.etaQ]
  have hroot : (∑k,ClippedResidual.exposure (Uniform07.xi row) y
      (listBids (remainder X.1 E) k)) = (commonBudget c X : ℝ) := by
    calc
      _ = ClippedResidual.remainingDemand (Uniform07.xi row) (fun k => entryBid (X.1 k)) E y := by
        unfold ClippedResidual.remainingDemand
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ E
        · simp [remainder_bid, hk, ClippedResidual.exposure_zero hy0.le]
        · simp only [listBids_eq_entry, remainder_entry, if_neg hk]
      _ = _ := hr
  apply clipped_marginal_seed_change (Uniform07.xi_pos row) hξ1 hy0
    (by rw [← hκ]; exact hguard.le.trans hy.1) hseed X.1 L' E (commonBudget c X)
    hbid hbid' hR.le hchange hroot

end FCAppendix.Affine.Uniform07Finishing.Weighted
