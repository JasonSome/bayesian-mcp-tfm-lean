import FCAppendix.Exclusive.SourceLowTypeSmallBid
import FCAppendix.Exclusive.SourceLowTypePayoff
import FCAppendix.Exclusive.SourceLowTypeCountTail

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Global
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def BandRivals (lower upper : ℝ) (i : Fin m) (d : UserProfile m n) : Prop :=
  ∀ j, j ≠ i → (d j).1.2.routeCount = 0 ∨
    ((d j).1.2.routeCount = n ∧ (d j).1.2.bid ∈ Icc lower upper)

theorem BandRivals.highRivals {lower upper : ℝ} {i : Fin m} {d : UserProfile m n}
    (hd : BandRivals lower upper i d) : HighRivals lower i d := by
  intro j hj
  rcases hd j hj with hz | ⟨hr,hb⟩
  · exact Or.inl hz
  · exact Or.inr ⟨hr,hb.1⟩

theorem focalList_rival_band {lower upper : ℝ} (i : Fin m) (b : ℝ)
    (d : UserProfile m n) (hd : BandRivals lower upper i d) :
    ∀ j, j ≠ i → listBids (focalList i b d) j = 0 ∨
      listBids (focalList i b d) j ∈ Icc lower upper := by
  classical
  intro j hji
  rcases hd j hji with hz | ⟨_,hb⟩
  · exact Or.inl (by simp [listBids,focalList,readBid,hji,hz])
  · by_cases hk : (d j).1.2.routeCount = 0
    · exact Or.inl (by simp [listBids,focalList,readBid,hji,hk])
    · exact Or.inr (by simpa [listBids,focalList,readBid,hji,hk] using hb)

theorem positiveRival_card_focalList (i : Fin m) (b : ℝ) (d : UserProfile m n)
    {lower : ℝ} (hlo : 0 < lower) (hd : HighRivals lower i d) :
    Fintype.card (PositiveRival (listBids (focalList i b d)) i) = (activeRivals i d).card := by
  classical
  have hmem (j : Fin m) : (j ≠ i ∧ 0 < listBids (focalList i b d) j) ↔
      j ∈ activeRivals i d := by
    by_cases hji : j = i
    · simp [hji,activeRivals]
    · rcases hd j hji with hz | ⟨_,hfloor⟩
      · simp [listBids,focalList,readBid,hji,hz,activeRivals]
      · by_cases hk : (d j).1.2.routeCount = 0
        · simp [listBids,focalList,readBid,hji,hk,activeRivals]
        · have hp := hlo.trans_le hfloor
          simp [listBids,focalList,readBid,hji,hk,activeRivals,hp]
  let e : PositiveRival (listBids (focalList i b d)) i ≃ activeRivals i d :=
    { toFun := fun j => ⟨j.val,(hmem j.val).mp j.property⟩
      invFun := fun j => ⟨j.val,(hmem j.val).mpr j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem activeRivals_card_eq_submittedRivals (i : Fin (m+1)) (d : UserProfile (m+1) n) :
    (activeRivals i d).card = submittedRivals i d := by
  classical
  let T := {j : Fin m // (d (i.succAbove j)).1.2.routeCount ≠ 0}
  let f : T → activeRivals i d := fun j =>
    ⟨i.succAbove j.val,(mem_activeRivals i _ d).mpr ⟨Fin.succAbove_ne _ _,j.property⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j l he
      apply Subtype.ext
      exact Fin.succAbove_right_injective (congrArg Subtype.val he)
    · intro j
      obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq ((mem_activeRivals i j.val d).mp j.property).1
      refine ⟨⟨k,?_⟩,?_⟩
      · simpa only [hk] using ((mem_activeRivals i j.val d).mp j.property).2
      · exact Subtype.ext hk
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_coe] at hcard
  rw [← hcard]
  change Fintype.card {j : Fin m // (d (i.succAbove j)).1.2.routeCount ≠ 0} = _
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [submittedRivals,submissions,ite_not]

theorem actual_price_bad_le_count_bad (Γ : FiniteGame (m+1) n c Seed)
    (i : Fin (m+1)) (hn : 2 ≤ n) (hc : 0 < c)
    (h eta lower upper lowerPrice upperPrice : ℝ) (hlo : 0 < lower)
    (hd : ∀ᵐ d ∂userProfileLaw Γ, BandRivals lower upper i d)
    (hscalar : ∀ N : ℕ, N ≤ m → |((N : ℝ)+1)/((m : ℝ)+1)-h| < eta →
      c < N ∧
      lowerPrice ≤ lower*(((N : ℝ)-c)/N)^(n-1) ∧
      upper*(((N : ℝ)-c+1)/N)^(n-1) ≤ upperPrice)
    (b : ℝ) :
    (userProfileLaw Γ).real {d | focalPrice n hn c i b d ∉ Icc lowerPrice upperPrice} ≤
      (userProfileLaw Γ).real
        {d | eta ≤ |(1+(submittedRivals i d : ℝ))/((m : ℝ)+1)-h|} := by
  have hsubset : {d | focalPrice n hn c i b d ∉ Icc lowerPrice upperPrice} ≤ᵐ[userProfileLaw Γ]
      {d | eta ≤ |(1+(submittedRivals i d : ℝ))/((m : ℝ)+1)-h|} := by
    filter_upwards [hd] with d hd hbad
    by_contra hnot
    have hgood : |((submittedRivals i d : ℝ)+1)/((m : ℝ)+1)-h| < eta := by
      simpa only [add_comm] using lt_of_not_ge hnot
    have hcount : submittedRivals i d ≤ m := by
      rw [← activeRivals_card_eq_submittedRivals i d]
      have hh := Finset.card_le_card (Finset.filter_subset
        (fun j => (d j).1.2.routeCount ≠ 0) (Finset.univ.erase i))
      simpa [activeRivals,Finset.card_erase_of_mem (Finset.mem_univ i)] using hh
    have hs := hscalar (submittedRivals i d) hcount hgood
    have hN := (positiveRival_card_focalList i b d hlo hd.highRivals).trans
      (activeRivals_card_eq_submittedRivals i d)
    have hp := canonical_native_price_bracket n c hn hc (listBids (focalList i b d)) i
      lower upper hlo (focalList_rival_band i b d hd) (by simpa only [hN] using hs.1)
    rw [hN] at hp
    exact hbad ⟨hs.2.1.trans hp.1,hp.2.trans hs.2.2⟩
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae hsubset)

end FCAppendix.Bayes.ExclusiveSource
