import FCAppendix.Exclusive.SourceLowTypePolicy
import FCAppendix.Exclusive.NarrowGlobalGuardsPrice

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set
open Exclusive.Narrow.Global
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem listBids_eq_getD (ℓ : LocalList m) (i : Fin m) : listBids ℓ i = (ℓ i).getD 0 := by
  cases hh : ℓ i <;> simp [listBids,readBid,hh]

theorem mem_positives_iff (ℓ : LocalList m) (i : Fin m) :
    i ∈ Marker.positives ℓ ↔ 0 < listBids ℓ i := by
  classical
  simp [Marker.positives,listBids_eq_getD]

theorem positiveCount_list (ℓ : LocalList m) :
    positiveCount (listBids ℓ) = (Marker.positives ℓ).card := by
  let e : PositiveIndex (listBids ℓ) ≃ Marker.positives ℓ :=
    { toFun := fun j => ⟨j.val,(mem_positives_iff ℓ j.val).mpr j.property⟩
      invFun := fun j => ⟨j.val,(mem_positives_iff ℓ j.val).mp j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [positiveCount,Fintype.card_coe] using Fintype.card_congr e

theorem positiveRival_card_list (ℓ : LocalList m) (i : Fin m)
    (hi : i ∈ Marker.positives ℓ) :
    Fintype.card (PositiveRival (listBids ℓ) i)+1 = (Marker.positives ℓ).card := by
  classical
  let e : PositiveRival (listBids ℓ) i ≃ (Marker.positives ℓ).erase i :=
    { toFun := fun j => ⟨j.val,Finset.mem_erase.mpr
        ⟨j.property.1,(mem_positives_iff ℓ j.val).mpr j.property.2⟩⟩
      invFun := fun j => ⟨j.val,(Finset.mem_erase.mp j.property).1,
        (mem_positives_iff ℓ j.val).mp (Finset.mem_erase.mp j.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh : Fintype.card (PositiveRival (listBids ℓ) i) = ((Marker.positives ℓ).erase i).card :=
    (Fintype.card_congr e).trans (Fintype.card_coe _)
  rw [hh,Finset.card_erase_of_mem hi]
  have := Finset.card_pos.mpr ⟨i,hi⟩
  omega

theorem canonical_low_marginal_zero (hn : 2 ≤ n) (hc : 0 < c)
    (ℓ : LocalList m) (i : Fin m) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hentry : listBids ℓ i = b)
    (hhigh : ∀ j ∈ Marker.positives ℓ, j ≠ i → a ≤ listBids ℓ j)
    (hlarge : n*c < (Marker.positives ℓ).card)
    (hbid : b < a*(1-1/(n:ℝ))^(n-1)) :
    canonicalMarginal n hn c (listBids ℓ) i = 0 := by
  have hi : i ∈ Marker.positives ℓ := (mem_positives_iff ℓ i).mpr (hentry ▸ hb)
  have hcard := positiveRival_card_list ℓ i hi
  have hN : n*c ≤ Fintype.card (PositiveRival (listBids ℓ) i) := by omega
  have hover : c < positiveCount (listBids ℓ) := by
    rw [positiveCount_list]
    have hmul : c ≤ n*c := by nlinarith
    omega
  obtain ⟨_,hroot⟩ := canonicalPrice_overloaded n hn c (listBids ℓ) hover
  rw [totalDemand_eq_focal_positiveRivals,activeDemand,hentry,if_pos hb] at hroot
  have hz := LowType.many_high_rivals_reject_low_bid n c hn hc hN
    (fun j : PositiveRival (listBids ℓ) i => listBids ℓ j.val) ha
    (fun j => hhigh j.val ((mem_positives_iff ℓ j.val).mpr j.property.2) j.property.1)
    hb (canonicalPrice_nonneg n hn c (listBids ℓ))
    (by simpa only [add_comm] using hroot) hbid
  simpa only [canonicalMarginal,activeDemand,hentry,if_pos hb] using hz

theorem seedLottery_marginal_zero_of_rejects (Γ : FiniteGame m n c Seed)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m)
    (h : ∀ s, i ∉ (Γ.policy j ℓ s).val) :
    Proposer.marginal (seedLottery Γ j ℓ) i = 0 := by
  apply CommonList.marginal_eq_zero_of_forall
  intro S hS his
  obtain ⟨s,rfl⟩ := seedLottery_support_exists Γ j ℓ S hS
  exact h s his

theorem source_low_marginal_zero (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hentry : listBids ℓ i = b)
    (hlow : Marker.lows cutoff ℓ = {i}) (hzero : Marker.zeros ℓ = ∅)
    (hdist : Set.InjOn (fun l => (ℓ l).getD 0) (Marker.positives ℓ))
    (hhigh : ∀ l ∈ Marker.positives ℓ, l ≠ i → a ≤ listBids ℓ l)
    (hcut : cutoff ≤ a*(1-1/(n:ℝ))^(n-1)) (hbid : b < cutoff) :
    Proposer.marginal (seedLottery Γ j ℓ) i = 0 := by
  classical
  by_cases hsmall : (Marker.positives ℓ).card ≤ n*c
  · have helig : Marker.SourceEligible hm cutoff ℓ n c := by
      rw [Marker.sourceEligible_iff]
      refine ⟨?_,hdist⟩
      simp only [Marker.Eligible,Marker.EligibleCode,hlow,hzero,Finset.card_singleton,
        Finset.card_empty]
      exact ⟨hsmall,trivial,by omega⟩
    apply seedLottery_marginal_zero_of_rejects
    intro s
    rw [hpolicy]
    exact Marker.sourceContinuation_rejects_role_zero hm hn hc cutoff fallback ℓ
      helig i hlow hzero s
  · have helig : ¬ Marker.SourceEligible hm cutoff ℓ n c := fun h => hsmall h.1.1
    have he : (fun s => (Γ.policy j ℓ s).val) = fun s => (fallback ℓ s).val := by
      funext s
      rw [hpolicy]
      simp only [Marker.sourceContinuation,dif_neg helig]
    have hlaw : seedLottery Γ j ℓ = canonicalLottery n hn c (listBids ℓ) := by
      unfold seedLottery
      convert hcanonical ℓ using 1
      congr 1
    rw [hlaw,canonicalLottery_marginal]
    exact canonical_low_marginal_zero hn hc ℓ i ha hb hentry hhigh
      (lt_of_not_ge hsmall) (hbid.trans_le hcut)

end FCAppendix.Bayes.ExclusiveSource
