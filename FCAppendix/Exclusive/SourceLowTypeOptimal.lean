import FCAppendix.Exclusive.SourceLowTypeRejection

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exclusiveTariffPayoff_zero_routes (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) (a : JointAction n)
    (ha : a.routeCount = 0) : exclusiveTariffPayoff Γ tariff i v a = 0 := by
  rw [exclusiveTariffPayoff_eq_test,problem_outcome,CountLaw.expect_ofMeasure]
  have hz (omega : Sample m n Seed) : (focalCount Γ i a omega).val = 0 := by
    have hh := focalCount_le Γ i a omega
    omega
  simp [hz,payoffTest,successIndicator,Γ.G.zero]

theorem source_low_bestResponse (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (tariff : UserTariff) (ha : tariff.Allowed) (i : Fin m)
    {highFloor lowerPrice upperPrice lowUpper : ℝ} (hhigh : 0 < highFloor)
    (hcutfloor : cutoff ≤ highFloor)
    (hthreshold : cutoff ≤ highFloor*(1-1/(n:ℝ))^(n-1))
    (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals highFloor i d ∧
      Set.InjOn (fun j => (d j).1.2.bid) (activeRivals i d))
    (hlo : 0 < lowerPrice) (hlohi : lowerPrice ≤ upperPrice)
    (hcut : upperPrice < cutoff) (hL : 0 ≤ lowUpper)
    (hlow : lowUpper < min cutoff lowerPrice)
    (hbad : ∀ b ≥ cutoff, (userProfileLaw Γ).real
      {d | focalPrice n hn c i b d ∉ Icc lowerPrice upperPrice} <
      (demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper))/
        (lowUpper+demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper)))
    (v : ℝ) (hv : v-Γ.g ≤ lowUpper) :
    ExclusiveTariffBestResponse Γ tariff i v (Interim.abstain n) := by
  intro act
  rw [exclusiveTariffPayoff_abstain]
  by_cases hk : act.routeCount = 0
  · exact (exclusiveTariffPayoff_zero_routes Γ tariff i v act hk).le
  · by_cases hb : act.bid < cutoff
    · exact (source_actual_small_bid_zero Γ hm hn hc cutoff fallback hfallback hcanonical
        hpolicy tariff i hhigh hcutfloor hthreshold hd v act hb).le
    · have hR : ∀ᵐ d ∂userProfileLaw Γ, HighRivals cutoff i d := hd.mono fun d h => by
        intro j hj
        rcases h.1 j hj with hz | ⟨hr,hb⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hr,hcutfloor.trans hb⟩
      exact (source_actual_large_bid_negative Γ hm hn hc cutoff fallback hfallback hcanonical
        hpolicy tariff ha i hR v act (by omega) (le_of_not_gt hb) hlo hlohi hcut hL hv
        hlow (hbad act.bid (le_of_not_gt hb))).le

end FCAppendix.Bayes.ExclusiveSource
