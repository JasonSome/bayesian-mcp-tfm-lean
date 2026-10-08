import FCAppendix.PayOnce.EffectiveBidLaw
import FCAppendix.PayOnce.Sorting

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set
open PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_monotone_effective_pure_bid (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) (i : Fin m) :
    ∃ bid : ℝ → ℝ, Monotone bid ∧ Measurable bid ∧
      (∀ v, 0 ≤ bid v ∧ bid v ≤ max (v-Γ.g) 0) ∧
      (∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1) ∧
      ∀ᵐ v ∂Γ.F, Γ.g < v → 0 < bid v ∧ bid v < v-Γ.g ∧
        ∀ᵐ a ∂Γ.σ v, a.bid = bid v ∧ a.routeCount = k+1 := by
  obtain ⟨bid,hmono,hmeas,hbounds,hpure⟩ :=
    exists_monotone_pure_bid Γ hk hc hcm hA hG hu B hB hsym hvalue i
  refine ⟨bid,hmono,hmeas,hbounds,?_,hpure⟩
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((measurable_effectiveBid (k+1)).comp measurable_snd)
      (hmeas.comp measurable_fst))
  have hzero := Measure.ae_ae_of_ae_compProd hinactive
  filter_upwards [hpure,hzero] with v hv hz
  by_cases hpos : Γ.g < v
  · filter_upwards [(hv hpos).2.2] with a ha
    change effectiveBid a = bid v
    simp only [effectiveBid,ha.2,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,ha.1]
  · have hb : bid v = 0 := le_antisymm
      (by simpa only [max_eq_right (sub_nonpos.mpr (le_of_not_gt hpos))] using (hbounds v).2)
      (hbounds v).1
    filter_upwards [hz] with a ha
    change effectiveBid a = bid v
    simp only [effectiveBid,ha (le_of_not_gt hpos),if_true,hb]

theorem realEffectiveBidLaw_eq_pure_map (Γ : FiniteGame m (k+1) c Seed)
    (bid : ℝ → ℝ) (hbid : Measurable bid)
    (heq : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1) :
    (PayOnce.BidScaling.realBidLaw Γ : Measure ℝ) = Γ.F.map bid := by
  rw [realEffectiveBidLaw_eq_action_map,Measure.map_congr heq]
  change (Γ.F ⊗ₘ Γ.σ).map (bid ∘ Prod.fst) = Γ.F.map bid
  rw [← Measure.map_map hbid measurable_fst]
  change ((Γ.F ⊗ₘ Γ.σ).fst).map bid = _
  rw [Measure.fst_compProd]

end FCAppendix.Bayes
