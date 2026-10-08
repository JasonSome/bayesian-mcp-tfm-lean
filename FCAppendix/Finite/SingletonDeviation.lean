import FCAppendix.Finite.ReceiptBoundsAE

namespace FCAppendix
namespace CountLaw

theorem utility_le_bid_net_success {n : ℕ} (μ : CountLaw n)
    (v b g : ℝ) (A G : Schedule n) (hb : 0 ≤ b) (hg : 0 ≤ g) :
    μ.utility v b g A G ≤ (v - g - b) * μ.success := by
  rw [utility_eq]
  have hA := mul_le_mul_of_nonneg_left (μ.success_le_charge A) hb
  have hG := mul_le_mul_of_nonneg_left (μ.success_le_charge G) hg
  linarith

end CountLaw
namespace Bayes

open MeasureTheory Game

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem singleton_payoff (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (a : JointAction n) (hk : a.routeCount = 1) (v : ℝ) :
    (problem Γ i).payoff v a = (v - Γ.g - a.bid) * meanAcceptProb Γ i a.bid := by
  have hle := load_le_routeCount_mul_success Γ i a
  have hls : ((problem Γ i).outcome a).load = ((problem Γ i).outcome a).success := by
    simp only [hk, Nat.cast_one, one_mul] at hle
    exact le_antisymm hle ((problem Γ i).outcome a).success_le_load
  have hA : ((problem Γ i).outcome a).charge Γ.A = ((problem Γ i).outcome a).success := by
    exact le_antisymm (((problem Γ i).outcome a).charge_le_load Γ.A |>.trans_eq hls)
      (((problem Γ i).outcome a).success_le_charge Γ.A)
  have hG : ((problem Γ i).outcome a).charge Γ.G = ((problem Γ i).outcome a).success := by
    exact le_antisymm (((problem Γ i).outcome a).charge_le_load Γ.G |>.trans_eq hls)
      (((problem Γ i).outcome a).success_le_charge Γ.G)
  have hs : ((problem Γ i).outcome a).success = meanAcceptProb Γ i a.bid := by
    rw [← hls, load_eq_mean Γ hn i a, hk, Nat.cast_one, one_mul]
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G = _
  rw [CountLaw.utility_eq, hA, hG, hs]
  ring

theorem envelope_lower_singleton (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (i : Fin m) (a : JointAction n) (hk : a.routeCount = 1)
    (r : ℝ) (hr : 0 ≤ r) (hq : 1 - r ≤ meanAcceptProb Γ i a.bid) (v : ℝ) :
    max (v - Γ.g - a.bid) 0 - r * max (v - Γ.g) 0 ≤ (problem Γ i).envelope v := by
  by_cases hw : 0 ≤ v - Γ.g - a.bid
  · rw [max_eq_left hw, max_eq_left (by linarith [a.bid_nonneg])]
    have hdev := (problem Γ i).action_le_envelope v a
    rw [singleton_payoff Γ hn i a hk v] at hdev
    have hmul := mul_le_mul_of_nonneg_left hq hw
    have hrt := mul_nonneg hr a.bid_nonneg
    nlinarith
  · rw [max_eq_right (le_of_not_ge hw)]
    have hnonneg := (problem Γ i).envelope_nonneg v
    have herr := mul_nonneg hr (le_max_right (v - Γ.g) 0)
    linarith

theorem bestResponse_bid_le_singleton (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (i : Fin m) (a : JointAction n) (hk : a.routeCount = 1)
    (r : ℝ) (hr : 0 ≤ r) (hq : 1 - r ≤ meanAcceptProb Γ i a.bid)
    (v : ℝ) (b : JointAction n) (hbr : (problem Γ i).BestResponse v b)
    (hbv : b.bid ≤ max (v - Γ.g) 0) :
    b.bid ≤ a.bid + r * max (v - Γ.g) 0 := by
  by_cases hbt : b.bid ≤ a.bid
  · exact hbt.trans (le_add_of_nonneg_right (mul_nonneg hr (le_max_right _ _)))
  · have hbt' : a.bid < b.bid := lt_of_not_ge hbt
    have hw : 0 < v - Γ.g := by
      by_contra hh
      have hnw : v - Γ.g ≤ 0 := le_of_not_gt hh
      rw [max_eq_right hnw] at hbv
      linarith [a.bid_nonneg]
    rw [max_eq_left hw.le] at hbv ⊢
    have hwt : 0 ≤ v - Γ.g - a.bid := by linarith
    have hdev := hbr a
    rw [singleton_payoff Γ hn i a hk v] at hdev
    have hpay := ((problem Γ i).outcome b).utility_le_bid_net_success v b.bid Γ.g Γ.A Γ.G
      b.bid_nonneg Γ.g_nonneg
    change (problem Γ i).payoff v b ≤ _ at hpay
    have hbnet : 0 ≤ v - Γ.g - b.bid := by linarith
    have hupper := mul_le_mul_of_nonneg_left (((problem Γ i).outcome b).success_le_one) hbnet
    have hmul := mul_le_mul_of_nonneg_left hq hwt
    have hrt := mul_nonneg hr a.bid_nonneg
    nlinarith

theorem alphaGt_singleton_price_le_value_tail (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ)
    (j : Fin n) (i : Fin m) (a : JointAction n) (hk : a.routeCount = 1)
    (r : ℝ) (hr : 0 < r) (hq : 1 - r ≤ meanAcceptProb Γ i a.bid)
    (d : ℝ) (hd : 0 < d) :
    alphaGt Γ j (a.bid + d) ≤ Γ.F.real (Set.Ioi (Γ.g + d / r)) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hbr : ∀ᵐ x ∂(userLaw Γ), (problem Γ i).BestResponse x.1.1 x.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hΓ.users i)
  have hsub : aboveAt j (a.bid + d) ≤ᵐ[userLaw Γ]
      {x : UserDraw n | Γ.g + d / r < x.1.1} := by
    filter_upwards [hbr, ae_no_overbid_userLaw_onPath Γ hm hc hΓ] with x hx hb hreach
    have hroute : 0 < x.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hreach.1⟩
      rwa [card_firstK _ _ x.1.2.routeCount_le] at hcard
    have hprice := bestResponse_bid_le_singleton Γ hn i a hk r hr.le hq x.1.1 x.1.2 hx
      (hb hroute)
    have hgap : d < r * max (x.1.1 - Γ.g) 0 := by linarith [hreach.2]
    have hw : 0 < x.1.1 - Γ.g := by
      by_contra hh
      rw [max_eq_right (le_of_not_gt hh), mul_zero] at hgap
      linarith
    rw [max_eq_left hw.le] at hgap
    have hdiv : d / r < x.1.1 - Γ.g := (div_lt_iff₀ hr).mpr (by nlinarith)
    change Γ.g + d / r < x.1.1
    linarith
  have heq : userLaw Γ {x : UserDraw n | Γ.g + d / r < x.1.1} =
      Γ.F (Set.Ioi (Γ.g + d / r)) := by
    rw [← userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun x : UserDraw n => x.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  change (userLaw Γ (aboveAt j (a.bid + d))).toReal ≤
    (Γ.F (Set.Ioi (Γ.g + d / r))).toReal
  rw [← heq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

end Bayes
end FCAppendix
