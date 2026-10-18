import FCAppendix.Exclusive.SourceLowTypePolicy

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource

open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def payoffTest (tariff : UserTariff) (G : Schedule n) (g v b : ℝ) (r : ℕ) : ℝ :=
  v*successIndicator r-b*tariff.charge r-g*G.charge r

theorem exclusiveTariffPayoff_eq_test (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) (a : JointAction n) :
    exclusiveTariffPayoff Γ tariff i v a =
      ((problem Γ i).outcome a).expect
        (fun r => payoffTest tariff Γ.G Γ.g v a.bid r.val) := by
  simp only [payoffTest]
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul,FiniteLaw.expect_const_mul]
  rfl

theorem binomial_payoffTest (tariff : UserTariff) (G : Schedule n)
    (k : ℕ) (g v b p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Narrow.binomialPolynomial k (payoffTest tariff G g v b) p =
      LowType.binomialPayoff tariff G k g v b p := by
  rw [Narrow.binomialPolynomial_eq_expect k (payoffTest tariff G g v b) p hp0 hp1,
    LowType.binomialPayoff_eq tariff G k g v b p hp0 hp1]
  simp only [payoffTest,FiniteLaw.expect_sub,FiniteLaw.expect_const_mul,
    CountLaw.success,UserTariff.expected]

theorem source_interim_test_large_bid (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (i : Fin m) (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals cutoff i d)
    (x : ℝ × JointAction n) (hb : cutoff ≤ x.2.bid) (f : ℕ → ℝ) :
    ((problem Γ i).outcome x.2).expect (fun r => f r.val) =
      ∫ d, Narrow.binomialPolynomial x.2.routeCount f
        (focalMarginal n hn c i x.2.bid d) ∂userProfileLaw Γ := by
  rw [interim_expect_eq_profile_update Γ i x]
  have he (τ : Equiv.Perm (Fin n)) :
      (∫ d, (profileCountLaw Γ (Function.update d i (x,τ)) i).expect
        (fun r => f r.val) ∂userProfileLaw Γ) =
      ∫ d, Narrow.binomialPolynomial x.2.routeCount f
        (focalMarginal n hn c i x.2.bid d) ∂userProfileLaw Γ := by
    apply integral_congr_ae
    filter_upwards [hd] with d hd
    exact source_profile_test_large_bid Γ hm hn hc cutoff fallback hfallback hcanonical
      hpolicy i d hd x hb τ f
  simp_rw [he]
  simp

theorem source_actual_payoff_large_bid (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (tariff : UserTariff) (i : Fin m)
    (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals cutoff i d)
    (v : ℝ) (a : JointAction n) (hb : cutoff ≤ a.bid) :
    exclusiveTariffPayoff Γ tariff i v a =
      ∫ d, LowType.binomialPayoff tariff Γ.G a.routeCount Γ.g v a.bid
        (focalMarginal n hn c i a.bid d) ∂userProfileLaw Γ := by
  rw [exclusiveTariffPayoff_eq_test,
    source_interim_test_large_bid Γ hm hn hc cutoff fallback hfallback hcanonical
      hpolicy i hd (v,a) hb]
  apply integral_congr_ae
  exact Eventually.of_forall fun d => binomial_payoffTest tariff Γ.G a.routeCount
    Γ.g v a.bid _ (focalMarginal_bounds hn i a.bid d).1
      (focalMarginal_bounds hn i a.bid d).2

def focalPrice (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (i : Fin m) (b : ℝ)
    (d : UserProfile m n) : ℝ :=
  canonicalPrice n hn c (listBids (focalList i b d))

theorem measurable_focalPrice (hn : 2 ≤ n) (hc : 0 < c) (i : Fin m) (b : ℝ) :
    Measurable (focalPrice n hn c i b) :=
  (measurable_canonicalPrice n hn c hc).comp
    ((measurable_listBids m).comp (measurable_focalList i b))

theorem focalMarginal_eq_demand (hn : 2 ≤ n) (i : Fin m) {b : ℝ} (hb : 0 < b)
    (d : UserProfile m n) :
    focalMarginal n hn c i b d = demand n b (focalPrice n hn c i b d) := by
  classical
  simp [focalMarginal,canonicalListMarginal,canonicalMarginal,activeDemand,
    focalPrice,listBids,focalList,readBid,hb]

theorem source_actual_large_bid_negative (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed)
    (hfallback : Measurable (fun p : LocalList m × Seed => (fallback p.1 p.2).val))
    (hcanonical : ∀ ℓ, FiniteLaw.ofMeasure Γ.seedLaw (fun s => (fallback ℓ s).val)
      (hfallback.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids ℓ))
    (hpolicy : ∀ j ℓ s, (Γ.policy j ℓ s).val =
      (Marker.sourceContinuation hm hn hc cutoff fallback ℓ s).val)
    (tariff : UserTariff) (ha : tariff.Allowed) (i : Fin m)
    (hd : ∀ᵐ d ∂userProfileLaw Γ, HighRivals cutoff i d)
    (v : ℝ) (a : JointAction n) (hk : 1 ≤ a.routeCount) (hb : cutoff ≤ a.bid)
    {lowerPrice upperPrice lowUpper : ℝ}
    (hlo : 0 < lowerPrice) (hlohi : lowerPrice ≤ upperPrice)
    (hcut : upperPrice < cutoff) (hL : 0 ≤ lowUpper) (hw : v-Γ.g ≤ lowUpper)
    (hlow : lowUpper < min cutoff lowerPrice)
    (hbad : (userProfileLaw Γ).real
      {d | focalPrice n hn c i a.bid d ∉ Icc lowerPrice upperPrice} <
      (demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper))/
        (lowUpper+demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper))) :
    exclusiveTariffPayoff Γ tariff i v a < 0 := by
  have hb0 : 0 < a.bid := (hlo.trans_le hlohi |>.trans hcut).trans_le hb
  rw [source_actual_payoff_large_bid Γ hm hn hc cutoff fallback hfallback hcanonical
    hpolicy tariff i hd v a hb]
  simp_rw [focalMarginal_eq_demand hn i hb0]
  apply LowType.large_bid_deviation_negative (userProfileLaw Γ)
    {d | focalPrice n hn c i a.bid d ∈ Icc lowerPrice upperPrice}
    ((measurable_focalPrice hn hc i a.bid) measurableSet_Icc)
    n hn tariff ha Γ.G a.routeCount hk a.routeCount_le Γ.g_nonneg hlo hlohi hcut hb
    hL hw hlow (focalPrice n hn c i a.bid) (measurable_focalPrice hn hc i a.bid)
    (fun d => canonicalPrice_nonneg n hn c _) (fun _ h => h)
  exact hbad

end FCAppendix.Bayes.ExclusiveSource
