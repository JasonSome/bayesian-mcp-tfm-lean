import FCAppendix.Exclusive.NarrowCalculus
import FCAppendix.Probability.ActiveCountBounds

namespace FCAppendix.Exclusive.LowType

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

variable {n k : ℕ}

theorem success_le_count (k : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    PayOnce.success k p ≤ (k:ℝ)*p := by
  simpa only [IndependentCounts.binomial_success,IndependentCounts.binomial_load,PayOnce.success]
    using (IndependentCounts.binomial k p hp0 hp1).success_le_load

theorem marginal_le_success (hk : 1 ≤ k) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p ≤ PayOnce.success k p := by
  have hh := pow_le_pow_of_le_one (sub_nonneg.mpr hp1) (by linarith : 1-p ≤ 1) hk
  rw [pow_one] at hh
  unfold PayOnce.success
  linarith

theorem unique_payment_ge_price_success (hk : 1 ≤ k) (hkn : k ≤ n)
    {p b lam : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 ≤ b)
    (hprice : b*(1-p)^(n-1)=lam) :
    lam*PayOnce.success k p ≤ b*(k:ℝ)*p*(1-p)^(k-1) := by
  have hq0 : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hq1 : 1-p ≤ 1 := by linarith
  have hpow : (1-p)^(n-1) ≤ (1-p)^(k-1) :=
    pow_le_pow_of_le_one hq0 hq1 (by omega)
  have hlam : 0 ≤ lam := hprice ▸ mul_nonneg hb (pow_nonneg hq0 _)
  calc
    lam*PayOnce.success k p ≤ lam*((k:ℝ)*p) :=
      mul_le_mul_of_nonneg_left (success_le_count k hp0 hp1) hlam
    _ ≤ (b*(1-p)^(k-1))*((k:ℝ)*p) :=
      mul_le_mul_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hpow hb])
        (mul_nonneg (Nat.cast_nonneg _) hp0)
    _ = b*(k:ℝ)*p*(1-p)^(k-1) := by ring

theorem affine_expected_ge_success (eta : ℝ) (heta : 0 ≤ eta) (μ : CountLaw k) :
    μ.success ≤ (UserTariff.affine eta).expected μ := by
  rw [UserTariff.expected_affine]
  have hh := mul_nonneg heta (sub_nonneg.mpr μ.success_le_load)
  nlinarith

theorem base_expected_ge_success (G : Schedule n) (hkn : k ≤ n) (μ : CountLaw k) :
    μ.success ≤ μ.expect (fun r => G.charge r.val) := by
  apply μ.expect_mono
  intro r
  by_cases hr : r.val=0
  · simp [hr,G.zero,successIndicator]
  · simp only [successIndicator,if_neg hr]
    exact G.lower r.val (by omega) (by omega)

noncomputable def binomialPayoff (tariff : UserTariff) (G : Schedule n)
    (k : ℕ) (g v b p : ℝ) : ℝ :=
  v*PayOnce.success k p-b*Narrow.binomialPolynomial k tariff.charge p-
    g*Narrow.binomialPolynomial k G.charge p

theorem binomialPayoff_eq (tariff : UserTariff) (G : Schedule n)
    (k : ℕ) (g v b p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialPayoff tariff G k g v b p=
      v*(IndependentCounts.binomial k p hp0 hp1).success-
        b*tariff.expected (IndependentCounts.binomial k p hp0 hp1)-
        g*(IndependentCounts.binomial k p hp0 hp1).expect (fun r => G.charge r.val) := by
  rw [binomialPayoff,Narrow.binomialPolynomial_eq_expect,
    Narrow.binomialPolynomial_eq_expect,IndependentCounts.binomial_success]
  rfl

theorem payment_ge_min_price_success (tariff : UserTariff) (ha : tariff.Allowed)
    (hk : 1 ≤ k) (hkn : k ≤ n) {p b lam : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 ≤ b)
    (hprice : b*(1-p)^(n-1)=lam) :
    min b lam*PayOnce.success k p ≤
      b*tariff.expected (IndependentCounts.binomial k p hp0 hp1) := by
  cases tariff with
  | unique =>
    rw [UserTariff.expected_unique_binomial]
    calc
      min b lam*PayOnce.success k p ≤ lam*PayOnce.success k p :=
        mul_le_mul_of_nonneg_right (min_le_right _ _)
          (by simpa only [IndependentCounts.binomial_success,PayOnce.success] using
            (IndependentCounts.binomial k p hp0 hp1).success_nonneg)
      _ ≤ b*(k:ℝ)*p*(1-p)^(k-1) := unique_payment_ge_price_success hk hkn hp0 hp1 hb hprice
      _ = b*((k:ℝ)*p*(1-p)^(k-1)) := by ring
  | affine eta =>
    have hh := mul_le_mul_of_nonneg_left
      (affine_expected_ge_success eta ha.1 (IndependentCounts.binomial k p hp0 hp1)) hb
    rw [IndependentCounts.binomial_success] at hh
    exact (mul_le_mul_of_nonneg_right (min_le_left b lam)
      (by simpa only [IndependentCounts.binomial_success,PayOnce.success] using
        (IndependentCounts.binomial k p hp0 hp1).success_nonneg)).trans hh

theorem good_event_payoff_upper (tariff : UserTariff) (ha : tariff.Allowed)
    (G : Schedule n) (hk : 1 ≤ k) (hkn : k ≤ n)
    {g v b p lam lowerPrice cutoff lowUpper pmin : ℝ}
    (hg : 0 ≤ g) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb : 0 ≤ b)
    (hprice : b*(1-p)^(n-1)=lam) (hlam : lowerPrice ≤ lam)
    (hcut : cutoff ≤ b) (hw : v-g ≤ lowUpper)
    (hlow : lowUpper < min cutoff lowerPrice) (hpm : pmin ≤ p) :
    binomialPayoff tariff G k g v b p ≤
      -pmin*(min cutoff lowerPrice-lowUpper) := by
  let μ := IndependentCounts.binomial k p hp0 hp1
  have hbase := mul_le_mul_of_nonneg_left (base_expected_ge_success G hkn μ) hg
  have hpay := payment_ge_min_price_success tariff ha hk hkn hp0 hp1 hb hprice
  have hS0 : 0 ≤ PayOnce.success k p := by simpa only [μ,IndependentCounts.binomial_success,PayOnce.success] using μ.success_nonneg
  have hfloor : min cutoff lowerPrice ≤ min b lam := min_le_min hcut hlam
  have hpayment : min cutoff lowerPrice*PayOnce.success k p ≤ b*tariff.expected μ :=
    (mul_le_mul_of_nonneg_right hfloor hS0).trans hpay
  have hSmin : pmin ≤ PayOnce.success k p := hpm.trans (marginal_le_success hk hp0 hp1)
  rw [binomialPayoff_eq tariff G k g v b p hp0 hp1]
  change v*μ.success-b*tariff.expected μ-g*μ.expect (fun r => G.charge r.val) ≤ _
  have hμ : μ.success=PayOnce.success k p := IndependentCounts.binomial_success _ _ _ _
  rw [hμ] at hbase ⊢
  nlinarith [mul_le_mul_of_nonneg_right hw hS0,
    mul_le_mul_of_nonneg_left hSmin (sub_nonneg.mpr hlow.le)]

theorem payoff_le_low_upper (tariff : UserTariff) (ha : tariff.Allowed)
    (G : Schedule n) (hkn : k ≤ n) {g v b p L : ℝ}
    (hg : 0 ≤ g) (hb : 0 ≤ b) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hL : 0 ≤ L) (hw : v-g ≤ L) :
    binomialPayoff tariff G k g v b p ≤ L := by
  let μ := IndependentCounts.binomial k p hp0 hp1
  have hbase := mul_le_mul_of_nonneg_left (base_expected_ge_success G hkn μ) hg
  have hcost : 0 ≤ b*tariff.expected μ := mul_nonneg hb
    (μ.expect_nonneg (fun r => tariff.charge_nonneg ha r.val))
  rw [binomialPayoff_eq tariff G k g v b p hp0 hp1]
  change v*μ.success-b*tariff.expected μ-g*μ.expect (fun r => G.charge r.val) ≤ L
  have h1 := mul_le_mul_of_nonneg_right hw μ.success_nonneg
  have h2 := mul_le_mul_of_nonneg_left μ.success_le_one hL
  nlinarith

theorem good_event_kernel_payoff_upper (n : ℕ) (hn : 2 ≤ n)
    (tariff : UserTariff) (ha : tariff.Allowed) (G : Schedule n)
    (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    {g v b lam lowerPrice upperPrice cutoff lowUpper : ℝ}
    (hg : 0 ≤ g) (hlo : 0 < lowerPrice) (hlam : lam ∈ Icc lowerPrice upperPrice)
    (hcut : upperPrice < cutoff) (hb : cutoff ≤ b) (hw : v-g ≤ lowUpper)
    (hlow : lowUpper < min cutoff lowerPrice) :
    binomialPayoff tariff G k g v b (demand n b lam) ≤
      -demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper) := by
  have hlam0 : 0 < lam := hlo.trans_le hlam.1
  have hu0 : 0 < upperPrice := hlam0.trans_le hlam.2
  have ht0 : 0 < cutoff := hu0.trans hcut
  have hb0 : 0 < b := ht0.trans_le hb
  have hp0 : 0 ≤ demand n b lam := demand_nonneg _ _ _
  have hp1 : demand n b lam ≤ 1 := demand_le_one n hb0 hlam0.le
  have hprice : b*(1-demand n b lam)^(n-1)=lam := by
    rw [demand_receipt n hn hb0 hlam0,min_eq_right (hlam.2.trans (hcut.trans_le hb).le)]
  have hpmin : demand n cutoff upperPrice ≤ demand n b lam :=
    (demand_mono_bid n hn ht0 hb hu0.le).trans
      (demand_antitone n hn hb0 hlam0.le hlam.2)
  exact good_event_payoff_upper tariff ha G hk hkn hg hp0 hp1 hb0.le
    hprice hlam.1 hb hw hlow hpmin

theorem demand_at_reference_failure (n : ℕ) (hn : 2 ≤ n) {a q : ℝ}
    (ha : 0 < a) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    demand n a (a*q^(n-1))=1-q := by
  have he : (a*q^(n-1))/a=q^(n-1) := by field_simp
  have hp : ((q^(n-1))^rate n)=q := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq0.le,
      mul_comm (((n-1:ℕ):ℝ)) (rate n),rate_mul n hn,Real.rpow_one]
  rw [demand,he,hp,max_eq_right (sub_nonneg.mpr hq1)]

theorem many_high_rivals_reject_low_bid {ι : Type*} [Fintype ι]
    (n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c)
    (hN : n*c ≤ Fintype.card ι) (B : ι → ℝ) {a b lam : ℝ}
    (ha : 0 < a) (hB : ∀ i, a ≤ B i) (hb : 0 < b) (hlam : 0 ≤ lam)
    (hroot : (∑ i, demand n (B i) lam)+demand n b lam=c)
    (hbid : b < a*(1-1/(n:ℝ))^(n-1)) :
    demand n b lam=0 := by
  classical
  let crit := a*(1-1/(n:ℝ))^(n-1)
  have hnR : (1:ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 < 1-1/(n:ℝ) := by
    have := (div_lt_one (by positivity : (0:ℝ) < n)).mpr hnR
    linarith
  have hq1 : 1-1/(n:ℝ) ≤ 1 := by
    have hdiv : 0 ≤ 1/(n:ℝ) := by positivity
    linarith
  have hcrit : demand n a crit=1/(n:ℝ) := by
    rw [demand_at_reference_failure n hn ha hq0 hq1]
    ring
  have hprice : crit ≤ lam := by
    by_contra hnot
    have hlt : lam < crit := lt_of_not_ge hnot
    have hpos : 0 < demand n a lam := by
      have hh := demand_antitone n hn ha hlam hlt.le
      rw [hcrit] at hh
      exact (one_div_pos.mpr (by positivity : (0:ℝ) < n)).trans_le hh
    have hstrict : 1/(n:ℝ) < demand n a lam := by
      simpa only [hcrit] using demand_strict n hn ha hlam hlt hpos
    have hN0 : 0 < Fintype.card ι := (Nat.mul_pos (by omega) hc).trans_le hN
    letI : Nonempty ι := Fintype.card_pos_iff.mp hN0
    have hsum : (Fintype.card ι:ℝ)*(1/(n:ℝ)) < ∑ i, demand n (B i) lam := by
      have hh := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ => hstrict.trans_le (demand_mono_bid n hn ha (hB i) hlam))
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hh
    have hNc : (c:ℝ) ≤ (Fintype.card ι:ℝ)*(1/(n:ℝ)) := by
      have hh : (n:ℝ)*c ≤ Fintype.card ι := by exact_mod_cast hN
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity : (0:ℝ) < n)).mpr
      simpa only [mul_comm] using hh
    have hnonneg := demand_nonneg n b lam
    linarith
  exact (demand_eq_zero_iff n hn hb hlam).mpr (hbid.le.trans hprice)

theorem continuous_binomialPayoff (tariff : UserTariff) (G : Schedule n)
    (k : ℕ) (g v b : ℝ) : Continuous (binomialPayoff tariff G k g v b) := by
  have hc (f : ℕ → ℝ) : Continuous (Narrow.binomialPolynomial k f) :=
    continuous_iff_continuousAt.mpr fun p => (Narrow.hasDerivAt_binomialPolynomial k f p).continuousAt
  exact ((continuous_const.mul (PayOnce.continuous_success k)).sub
    (continuous_const.mul (hc tariff.charge))).sub (continuous_const.mul (hc G.charge))

theorem integrable_binomialPayoff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (tariff : UserTariff) (G : Schedule n)
    (k : ℕ) (g v b : ℝ) (p : Ω → ℝ) (hp : Measurable p)
    (hprange : ∀ ω, p ω ∈ Icc (0:ℝ) 1) :
    Integrable (fun ω => binomialPayoff tariff G k g v b (p ω)) μ := by
  have hc := continuous_binomialPayoff tariff G k g v b
  obtain ⟨B,hB⟩ := (isCompact_Icc.image (continuous_abs.comp hc)).bddAbove
  apply Integrable.of_bound (hc.measurable.comp hp).aestronglyMeasurable B
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  exact hB (mem_image_of_mem _ (hprange ω))

theorem integral_upper_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (u : Ω → ℝ) (hu : Integrable u μ) (L d : ℝ)
    (houtside : ∀ᵐ ω ∂μ, u ω ≤ L)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ E → u ω ≤ -d) :
    (∫ ω, u ω ∂μ) ≤ L-(L+d)*μ.real E := by
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) μ := (integrable_const _).indicator hE
  have hmajor : Integrable (fun ω => L-(L+d)*E.indicator (fun _ => (1:ℝ)) ω) μ :=
    (integrable_const _).sub (hI.const_mul _)
  calc
    (∫ ω, u ω ∂μ) ≤ ∫ ω, L-(L+d)*E.indicator (fun _ => (1:ℝ)) ω ∂μ := by
      apply integral_mono_ae hu hmajor
      filter_upwards [houtside,hgood] with ω ho hg
      by_cases hω : ω ∈ E
      · simpa [Set.indicator,hω] using hg hω
      · simpa [Set.indicator,hω] using ho
    _ = L-(L+d)*μ.real E := by
      rw [integral_sub (integrable_const _) (hI.const_mul _),integral_const,
        integral_const_mul,integral_indicator_const _ hE]
      simp only [probReal_univ,smul_eq_mul,one_mul,mul_one]

theorem integral_negative_of_good_event {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (u : Ω → ℝ) (hu : Integrable u μ) {L d : ℝ} (hL : 0 ≤ L) (hd : 0 < d)
    (houtside : ∀ᵐ ω ∂μ, u ω ≤ L)
    (hgood : ∀ᵐ ω ∂μ, ω ∈ E → u ω ≤ -d)
    (hbad : μ.real Eᶜ < d/(L+d)) :
    (∫ ω, u ω ∂μ) < 0 := by
  have hbound := integral_upper_of_good_event μ E hE u hu L d houtside hgood
  have hden : 0 < L+d := by linarith
  have htail := (lt_div_iff₀ hden).mp hbad
  rw [probReal_compl_eq_one_sub hE] at htail
  nlinarith

theorem large_bid_deviation_negative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (n : ℕ) (hn : 2 ≤ n) (tariff : UserTariff) (ha : tariff.Allowed)
    (G : Schedule n) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    {g v b lowerPrice upperPrice cutoff lowUpper : ℝ}
    (hg : 0 ≤ g) (hlo : 0 < lowerPrice) (hlohi : lowerPrice ≤ upperPrice)
    (hcut : upperPrice < cutoff) (hb : cutoff ≤ b)
    (hL : 0 ≤ lowUpper) (hw : v-g ≤ lowUpper)
    (hlow : lowUpper < min cutoff lowerPrice)
    (lam : Ω → ℝ) (hlam : Measurable lam) (hlam0 : ∀ ω, 0 ≤ lam ω)
    (hprice : ∀ ω ∈ E, lam ω ∈ Icc lowerPrice upperPrice)
    (hbad : μ.real Eᶜ <
      (demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper))/
        (lowUpper+demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper))) :
    (∫ ω, binomialPayoff tariff G k g v b (demand n b (lam ω)) ∂μ) < 0 := by
  have hu0 : 0 < upperPrice := hlo.trans_le hlohi
  have ht0 : 0 < cutoff := hu0.trans hcut
  have hb0 : 0 < b := ht0.trans_le hb
  have hpm : 0 < demand n cutoff upperPrice := (demand_pos_iff n hn ht0 hu0.le).mpr hcut
  have hd : 0 < demand n cutoff upperPrice*(min cutoff lowerPrice-lowUpper) :=
    mul_pos hpm (sub_pos.mpr hlow)
  have hmeas : Measurable (fun ω => demand n b (lam ω)) := (continuous_demand n hn b).measurable.comp hlam
  have hrange : ∀ ω, demand n b (lam ω) ∈ Icc (0:ℝ) 1 := fun ω =>
    ⟨demand_nonneg _ _ _,demand_le_one n hb0 (hlam0 ω)⟩
  apply integral_negative_of_good_event μ E hE _
    (integrable_binomialPayoff μ tariff G k g v b _ hmeas hrange) hL hd _ _ hbad
  · exact Eventually.of_forall fun ω => payoff_le_low_upper tariff ha G hkn hg hb0.le
      (hrange ω).1 (hrange ω).2 hL hw
  · apply Eventually.of_forall
    intro ω hω
    simpa only [neg_mul] using good_event_kernel_payoff_upper n hn tariff ha G
      k hk hkn hg hlo (hprice ω hω) hcut hb hw hlow

end FCAppendix.Exclusive.LowType
