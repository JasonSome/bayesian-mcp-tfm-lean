import FCAppendix.Exclusive.NarrowGlobalPriceNeighborhood
import FCAppendix.Exclusive.NarrowGlobalCentralPayoff
import FCAppendix.Exclusive.NarrowGlobalGuardsHigh
import FCAppendix.Exclusive.SourceCentralScale

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory Filter Topology
open Existence
open scoped BigOperators

variable {V : Type*}

def sampledRivalBid (scale : ℝ) (beta : V → ℝ) (x : Bool×V) : ℝ :=
  if x.1 then scale*Real.exp (beta x.2) else 0

def sampledBids {m : ℕ} (scale : ℝ) (beta : V → ℝ) (b : ℝ)
    (omega : RivalProfile m V) : Fin (m+1) → ℝ :=
  Fin.cases b (fun j => sampledRivalBid scale beta (omega j))

def sampledPrice {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (c : ℕ)
    (scale : ℝ) (beta : V → ℝ) (b : ℝ) (omega : RivalProfile m V) : ℝ :=
  canonicalPrice (d+1) (by omega) c (sampledBids scale beta b omega)

lemma sampledBids_rival_band {m : ℕ} (scale delta : ℝ) (hscale : 0 < scale)
    (beta : V → ℝ) (hbeta : ∀ v, beta v ∈ Icc (-delta) delta)
    (b : ℝ) (omega : RivalProfile m V) :
    ∀ j : Fin (m+1), j ≠ 0 → sampledBids scale beta b omega j=0 ∨
      sampledBids scale beta b omega j ∈
        Icc (scale*Real.exp (-delta)) (scale*Real.exp delta) := by
  intro j
  refine Fin.cases ?_ ?_ j
  · intro h
    exact False.elim (h rfl)
  · intro k _
    cases hx : (omega k).1
    · exact Or.inl (by simp [sampledBids,sampledRivalBid,hx])
    · apply Or.inr
      simp only [sampledBids,Fin.cases_succ,sampledRivalBid,hx,ite_true]
      exact ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbeta _).1) hscale.le,
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hbeta _).2) hscale.le⟩

lemma positiveRival_card_sampledBids {m : ℕ} (scale : ℝ) (hscale : 0 < scale)
    (beta : V → ℝ) (b : ℝ) (omega : RivalProfile m V) :
    Fintype.card (PositiveRival (sampledBids scale beta b omega) 0)=activeCount omega := by
  classical
  have hcard : Fintype.card (PositiveRival (sampledBids scale beta b omega) 0)=
      ∑ j : Fin (m+1), if j ≠ 0 ∧ 0 < sampledBids scale beta b omega j then 1 else 0 := by
    rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hcard,Fin.sum_univ_succ]
  simp only [ne_eq,not_true_eq_false,false_and,ite_false,zero_add,activeCount]
  apply Finset.sum_congr rfl
  intro j _
  have hpos : 0 < scale*Real.exp (beta (omega j).2) := mul_pos hscale (Real.exp_pos _)
  cases hx : (omega j).1 <;> simp [sampledBids,sampledRivalBid,hx,activeNat,hpos]

lemma sampledPrice_nonneg {m : ℕ} (d : ℕ) (hd : 1 ≤ d) (c : ℕ)
    (scale : ℝ) (beta : V → ℝ) (b : ℝ) (omega : RivalProfile m V) :
    0 ≤ sampledPrice d hd c scale beta b omega := canonicalPrice_nonneg _ _ _ _

lemma measurable_sampledBids [MeasurableSpace V] {m : ℕ}
    (scale : ℝ) (beta : V → ℝ) (hbeta : Measurable beta) (b : ℝ) :
    Measurable (sampledBids (m := m) scale beta b) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ ?_ i
  · exact measurable_const
  · intro j
    have hm : Measurable (sampledRivalBid scale beta) := by
      apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      · exact measurable_const.mul (Real.continuous_exp.measurable.comp (hbeta.comp measurable_snd))
      · exact measurable_const
    exact hm.comp (measurable_pi_apply j)

lemma measurable_sampledPrice [MeasurableSpace V] {m : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (c : ℕ) (hc : 0 < c)
    (scale : ℝ) (beta : V → ℝ) (hbeta : Measurable beta) (b : ℝ) :
    Measurable (sampledPrice (m := m) d hd c scale beta b) :=
  (measurable_canonicalPrice (d+1) (by omega) c hc).comp (measurable_sampledBids scale beta hbeta b)

lemma measurable_activeCount_sample [MeasurableSpace V] (m : ℕ) :
    Measurable (activeCount (m := m) (V := V)) := by
  unfold activeCount
  exact Finset.measurable_sum _ fun j _ => (measurable_of_countable activeNat).comp
    (measurable_fst.comp (measurable_pi_apply j))

theorem sampled_price_neighborhood (d : ℕ) (hd : 1 ≤ d)
    (h rho cap tolerance : ℝ) (hh : 0 < h) (hrho : 0 < rho) (hrh : rho < h)
    (hcap : 0 < cap) (htol : 0 < tolerance) :
    ∃ delta eta : ℝ, ∃ M0 : ℕ, 0 < delta ∧ 0 < eta ∧ 0 < M0 ∧
      ∀ {V : Type*} (m c : ℕ), M0 ≤ m+1 → ∀ (scale : ℝ), 0 < scale → scale ≤ cap →
      ∀ beta : V → ℝ, (∀ v, beta v ∈ Icc (-delta) delta) →
      ∀ (b : ℝ) (omega : RivalProfile m V),
      |(1+(activeCount omega:ℝ))/((m:ℝ)+1)-h| < eta →
      |(c:ℝ)/((m:ℝ)+1)-rho| < eta →
      0 < c ∧ |sampledPrice d hd c scale beta b omega-scale*(1-rho/h)^d| < tolerance := by
  obtain ⟨delta,eta,M0,hd0,he0,hM0,hprice⟩ :=
    canonical_native_price_neighborhood d hd h rho cap tolerance hh hrho hrh hcap htol
  refine ⟨delta,eta,M0,hd0,he0,hM0,?_⟩
  intro V m c hm scale hs hsc beta hb b omega hN hC
  have hh := hprice (m+1) c hm (sampledBids scale beta b omega) 0 scale hs hsc
    (sampledBids_rival_band scale delta hs beta hb b omega)
  rw [positiveRival_card_sampledBids scale hs beta b omega] at hh
  have h := hh (by simpa only [Nat.cast_add,Nat.cast_one,add_comm] using hN)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hC)
  exact ⟨h.2.1,h.2.2⟩

theorem exists_count_bad_probability_bound_all_types (h : unitInterval)
    {eta probability : ℝ} (heta : 0 < eta) (hprobability : 0 < probability) :
    ∃ M0 : ℕ, ∀ (V : Type*) [MeasurableSpace V], ∀ m ≥ M0,
      ∀ (nu : Measure V) [IsProbabilityMeasure nu],
      (iidRivalLaw m h nu).real
        {omega | eta ≤ |(1+(activeCount omega:ℝ))/((m:ℝ)+1)-(h:ℝ)|} < probability := by
  have hinv : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hexp : Tendsto (fun m : ℕ => 2*Real.exp (-2*(m:ℝ)*(eta/2)^2)) atTop (𝓝 0) := by
    have hp : 0 < 2*(eta/2)^2 := by positivity
    have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop hp)
    simpa only [Function.comp_def,mul_zero,show ∀ x : ℝ,
      -(2*(eta/2)^2*x) = -2*x*(eta/2)^2 by intro x; ring] using ht.const_mul 2
  obtain ⟨M0,hM0⟩ := eventually_atTop.mp
    ((hinv.eventually_le_const (by positivity : (0:ℝ)<eta/2)).and
      ((hexp.eventually_lt_const hprobability).and (eventually_ge_atTop 1)))
  refine ⟨M0,?_⟩
  intro V _ m hm nu _
  exact (forcedActiveFraction_two_sided_le h nu m (by have := (hM0 m hm).2.2; omega)
    heta (hM0 m hm).1).trans_lt (hM0 m hm).2.1

lemma referenceCentralBid_eq_referenceBidScale (d : ℕ) (a : UserTariff) (p0 : ℝ) :
    referenceCentralBid d a p0=referenceBidScale d a p0 := by
  dsimp [referenceCentralBid,referenceBid,normalizedPrice,referenceBidScale]

lemma referenceCentralBid_price (d : ℕ) (a : UserTariff) (p0 : ℝ) (hp1 : p0 < 1) :
    referenceCentralBid d a p0*(1-p0)^d=normalizedPrice d a p0 := by
  dsimp [referenceCentralBid,referenceBid]
  exact div_mul_cancel₀ _ (pow_pos (sub_pos.mpr hp1) d).ne'

lemma pricedPayoff_central_eq_reference (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (p0 : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) :
    pricedPayoff (d+1) (d+1) a (referenceCentralBid d a p0) (normalizedPrice d a p0)=
      referenceUtility d a (normalizedPrice d a p0) 1 p0 := by
  have hlu : 0 < normalizedPrice d a p0 := one_div_pos.mpr
    (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1
  have hs : 0 < referenceCentralBid d a p0 := div_pos hlu (pow_pos (sub_pos.mpr hp1) _)
  have hp : menuMarginal (d+1) (referenceCentralBid d a p0) (normalizedPrice d a p0)=p0 := by
    rw [menuMarginal_eq_activeDemand _ (by omega) _ _ hlu,activeDemand,if_pos hs,
      ← referenceCentralBid_price d a p0 hp1]
    simpa only [Nat.add_sub_cancel,sub_sub_cancel] using
      LowType.demand_at_reference_failure (d+1) (by omega) hs (sub_pos.mpr hp1) (by linarith)
  unfold pricedPayoff referenceUtility
  rw [hp,referenceBidCost_eq_actual d a _ p0 hp0 hp1,
    binomialPolynomial_eq_expect _ _ _ hp0 hp1.le]
  simp only [one_mul]
  rfl

end FCAppendix.Exclusive.Narrow.Global
