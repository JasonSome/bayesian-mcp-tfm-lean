import FCAppendix.Exclusive.CommonListKernel
import FCAppendix.Proposer.MeasurableLotteryPolicy

noncomputable section
namespace FCAppendix.Exclusive
open MeasureTheory Set Game
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
attribute [local instance] Classical.propDecidable

abbrev PositiveIndex (b : ι → ℝ) := {i : ι // 0 < b i}
def positiveCount (b : ι → ℝ) : ℕ := Fintype.card (PositiveIndex b)

def activeDemand (n : ℕ) (b t : ℝ) : ℝ := if 0 < b then demand n b t else 0

def totalDemand (n : ℕ) (b : ι → ℝ) (t : ℝ) : ℝ := ∑ i, activeDemand n (b i) t

lemma totalDemand_eq_positive (n : ℕ) (b : ι → ℝ) (t : ℝ) :
    totalDemand n b t = ∑ i : PositiveIndex b, demand n (b i.val) t := by
  classical
  simp only [totalDemand, activeDemand]
  rw [← Finset.sum_filter]
  simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
    (p := fun i => 0 < b i) (fun i => demand n (b i) t)).symm

def canonicalPrice (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) : ℝ :=
  if h : c < positiveCount b then
    (exists_price n hn (fun i : PositiveIndex b => b i.val) (fun i => i.property) c h).choose
  else 0

lemma canonicalPrice_overloaded (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ)
    (hc : c < positiveCount b) :
    0 < canonicalPrice n hn c b ∧ totalDemand n b (canonicalPrice n hn c b) = c := by
  rw [canonicalPrice, dif_pos hc, totalDemand_eq_positive]
  exact (exists_price n hn (fun i : PositiveIndex b => b i.val)
    (fun i => i.property) c hc).choose_spec

lemma canonicalPrice_nonneg (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) :
    0 ≤ canonicalPrice n hn c b := by
  by_cases hc : c < positiveCount b
  · exact (canonicalPrice_overloaded n hn c b hc).1.le
  · simp only [canonicalPrice, dif_neg hc, le_refl]

lemma totalDemand_le_count (n : ℕ) (b : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    totalDemand n b t ≤ positiveCount b := by
  rw [totalDemand_eq_positive]
  calc
    _ ≤ ∑ _i : PositiveIndex b, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => demand_le_one n i.property ht
    _ = _ := by simp [positiveCount]

theorem canonicalPrice_lt_iff (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (t : ℝ) :
    canonicalPrice n hn c b < t ↔ 0 < t ∧ totalDemand n b t < c := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  by_cases hover : c < positiveCount b
  · obtain ⟨hp,hr⟩ := canonicalPrice_overloaded n hn c b hover
    constructor
    · intro h
      refine ⟨hp.trans h, ?_⟩
      have hh := sum_demand_strict n hn (fun i : PositiveIndex b => b i.val)
        (fun i => i.property) hp.le h
        (by rw [← totalDemand_eq_positive,hr]; exact hcR)
      simpa only [← totalDemand_eq_positive,hr] using hh
    · rintro ⟨ht,hd⟩
      by_contra hnot
      have hs : totalDemand n b (canonicalPrice n hn c b) ≤ totalDemand n b t := by
        simp only [totalDemand_eq_positive]
        apply Finset.sum_le_sum
        intro i _
        exact demand_antitone n hn i.property ht.le (le_of_not_gt hnot)
      rw [hr] at hs
      exact (not_lt_of_ge hs) hd
  · have hz : canonicalPrice n hn c b = 0 := by simp [canonicalPrice,hover]
    rw [hz]
    constructor
    · intro ht
      refine ⟨ht, ?_⟩
      have hle := totalDemand_le_count n b t ht.le
      by_cases hless : positiveCount b < c
      · exact hle.trans_lt (Nat.cast_lt.mpr hless)
      · have he : positiveCount b = c := by omega
        have he' : Fintype.card (PositiveIndex b) = c := he
        have hh := sum_demand_strict n hn (fun i : PositiveIndex b => b i.val)
          (fun i => i.property) (le_refl 0) ht
          (by rw [sum_demand_zero_price n hn,he']; exact hcR)
        rw [sum_demand_zero_price n hn,he'] at hh
        rw [totalDemand_eq_positive]
        exact hh
    · exact And.left

lemma measurable_activeDemand (n : ℕ) (hn : 2 ≤ n) :
    Measurable (fun z : ℝ × ℝ => activeDemand n z.1 z.2) := by
  unfold activeDemand demand
  apply Measurable.ite (measurableSet_lt measurable_const measurable_fst) _ measurable_const
  exact measurable_const.max (measurable_const.sub
    ((Real.continuous_rpow_const (rate_pos n hn).le).measurable.comp
      (measurable_snd.div measurable_fst)))

theorem measurable_canonicalPrice (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c) :
    Measurable (canonicalPrice (ι := ι) n hn c) := by
  apply measurable_of_Iio
  intro t
  have he : canonicalPrice n hn c ⁻¹' Iio t =
      {b : ι → ℝ | 0 < t} ∩ {b | totalDemand n b t < c} := by
    ext b
    exact canonicalPrice_lt_iff n hn c hc b t
  rw [he]
  apply (MeasurableSet.const _).inter
  have hm : Measurable (fun b : ι → ℝ => totalDemand n b t) := by
    unfold totalDemand
    apply Finset.measurable_sum
    intro i _
    have hpair : Measurable (fun b : ι → ℝ => (b i,t)) :=
      (measurable_pi_apply i).prodMk measurable_const
    have hh := (measurable_activeDemand n hn).comp hpair
    exact hh
  exact measurableSet_lt hm measurable_const

def canonicalMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (i : ι) : ℝ :=
  activeDemand n (b i) (canonicalPrice n hn c b)

lemma canonicalMarginal_bounds (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (i : ι) :
    0 ≤ canonicalMarginal n hn c b i ∧ canonicalMarginal n hn c b i ≤ 1 := by
  unfold canonicalMarginal activeDemand
  split_ifs with hb
  · exact ⟨demand_nonneg _ _ _, demand_le_one n hb (canonicalPrice_nonneg n hn c b)⟩
  · exact ⟨le_refl 0, zero_le_one⟩

lemma canonicalMarginal_nonpositive (n : ℕ) (hn : 2 ≤ n) (c : ℕ)
    (b : ι → ℝ) (i : ι) (hi : b i ≤ 0) : canonicalMarginal n hn c b i = 0 := by
  simp only [canonicalMarginal, activeDemand, if_neg (not_lt_of_ge hi)]

lemma canonicalMarginal_sum (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) :
    (∑ i, canonicalMarginal n hn c b i) = (min c (positiveCount b) : ℕ) := by
  change totalDemand n b (canonicalPrice n hn c b) = _
  by_cases hover : c < positiveCount b
  · rw [(canonicalPrice_overloaded n hn c b hover).2, Nat.min_eq_left hover.le]
  · have hz : canonicalPrice n hn c b = 0 := by simp [canonicalPrice,hover]
    rw [hz,totalDemand_eq_positive,sum_demand_zero_price n hn,Nat.min_eq_right (le_of_not_gt hover)]
    rfl

theorem measurable_canonicalMarginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c) :
    Measurable (canonicalMarginal (ι := ι) n hn c) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_activeDemand n hn).comp
    ((measurable_pi_apply i).prodMk (measurable_canonicalPrice n hn c hc))

variable [DecidableEq ι]

def canonicalLottery (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (canonicalMarginal n hn c b)

lemma canonicalLottery_implements (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) :
    ExactCapacity.Implements (canonicalMarginal n hn c b) (min c (positiveCount b))
      (canonicalLottery n hn c b) :=
  ExactCapacity.symmetricLottery_implements _ _
    (fun i => (canonicalMarginal_bounds n hn c b i).1)
    (fun i => (canonicalMarginal_bounds n hn c b i).2) (canonicalMarginal_sum n hn c b)

lemma canonicalLottery_marginal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (i : ι) :
    Proposer.marginal (canonicalLottery n hn c b) i = canonicalMarginal n hn c b i :=
  (canonicalLottery_implements n hn c b).2 i

omit [DecidableEq ι] in
lemma canonicalMarginal_underloaded (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ)
    (hc : positiveCount b ≤ c) (i : ι) :
    canonicalMarginal n hn c b i = if 0 < b i then 1 else 0 := by
  simp only [canonicalMarginal,canonicalPrice,dif_neg (not_lt_of_ge hc),activeDemand]
  split_ifs <;> simp only [demand_zero_price n hn]

omit [DecidableEq ι] in

lemma canonical_receipt_le_price (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) (i : ι) :
    b i * (1-canonicalMarginal n hn c b i)^(n-1) ≤ canonicalPrice n hn c b := by
  by_cases hb : 0 < b i
  · by_cases hover : c < positiveCount b
    · have hp := (canonicalPrice_overloaded n hn c b hover).1
      change b i * (1-activeDemand n (b i) (canonicalPrice n hn c b))^(n-1) ≤ _
      rw [activeDemand,if_pos hb,demand_receipt n hn hb hp]
      exact min_le_right _ _
    · rw [canonicalMarginal_underloaded n hn c b (le_of_not_gt hover) i,if_pos hb]
      simp only [sub_self,zero_pow (by omega : n-1 ≠ 0),mul_zero]
      exact canonicalPrice_nonneg n hn c b
  · rw [canonicalMarginal_nonpositive n hn c b i (le_of_not_gt hb)]
    simpa only [sub_zero,one_pow,mul_one] using
      (le_of_not_gt hb).trans (canonicalPrice_nonneg n hn c b)

omit [DecidableEq ι] in

lemma canonical_receipt_of_marginal_pos (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ)
    (i : ι) (hi : 0 < canonicalMarginal n hn c b i) :
    b i * (1-canonicalMarginal n hn c b i)^(n-1) = canonicalPrice n hn c b := by
  have hb : 0 < b i := by
    by_contra h
    rw [canonicalMarginal_nonpositive n hn c b i (le_of_not_gt h)] at hi
    exact (lt_irrefl _) hi
  by_cases hover : c < positiveCount b
  · have hp := (canonicalPrice_overloaded n hn c b hover).1
    have hd : canonicalMarginal n hn c b i = demand n (b i) (canonicalPrice n hn c b) := by
      simp only [canonicalMarginal,activeDemand,if_pos hb]
    rw [hd] at hi ⊢
    rw [demand_receipt n hn hb hp]
    exact min_eq_right ((demand_pos_iff n hn hb hp.le).mp hi).le
  · rw [canonicalMarginal_underloaded n hn c b (le_of_not_gt hover) i,if_pos hb]
    simp only [sub_self,zero_pow (by omega : n-1 ≠ 0),mul_zero]
    simp only [canonicalPrice,dif_neg hover]

theorem canonicalLottery_support_optimal (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) :
    ∀ S, (canonicalLottery n hn c b).mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * (1-canonicalMarginal n hn c b i)^(n-1)) S := by
  intro S hS
  have hcard := (canonicalLottery_implements n hn c b).1 S hS
  have hprice := canonicalPrice_nonneg n hn c b
  have hsel : ∀ i ∈ S, b i * (1-canonicalMarginal n hn c b i)^(n-1) =
      canonicalPrice n hn c b := by
    intro i hi
    apply canonical_receipt_of_marginal_pos n hn c b i
    have hp := FiniteLaw.marginal_pos_of_support_mem (canonicalLottery n hn c b) S hS i hi
    rwa [(canonicalLottery_implements n hn c b).2 i] at hp
  have hvalue : (c : ℝ)*canonicalPrice n hn c b = (S.card : ℝ)*canonicalPrice n hn c b := by
    by_cases hover : c < positiveCount b
    · rw [hcard,Nat.min_eq_left hover.le]
    · simp only [canonicalPrice,dif_neg hover,mul_zero]
  refine ⟨hcard.le.trans (Nat.min_le_left _ _),?_⟩
  intro T hT
  calc
    (∑ i ∈ T, b i * (1-canonicalMarginal n hn c b i)^(n-1)) ≤
        ∑ _i ∈ T, canonicalPrice n hn c b :=
      Finset.sum_le_sum fun i _ => canonical_receipt_le_price n hn c b i
    _ = (T.card : ℝ)*canonicalPrice n hn c b := by simp
    _ ≤ (c : ℝ)*canonicalPrice n hn c b :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hT) hprice
    _ = (S.card : ℝ)*canonicalPrice n hn c b := hvalue
    _ = ∑ _i ∈ S, canonicalPrice n hn c b := by simp
    _ = ∑ i ∈ S, b i * (1-canonicalMarginal n hn c b i)^(n-1) :=
      Finset.sum_congr rfl fun i hi => (hsel i hi).symm

theorem canonicalLottery_equilibrium (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (b : ι → ℝ) :
    ExclusiveEquilibrium n c b (canonicalLottery n hn c b) := by
  refine ⟨fun S hS => (canonicalLottery_support_optimal n hn c b S hS).1,?_⟩
  intro ν hν
  rw [exclusive_payoff_eq,exclusive_payoff_eq]
  rw [← Proposer.revenue_marginals,← Proposer.revenue_marginals]
  unfold Proposer.revenue
  simp_rw [canonicalLottery_marginal]
  apply (canonicalLottery n hn c b).const_le_expect_of_support
  intro S hS
  apply ν.expect_le_const_of_support
  intro T hT
  exact (canonicalLottery_support_optimal n hn c b S hS).2 T (hν T hT)

def readBid : Option ℝ → ℝ
  | none => 0
  | some b => b

lemma measurable_readBid : Measurable readBid := by
  intro E hE
  change MeasurableSet ((fun b : ℝ => b) ⁻¹' E)
  exact hE

def listBids {m : ℕ} (L : LocalList m) : Fin m → ℝ := fun i => readBid (L i)
lemma measurable_listBids (m : ℕ) : Measurable (listBids (m := m)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_readBid.comp (measurable_pi_apply i)

def canonicalListMarginal {m : ℕ} (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (L : LocalList m) : Fin m → ℝ :=
  canonicalMarginal n hn c (listBids L)

lemma measurable_canonicalListMarginal (m n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c) :
    Measurable (canonicalListMarginal (m := m) n hn c) :=
  (measurable_canonicalMarginal n hn c hc).comp (measurable_listBids m)

theorem exists_canonical_localPolicy (m n c : ℕ) (hn : 2 ≤ n) (hc : 0 < c) :
    ∃ (policy : LocalPolicy m c unitInterval)
      (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)),
      ∀ L, FiniteLaw.ofMeasure volume (fun u => (policy L u).val)
        (hpolicy.comp (measurable_const.prodMk measurable_id)) =
        canonicalLottery n hn c (listBids L) := by
  apply Game.exists_measurable_localPolicy_finiteLaw
    (canonicalListMarginal n hn c) (measurable_canonicalListMarginal m n hn c hc)
    (fun L => min c (positiveCount (listBids L))) (fun _ => Nat.min_le_left _ _)
    (fun L i => (canonicalMarginal_bounds n hn c (listBids L) i).1)
    (fun L i => (canonicalMarginal_bounds n hn c (listBids L) i).2)
    (fun L => canonicalMarginal_sum n hn c (listBids L))
  intro L i hi
  apply canonicalMarginal_nonpositive n hn c (listBids L) i
  simp only [listBids,hi,readBid,le_refl]

omit [DecidableEq ι] in

lemma totalDemand_relabel (n : ℕ) (b : ι → ℝ) (e : Equiv.Perm ι) (t : ℝ) :
    totalDemand n (b ∘ e) t = totalDemand n b t :=
  Equiv.sum_comp e (fun i => activeDemand n (b i) t)

omit [DecidableEq ι] in

theorem canonicalPrice_relabel (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (e : Equiv.Perm ι) :
    canonicalPrice n hn c (b ∘ e) = canonicalPrice n hn c b := by
  have he (t : ℝ) : canonicalPrice n hn c (b ∘ e) < t ↔ canonicalPrice n hn c b < t := by
    rw [canonicalPrice_lt_iff n hn c hc,canonicalPrice_lt_iff n hn c hc,totalDemand_relabel]
  apply le_antisymm
  · exact le_of_not_gt fun h => (lt_irrefl _) ((he (canonicalPrice n hn c (b ∘ e))).mpr h)
  · exact le_of_not_gt fun h => (lt_irrefl _) ((he (canonicalPrice n hn c b)).mp h)

omit [DecidableEq ι] in
theorem canonicalMarginal_relabel (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (e : Equiv.Perm ι) :
    canonicalMarginal n hn c (b ∘ e) = canonicalMarginal n hn c b ∘ e := by
  funext i
  simp only [canonicalMarginal,Function.comp_apply,canonicalPrice_relabel n hn c hc]

theorem canonicalLottery_relabel (n : ℕ) (hn : 2 ≤ n) (c : ℕ) (hc : 0 < c)
    (b : ι → ℝ) (e : Equiv.Perm ι) :
    canonicalLottery n hn c (b ∘ e.symm) =
      (canonicalLottery n hn c b).map (fun S => S.map e.toEmbedding) := by
  unfold canonicalLottery
  rw [canonicalMarginal_relabel n hn c hc]
  exact ExactCapacity.symmetricLottery_equivariant _ e

end FCAppendix.Exclusive
