import FCAppendix.Affine.Tail04.WeightedBernoulliInterval
import FCAppendix.Affine.Tail04.RankForcedFlags
import FCAppendix.Affine.Tail04.TypicalLottery

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bernoulli_interval_from_bulk (p w : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (J : Finset ι) (hJ : J.Nonempty) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i ∈ J, epsilon ≤ p i) (hp' : ∀ i ∈ J, p i ≤ 1-epsilon)
    {a : ℝ} (ha : 0 < a) (hw : ∀ i ∈ J, a ≤ |w i|) (l : ℝ) (r : ℕ) :
    (BidDependentFlags.flags p hp0 hp1).prob
      (fun flags => weightedSum w flags ∈ Ico l (l+(r:ℝ)*a)) ≤
      2/(epsilon*(J.card : ℝ)) + (r:ℝ)*Real.sqrt (2/(epsilon*(J.card : ℝ)+1)) := by
  classical
  letI : Fintype {i : ι // i ∈ J} := Subtype.fintype (fun i => i ∈ J)
  letI : Fintype {i : ι // i ∉ J} := Subtype.fintype (fun i => i ∉ J)
  let core := fun i : {i // i ∈ J} => IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)
  let rest := fun i : {i // i ∉ J} => IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)
  let coreWeight := fun i : {i // i ∈ J} => w i
  let restWeight := fun i : {i // i ∉ J} => w i
  have hsum (flags : ι → Bool) : weightedSum w flags =
      weightedSum coreWeight (fun i => flags i) +
        weightedSum restWeight (fun i => flags i) := by
    unfold weightedSum coreWeight restWeight
    exact (Fintype.sum_subtype_add_sum_subtype (p := fun i => i ∈ J)
      (fun i => w i * bit (flags i))).symm
  have heq : (BidDependentFlags.flags p hp0 hp1).prob
      (fun flags => weightedSum w flags ∈ Ico l (l+(r:ℝ)*a)) =
      ((BidDependentFlags.product core).prod (BidDependentFlags.product rest)).expect
        (fun z => if weightedSum coreWeight z.1 + weightedSum restWeight z.2 ∈
          Ico l (l+(r:ℝ)*a) then 1 else 0) := by
    rw [← BidDependentFlags.product_split
      (fun i => IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)) (fun i => i ∈ J),
      FiniteLaw.expect_map, FiniteLaw.prob_eq_expect]
    apply FiniteLaw.expect_congr
    intro flags
    rw [hsum]
  rw [heq, FiniteLaw.expect_prod, finite_expect_swap]
  apply FiniteLaw.expect_le_const
  intro outside
  have heq' : (BidDependentFlags.product core).expect
      (fun inside => if weightedSum coreWeight inside + weightedSum restWeight outside ∈
        Ico l (l+(r:ℝ)*a) then 1 else 0) =
      (BidDependentFlags.product core).prob (fun inside => weightedSum coreWeight inside ∈
        Ico (l-weightedSum restWeight outside) (l-weightedSum restWeight outside+(r:ℝ)*a)) := by
    rw [FiniteLaw.prob_eq_expect]
    apply FiniteLaw.expect_congr
    intro inside
    congr 1
    simp only [Set.mem_Ico]
    apply propext
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [heq']
  have hcard : Fintype.card {i // i ∈ J} = J.card := by
    simp [Fintype.card_subtype]
  have hN : 0 < Fintype.card {i // i ∈ J} := by
    rw [hcard]
    exact Finset.card_pos.mpr hJ
  have hh := bernoulli_weighted_interval epsilon (fun i : {i // i ∈ J} => p i)
    coreWeight heps heps' (fun i => hp i i.property) (fun i => hp' i i.property)
    hN ha (fun i => hw i i.property) (l-weightedSum restWeight outside) r
  simpa only [hcard,BidDependentFlags.flags,core] using hh

theorem weightedSum_forceExclusive (w : ι → ℝ) (target : ι) (flags : ι → Bool) :
    weightedSum w (forceExclusive target flags) = weightedSum w flags - w target * bit (flags target) := by
  have hterm (i : ι) :
      w i * bit (forceExclusive target flags i) =
        w i * bit (flags i) - (if i=target then w target * bit (flags target) else 0) := by
    by_cases hi : i=target
    · subst i
      simp [forceExclusive, bit]
    · simp [forceExclusive, hi]
  unfold weightedSum
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp

theorem forcing_changes_weight_by_le (w : ι → ℝ) (target : ι) (flags : ι → Bool)
    {C : ℝ} (hC : |w target| ≤ C) :
    |weightedSum w (forceExclusive target flags)-weightedSum w flags| ≤ C := by
  rw [weightedSum_forceExclusive]
  cases flags target <;> simp [bit]
  · exact (abs_nonneg (w target)).trans hC
  · exact hC

theorem forced_interval_from_bulk (targetLaw : FiniteLaw ι) (p w : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (J : Finset ι) (hJ : J.Nonempty) {epsilon : ℝ}
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i ∈ J, epsilon ≤ p i) (hp' : ∀ i ∈ J, p i ≤ 1-epsilon)
    {a : ℝ} (ha : 0 < a) (hw : ∀ i ∈ J, a ≤ |w i|)
    {C : ℝ} (hweight : ∀ i, |w i| ≤ C) (l : ℝ) (r rWide : ℕ)
    (hwidth : (r:ℝ)*a + 2*C ≤ (rWide:ℝ)*a) :
    (targetLaw.prod (BidDependentFlags.flags p hp0 hp1)).prob
      (fun z => weightedSum w (forceExclusive z.1 z.2) ∈ Ico l (l+(r:ℝ)*a)) ≤
      2/(epsilon*(J.card : ℝ)) + (rWide:ℝ)*Real.sqrt (2/(epsilon*(J.card : ℝ)+1)) := by
  rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_prod]
  apply FiniteLaw.expect_le_const
  intro target
  have hsub : (BidDependentFlags.flags p hp0 hp1).prob
      (fun flags => weightedSum w (forceExclusive target flags) ∈ Ico l (l+(r:ℝ)*a)) ≤
      (BidDependentFlags.flags p hp0 hp1).prob
        (fun flags => weightedSum w flags ∈ Ico (l-C) (l-C+(rWide:ℝ)*a)) := by
    apply FiniteLaw.prob_mono
    intro flags hflags
    have hchange := (abs_le.mp (forcing_changes_weight_by_le w target flags (hweight target)))
    constructor <;> linarith [hflags.1,hflags.2,hchange.1,hchange.2]
  simpa only [FiniteLaw.prob_eq_expect] using
    hsub.trans (bernoulli_interval_from_bulk p w hp0 hp1 J hJ heps heps' hp hp' ha hw (l-C) rWide)

def unusedCoefficient (xi bid : ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  bid / b i - (1-xi/2)

theorem unusedCoefficient_separated {xi bid a bi : ℝ}
    (hbid : 0 ≤ bid) (hbi : 1 ≤ bi) (hprice : bid ≤ 1-xi/2-a) :
    a ≤ |bid/bi-(1-xi/2)| := by
  have hbi0 : 0 < bi := by linarith
  have hquot : bid/bi ≤ bid := by
    apply (div_le_iff₀ hbi0).mpr
    simpa using mul_le_mul_of_nonneg_left hbi hbid
  have hh := neg_le_abs (bid/bi-(1-xi/2))
  linarith

theorem unusedCoefficient_abs_le_one {xi bid bi : ℝ}
    (hxi0 : 0 ≤ xi) (_hxi2 : xi ≤ 2) (hbid0 : 0 ≤ bid)
    (hprice : bid ≤ 1-xi/2) (hbi : 1 ≤ bi) :
    |bid/bi-(1-xi/2)| ≤ 1 := by
  have hbi0 : 0 < bi := by linarith
  have hquot0 : 0 ≤ bid/bi := div_nonneg hbid0 hbi0.le
  have hquot1 : bid/bi ≤ bid := by
    apply (div_le_iff₀ hbi0).mpr
    simpa using mul_le_mul_of_nonneg_left hbi hbid0
  apply abs_le.mpr
  constructor <;> linarith

theorem unused_common_bid_interval [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (J : Finset ι) (hJ : J.Nonempty) {epsilon xi bid a : ℝ}
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i ∈ J, epsilon ≤ p i) (hp' : ∀ i ∈ J, p i ≤ 1-epsilon)
    (hxi0 : 0 ≤ xi) (hxi2 : xi ≤ 2) (hbid0 : 0 ≤ bid)
    (ha : 0 < a) (hprice : bid ≤ 1-xi/2-a) (hb : ∀ i, 1 ≤ b i)
    (l : ℝ) (r rWide : ℕ) (hwidth : (r:ℝ)*a+2 ≤ (rWide:ℝ)*a) :
    (rankForcedFlagLaw b p hp0 hp1).prob
      (fun z => weightedSum (unusedCoefficient xi bid b) z.2 ∈
        Ico l (l+(r:ℝ)*a)) ≤
      2/(epsilon*(J.card : ℝ)) + (rWide:ℝ)*Real.sqrt (2/(epsilon*(J.card : ℝ)+1)) := by
  have heq : independentFlagLaw p hp0 hp1 = BidDependentFlags.flags p hp0 hp1 := by
    apply FiniteLaw.ext
    intro flags
    rfl
  rw [rankForcedFlagLaw, heq, FiniteLaw.prob_eq_expect, FiniteLaw.expect_map]
  simpa only [FiniteLaw.prob_eq_expect] using forced_interval_from_bulk (Hybrid.rankLaw b) p (unusedCoefficient xi bid b)
    hp0 hp1 J hJ heps heps' hp hp' ha
    (fun i _ => unusedCoefficient_separated hbid0 (hb i) hprice)
    (C:=1) (fun i => unusedCoefficient_abs_le_one hxi0 hxi2 hbid0
      (by linarith) (hb i)) l r rWide (by simpa using hwidth)

end FCAppendix.Affine.Tail04.WeightedFlagBound
