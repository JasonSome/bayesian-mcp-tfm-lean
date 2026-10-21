import FCAppendix.Affine.Tail04.IntegerOwnerBalance

noncomputable section
namespace FCAppendix.Affine.Tail04.WeightedFlagBound
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def BetweenPrices (L1 bid L2 : ℝ) : Prop :=
  (L1 ≤ bid ∧ bid ≤ L2) ∨ (L2 ≤ bid ∧ bid ≤ L1)

def firstOwnerCount (N : ℕ) (mean1 mean2 : ℝ) (flags : ι → Bool) : ℕ :=
  balancedOwnerQuota (N-(flaggedMixedSet flags).card) mean1 mean2

def secondOwnerCount (N : ℕ) (mean1 mean2 : ℝ) (flags : ι → Bool) : ℕ :=
  (N-(flaggedMixedSet flags).card)-firstOwnerCount N mean1 mean2 flags

def intermediateCenter (xi : ℝ) (c N : ℕ) (mean1 mean2 : ℝ) : ℝ :=
  -xi*((c:ℝ)-(N:ℝ)/2-(mean1+mean2)/2)

theorem intermediate_implies_short_interval (xi bid : ℝ) (c N : ℕ)
    (mean1 mean2 : ℝ) (b : ι → ℝ) (flags : ι → Bool)
    (hxi : 0 ≤ xi) (hM : (flaggedMixedSet flags).card ≤ N)
    (hW : 0 < mixedReciprocalSum (flaggedMixedSet flags) b)
    (hmean : |mean2-mean1| ≤ (N-(flaggedMixedSet flags).card : ℕ))
    (hbetween : BetweenPrices
      (meanMixedPrice xi c (firstOwnerCount N mean1 mean2 flags) mean1 (flaggedMixedSet flags) b)
      bid
      (meanMixedPrice xi c (secondOwnerCount N mean1 mean2 flags) mean2 (flaggedMixedSet flags) b)) :
    weightedSum (unusedCoefficient xi bid b) flags ∈
      Icc (intermediateCenter xi c N mean1 mean2-xi/2)
        (intermediateCenter xi c N mean1 mean2+xi/2) := by
  obtain ⟨e1,e2,he1,he2,he1b,he2b,_⟩ :=
    balancedOwnerQuota_price_errors (N-(flaggedMixedSet flags).card) mean1 mean2 hmean
  have hcast : ((N-(flaggedMixedSet flags).card : ℕ):ℝ) =
      (N:ℝ)-(flaggedMixedSet flags).card := Nat.cast_sub hM
  rw [hcast] at he1 he2
  have hb1 : (firstOwnerCount N mean1 mean2 flags:ℝ) =
      ((N:ℝ)-(flaggedMixedSet flags).card+mean2-mean1)/2+e1 := he1
  have hb2 : (secondOwnerCount N mean1 mean2 flags:ℝ) =
      ((N:ℝ)-(flaggedMixedSet flags).card+mean1-mean2)/2+e2 := he2
  have hidentity1 := unused_price_weighted_identity xi bid c
    (firstOwnerCount N mean1 mean2 flags) N mean1 mean2 e1 b flags hW.ne' hb1
  have hidentity2 := unused_price_weighted_identity xi bid c
    (secondOwnerCount N mean1 mean2 flags) N mean2 mean1 e2 b flags hW.ne' hb2
  have he1lo := mul_le_mul_of_nonneg_left (abs_le.mp he1b).1 hxi
  have he1hi := mul_le_mul_of_nonneg_left (abs_le.mp he1b).2 hxi
  have he2lo := mul_le_mul_of_nonneg_left (abs_le.mp he2b).1 hxi
  have he2hi := mul_le_mul_of_nonneg_left (abs_le.mp he2b).2 hxi
  rcases hbetween with hbetween | hbetween
  · have hpos := mul_nonneg hW.le (sub_nonneg.mpr hbetween.1)
    have hneg := mul_nonpos_of_nonneg_of_nonpos hW.le (sub_nonpos.mpr hbetween.2)
    rw [hidentity1] at hpos
    rw [hidentity2] at hneg
    constructor <;> dsimp [intermediateCenter] <;> nlinarith
  · have hpos := mul_nonneg hW.le (sub_nonneg.mpr hbetween.1)
    have hneg := mul_nonpos_of_nonneg_of_nonpos hW.le (sub_nonpos.mpr hbetween.2)
    rw [hidentity2] at hpos
    rw [hidentity1] at hneg
    constructor <;> dsimp [intermediateCenter] <;> nlinarith

theorem exists_interval_cover {xi a : ℝ} (_hxi : 0 ≤ xi) (ha : 0 < a) :
    ∃ r rWide : ℕ, xi < (r:ℝ)*a ∧ (r:ℝ)*a+2 ≤ (rWide:ℝ)*a := by
  let r : ℕ := ⌈xi/a⌉₊+1
  let extra : ℕ := ⌈2/a⌉₊+1
  have h1 := mul_le_mul_of_nonneg_right (Nat.le_ceil (xi/a)) ha.le
  have h2 := mul_le_mul_of_nonneg_right (Nat.le_ceil ((2:ℝ)/a)) ha.le
  rw [div_mul_cancel₀ _ ha.ne'] at h1
  rw [div_mul_cancel₀ _ ha.ne'] at h2
  refine ⟨r,r+extra,?_,?_⟩
  · dsimp [r]
    push_cast
    nlinarith
  · dsimp [extra]
    push_cast
    nlinarith

def GuardedIntermediate (xi a bid : ℝ) (c : ℕ) (mean1 mean2 : ℝ)
    (b : ι → ℝ) (flags : ι → Bool) : Prop :=
  let N := Fintype.card ι
  let I := flaggedMixedSet flags
  let L1 := meanMixedPrice xi c (firstOwnerCount N mean1 mean2 flags) mean1 I b
  let L2 := meanMixedPrice xi c (secondOwnerCount N mean1 mean2 flags) mean2 I b
  0 < mixedReciprocalSum I b ∧
    |mean2-mean1| ≤ (N-I.card : ℕ) ∧
    L1 ≤ 1-xi/2-a ∧ L2 ≤ 1-xi/2-a ∧ BetweenPrices L1 bid L2

theorem guarded_intermediate_probability [Nonempty ι] (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (J : Finset ι) (hJ : J.Nonempty) {epsilon xi bid a : ℝ}
    (heps : 0 < epsilon) (heps' : epsilon < 1/2)
    (hp : ∀ i ∈ J, epsilon ≤ p i) (hp' : ∀ i ∈ J, p i ≤ 1-epsilon)
    (hxi0 : 0 ≤ xi) (hxi2 : xi ≤ 2) (hbid : 0 ≤ bid)
    (ha : 0 < a) (hb : ∀ i, 1 ≤ b i) (c : ℕ) (mean1 mean2 : ℝ)
    (r rWide : ℕ) (hcover : xi < (r:ℝ)*a)
    (hwidth : (r:ℝ)*a+2 ≤ (rWide:ℝ)*a) :
    (rankForcedFlagLaw b p hp0 hp1).prob
      (fun z => GuardedIntermediate xi a bid c mean1 mean2 b z.2) ≤
      2/(epsilon*(J.card:ℝ))+(rWide:ℝ)*Real.sqrt (2/(epsilon*(J.card:ℝ)+1)) := by
  classical
  by_cases hprice : bid ≤ 1-xi/2-a
  · let l := intermediateCenter xi c (Fintype.card ι) mean1 mean2-xi/2
    have hsub : (rankForcedFlagLaw b p hp0 hp1).prob
        (fun z => GuardedIntermediate xi a bid c mean1 mean2 b z.2) ≤
        (rankForcedFlagLaw b p hp0 hp1).prob
          (fun z => weightedSum (unusedCoefficient xi bid b) z.2 ∈ Ico l (l+(r:ℝ)*a)) := by
      apply FiniteLaw.prob_mono
      intro z hz
      have hM : (flaggedMixedSet z.2).card ≤ Fintype.card ι :=
        Finset.card_le_card (Finset.subset_univ _)
      have hi := intermediate_implies_short_interval xi bid c (Fintype.card ι)
        mean1 mean2 b z.2 hxi0 hM hz.1 hz.2.1 hz.2.2.2.2
      exact ⟨hi.1,by dsimp [l]; linarith [hi.2]⟩
    exact hsub.trans (unused_common_bid_interval b p hp0 hp1 J hJ heps heps' hp hp'
      hxi0 hxi2 hbid ha hprice hb l r rWide hwidth)
  · have hempty : (rankForcedFlagLaw b p hp0 hp1).prob
        (fun z => GuardedIntermediate xi a bid c mean1 mean2 b z.2)=0 := by
      rw [FiniteLaw.prob_eq_expect]
      have he (z : ι × (ι → Bool)) :
          ¬ GuardedIntermediate xi a bid c mean1 mean2 b z.2 := by
        intro hz
        rcases hz.2.2.2.2 with hbetween | hbetween
        · exact hprice (hbetween.2.trans hz.2.2.2.1)
        · exact hprice (hbetween.2.trans hz.2.2.1)
      simp only [if_neg (he _),FiniteLaw.expect_const]
    rw [hempty]
    have hJpos : 0 < (J.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hJ)
    positivity

end FCAppendix.Affine.Tail04.WeightedFlagBound
