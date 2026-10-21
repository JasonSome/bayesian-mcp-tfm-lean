import FCAppendix.Affine.Tail04.TypicalCountLaws
import FCAppendix.Affine.Tail04.FlagActivationMoments
import FCAppendix.Affine.Tail04.NativeFlagTransport
import FCAppendix.Affine.Hybrid.FavoredRankJump

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def mixedSelectionUtility (left right : FiniteLaw (Finset ι)) (i : ι)
    (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  (twoSelectionCountLaw left right i).utility v bi 0
    (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2)

def exclusiveUtility (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  CountLaw.utility (n := 2) (FiniteLaw.dirac (1 : Fin 3)) v bi 0
    (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2)

def selectionPromotionGap (left right : FiniteLaw (Finset ι)) (i : ι)
    (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  exclusiveUtility v bi eta heta0 heta1-
    mixedSelectionUtility left right i v bi eta heta0 heta1

theorem selectionPromotionGap_eq (left right : FiniteLaw (Finset ι)) (i : ι)
    (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    selectionPromotionGap left right i v bi eta heta0 heta1 =
      twoMixedFavoredGain v bi eta (left.prob (fun S => i ∈ S))
        (right.prob (fun S => i ∈ S)) :=
  actual_exclusive_minus_mixed left right i eta v bi heta0 heta1

theorem selectionPromotionGap_nonneg (left right : FiniteLaw (Finset ι)) (i : ι)
    {v bi eta : ℝ} (hvb : bi ≤ v) (hb : 0 ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 ≤ selectionPromotionGap left right i v bi eta heta0 heta1 := by
  rw [selectionPromotionGap_eq]
  simpa only [mul_zero, zero_mul] using twoMixedFavoredGain_lower
    (L:=0) (qmin:=0) hvb heta0 le_rfl hb le_rfl
    (left.prob_nonneg (fun S => i ∈ S)) (right.prob_nonneg (fun S => i ∈ S))
    (left.prob_le_one (fun S => i ∈ S)) (right.prob_le_one (fun S => i ∈ S))

theorem selectionPromotionGap_upper (left right : FiniteLaw (Finset ι)) (i : ι)
    {v bi eta : ℝ} (hvb : bi ≤ v) (hb : 0 ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    selectionPromotionGap left right i v bi eta heta0 heta1 ≤ (v-bi)+eta*bi := by
  let p := left.prob (fun S => i ∈ S)
  let q := right.prob (fun S => i ∈ S)
  have hp0 : 0 ≤ p := left.prob_nonneg _
  have hp1 : p ≤ 1 := left.prob_le_one _
  have hq0 : 0 ≤ q := right.prob_nonneg _
  have hq1 : q ≤ 1 := right.prob_le_one _
  have hfail : (1-p)*(1-q) ≤ 1 :=
    (mul_le_mul (by linarith : 1-p ≤ 1) (by linarith : 1-q ≤ 1)
      (by linarith : 0 ≤ 1-q) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)
  have hdup : p*q ≤ 1 :=
    (mul_le_mul hp1 hq1 hq0 (by norm_num : (0:ℝ) ≤ 1)).trans_eq (by ring)
  have hf := mul_le_mul_of_nonneg_left hfail (sub_nonneg.mpr hvb)
  have hd := mul_le_mul_of_nonneg_left hdup (mul_nonneg heta0 hb)
  rw [selectionPromotionGap_eq]
  unfold twoMixedFavoredGain
  change (v-bi)*(1-p)*(1-q)+eta*bi*p*q ≤ _
  nlinarith only [hf,hd]

def beforePromotionLaw (mu : FiniteLaw Ω)
    (left right : Ω → FiniteLaw (Finset ι)) (i : ι) : CountLaw 2 :=
  FiniteLaw.finiteMix mu (fun omega => twoSelectionCountLaw (left omega) (right omega) i)

def afterPromotionLaw (mu : FiniteLaw Ω)
    (left right : Ω → FiniteLaw (Finset ι)) (i : ι)
    (chi : Ω → ℝ) (hchi0 : ∀ omega, 0 ≤ chi omega) (hchi1 : ∀ omega, chi omega ≤ 1) :
    CountLaw 2 :=
  FiniteLaw.finiteMix mu (fun omega =>
    FiniteLaw.mixture (FiniteLaw.dirac 1)
      (twoSelectionCountLaw (left omega) (right omega) i)
      (chi omega) (hchi0 omega) (hchi1 omega))

def localPromotionGain (mu : FiniteLaw Ω)
    (left right : Ω → FiniteLaw (Finset ι)) (i : ι) (chi : Ω → ℝ)
    (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  mu.expect (fun omega => chi omega*
    selectionPromotionGap (left omega) (right omega) i v bi eta heta0 heta1)

theorem actual_count_law_promotion_gain (mu : FiniteLaw Ω)
    (left right : Ω → FiniteLaw (Finset ι)) (i : ι)
    (chi : Ω → ℝ) (hchi0 : ∀ omega, 0 ≤ chi omega) (hchi1 : ∀ omega, chi omega ≤ 1)
    (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    (afterPromotionLaw mu left right i chi hchi0 hchi1).utility v bi 0
        (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2)-
      (beforePromotionLaw mu left right i).utility v bi 0
        (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2) =
      localPromotionGain mu left right i chi v bi eta heta0 heta1 := by
  unfold afterPromotionLaw beforePromotionLaw CountLaw.utility localPromotionGain
  rw [FiniteLaw.expect_finiteMix,FiniteLaw.expect_finiteMix,← FiniteLaw.expect_sub]
  apply mu.expect_congr
  intro omega
  rw [FiniteLaw.expect_mixture]
  dsimp [selectionPromotionGap,exclusiveUtility,mixedSelectionUtility,CountLaw.utility]
  ring

theorem localPromotionGain_bounds (mu : FiniteLaw Ω)
    (left right : Ω → FiniteLaw (Finset ι)) (i : ι)
    (chi : Ω → ℝ) (hchi0 : ∀ omega, 0 ≤ chi omega) (hchi1 : ∀ omega, chi omega ≤ 1)
    {v bi eta : ℝ} (hvb : bi ≤ v) (hb : 0 ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 ≤ localPromotionGain mu left right i chi v bi eta heta0 heta1 ∧
      localPromotionGain mu left right i chi v bi eta heta0 heta1 ≤ (v-bi)+eta*bi := by
  constructor
  · exact mu.expect_nonneg (fun omega => mul_nonneg (hchi0 omega)
      (selectionPromotionGap_nonneg _ _ _ hvb hb heta0 heta1))
  · apply mu.expect_le_const
    intro omega
    calc
      _ ≤ selectionPromotionGap (left omega) (right omega) i v bi eta heta0 heta1 :=
        mul_le_of_le_one_left
          (selectionPromotionGap_nonneg _ _ _ hvb hb heta0 heta1) (hchi1 omega)
      _ ≤ _ := selectionPromotionGap_upper _ _ _ hvb hb heta0 heta1

theorem actual_pair_flag_probability (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i j : ι) (hij : i ≠ j) :
    (independentFlagLaw p hp0 hp1).prob (fun flags => flags i=true ∧ flags j=true) =
      p i*p j := by
  rw [FiniteLaw.prob_eq_expect]
  calc
    _ = (BidDependentFlags.product (fun k =>
        IndependentCounts.bernoulli (p k) (hp0 k) (hp1 k))).expect
        (fun flags => (if flags i=true then (1:ℝ) else 0)*
          (if flags j=true then (1:ℝ) else 0)) := by
      apply FiniteLaw.expect_congr
      intro flags
      by_cases hi : flags i=true <;> by_cases hj : flags j=true <;> simp [hi,hj]
    _ = _ := by
      rw [WeightedFlagBound.expect_distinct_coordinates _ i j hij
        (fun a : Bool => if a = true then (1:ℝ) else 0)
        (fun a : Bool => if a = true then (1:ℝ) else 0)]
      simp only [FiniteLaw.expect_singleton]
      rfl

theorem pair_good_probability_lower (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i j : ι) (hij : i ≠ j)
    (good : (ι → Bool) → Prop) :
    p i*p j-(independentFlagLaw p hp0 hp1).prob (fun flags => ¬good flags) ≤
      (independentFlagLaw p hp0 hp1).prob
        (fun flags => flags i=true ∧ flags j=true ∧ good flags) := by
  classical
  have h := (independentFlagLaw p hp0 hp1).prob_inter_lower
    (fun flags => flags i=true ∧ flags j=true) good
  rw [actual_pair_flag_probability p hp0 hp1 i j hij] at h
  have hc := (independentFlagLaw p hp0 hp1).prob_compl good
  have he : (independentFlagLaw p hp0 hp1).prob
      (fun flags => (flags i=true ∧ flags j=true) ∧ good flags) =
      (independentFlagLaw p hp0 hp1).prob
        (fun flags => flags i=true ∧ flags j=true ∧ good flags) := by
    rw [FiniteLaw.prob_eq_expect, FiniteLaw.prob_eq_expect]
    apply FiniteLaw.expect_congr
    intro flags
    simp only [and_assoc]
  rw [he] at h
  linarith

theorem flagged_localPromotionGain_lower (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i j : ι) (hij : i ≠ j)
    (left right : (ι → Bool) → FiniteLaw (Finset ι))
    (chi : (ι → Bool) → ℝ) (hchi0 : ∀ flags, 0 ≤ chi flags)
    (good : (ι → Bool) → Prop) (hgood : ∀ flags, good flags → chi flags=1)
    {v bi eta L qmin : ℝ} (hvb : bi ≤ v) (hL : 0 ≤ L) (hb : L ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hqmin : 0 ≤ qmin)
    (hleft : ∀ flags, flags i=true → flags j=true → good flags →
      qmin ≤ (left flags).prob (fun S => i ∈ S))
    (hright : ∀ flags, flags i=true → flags j=true → good flags →
      qmin ≤ (right flags).prob (fun S => i ∈ S)) :
    (eta*L*qmin^2)*(p i*p j-
        (independentFlagLaw p hp0 hp1).prob (fun flags => ¬good flags)) ≤
      localPromotionGain (independentFlagLaw p hp0 hp1) left right i chi
        v bi eta heta0 heta1 := by
  classical
  let g := eta*L*qmin^2
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hpoint (flags : ι → Bool) :
      (if flags i=true ∧ flags j=true ∧ good flags then g else 0) ≤
        chi flags*selectionPromotionGap (left flags) (right flags) i v bi eta heta0 heta1 := by
    by_cases h : flags i=true ∧ flags j=true ∧ good flags
    · rw [if_pos h,hgood flags h.2.2,one_mul,selectionPromotionGap_eq]
      exact twoMixedFavoredGain_lower hvb heta0 hL hb hqmin
        (hleft flags h.1 h.2.1 h.2.2) (hright flags h.1 h.2.1 h.2.2)
        ((left flags).prob_le_one _) ((right flags).prob_le_one _)
    · rw [if_neg h]
      exact mul_nonneg (hchi0 flags)
        (selectionPromotionGap_nonneg _ _ _ hvb (hL.trans hb) heta0 heta1)
  have hmono := (independentFlagLaw p hp0 hp1).expect_mono hpoint
  have hind : (independentFlagLaw p hp0 hp1).expect
      (fun flags => if flags i=true ∧ flags j=true ∧ good flags then g else 0) =
      g*(independentFlagLaw p hp0 hp1).prob
        (fun flags => flags i=true ∧ flags j=true ∧ good flags) := by
    rw [FiniteLaw.prob_eq_expect,← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_congr
    intro flags
    split_ifs <;> ring
  rw [hind] at hmono
  exact (mul_le_mul_of_nonneg_left
    (pair_good_probability_lower p hp0 hp1 i j hij good) hg).trans hmono

omit [Fintype ι] [DecidableEq ι] in

theorem realizedMixedMarginal_lower {xi qmin : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) (i : ι) (hb : 0 < b i)
    (hlambda : realizedMixedMultiplier xi c fixed I b ≤ (1-xi*qmin)*b i) :
    qmin ≤ realizedMixedMarginal xi c fixed I b i := by
  unfold realizedMixedMarginal
  apply (le_div_iff₀ hxi).mpr
  have h := (div_le_iff₀ hb).mpr hlambda
  linarith

theorem privateTypicalMixture_marginal_lower (mu : FiniteLaw Ω)
    {xi qmin : ℝ} (hxi : 0 < xi) (c : ℕ) (fixed : Ω → Finset ι)
    (I : Finset ι) (b : ι → ℝ) (hdis : ∀ omega, Disjoint (fixed omega) I)
    (hfixed : ∀ omega, (fixed omega).card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ omega i, i ∈ I →
      (1-xi)*b i ≤ realizedMixedMultiplier xi c (fixed omega) I b)
    (hhi : ∀ omega i, i ∈ I →
      realizedMixedMultiplier xi c (fixed omega) I b ≤ b i)
    (i : ι) (hi : i ∈ I)
    (hinterior : ∀ omega,
      realizedMixedMultiplier xi c (fixed omega) I b ≤ (1-xi*qmin)*b i) :
    qmin ≤ (privateTypicalMixture mu xi c fixed I b).prob (fun S => i ∈ S) := by
  rw [privateTypicalMixture_marginal mu hxi c fixed I b hdis hfixed hW hb hlo hhi]
  apply mu.const_le_expect
  intro omega
  have hn : i ∉ fixed omega := fun hf => (Finset.disjoint_left.mp (hdis omega)) hf hi
  simp only [typicalMarginal,if_neg hn,if_pos hi]
  exact realizedMixedMarginal_lower hxi c (fixed omega) I b i (hb i hi) (hinterior omega)

end FCAppendix.Affine.Tail04
