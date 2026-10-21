import FCAppendix.Proposer.MeasurableExactCapacity
import FCAppendix.Proposer.MeasurableLotteryPolicy
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rankScore (b : ι → ℝ) (i j : ι) : ℝ :=
  if b j < b i then 1 else if b i < b j then 0 else 1/2

def averageRank (b : ι → ℝ) (i : ι) : ℝ :=
  1/2 + ∑ j, rankScore b i j

def rankDenominator (ι : Type*) [Fintype ι] : ℝ :=
  (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)+1) / 2

omit [Fintype ι] [DecidableEq ι] in
lemma rankScore_add_reverse (b : ι → ℝ) (i j : ι) :
    rankScore b i j + rankScore b j i = 1 := by
  unfold rankScore
  split_ifs <;> linarith

omit [Fintype ι] [DecidableEq ι] in
lemma rankScore_bounds (b : ι → ℝ) (i j : ι) :
    0 ≤ rankScore b i j ∧ rankScore b i j ≤ 1 := by
  unfold rankScore
  split_ifs <;> norm_num

omit [DecidableEq ι] in
lemma averageRank_pos (b : ι → ℝ) (i : ι) : 0 < averageRank b i := by
  have hs : 0 ≤ ∑ j, rankScore b i j :=
    Finset.sum_nonneg (fun j _ => (rankScore_bounds b i j).1)
  unfold averageRank
  linarith

omit [DecidableEq ι] in
lemma averageRank_le (b : ι → ℝ) (i : ι) :
    averageRank b i ≤ (Fintype.card ι : ℝ)+1 := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => (rankScore_bounds b i j).2)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  unfold averageRank
  linarith

omit [DecidableEq ι] in
lemma sum_averageRank (b : ι → ℝ) :
    ∑ i, averageRank b i = rankDenominator ι := by
  have hs : (∑ i, ∑ j, rankScore b j i) = ∑ i, ∑ j, rankScore b i j :=
    Finset.sum_comm
  have hp : (∑ i, ∑ j, (rankScore b i j+rankScore b j i)) =
      (Fintype.card ι : ℝ)^2 := by
    simp only [rankScore_add_reverse, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    ring
  simp only [Finset.sum_add_distrib] at hp
  rw [hs] at hp
  simp only [averageRank, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, rankDenominator]
  nlinarith

omit [DecidableEq ι] in
lemma rankDenominator_pos [Nonempty ι] : 0 < rankDenominator ι := by
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold rankDenominator
  positivity

def rankLaw [Nonempty ι] (b : ι → ℝ) : FiniteLaw ι where
  mass i := averageRank b i / rankDenominator ι
  nonneg i := (div_pos (averageRank_pos b i) rankDenominator_pos).le
  total := by
    rw [← Finset.sum_div, sum_averageRank, div_self rankDenominator_pos.ne']

omit [DecidableEq ι] in
lemma rankLaw_mass_le [Nonempty ι] (b : ι → ℝ) (i : ι) :
    (rankLaw b).mass i ≤ 2/(Fintype.card ι : ℝ) := by
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  change averageRank b i / rankDenominator ι ≤ _
  apply (div_le_iff₀ rankDenominator_pos).2
  have he : 2/(Fintype.card ι : ℝ)*rankDenominator ι =
      (Fintype.card ι : ℝ)+1 := by
    unfold rankDenominator
    field_simp
  rw [he]
  exact averageRank_le b i

omit [DecidableEq ι] in
lemma averageRank_relabel (b : ι → ℝ) (e : Equiv.Perm ι) (i : ι) :
    averageRank (b ∘ e.symm) (e i) = averageRank b i := by
  unfold averageRank
  congr 1
  calc
    (∑ j, rankScore (b ∘ e.symm) (e i) j) =
        ∑ j, rankScore b i (e.symm j) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [rankScore]
    _ = ∑ j, rankScore b i j := Equiv.sum_comp e.symm _

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_rankScore (i j : ι) : Measurable (fun b : ι → ℝ => rankScore b i j) := by
  unfold rankScore
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
    measurable_const (Measurable.ite
      (measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
        measurable_const measurable_const)

omit [DecidableEq ι] in
lemma measurable_averageRank (i : ι) :
    Measurable (fun b : ι → ℝ => averageRank b i) :=
  measurable_const.add (Finset.measurable_sum _ (fun j _ => measurable_rankScore i j))

omit [DecidableEq ι] in
lemma measurable_rankLaw_mass [Nonempty ι] (i : ι) :
    Measurable (fun b : ι → ℝ => (rankLaw b).mass i) :=
  (measurable_averageRank i).div_const _

def fillFraction (K : ℕ) : ℝ :=
  ((K : ℝ)-1)/((Fintype.card ι : ℝ)-1)

def fillMarginal (K : ℕ) (target i : ι) : ℝ :=
  if i = target then 1 else fillFraction (ι := ι) K

def conditionalFill (K : ℕ) (target : ι) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (fillMarginal K target)

omit [DecidableEq ι] in
lemma fillFraction_bounds {K : ℕ} (hN : 2 ≤ Fintype.card ι)
    (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) :
    0 ≤ fillFraction (ι := ι) K ∧ fillFraction (ι := ι) K ≤ 1 := by
  have hNr : 1 < (Fintype.card ι : ℝ) := by exact_mod_cast (show 1 < Fintype.card ι by omega)
  have hKr : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hKNr : (K : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKN
  unfold fillFraction
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · exact (div_le_one (by linarith)).2 (by linarith)

lemma sum_fillMarginal {K : ℕ} (hN : 2 ≤ Fintype.card ι) (target : ι) :
    ∑ i, fillMarginal K target i = (K : ℝ) := by
  have hNr : (Fintype.card ι : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  have hpoint (i : ι) : fillMarginal K target i = fillFraction (ι := ι) K +
      (if i = target then 1-fillFraction (ι := ι) K else 0) := by
    unfold fillMarginal
    split_ifs <;> ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold fillFraction
  field_simp
  ring

lemma conditionalFill_implements {K : ℕ} (hN : 2 ≤ Fintype.card ι)
    (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) (target : ι) :
    (∀ S, (conditionalFill K target).mass S ≠ 0 → S.card = K) ∧
      ∀ i, (conditionalFill K target).prob (fun S => i ∈ S) = fillMarginal K target i := by
  have hb := fillFraction_bounds hN hK hKN
  exact ExactCapacity.symmetricLottery_implements _ K
    (fun i => by
      unfold fillMarginal
      split_ifs
      · exact zero_le_one
      · exact hb.1)
    (fun i => by unfold fillMarginal; split_ifs <;> first | exact le_rfl | exact hb.2)
    (sum_fillMarginal hN target)

lemma conditionalFill_relabel (K : ℕ) (target : ι) (e : Equiv.Perm ι) :
    conditionalFill K (e target) =
      (conditionalFill K target).map (fun S => S.map e.toEmbedding) := by
  have he : fillMarginal K (e target) = fillMarginal K target ∘ e.symm := by
    funext i
    have hi : i = e target ↔ e.symm i = target := by
      constructor
      · rintro rfl; simp
      · intro h; rw [←h]; simp
    simp only [fillMarginal,Function.comp_apply,hi]
  unfold conditionalFill
  rw [he]
  exact ExactCapacity.symmetricLottery_equivariant _ e

def favoredSetLaw [Nonempty ι] (b : ι → ℝ) (K : ℕ) : FiniteLaw (Finset ι) :=
  FiniteLaw.finiteMix (rankLaw b) (conditionalFill K)

lemma expect_point_indicator (nu : FiniteLaw ι) (i : ι) :
    nu.expect (fun j => if j = i then (1 : ℝ) else 0) = nu.mass i := by
  classical
  simp [FiniteLaw.expect]

lemma expect_fillMarginal (nu : FiniteLaw ι) (K : ℕ) (i : ι) :
    nu.expect (fun t => fillMarginal K t i) =
      fillFraction (ι := ι) K + (1-fillFraction (ι := ι) K)*nu.mass i := by
  have he (t : ι) : fillMarginal K t i = fillFraction (ι := ι) K +
      (1-fillFraction (ι := ι) K)*(if t = i then 1 else 0) := by
    unfold fillMarginal
    by_cases ht : t = i
    · subst t; simp
    · have hit : i ≠ t := Ne.symm ht
      simp [ht,hit]
  rw [nu.expect_congr he, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
    expect_point_indicator, FiniteLaw.expect_const]

lemma favoredSetLaw_inclusion [Nonempty ι] (b : ι → ℝ) {K : ℕ}
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) (i : ι) :
    (favoredSetLaw b K).prob (fun S => i ∈ S) =
      ((K : ℝ)-1)/((Fintype.card ι : ℝ)-1) +
      ((Fintype.card ι : ℝ)-(K : ℝ))/((Fintype.card ι : ℝ)-1) *
        (averageRank b i/rankDenominator ι) := by
  rw [FiniteLaw.prob_eq_expect, favoredSetLaw, FiniteLaw.expect_finiteMix]
  have he (t : ι) : (conditionalFill K t).expect
      (fun S => if i ∈ S then (1 : ℝ) else 0) = fillMarginal K t i := by
    rw [← FiniteLaw.prob_eq_expect]
    exact (conditionalFill_implements hN hK hKN t).2 i
  rw [FiniteLaw.expect_congr _ he, expect_fillMarginal]
  change fillFraction (ι := ι) K+(1-fillFraction (ι := ι) K)*
    (averageRank b i/rankDenominator ι) = _
  have hn : (Fintype.card ι : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  unfold fillFraction
  field_simp
  ring

lemma favoredSetLaw_centered [Nonempty ι] (b : ι → ℝ) {K : ℕ}
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) (i : ι) :
    (favoredSetLaw b K).prob (fun S => i ∈ S) - (K : ℝ)/(Fintype.card ι : ℝ) =
      ((Fintype.card ι : ℝ)-(K : ℝ))/((Fintype.card ι : ℝ)-1) *
        ((rankLaw b).mass i-1/(Fintype.card ι : ℝ)) := by
  rw [favoredSetLaw_inclusion b hN hK hKN i]
  have hN' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card ι : ℝ)-1 ≠ 0 := by linarith
  change _ = _ * (averageRank b i/rankDenominator ι-1/(Fintype.card ι : ℝ))
  field_simp
  ring

lemma favoredSetLaw_bias_le [Nonempty ι] (b : ι → ℝ) {K : ℕ}
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι) (i : ι) :
    |(favoredSetLaw b K).prob (fun S => i ∈ S)-(K : ℝ)/(Fintype.card ι : ℝ)| ≤
      1/(Fintype.card ι : ℝ) := by
  rw [favoredSetLaw_centered b hN hK hKN i, abs_mul]
  have hN' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKN' : (K : ℝ) ≤ Fintype.card ι := by exact_mod_cast hKN
  have hfrac0 : 0 ≤ ((Fintype.card ι : ℝ)-(K : ℝ))/((Fintype.card ι : ℝ)-1) :=
    div_nonneg (by linarith) (by linarith)
  have hfrac1 : ((Fintype.card ι : ℝ)-(K : ℝ))/((Fintype.card ι : ℝ)-1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have hr : |(rankLaw b).mass i-1/(Fintype.card ι : ℝ)| ≤ 1/(Fintype.card ι : ℝ) := by
    rw [abs_le]
    constructor
    · linarith [(rankLaw b).nonneg i]
    · have hm := rankLaw_mass_le b i
      rw [show 2/(Fintype.card ι : ℝ)=2*(1/(Fintype.card ι : ℝ)) by ring] at hm
      linarith
  rw [abs_of_nonneg hfrac0]
  calc
    _ ≤ 1 * |(rankLaw b).mass i-1/(Fintype.card ι : ℝ)| :=
      mul_le_mul_of_nonneg_right hfrac1 (abs_nonneg _)
    _ ≤ _ := by simpa using hr

lemma measurable_favoredSetLaw_mass [Nonempty ι] (K : ℕ) (S : Finset ι) :
    Measurable (fun b : ι → ℝ => (favoredSetLaw b K).mass S) := by
  unfold favoredSetLaw FiniteLaw.finiteMix FiniteLaw.expect
  exact Finset.measurable_sum _ (fun i _ => (measurable_rankLaw_mass i).mul_const _)

theorem exists_favoredSet_sampler [Nonempty ι]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    [StandardBorelSpace (Finset ι)] (K : ℕ) :
    ∃ f : (ι → ℝ) → unitInterval → Finset ι,
      Measurable (Function.uncurry f) ∧
      ∀ b, (volume : Measure unitInterval).map (f b) =
        FiniteLaw.probabilityMeasure (favoredSetLaw b K) :=
  FiniteLaw.exists_measurable_sampler (fun b => favoredSetLaw b K)
    (measurable_favoredSetLaw_mass K)

def ownerMarginal (E : Finset ι) (K1 : ℕ) (i : ι) : ℝ :=
  if i ∈ E then (K1 : ℝ)/(E.card : ℝ) else 0

def ownerDivision (E : Finset ι) (K1 : ℕ) : FiniteLaw (Finset ι × Finset ι) :=
  (ExactCapacity.symmetricLottery (ownerMarginal E K1)).map (fun A => (A, E \ A))

def exclusiveOwnersLaw [Nonempty ι] (b : ι → ℝ) (K1 K2 : ℕ) :
    FiniteLaw (Finset ι × Finset ι) :=
  FiniteLaw.finiteMix (favoredSetLaw b (K1+K2)) (fun E => ownerDivision E K1)

lemma ownerMarginal_sum {E : Finset ι} (hE : E.Nonempty) (K1 : ℕ) :
    ∑ i, ownerMarginal E K1 i = (K1 : ℝ) := by
  classical
  have hc : (E.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hE
  simp only [ownerMarginal, Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  field_simp

lemma ownerDivision_support {E : Finset ι} (hE : E.Nonempty) {K1 : ℕ}
    (hK : K1 ≤ E.card) (A B : Finset ι)
    (hAB : (ownerDivision E K1).mass (A,B) ≠ 0) :
    A ⊆ E ∧ A.card = K1 ∧ B = E \ A ∧ Disjoint A B ∧ A ∪ B = E := by
  classical
  have hc : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
  have hKr : (K1 : ℝ) ≤ E.card := by exact_mod_cast hK
  have hp0 : ∀ i, 0 ≤ ownerMarginal E K1 i := by
    intro i
    unfold ownerMarginal
    split_ifs <;> positivity
  have hp1 : ∀ i, ownerMarginal E K1 i ≤ 1 := by
    intro i
    unfold ownerMarginal
    split_ifs
    · exact (div_le_one hc).2 hKr
    · norm_num
  have himpl := ExactCapacity.symmetricLottery_implements (ownerMarginal E K1) K1
    hp0 hp1 (ownerMarginal_sum hE K1)
  have hpre : ∃ T, (ExactCapacity.symmetricLottery (ownerMarginal E K1)).mass T ≠ 0 ∧
      (T,E \ T) = (A,B) := by
    by_contra h
    have hz (T : Finset ι) (he : (T,E \ T) = (A,B)) :
        (ExactCapacity.symmetricLottery (ownerMarginal E K1)).mass T = 0 := by
      by_contra hn
      exact h ⟨T, hn, he⟩
    apply hAB
    unfold ownerDivision FiniteLaw.map
    apply Finset.sum_eq_zero
    intro T _
    split_ifs with he
    · exact hz T he
    · rfl
  obtain ⟨T, hT, heq⟩ := hpre
  have hTA : T=A := congrArg Prod.fst heq
  have hTB : E \ T=B := congrArg Prod.snd heq
  subst A
  subst B
  have hsub : T ⊆ E := by
    intro i hi
    by_contra hn
    have hpos := FiniteLaw.marginal_pos_of_support_mem _ T hT i hi
    rw [himpl.2 i] at hpos
    simp [ownerMarginal, hn] at hpos
  exact ⟨hsub, himpl.1 T hT, rfl, (by exact Finset.disjoint_left.mpr (fun _ hi hn=> (Finset.mem_sdiff.mp hn).2 hi)),
    Finset.union_sdiff_of_subset hsub⟩

end FCAppendix.Affine.Hybrid
