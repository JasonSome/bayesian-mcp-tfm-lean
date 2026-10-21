import FCAppendix.Affine.Tail04.TypicalMeanCount
import FCAppendix.Affine.Tail04.FlagRelabel
import FCAppendix.Affine.Tail04.FavoredLocalCountGain

noncomputable section
namespace FCAppendix.Affine.Tail04
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def targetMixedSet (target : ι) (flags : ι → Bool) : Finset ι :=
  flaggedMixedSet (forceExclusive target flags)

def targetTypicalWeight (phi : ℕ → ℝ → unitInterval) (b : ι → ℝ)
    (target : ι) (flags : ι → Bool) : ℝ :=
  phi (targetMixedSet target flags).card
    (mixedReciprocalSum (targetMixedSet target flags) b)

def targetStateCount (Q : ℕ → ℝ → ℝ → CountLaw 2) (b : ι → ℝ)
    (target : ι) (flags : ι → Bool) (focal : ι) : CountLaw 2 :=
  if focal ∈ targetMixedSet target flags then
    Q (targetMixedSet target flags).card
      (mixedReciprocalSum (targetMixedSet target flags) b) (b focal)
  else FiniteLaw.dirac 1

theorem targetStateCount_self (Q : ℕ → ℝ → ℝ → CountLaw 2) (b : ι → ℝ)
    (target : ι) (flags : ι → Bool) :
    targetStateCount Q b target flags target=FiniteLaw.dirac 1 := by
  rw [targetStateCount,if_neg]
  exact forced_target_not_mixed target flags

theorem targetTypicalWeight_bounds (phi : ℕ → ℝ → unitInterval) (b : ι → ℝ)
    (target : ι) (flags : ι → Bool) :
    0 ≤ targetTypicalWeight phi b target flags ∧ targetTypicalWeight phi b target flags ≤ 1 :=
  (phi (targetMixedSet target flags).card
    (mixedReciprocalSum (targetMixedSet target flags) b)).property

def conditionalTargetCount (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (target focal : ι) (fallback : CountLaw 2) : CountLaw 2 :=
  FiniteLaw.finiteMix (independentFlagLaw p hp0 hp1) (fun flags =>
    FiniteLaw.mixture (targetStateCount Q b target flags focal) fallback
      (targetTypicalWeight phi b target flags)
      (targetTypicalWeight_bounds phi b target flags).1
      (targetTypicalWeight_bounds phi b target flags).2)

theorem targetTypicalWeight_relabel (phi : ℕ → ℝ → unitInterval) (b : ι → ℝ)
    (e : Equiv.Perm ι) (target : ι) (flags : ι → Bool) :
    targetTypicalWeight phi (b ∘ e.symm) (e target) (relabelFlags e flags)=
      targetTypicalWeight phi b target flags := by
  unfold targetTypicalWeight targetMixedSet
  rw [forcedMixedSet_relabel,Finset.card_map,mixedReciprocalSum_relabel]

theorem targetStateCount_relabel (Q : ℕ → ℝ → ℝ → CountLaw 2) (b : ι → ℝ)
    (e : Equiv.Perm ι) (target : ι) (flags : ι → Bool) (focal : ι) :
    targetStateCount Q (b ∘ e.symm) (e target) (relabelFlags e flags) (e focal)=
      targetStateCount Q b target flags focal := by
  unfold targetStateCount targetMixedSet
  rw [forcedMixedSet_relabel]
  simp only [Finset.mem_map_equiv,Finset.card_map,mixedReciprocalSum_relabel,
    Function.comp_apply,Equiv.symm_apply_apply]

theorem conditionalTargetCount_relabel (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (e : Equiv.Perm ι)
    (target focal : ι) (fallback : CountLaw 2) :
    conditionalTargetCount Q phi (b ∘ e.symm) (p ∘ e.symm)
      (fun i => hp0 (e.symm i)) (fun i => hp1 (e.symm i))
      (e target) (e focal) fallback =
      conditionalTargetCount Q phi b p hp0 hp1 target focal fallback := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [conditionalTargetCount,FiniteLaw.expect_finiteMix]
  rw [independentFlagLaw_expect_relabel]
  apply FiniteLaw.expect_congr
  intro flags
  simp only [targetStateCount_relabel,targetTypicalWeight_relabel]

theorem conditionalTargetCount_swap (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i j : ι) (hb : b i=b j) (hp : p i=p j) (fallback : CountLaw 2) :
    conditionalTargetCount Q phi b p hp0 hp1 j i fallback =
      conditionalTargetCount Q phi b p hp0 hp1 i j fallback := by
  have hb' : b ∘ (Equiv.swap i j).symm=b := by
    simpa using Hybrid.bid_comp_swap_of_eq b i j hb
  have hp' : p ∘ (Equiv.swap i j).symm=p := by
    simpa using Hybrid.bid_comp_swap_of_eq p i j hp
  have h := conditionalTargetCount_relabel Q phi b p hp0 hp1
    (Equiv.swap i j) i j fallback
  simpa only [hb',hp',Equiv.swap_apply_left,Equiv.swap_apply_right] using h

theorem conditionalTargetCount_rival_tie (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i t u : ι) (hit : i ≠ t) (hiu : i ≠ u)
    (hb : b t=b u) (hp : p t=p u) (fallback : CountLaw 2) :
    conditionalTargetCount Q phi b p hp0 hp1 t i fallback =
      conditionalTargetCount Q phi b p hp0 hp1 u i fallback := by
  have hb' : b ∘ (Equiv.swap t u).symm=b := by
    simpa using Hybrid.bid_comp_swap_of_eq b t u hb
  have hp' : p ∘ (Equiv.swap t u).symm=p := by
    simpa using Hybrid.bid_comp_swap_of_eq p t u hp
  have he : Equiv.swap t u i=i := Equiv.swap_apply_of_ne_of_ne hit hiu
  have h := conditionalTargetCount_relabel Q phi b p hp0 hp1
    (Equiv.swap t u) t i fallback
  simpa only [hb',hp',Equiv.swap_apply_left,he] using h.symm

def typicalRankCount [Nonempty ι] (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (focal : ι) (fallback : CountLaw 2) : CountLaw 2 :=
  FiniteLaw.finiteMix (Hybrid.rankLaw b) (fun target =>
    conditionalTargetCount Q phi b p hp0 hp1 target focal fallback)

def affineCountUtility (C : CountLaw 2) (v bi eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  C.utility v bi 0 (Schedule.affine 2 eta heta0 heta1) (Schedule.once 2)

theorem typicalRankCount_utility [Nonempty ι] (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : ι) (fallback : CountLaw 2) (v eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    affineCountUtility (typicalRankCount Q phi b p hp0 hp1 i fallback)
      v (b i) eta heta0 heta1 =
      (Hybrid.rankLaw b).expect (fun target =>
        affineCountUtility (conditionalTargetCount Q phi b p hp0 hp1 target i fallback)
          v (b i) eta heta0 heta1) := by
  unfold affineCountUtility typicalRankCount CountLaw.utility
  exact FiniteLaw.expect_finiteMix _ _ _

theorem exclusiveUtility_eq (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    exclusiveUtility v bi eta heta0 heta1=v-bi := by
  unfold exclusiveUtility CountLaw.utility
  rw [FiniteLaw.expect_dirac]
  norm_num [userPayoff,Schedule.affine,Schedule.once,successIndicator]

theorem exclusive_minus_count_nonneg (C : CountLaw 2) {v bi eta : ℝ}
    (hvb : bi ≤ v) (hb : 0 ≤ bi) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 ≤ exclusiveUtility v bi eta heta0 heta1-affineCountUtility C v bi eta heta0 heta1 := by
  rw [exclusiveUtility_eq]
  unfold affineCountUtility
  rw [CountLaw.utility_eq,CountLaw.charge_affine]
  have hs := mul_nonneg (sub_nonneg.mpr hvb) (sub_nonneg.mpr C.success_le_one)
  have hd := mul_nonneg (mul_nonneg heta0 hb) C.duplicates_nonneg
  nlinarith only [hs,hd]

def targetExchangeGain (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i j : ι) (v eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) : ℝ :=
  (independentFlagLaw p hp0 hp1).expect (fun flags =>
    targetTypicalWeight phi b i flags*
      (exclusiveUtility v (b i) eta heta0 heta1-
        affineCountUtility (targetStateCount Q b i flags j) v (b i) eta heta0 heta1))

theorem conditionalTargetCount_utility_difference (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i j : ι) (hb : b i=b j) (hp : p i=p j) (fallback : CountLaw 2)
    (v eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    affineCountUtility (conditionalTargetCount Q phi b p hp0 hp1 i i fallback)
        v (b i) eta heta0 heta1-
      affineCountUtility (conditionalTargetCount Q phi b p hp0 hp1 j i fallback)
        v (b i) eta heta0 heta1 =
      targetExchangeGain Q phi b p hp0 hp1 i j v eta heta0 heta1 := by
  rw [conditionalTargetCount_swap Q phi b p hp0 hp1 i j hb hp fallback]
  unfold affineCountUtility conditionalTargetCount CountLaw.utility targetExchangeGain
  rw [FiniteLaw.expect_finiteMix,FiniteLaw.expect_finiteMix,← FiniteLaw.expect_sub]
  apply FiniteLaw.expect_congr
  intro flags
  rw [FiniteLaw.expect_mixture,FiniteLaw.expect_mixture,targetStateCount_self]
  dsimp [exclusiveUtility,affineCountUtility,CountLaw.utility]
  ring

theorem targetExchangeGain_nonneg (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i j : ι) {v eta : ℝ} (hvb : b i ≤ v) (hb : 0 ≤ b i)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    0 ≤ targetExchangeGain Q phi b p hp0 hp1 i j v eta heta0 heta1 :=
  (independentFlagLaw p hp0 hp1).expect_nonneg (fun flags =>
    mul_nonneg (targetTypicalWeight_bounds phi b i flags).1
      (exclusive_minus_count_nonneg _ hvb hb heta0 heta1))

theorem exclusive_minus_meanCount (xi : ℝ) (c ell0 ell1 : ℕ)
    (mean0 mean1 : ℝ) (M : ℕ) (W bi v eta : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    exclusiveUtility v bi eta heta0 heta1-
      affineCountUtility (meanCountLaw xi c ell0 ell1 mean0 mean1 M W bi)
        v bi eta heta0 heta1 =
      twoMixedFavoredGain v bi eta (meanMarginal xi c ell0 mean0 M W bi)
        (meanMarginal xi c ell1 mean1 M W bi) := by
  rw [exclusiveUtility_eq]
  unfold affineCountUtility meanCountLaw CountLaw.utility
  rw [twoCoinCountLaw_expect]
  norm_num [userPayoff,Schedule.affine,Schedule.once,successIndicator]
  unfold twoMixedFavoredGain
  ring

theorem source_targetExchangeGain_lower (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i j : ι) (hij : i ≠ j) (hbTie : b i=b j)
    (good : (ι → Bool) → Prop)
    (hgood : ∀ flags, good flags → targetTypicalWeight phi b i flags=1)
    {v eta L qmin : ℝ} (hvb : b i ≤ v) (hL : 0 ≤ L) (hb : L ≤ b i)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hqmin : 0 ≤ qmin)
    (hq0 : ∀ flags, flags i=true → flags j=true → good flags →
      qmin ≤ meanMarginal P.xi P.c (P.owner0 (targetMixedSet i flags).card)
        P.privateMean0 (targetMixedSet i flags).card
        (mixedReciprocalSum (targetMixedSet i flags) b) (b i))
    (hq1 : ∀ flags, flags i=true → flags j=true → good flags →
      qmin ≤ meanMarginal P.xi P.c (P.owner1 (targetMixedSet i flags).card)
        P.privateMean1 (targetMixedSet i flags).card
        (mixedReciprocalSum (targetMixedSet i flags) b) (b i)) :
    (eta*L*qmin^2)*(p i*p j-
        (independentFlagLaw p hp0 hp1).prob (fun flags => ¬good flags)) ≤
      targetExchangeGain P.mixedCount phi b p hp0 hp1 i j v eta heta0 heta1 := by
  classical
  let g := eta*L*qmin^2
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hpoint (flags : ι → Bool) :
      (if flags i=true ∧ flags j=true ∧ good flags then g else 0) ≤
        targetTypicalWeight phi b i flags*
          (exclusiveUtility v (b i) eta heta0 heta1-
            affineCountUtility (targetStateCount P.mixedCount b i flags j)
              v (b i) eta heta0 heta1) := by
    by_cases h : flags i=true ∧ flags j=true ∧ good flags
    · rw [if_pos h,hgood flags h.2.2,one_mul]
      have hj : j ∈ targetMixedSet i flags := by
        simp [targetMixedSet,flaggedMixedSet,forceExclusive,hij.symm,h.2.1]
      rw [targetStateCount,if_pos hj]
      change g ≤ exclusiveUtility v (b i) eta heta0 heta1-
        affineCountUtility (meanCountLaw P.xi P.c
          (P.owner0 (targetMixedSet i flags).card) (P.owner1 (targetMixedSet i flags).card)
          P.privateMean0 P.privateMean1 (targetMixedSet i flags).card
          (mixedReciprocalSum (targetMixedSet i flags) b) (b j))
          v (b i) eta heta0 heta1
      rw [← hbTie,exclusive_minus_meanCount]
      exact twoMixedFavoredGain_lower hvb heta0 hL hb hqmin
        (hq0 flags h.1 h.2.1 h.2.2) (hq1 flags h.1 h.2.1 h.2.2)
        (probabilityClip_bounds _).2 (probabilityClip_bounds _).2
    · rw [if_neg h]
      exact mul_nonneg (targetTypicalWeight_bounds phi b i flags).1
        (exclusive_minus_count_nonneg _ hvb (hL.trans hb) heta0 heta1)
  have hh := (independentFlagLaw p hp0 hp1).expect_mono hpoint
  have hind : (independentFlagLaw p hp0 hp1).expect
      (fun flags => if flags i=true ∧ flags j=true ∧ good flags then g else 0) =
      g*(independentFlagLaw p hp0 hp1).prob
        (fun flags => flags i=true ∧ flags j=true ∧ good flags) := by
    rw [FiniteLaw.prob_eq_expect,← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_congr
    intro flags
    split_ifs <;> ring
  rw [hind] at hh
  exact (mul_le_mul_of_nonneg_left
    (pair_good_probability_lower p hp0 hp1 i j hij good) hg).trans hh

end FCAppendix.Affine.Tail04
