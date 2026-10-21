import FCAppendix.Affine.ClippedResidualRoots
import FCAppendix.Proposer.Threshold

noncomputable section
namespace FCAppendix.Affine.ClippedResidual
open MeasureTheory Set Game Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def revenueAgainst (ξ : ℝ) (b : ι→ℝ)
    (own other : FiniteLaw (Finset ι)) : ℝ :=
  own.expect (fun S => other.expect (fun T =>
    LowBody.CompleteInformation.revenue (1-ξ) b S T))

theorem revenueAgainst_eq (ξ : ℝ) (b : ι→ℝ) (own other : FiniteLaw (Finset ι)) :
    revenueAgainst ξ b own other =
      Proposer.revenue own (fun i => b i*(1-ξ*Proposer.marginal other i)) := by
  unfold revenueAgainst Proposer.revenue
  apply own.expect_congr
  intro S
  unfold LowBody.CompleteInformation.revenue
  rw [FiniteLaw.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun T : Finset ι => if i∈T then (1-ξ)*b i else b i)=
      (fun T => b i-ξ*b i*(if i∈T then 1 else 0)) := by
    funext T
    split <;> simp
    ring
  rw [he,FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_const_mul,
    ←FiniteLaw.prob_eq_expect]
  unfold Proposer.marginal
  ring

lemma exposure_pos {ξ z b : ℝ} (hξ : 0<ξ) (hz : 0<z) (hb : z<b) :
    0<exposure ξ z b := by
  unfold exposure
  apply lt_min zero_lt_one
  exact div_pos (lt_max_of_lt_right (sub_pos.mpr hb))
    (mul_pos hξ (hz.trans_le (le_max_right _ _)))

lemma exposure_receipt {ξ z b : ℝ} (hξ : 0<ξ) (hz : 0<z)
    (hb : z<b) (hguard : (1-ξ)*b≤ z) :
    b*(1-ξ*exposure ξ z b)=z := by
  rw [exposure_of_between hξ hz hb hguard]
  have hb0 : b≠0 := ne_of_gt (hz.trans hb)
  field_simp [hξ.ne',hb0]
  ring

omit [Fintype ι] [DecidableEq ι] in

theorem exposure_threshold {ξ U z : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hz : 0<z) (hguard : (1-ξ)*U≤ z) (b : ι→ℝ) (hb : ∀i,b i≤ U) :
    Proposer.Threshold (fun i => exposure ξ z (b i))
      (fun i => b i*(1-ξ*exposure ξ z (b i))) z := by
  have hc (i : ι) : (1-ξ)*b i≤ z :=
    (mul_le_mul_of_nonneg_left (hb i) (by linarith)).trans hguard
  have he (i : ι) (hi : 0<exposure ξ z (b i)) :
      b i*(1-ξ*exposure ξ z (b i))=z := by
    have hbi : z<b i := by
      by_contra hn
      rw [exposure_zero (le_of_not_gt hn)] at hi
      exact (lt_irrefl 0) hi
    exact exposure_receipt hξ hz hbi (hc i)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    dsimp only at hi
    have hbi : b i≤ z := by
      by_contra hn
      have hp := exposure_pos hξ hz (lt_of_not_ge hn)
      rw [hi] at hp
      exact (lt_irrefl 0) hp
    simpa only [hi,mul_zero,sub_zero,mul_one] using hbi
  · intro i hi
    dsimp only at hi
    exact (he i (by rw [hi]; norm_num)).ge
  · intro i hi _
    exact he i hi

def smallMarginal (ξ z : ℝ) (b : ι→ℝ) (E : Finset ι) (i : ι) : ℝ :=
  if i∈E then 0 else exposure ξ z (b i)

def largeMarginal (ξ z : ℝ) (b : ι→ℝ) (E : Finset ι) (i : ι) : ℝ :=
  if i∈E then 1 else exposure ξ z (b i)

omit [Fintype ι] in
lemma marginal_bounds {ξ z : ℝ} (hξ : 0<ξ) (hz : 0<z)
    (b : ι→ℝ) (E : Finset ι) (i : ι) :
    (0≤ smallMarginal ξ z b E i ∧ smallMarginal ξ z b E i≤1) ∧
    (0≤ largeMarginal ξ z b E i ∧ largeMarginal ξ z b E i≤1) := by
  by_cases hi : i∈E
  · simp [smallMarginal,largeMarginal,hi]
  · exact ⟨by simpa only [smallMarginal,if_neg hi] using
        And.intro (exposure_nonneg hξ hz) (exposure_le_one ξ z (b i)),
      by simpa only [largeMarginal,if_neg hi] using
        And.intro (exposure_nonneg hξ hz) (exposure_le_one ξ z (b i))⟩

lemma largeMarginal_sum (ξ z : ℝ) (b : ι→ℝ) (E : Finset ι) :
    (∑i,largeMarginal ξ z b E i)=(∑i,smallMarginal ξ z b E i)+(E.card:ℝ) := by
  rw [←Game.sum_membership_real E,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i∈E <;> simp [smallMarginal,largeMarginal,hi]

omit [Fintype ι] in
lemma pair_threshold {ξ U z : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (hz : 0<z) (hguard : (1-ξ)*U≤ z) (b : ι→ℝ) (hb : ∀i,b i≤ U)
    (E : Finset ι) (hE : ∀i∈E,z≤ b i) :
    Proposer.Threshold (smallMarginal ξ z b E)
      (fun i => b i*(1-ξ*largeMarginal ξ z b E i)) z ∧
    Proposer.Threshold (largeMarginal ξ z b E)
      (fun i => b i*(1-ξ*smallMarginal ξ z b E i)) z := by
  have ht := exposure_threshold hξ hξ1 hz hguard b hb
  have hlow (i : ι) : (1-ξ)*b i≤ z :=
    (mul_le_mul_of_nonneg_left (hb i) (by linarith)).trans hguard
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro i hi
      by_cases hiE : i∈E
      · change b i*(1-ξ*largeMarginal ξ z b E i)≤z
        rw [largeMarginal,if_pos hiE]
        nlinarith [hlow i]
      · simpa only [largeMarginal,if_neg hiE] using
          ht.1 i (by simpa [smallMarginal,hiE] using hi)
    · intro i hi
      have hiE : i∉E := by intro h; simp [smallMarginal,h] at hi
      simpa only [largeMarginal,if_neg hiE] using
        ht.2.1 i (by simpa [smallMarginal,hiE] using hi)
    · intro i hi hlo
      have hiE : i∉E := by intro h; simp [smallMarginal,h] at hi
      simpa only [largeMarginal,if_neg hiE] using
        ht.2.2 i (by simpa [smallMarginal,hiE] using hi)
          (by simpa [smallMarginal,hiE] using hlo)
  · refine ⟨?_,?_,?_⟩
    · intro i hi
      have hiE : i∉E := by intro h; simp [largeMarginal,h] at hi
      simpa only [smallMarginal,if_neg hiE] using
        ht.1 i (by simpa [largeMarginal,hiE] using hi)
    · intro i hi
      by_cases hiE : i∈E
      · simpa [smallMarginal,hiE] using hE i hiE
      · simpa only [smallMarginal,if_neg hiE] using
          ht.2.1 i (by simpa [largeMarginal,hiE] using hi)
    · intro i hi hlo
      have hiE : i∉E := by intro h; simp [largeMarginal,h] at hlo
      simpa only [smallMarginal,if_neg hiE] using
        ht.2.2 i (by simpa [largeMarginal,hiE] using hi)
          (by simpa [largeMarginal,hiE] using hlo)

theorem pair_at_root {ξ U z : ℝ} (b : ι→ℝ) (E : Finset ι) (d : ℕ)
    (hξ : 0<ξ) (hξ1 : ξ<1) (hz : 0<z) (hguard : (1-ξ)*U≤z)
    (hbU : ∀i,b i≤U) (hE : ∀i∈E,z≤b i)
    (hroot : remainingDemand ξ b E z=(d:ℝ)) :
    let small := ExactCapacity.symmetricLottery (smallMarginal ξ z b E)
    let large := ExactCapacity.symmetricLottery (largeMarginal ξ z b E)
    (∀S,small.mass S≠0→S.card=d) ∧
    (∀S,large.mass S≠0→S.card=d+E.card) ∧
    (∀i,Proposer.marginal small i=smallMarginal ξ z b E i) ∧
    (∀i,Proposer.marginal large i=largeMarginal ξ z b E i) ∧
    (∀ν : FiniteLaw (Finset ι),(∀S,ν.mass S≠0→S.card≤d)→
      revenueAgainst ξ b ν large≤revenueAgainst ξ b small large) ∧
    (∀ν : FiniteLaw (Finset ι),(∀S,ν.mass S≠0→S.card≤d+E.card)→
      revenueAgainst ξ b ν small≤revenueAgainst ξ b large small) := by
  have hp := marginal_bounds hξ hz b E
  have hs : (∑i,smallMarginal ξ z b E i)=(d:ℝ) := hroot
  have hl : (∑i,largeMarginal ξ z b E i)=((d+E.card:ℕ):ℝ) := by
    rw [largeMarginal_sum,hs,Nat.cast_add]
  have hsmall := ExactCapacity.symmetricLottery_implements (smallMarginal ξ z b E) d
    (fun i=>(hp i).1.1) (fun i=>(hp i).1.2) hs
  have hlarge := ExactCapacity.symmetricLottery_implements (largeMarginal ξ z b E) (d+E.card)
    (fun i=>(hp i).2.1) (fun i=>(hp i).2.2) hl
  have ht := pair_threshold hξ hξ1 hz hguard b hbU E hE
  refine ⟨hsmall.1,hlarge.1,hsmall.2,hlarge.2,?_,?_⟩
  · intro ν hν
    rw [revenueAgainst_eq,revenueAgainst_eq,Proposer.revenue_marginals,Proposer.revenue_marginals]
    simp only [Proposer.marginal,hlarge.2,hsmall.2]
    exact Proposer.threshold_linear_optimal _ _ z d (fun i=>(hp i).1.1)
      (fun i=>(hp i).1.2) hs hz.le ht.1 (Proposer.marginal ν)
      (fun i=>ν.prob_nonneg _) (fun i=>ν.prob_le_one _) (Proposer.marginal_capacity ν d hν)
  · intro ν hν
    rw [revenueAgainst_eq,revenueAgainst_eq,Proposer.revenue_marginals,Proposer.revenue_marginals]
    simp only [Proposer.marginal,hlarge.2,hsmall.2]
    exact Proposer.threshold_linear_optimal _ _ z ((d+E.card:ℕ):ℝ) (fun i=>(hp i).2.1)
      (fun i=>(hp i).2.2) hl hz.le ht.2 (Proposer.marginal ν)
      (fun i=>ν.prob_nonneg _) (fun i=>ν.prob_le_one _) (Proposer.marginal_capacity ν (d+E.card) hν)

theorem exists_guarded_pair {ξ U lo hi slack : ℝ} (b : ι→ℝ) (E : Finset ι) (d : ℕ)
    (hξ : 0<ξ) (hξ1 : ξ<1) (hU : 0<U) (hlo : 0<lo) (hlh : lo<hi)
    (hguard : (1-ξ)*U≤ lo) (hbU : ∀i,b i≤ U) (hd : 0<d) (heps : 0<slack)
    (hlow : (d:ℝ)+(E.card:ℝ)+slack<∑i,exposure ξ lo (b i))
    (hhigh : (∑i,exposure ξ hi (b i))<(d:ℝ)-slack)
    (hE : ∀i∈E,hi≤ b i) :
    ∃ (z : ℝ) (small large : FiniteLaw (Finset ι)),
      z∈Icc lo hi ∧
      (∀S,small.mass S≠0→S.card=d) ∧
      (∀S,large.mass S≠0→S.card=d+E.card) ∧
      (∀i,Proposer.marginal small i=smallMarginal ξ z b E i) ∧
      (∀i,Proposer.marginal large i=largeMarginal ξ z b E i) ∧
      (∀ν : FiniteLaw (Finset ι),(∀S,ν.mass S≠0→S.card≤ d)→
        revenueAgainst ξ b ν large≤ revenueAgainst ξ b small large) ∧
      (∀ν : FiniteLaw (Finset ι),(∀S,ν.mass S≠0→S.card≤ d+E.card)→
        revenueAgainst ξ b ν small≤ revenueAgainst ξ b large small) := by
  obtain ⟨z,⟨hz,hzd⟩,_⟩ := exists_unique_balanced_root b E hξ hξ1 hU hlo hlh hguard
    hbU (by exact_mod_cast hd) heps hlow hhigh
  have hz0 := hlo.trans_le hz.1
  have hp := marginal_bounds hξ hz0 b E
  have hs : (∑i,smallMarginal ξ z b E i)=(d:ℝ) := hzd
  have hl : (∑i,largeMarginal ξ z b E i)=((d+E.card:ℕ):ℝ) := by
    rw [largeMarginal_sum,hs,Nat.cast_add]
  let small := ExactCapacity.symmetricLottery (smallMarginal ξ z b E)
  let large := ExactCapacity.symmetricLottery (largeMarginal ξ z b E)
  have hsmall := ExactCapacity.symmetricLottery_implements (smallMarginal ξ z b E) d
    (fun i=>(hp i).1.1) (fun i=>(hp i).1.2) hs
  have hlarge := ExactCapacity.symmetricLottery_implements (largeMarginal ξ z b E) (d+E.card)
    (fun i=>(hp i).2.1) (fun i=>(hp i).2.2) hl
  have ht := pair_threshold hξ hξ1 hz0 (hguard.trans hz.1) b hbU E
    (fun i hiE => hz.2.trans (hE i hiE))
  refine ⟨z,small,large,hz,hsmall.1,hlarge.1,hsmall.2,hlarge.2,?_,?_⟩
  · intro ν hν
    rw [revenueAgainst_eq,revenueAgainst_eq,Proposer.revenue_marginals,Proposer.revenue_marginals]
    dsimp only [small,large]
    simp only [Proposer.marginal,hlarge.2,hsmall.2]
    exact Proposer.threshold_linear_optimal _ _ z d (fun i=>(hp i).1.1)
      (fun i=>(hp i).1.2) hs hz0.le ht.1 (Proposer.marginal ν)
      (fun i=>ν.prob_nonneg _) (fun i=>ν.prob_le_one _) (Proposer.marginal_capacity ν d hν)
  · intro ν hν
    rw [revenueAgainst_eq,revenueAgainst_eq,Proposer.revenue_marginals,Proposer.revenue_marginals]
    dsimp only [small,large]
    simp only [Proposer.marginal,hlarge.2,hsmall.2]
    exact Proposer.threshold_linear_optimal _ _ z ((d+E.card:ℕ):ℝ) (fun i=>(hp i).2.1)
      (fun i=>(hp i).2.2) hl hz0.le ht.2 (Proposer.marginal ν)
      (fun i=>ν.prob_nonneg _) (fun i=>ν.prob_le_one _) (Proposer.marginal_capacity ν (d+E.card) hν)
end FCAppendix.Affine.ClippedResidual
