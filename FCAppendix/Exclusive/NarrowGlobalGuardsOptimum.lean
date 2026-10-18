import FCAppendix.Exclusive.NarrowGlobalGuardsReference
import FCAppendix.Exclusive.NarrowLocalIdentification

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open MeasureTheory Set Filter Topology

lemma fTariff_strictMonoOn (d : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed) :
    StrictMonoOn (fTariff d a) (Ico 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico 0 1)
  · intro p hp
    exact (hasDerivAt_fTariff d hd a p hp.2).continuousAt.continuousWithinAt
  · intro p hp
    have hp' : p ∈ Ico (0:ℝ) 1 := interior_subset hp
    rw [(hasDerivAt_fTariff d hd a p hp'.2).deriv]
    exact (fTariff_pos_and_derivative_pos d hd a ha hp'.1 hp'.2).2

def referenceUtility (d : ℕ) (a : UserTariff) (lam v p : ℝ) : ℝ :=
  v*PayOnce.success (d+1) p-referenceBidCost d a lam p

lemma hasDerivAt_referenceUtility (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (lam v p : ℝ) (hp : p < 1) :
    HasDerivAt (referenceUtility d a lam v)
      (((d+1:ℕ):ℝ)*(1-p)^d*(v-lam*fTariff d a p)) p := by
  apply (((hasDerivAt_success d p).const_mul v).sub
    (hasDerivAt_referenceBidCost d hd a lam p hp)).congr_deriv
  ring

lemma referenceUtility_zero (d : ℕ) (a : UserTariff) (lam v : ℝ) :
    referenceUtility d a lam v 0 = 0 := by
  cases a <;> simp [referenceUtility,referenceBidCost,referenceBid,PayOnce.success]

theorem referenceUtility_strict_global (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (ha : a.Allowed) (lam v p0 : ℝ) (hlam : 0 < lam)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hFOC : v = lam*fTariff d a p0)
    (p : ℝ) (hp : p ∈ Ico 0 1) (hne : p ≠ p0) :
    referenceUtility d a lam v p < referenceUtility d a lam v p0 := by
  have hmono := fTariff_strictMonoOn d hd a ha
  have hcont : ContinuousOn (referenceUtility d a lam v) (Iio 1) := fun p hp =>
    (hasDerivAt_referenceUtility d hd a lam v p hp).continuousAt.continuousWithinAt
  have hleft : StrictMonoOn (referenceUtility d a lam v) (Icc 0 p0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 p0)
    · exact hcont.mono fun x hx => hx.2.trans_lt hp1
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hasDerivAt_referenceUtility d hd a lam v x (hx.2.trans hp1)).deriv]
      have hcost := hmono ⟨hx.1.le,hx.2.trans hp1⟩ ⟨hp0.le,hp1⟩ hx.2
      have hq : 0 < 1-x := sub_pos.mpr (hx.2.trans hp1)
      apply mul_pos
      · positivity
      · rw [hFOC]
        exact sub_pos.mpr (mul_lt_mul_of_pos_left hcost hlam)
  have hright : StrictAntiOn (referenceUtility d a lam v) (Ico p0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico p0 1)
    · exact hcont.mono fun _ hx => hx.2
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hasDerivAt_referenceUtility d hd a lam v x hx.2).deriv]
      have hcost := hmono ⟨hp0.le,hp1⟩ ⟨hp0.le.trans hx.1.le,hx.2⟩ hx.1
      have hq : 0 < 1-x := sub_pos.mpr hx.2
      apply mul_neg_of_pos_of_neg
      · positivity
      · rw [hFOC]
        exact sub_neg.mpr (mul_lt_mul_of_pos_left hcost hlam)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hleft ⟨hp.1,hlt.le⟩ ⟨hp0.le,le_refl _⟩ hlt
  · exact hright ⟨le_refl _,hp1⟩ ⟨hgt.le,hp.2⟩ hgt

theorem referenceUtility_pos (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (ha : a.Allowed) (lam v p0 : ℝ) (hlam : 0 < lam)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hFOC : v = lam*fTariff d a p0) :
    0 < referenceUtility d a lam v p0 := by
  have h := referenceUtility_strict_global d hd a ha lam v p0 hlam hp0 hp1 hFOC
    0 ⟨le_refl _,zero_lt_one⟩ hp0.ne
  simpa only [referenceUtility_zero] using h

theorem referenceUtility_compact_gap (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (ha : a.Allowed) (lam v p0 : ℝ) (hlam : 0 < lam)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hFOC : v = lam*fTariff d a p0)
    (K : Set ℝ) (hK : IsCompact K) (hsub : K ⊆ Ico 0 1) (hne : p0 ∉ K) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ p ∈ K,
      referenceUtility d a lam v p + gap ≤ referenceUtility d a lam v p0 := by
  by_cases hnon : K.Nonempty
  · have hcont : ContinuousOn (referenceUtility d a lam v) K := fun p hp =>
      (hasDerivAt_referenceUtility d hd a lam v p (hsub hp).2).continuousAt.continuousWithinAt
    obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hnon hcont
    have hstrict := referenceUtility_strict_global d hd a ha lam v p0 hlam hp0 hp1 hFOC
      p (hsub hp) (fun he => hne (he ▸ hp))
    refine ⟨referenceUtility d a lam v p0-referenceUtility d a lam v p,
      sub_pos.mpr hstrict,?_⟩
    intro q hq
    have hh := hmax hq
    change referenceUtility d a lam v q ≤ referenceUtility d a lam v p at hh
    linarith
  · refine ⟨1,zero_lt_one,?_⟩
    intro p hp
    exact (hnon ⟨p,hp⟩).elim

lemma binomialPolynomial_at_zero (k : ℕ) (f : ℕ → ℝ) :
    binomialPolynomial k f 0 = f 0 := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp only [binomialPolynomial,sub_zero,one_mul,zero_mul,add_zero,ih]

lemma bidCostAtSuccess_zero (n k : ℕ) (a : UserTariff) (lam : ℝ) :
    bidCostAtSuccess n k a lam 0 = 0 := by
  simp only [bidCostAtSuccess,zero_div,mul_zero,neg_zero,Real.exp_zero,sub_self,
    binomialPolynomial_at_zero,UserTariff.charge_zero,mul_one]

lemma referenceBid_exp (d : ℕ) (lam y : ℝ) :
    referenceBid d lam (1-Real.exp (-y)) = lam*Real.exp ((d:ℝ)*y) := by
  rw [referenceBid,sub_sub_cancel,Real.exp_neg,inv_pow,div_inv_eq_mul,Real.exp_nat_mul]

lemma fullRouteCost_eq_reference (d : ℕ) (a : UserTariff) (lam A : ℝ) (hA : 0 < A) :
    bidCostAtSuccess (d+1) (d+1) a lam A =
      referenceBidCost d a lam (1-Real.exp (-(A/((d+1:ℕ):ℝ)))) := by
  let y := A/((d+1:ℕ):ℝ)
  have hy : 0 < y := div_pos hA (by positivity)
  have hp0 : 0 ≤ 1-Real.exp (-y) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hp1 : 1-Real.exp (-y) < 1 := by linarith [Real.exp_pos (-y)]
  unfold bidCostAtSuccess
  rw [binomialPolynomial_eq_expect (d+1) a.charge _ hp0 hp1.le]
  have hb : lam*Real.exp ((((d+1:ℕ):ℝ)-1)*y) = referenceBid d lam (1-Real.exp (-y)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using (referenceBid_exp d lam y).symm
  change lam*Real.exp ((((d+1:ℕ):ℝ)-1)*y)*_ = _
  rw [hb]
  simpa only [UserTariff.expected] using
    (referenceBidCost_eq_actual d a lam (1-Real.exp (-y)) hp0 hp1).symm

def referenceRouteUtility (n k : ℕ) (a : UserTariff) (lam v A : ℝ) : ℝ :=
  v*(1-Real.exp (-A))-bidCostAtSuccess n k a lam A

lemma fullRouteUtility_eq_reference (d : ℕ) (a : UserTariff) (lam v A : ℝ) (hA : 0 < A) :
    referenceRouteUtility (d+1) (d+1) a lam v A =
      referenceUtility d a lam v (1-Real.exp (-(A/((d+1:ℕ):ℝ)))) := by
  rw [referenceRouteUtility,fullRouteCost_eq_reference d a lam A hA,referenceUtility,
    prescribed_success (d+1) (by omega) A]

theorem referenceRouteUtility_strict_global (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (a : UserTariff) (ha : a.Allowed)
    (lam v p0 : ℝ) (hlam : 0 < lam) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hFOC : v = lam*fTariff d a p0) (A : ℝ) (hA : 0 ≤ A) :
    referenceRouteUtility (d+1) k a lam v A < referenceUtility d a lam v p0 := by
  by_cases hzero : A = 0
  · simp only [hzero,referenceRouteUtility,neg_zero,Real.exp_zero,sub_self,mul_zero,
      bidCostAtSuccess_zero]
    exact referenceUtility_pos d hd a ha lam v p0 hlam hp0 hp1 hFOC
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
  have hroute := bidCostAtSuccess_route_strict (d+1) k (d+1) (by omega) hk hkn a ha lam A hlam hAp
  have hfull : referenceRouteUtility (d+1) k a lam v A <
      referenceRouteUtility (d+1) (d+1) a lam v A := by
    unfold referenceRouteUtility
    linarith
  rw [fullRouteUtility_eq_reference d a lam v A hAp] at hfull
  let p := 1-Real.exp (-(A/((d+1:ℕ):ℝ)))
  have hy : 0 < A/((d+1:ℕ):ℝ) := div_pos hAp (by positivity)
  have hp : p ∈ Ico (0:ℝ) 1 :=
    ⟨sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)),by dsimp [p]; linarith [Real.exp_pos (-(A/((d+1:ℕ):ℝ))) ]⟩
  by_cases he : p = p0
  · simpa only [show 1-Real.exp (-(A/((d+1:ℕ):ℝ))) = p0 from he] using hfull
  · exact hfull.trans (referenceUtility_strict_global d hd a ha lam v p0 hlam hp0 hp1 hFOC p hp he)

lemma continuous_bidCostAtSuccess (n k : ℕ) (a : UserTariff) (lam : ℝ) :
    Continuous (bidCostAtSuccess n k a lam) := by
  have hpoly : Continuous (binomialPolynomial k a.charge) :=
    continuous_iff_continuousAt.mpr fun p => (hasDerivAt_binomialPolynomial k a.charge p).continuousAt
  unfold bidCostAtSuccess
  fun_prop

lemma continuous_referenceRouteUtility (n k : ℕ) (a : UserTariff) (lam v : ℝ) :
    Continuous (referenceRouteUtility n k a lam v) := by
  have hc := continuous_bidCostAtSuccess n k a lam
  unfold referenceRouteUtility
  fun_prop

theorem referenceRouteUtility_compact_gap (d k : ℕ) (hd : 1 ≤ d)
    (hk : 0 < k) (hkn : k < d+1) (a : UserTariff) (ha : a.Allowed)
    (lam v p0 : ℝ) (hlam : 0 < lam) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hFOC : v = lam*fTariff d a p0) (R : ℝ) (hR : 0 ≤ R) :
    ∃ gap : ℝ, 0 < gap ∧ ∀ A ∈ Icc (0:ℝ) R,
      referenceRouteUtility (d+1) k a lam v A + gap ≤ referenceUtility d a lam v p0 := by
  obtain ⟨A,hA,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0,⟨le_refl _,hR⟩⟩
    (continuous_referenceRouteUtility (d+1) k a lam v).continuousOn
  have hs := referenceRouteUtility_strict_global d k hd hk hkn a ha lam v p0 hlam hp0 hp1 hFOC A hA.1
  refine ⟨referenceUtility d a lam v p0-referenceRouteUtility (d+1) k a lam v A,
    sub_pos.mpr hs,?_⟩
  intro B hB
  have hh := hmax hB
  change referenceRouteUtility (d+1) k a lam v B ≤ referenceRouteUtility (d+1) k a lam v A at hh
  linarith

end FCAppendix.Exclusive.Narrow.Global
