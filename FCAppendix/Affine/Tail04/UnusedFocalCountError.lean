import FCAppendix.Affine.Tail04.FocalInsertionSampling
import FCAppendix.Affine.Tail04.IidJoinedMenuError
import FCAppendix.Affine.Tail04.UnusedBidIntermediate

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedFocalCountError
open MeasureTheory ProbabilityTheory Set Classical
open MenuError FocalResponse WeightedFlagBound EqualPrivateSignal EqualPrivateUpper
open LocalHighCommon
open scoped BigOperators

def canonicalProbability (ξ lam b : ℝ) : ℝ :=
  probabilityClip ((b-lam)/(ξ*b))

lemma canonicalProbability_mem (ξ lam b : ℝ) :
    canonicalProbability ξ lam b∈Icc (0:ℝ) 1 := probabilityClip_bounds _

def canonicalCount (ξ lam b : ℝ) : CountLaw 2 :=
  twoCoinCountLaw (canonicalProbability ξ lam b) (canonicalProbability ξ lam b)
    (canonicalProbability_mem _ _ _).1 (canonicalProbability_mem _ _ _).2
    (canonicalProbability_mem _ _ _).1 (canonicalProbability_mem _ _ _).2

def actualCount (ξ b W L0 L1 : ℝ) : CountLaw 2 :=
  let p:=focalPair ξ b W L0 L1
  twoCoinCountLaw p.left p.right p.left_mem.1 p.left_mem.2 p.right_mem.1 p.right_mem.2

lemma canonicalCount_expect (ξ lam b : ℝ) (f : Fin 3→ℝ) :
    (canonicalCount ξ lam b).expect f=
      coinMoment (canonicalProbability ξ lam b) (canonicalProbability ξ lam b) f :=
  twoCoinCountLaw_expect _ _ _ _ _ _ f

lemma actualCount_expect (ξ b W L0 L1 : ℝ) (f : Fin 3→ℝ) :
    (actualCount ξ b W L0 L1).expect f=
      coinMoment (focalPair ξ b W L0 L1).left (focalPair ξ b W L0 L1).right f :=
  twoCoinCountLaw_expect _ _ _ _ _ _ f

lemma canonicalProbability_positive {ξ lam b : ℝ} (hξ : ξ≠0) (hb : b≠0) :
    canonicalProbability ξ lam b=clippedMarginal ξ b lam 1 := by
  unfold canonicalProbability clippedMarginal
  congr 1
  field_simp [hξ,hb]

lemma canonicalCount_positive {ξ lam b : ℝ} (hξ : ξ≠0) (hb : b≠0) :
    canonicalCount ξ lam b=clippedCount ξ b lam lam 1 := by
  apply FiniteLaw.ext_expect
  intro f
  rw [canonicalCount_expect,clippedCount_expect,canonicalProbability_positive hξ hb]

lemma clip_zero {x : ℝ} (hx : x≤0) : probabilityClip x=0 := by
  simp only [probabilityClip,max_eq_left hx,min_eq_right (by norm_num : (0:ℝ)≤1)]

lemma canonical_zero {ξ lam b : ℝ} (hξ : 0< ξ) (hb : 0≤ b) (hlam : b≤ lam) :
    canonicalProbability ξ lam b=0 := by
  exact clip_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hlam)
    (mul_nonneg hξ.le hb))

lemma denominator_pos {ξ b W : ℝ} (hξ : 0< ξ) (hb : 0≤ b) (hW : 0< W) :
    0< denominator ξ b W := by
  unfold denominator
  positivity

lemma denominator_unsaturated {ξ b W L B : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : b≤ B) (hW : 0< W)
    (hL : (1-ξ)*B≤ L) : b-L< denominator ξ b W := by
  have hκ : 0≤1-ξ := by linarith
  have hbase := mul_le_mul_of_nonneg_left hb hκ
  have hterm : 0< ξ/W := div_pos hξ hW
  unfold denominator
  have hid : ξ*(b+1/W)=ξ*b+ξ/W := by ring
  rw [hid]
  linarith

lemma pair_outside_between {ξ b W L0 L1 : ℝ}
    (hD : 0< denominator ξ b W)
    (h0 : b-L0< denominator ξ b W) (h1 : b-L1< denominator ξ b W)
    (hne : ¬BetweenPrices L0 b L1) :
    (focalPair ξ b W L0 L1).left=probabilityClip ((b-L0)/denominator ξ b W) ∧
    (focalPair ξ b W L0 L1).right=probabilityClip ((b-L1)/denominator ξ b W) := by
  by_cases hb0 : b≤ L0
  · have hb1 : b≤ L1 := by
      by_contra hh
      exact hne (Or.inr ⟨(lt_of_not_ge hh).le,hb0⟩)
    have hp0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb0) hD.le
    have hp1 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb1) hD.le
    simp [focalPair,solution,hp0,hp1,zeroZero,clip_zero hp0,clip_zero hp1]
  · have hb1 : L1< b := by
      by_contra hh
      exact hne (Or.inl ⟨(lt_of_not_ge hb0).le,le_of_not_gt hh⟩)
    have hpair := focalPair_interior ξ b W L0 L1 hD
      (sub_pos.mpr (lt_of_not_ge hb0)) (sub_pos.mpr hb1) h0 h1
    have hp0 : (b-L0)/denominator ξ b W∈Icc (0:ℝ) 1 :=
      ⟨(div_pos (sub_pos.mpr (lt_of_not_ge hb0)) hD).le,((div_lt_one hD).mpr h0).le⟩
    have hp1 : (b-L1)/denominator ξ b W∈Icc (0:ℝ) 1 :=
      ⟨(div_pos (sub_pos.mpr hb1) hD).le,((div_lt_one hD).mpr h1).le⟩
    simpa only [probabilityClip_eq hp0,probabilityClip_eq hp1] using hpair

lemma clipped_denominator_error {a c d : ℝ} (hc : 0< c) (hcd : c≤ d) (ha : a≤ d) :
    |probabilityClip (a/d)-probabilityClip (a/c)|≤(d-c)/c := by
  have hd : 0< d := hc.trans_le hcd
  have hgap : 0≤(d-c)/c := div_nonneg (sub_nonneg.mpr hcd) hc.le
  by_cases ha0 : a≤0
  · rw [clip_zero (div_nonpos_of_nonpos_of_nonneg ha0 hd.le),
      clip_zero (div_nonpos_of_nonpos_of_nonneg ha0 hc.le),sub_self,abs_zero]
    exact hgap
  · have ha0' : 0≤ a := (lt_of_not_ge ha0).le
    have hdiv : a/d≤ a/c := div_le_div_of_nonneg_left ha0' hc hcd
    have he : a/c-a/d=(a/d)*((d-c)/c) := by
      field_simp [hc.ne',hd.ne']
    have hlip := clip_lipschitz (a/d) (a/c)
    rw [abs_of_nonpos (sub_nonpos.mpr hdiv),neg_sub,he] at hlip
    exact hlip.trans (by
      have hh := mul_le_mul_of_nonneg_right ((div_le_one hd).mpr ha) hgap
      simpa only [one_mul] using hh)

lemma marginal_error {ξ b W L lam : ℝ} (hξ : 0< ξ) (hb : 0< b) (hW : 0< W)
    (hL : b-L≤ denominator ξ b W) :
    |probabilityClip ((b-L)/denominator ξ b W)-canonicalProbability ξ lam b|≤
      1/(b*W)+|L-lam|/(ξ*b) := by
  have hc : 0< ξ*b := mul_pos hξ hb
  have hd : ξ*b≤ denominator ξ b W := by
    unfold denominator
    have hterm : 0≤ ξ/W := div_nonneg hξ.le hW.le
    nlinarith [show ξ*(b+1/W)=ξ*b+ξ/W by ring]
  have hden := clipped_denominator_error hc hd hL
  have hcorr : (denominator ξ b W-ξ*b)/(ξ*b)=1/(b*W) := by
    unfold denominator
    field_simp [hξ.ne',hb.ne',hW.ne']; ring
  rw [hcorr] at hden
  have hprice := clip_lipschitz ((b-L)/(ξ*b)) ((b-lam)/(ξ*b))
  have he : (b-L)/(ξ*b)-(b-lam)/(ξ*b)=(lam-L)/(ξ*b) := by ring
  rw [he,abs_div,abs_of_pos hc,abs_sub_comm lam L] at hprice
  exact (abs_sub_le _ (probabilityClip ((b-L)/(ξ*b))) _).trans (add_le_add hden hprice)

lemma tiny_bid_count {ξ b W L0 L1 lam : ℝ}
    (hξ : 0< ξ) (hb : 0≤ b) (hW : 0< W)
    (h0 : b≤ L0) (h1 : b≤ L1) (hlam : b≤ lam) :
    actualCount ξ b W L0 L1=canonicalCount ξ lam b := by
  have hD := denominator_pos hξ hb hW
  have hp0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h0) hD.le
  have hp1 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h1) hD.le
  apply FiniteLaw.ext_expect
  intro f
  rw [actualCount_expect,canonicalCount_expect,canonical_zero hξ hb hlam]
  simp [focalPair,solution,hp0,hp1,zeroZero]

theorem all_nonnegative_bid_count_error (f : Fin 3→ℝ)
    {ξ b W L0 L1 lam B : ℝ} (hξ : 0< ξ) (hξh : ξ<1/2)
    (hB : 1≤ B) (hb : b∈Icc (0:ℝ) B) (hW : 0< W)
    (h0 : (1-ξ)*B≤ L0) (h1 : (1-ξ)*B≤ L1) (hlam : (1-ξ)*B≤ lam) :
    |(actualCount ξ b W L0 L1).expect f-(canonicalCount ξ lam b).expect f|≤
      MenuError.oscillation f*((4/ξ)*(|L0-lam|+|L1-lam|)+8/W+
        2*(if BetweenPrices L0 b L1 then 1 else 0)) := by
  have hκ : 0≤1-ξ := by linarith
  have hhalf : (1:ℝ)/2<(1-ξ)*B := by
    have hh := mul_le_mul_of_nonneg_left hB hκ
    nlinarith
  have hright0 : 0≤(4/ξ)*(|L0-lam|+|L1-lam|)+8/W := by positivity
  by_cases htiny : b≤1/4
  · rw [tiny_bid_count (lam:=lam) hξ hb.1 hW (by linarith) (by linarith) (by linarith),sub_self,abs_zero]
    apply mul_nonneg (oscillation_nonneg f)
    split_ifs <;> linarith
  · have hb0 : 0< b := by linarith
    have hbq : 1/4≤ b := (lt_of_not_ge htiny).le
    by_cases hbetween : BetweenPrices L0 b L1
    · simp only [if_pos hbetween]
      exact (count_expect_difference_bound _ _ f).trans (by
        have hh := mul_le_mul_of_nonneg_left
          (show (2:ℝ)≤(4/ξ)*(|L0-lam|+|L1-lam|)+8/W+2 by linarith)
          (oscillation_nonneg f)
        simpa only [mul_comm (2:ℝ),one_mul] using hh)
    · have hD := denominator_pos hξ hb.1 hW
      have hu0 := denominator_unsaturated hξ (by linarith : ξ≤1) hb.2 hW h0
      have hu1 := denominator_unsaturated hξ (by linarith : ξ≤1) hb.2 hW h1
      have hpair := pair_outside_between hD hu0 hu1 hbetween
      have hm0 := marginal_error hξ hb0 hW hu0.le (lam:=lam)
      have hm1 := marginal_error hξ hb0 hW hu1.le (lam:=lam)
      have hprice (L : ℝ) : |L-lam|/(ξ*b)≤(4/ξ)*|L-lam| := by
        have hi : 1/(ξ*b)≤4/ξ := by
          apply (div_le_div_iff₀ (mul_pos hξ hb0) hξ).mpr
          nlinarith
        have hh := mul_le_mul_of_nonneg_right hi (abs_nonneg (L-lam))
        simpa only [div_mul_eq_mul_div,one_mul] using hh
      have hwsmall : 1/(b*W)≤4/W := by
        apply (div_le_div_iff₀ (mul_pos hb0 hW) hW).mpr
        nlinarith
      have htotal :
          |(focalPair ξ b W L0 L1).left-canonicalProbability ξ lam b|+
          |(focalPair ξ b W L0 L1).right-canonicalProbability ξ lam b|≤
            (4/ξ)*(|L0-lam|+|L1-lam|)+8/W := by
        rw [hpair.1,hpair.2]
        have he0 := hprice L0
        have he1 := hprice L1
        simp only [mul_add,div_eq_mul_inv,one_mul] at hm0 hm1 he0 he1 hwsmall ⊢
        linarith
      rw [actualCount_expect,canonicalCount_expect]
      have hh := coinMoment_lipschitz f (focalPair ξ b W L0 L1).left_mem
        (focalPair ξ b W L0 L1).right_mem (canonicalProbability_mem ξ lam b)
        (canonicalProbability_mem ξ lam b)
      simp only [if_neg hbetween,mul_zero,add_zero]
      exact hh.trans (mul_le_mul_of_nonneg_left htotal (oscillation_nonneg f))

theorem original_private_count_error (N H0 H1 c : ℕ)
    {ξ B R Rp Rm : ℝ} (reg : Bool) (O0 O1 I : Finset (Fin N))
    (bids : Fin N→ℝ) (y lam : ℝ)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hξ : 0< ξ) (hξh : ξ<1/2) (hB : 1≤ B) (hy : y∈Icc (0:ℝ) B)
    (hbids : ∀ i,bids i∈Icc (1:ℝ) B)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : FocalInsertion.LocalGuard N H0 c ξ B reg O0 I bids)
    (hg1 : FocalInsertion.LocalGuard N H1 c ξ B reg O1 I bids)
    (hlam : (1-ξ)*B≤ lam) (f : Fin 3→ℝ) :
    let ν0:=AtypicalOriginalPosterior.markLaw θ0
    let ν1:=AtypicalOriginalPosterior.markLaw θ1
    let W:=mixedReciprocalSum I bids
    let L0:=TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I bids ν0
    let L1:=TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I bids ν1
    |(originalIndependentCountLaw
      (FocalInsertion.zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (FocalInsertion.oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (FocalInsertion.measurable_zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (FocalInsertion.measurable_oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (bids,y) θ0 θ1 none none).expect f-(canonicalCount ξ lam y).expect f|≤
        MenuError.oscillation f*((4/ξ)*(|L0-lam|+|L1-lam|)+8/W+
          2*(if BetweenPrices L0 y L1 then 1 else 0)) := by
  dsimp only
  rw [FocalInsertion.original_focal_count N H0 H1 c reg O0 O1 I bids y θ0 θ1
    hξ (by linarith : ξ≤1) hbids hs hg0 hg1]
  have hW := mixedReciprocalSum_pos I bids hs.2.2.2.2.2
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hbids i).1)
  have hL0 : (1-ξ)*B≤ TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I bids
      (AtypicalOriginalPosterior.markLaw θ0) :=
    (AtypicalOriginalPosterior.markLaw θ0).const_le_expect (fun z => (hg0 z).1)
  have hL1 : (1-ξ)*B≤ TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I bids
      (AtypicalOriginalPosterior.markLaw θ1) :=
    (AtypicalOriginalPosterior.markLaw θ1).const_le_expect (fun z => (hg1 z).1)
  exact all_nonnegative_bid_count_error f hξ hξh hB hy hW hL0 hL1 hlam

end FCAppendix.Affine.Tail04.UnusedFocalCountError
