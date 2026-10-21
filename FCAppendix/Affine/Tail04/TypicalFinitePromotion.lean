import FCAppendix.Affine.Tail04.TypicalCountContinuity
import FCAppendix.Affine.Hybrid.FavoredFiniteRank

noncomputable section
namespace FCAppendix.Affine.Tail04.TypicalFinitePromotion
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def conditionalUtility (P : TypicalCountParameters) (phi : ℕ → ℝ → unitInterval)
    (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (fallback : CountLaw 2)
    (b : ι → ℝ) (target : ι) : ℝ :=
  affineCountUtility
    (conditionalTargetCount P.mixedCount phi b (sourceFlagProb e0 B b)
      (sourceFlagProb_nonneg e0 B b) (sourceFlagProb_le_one e0 B b) target i fallback)
    v (b i) eta he0 he1

def variation (f : (ι → ℝ) → ι → ℝ) (b d : ι → ℝ) : ℝ :=
  ∑ j,|f b j-f d j|

omit [DecidableEq ι] [Nonempty ι] in
lemma variation_nonneg (f : (ι → ℝ) → ι → ℝ) (b d : ι → ℝ) :
    0≤ variation f b d := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

omit [DecidableEq ι] [Nonempty ι] in
lemma variation_bounds (f : (ι → ℝ) → ι → ℝ) (b d : ι → ℝ) (j : ι) :
    |f b j-f d j|≤ variation f b d := by
  exact Finset.single_le_sum (fun k _ => abs_nonneg (f b k-f d k)) (Finset.mem_univ j)

omit [DecidableEq ι] in
lemma rank_expect_variation (f : (ι → ℝ) → ι → ℝ) (b d w : ι → ℝ) :
    |(Hybrid.rankLaw w).expect (f b)-(Hybrid.rankLaw w).expect (f d)|≤ variation f b d :=
  Hybrid.abs_expect_sub_expect_le _ _ _ _ (variation_bounds f b d)

omit [Nonempty ι] in
lemma conditionalUtility_difference (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1)
    (i j : ι) (fallback : CountLaw 2) (d : ι → ℝ) (hd : d i=d j) :
    conditionalUtility P phi e0 B eta v he0 he1 i fallback d i-
      conditionalUtility P phi e0 B eta v he0 he1 i fallback d j=
      targetExchangeGain P.mixedCount phi d (sourceFlagProb e0 B d)
        (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d) i j v eta he0 he1 :=
  conditionalTargetCount_utility_difference P.mixedCount phi d (sourceFlagProb e0 B d)
    (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d) i j hd
    (by simp only [sourceFlagProb,hd]) fallback v eta he0 he1

theorem actual_finite_transfer (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1)
    (i : ι) (fallback : CountLaw 2) (b d : ι → ℝ) (y : ℝ) (hy : b i≤ y)
    (hd : ∀ j,b j∈Icc (b i) y → d i=d j) :
    (∑ j,Hybrid.rankTransfer b i y j*
      targetExchangeGain P.mixedCount phi d (sourceFlagProb e0 B d)
        (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d) i j v eta he0 he1)/
        Hybrid.rankDenominator ι-
      variation (conditionalUtility P phi e0 B eta v he0 he1 i fallback) b d-
      variation (conditionalUtility P phi e0 B eta v he0 he1 i fallback)
        (Function.update b i y) d ≤
      sourceTypicalJointPayoff P phi e0 B eta he0 he1 i fallback (v,Function.update b i y)-
        sourceTypicalJointPayoff P phi e0 B eta he0 he1 i fallback (v,b) := by
  let f := conditionalUtility P phi e0 B eta v he0 he1 i fallback
  have h0 := rank_expect_variation f b d b
  have h1 := rank_expect_variation f (Function.update b i y) d (Function.update b i y)
  have hr := Hybrid.rankLaw_update_expect b i y (f d)
  have hsum : (∑ j,Hybrid.rankTransfer b i y j*(f d i-f d j))=
      ∑ j,Hybrid.rankTransfer b i y j*
        targetExchangeGain P.mixedCount phi d (sourceFlagProb e0 B d)
          (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d) i j v eta he0 he1 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : b j∈Icc (b i) y
    · rw [conditionalUtility_difference P phi e0 B eta v he0 he1 i j fallback d (hd j hj)]
    · rw [Hybrid.rankTransfer_eq_zero_of_not_between b i j y hy hj]
      ring
  rw [hsum] at hr
  simp only [sourceTypicalJointPayoff,typicalRankCount_utility]
  change _ ≤ (Hybrid.rankLaw (Function.update b i y)).expect (f (Function.update b i y))-
    (Hybrid.rankLaw b).expect (f b)
  rcases abs_le.mp h0 with ⟨h0l,h0u⟩
  rcases abs_le.mp h1 with ⟨h1l,h1u⟩
  linarith

def crossed (b : ι → ℝ) (i : ι) (y : ℝ) : Finset ι :=
  Finset.univ.filter fun j => j≠i ∧ b j∈Icc (b i) y

theorem actual_finite_transfer_lower (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B eta v L qmin : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (hL : 0≤ L) (hq : 0≤ qmin)
    (i : ι) (fallback : CountLaw 2) (b d : ι → ℝ) (y : ℝ) (hy : b i< y)
    (hd : ∀ j,b j∈Icc (b i) y → d i=d j) (hv : d i≤ v) (hb : L≤ d i)
    (good : (ι → Bool) → Prop)
    (hgood : ∀ z,good z → targetTypicalWeight phi d i z=1)
    (hsmall : (independentFlagLaw (sourceFlagProb e0 B d)
      (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d)).prob (fun z => ¬good z)≤
        (sourceFlagProb e0 B d i)^2)
    (hq0 : ∀ z,good z → qmin≤ meanMarginal P.xi P.c
      (P.owner0 (targetMixedSet i z).card) P.privateMean0 (targetMixedSet i z).card
        (mixedReciprocalSum (targetMixedSet i z) d) (d i))
    (hq1 : ∀ z,good z → qmin≤ meanMarginal P.xi P.c
      (P.owner1 (targetMixedSet i z).card) P.privateMean1 (targetMixedSet i z).card
        (mixedReciprocalSum (targetMixedSet i z) d) (d i)) :
    (eta*L*qmin^2)*((sourceFlagProb e0 B d i)^2-
      (independentFlagLaw (sourceFlagProb e0 B d)
        (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d)).prob (fun z => ¬good z))*
          (crossed b i y).card/(2*Hybrid.rankDenominator ι)-
      variation (conditionalUtility P phi e0 B eta v he0 he1 i fallback) b d-
      variation (conditionalUtility P phi e0 B eta v he0 he1 i fallback)
        (Function.update b i y) d ≤
      sourceTypicalJointPayoff P phi e0 B eta he0 he1 i fallback (v,Function.update b i y)-
        sourceTypicalJointPayoff P phi e0 B eta he0 he1 i fallback (v,b) := by
  let p := sourceFlagProb e0 B d
  let β := (independentFlagLaw p (sourceFlagProb_nonneg e0 B d)
    (sourceFlagProb_le_one e0 B d)).prob (fun z => ¬good z)
  let g := (eta*L*qmin^2)*((p i)^2-β)
  have hg : 0≤ g := mul_nonneg (by positivity) (sub_nonneg.mpr hsmall)
  have hpoint (j : ι) :
      (if j∈crossed b i y then g/2 else 0)≤ Hybrid.rankTransfer b i y j*
        targetExchangeGain P.mixedCount phi d p (sourceFlagProb_nonneg e0 B d)
          (sourceFlagProb_le_one e0 B d) i j v eta he0 he1 := by
    by_cases hj : j∈crossed b i y
    · have hji := (Finset.mem_filter.mp hj).2.1
      have hjb := (Finset.mem_filter.mp hj).2.2
      have hpij : p i=p j := by simp only [p,sourceFlagProb,hd j hjb]
      have ht := source_targetExchangeGain_lower P phi d p (sourceFlagProb_nonneg e0 B d)
        (sourceFlagProb_le_one e0 B d) i j hji.symm (hd j hjb) good hgood
        hv hL hb he0 he1 hq (fun z _ _ hz => hq0 z hz) (fun z _ _ hz => hq1 z hz)
      have ht' : g≤ targetExchangeGain P.mixedCount phi d p
          (sourceFlagProb_nonneg e0 B d) (sourceFlagProb_le_one e0 B d) i j v eta he0 he1 := by
        simpa only [g,β,←hpij,pow_two] using ht
      have hr := Hybrid.rankTransfer_half_le_between b i j y hji hy hjb
      rw [if_pos hj]
      have hm := mul_le_mul hr ht' hg (Hybrid.rankTransfer_nonneg b i j y hy.le)
      nlinarith only [hm]
    · rw [if_neg hj]
      exact mul_nonneg (Hybrid.rankTransfer_nonneg b i j y hy.le)
        (targetExchangeGain_nonneg P.mixedCount phi d p (sourceFlagProb_nonneg e0 B d)
          (sourceFlagProb_le_one e0 B d) i j hv (hL.trans hb) he0 he1)
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset ι)) => hpoint j)
  have he : (∑ j : ι,if j∈crossed b i y then g/2 else 0)=g*(crossed b i y).card/2 := by
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he] at hs
  have hdpos := Hybrid.rankDenominator_pos (ι:=ι)
  have hh := div_le_div_of_nonneg_right hs hdpos.le
  have hx := actual_finite_transfer P phi e0 B eta v he0 he1 i fallback b d y hy.le hd
  have heq : (g*(crossed b i y).card/2)/Hybrid.rankDenominator ι=
      g*(crossed b i y).card/(2*Hybrid.rankDenominator ι) := by rw [div_div]
  rw [heq] at hh
  exact (sub_le_sub_right (sub_le_sub_right hh _) _).trans hx

def freeze (b : ι → ℝ) (a y center : ℝ) : ι → ℝ :=
  fun j => if b j∈Icc a y then center else b j

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma freeze_ties (b : ι → ℝ) (i : ι) (a y center : ℝ)
    (ha : a≤ b i) (hy : b i≤ y) (j : ι) (hj : b j∈Icc (b i) y) :
    freeze b a y center i=freeze b a y center j := by
  simp only [freeze,if_pos (show b i∈Icc a y from ⟨ha,hy⟩),
    if_pos (show b j∈Icc a y from ⟨ha.trans hj.1,hj.2⟩)]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma freeze_variation_bound (b : ι → ℝ) (a y center δ : ℝ)
    (hδ : 0≤ δ) (ha : center-δ≤ a) (hy : y≤ center+δ) (j : ι) :
    |freeze b a y center j-b j|≤ δ := by
  by_cases hj : b j∈Icc a y
  · rw [freeze,if_pos hj]
    exact abs_le.mpr ⟨by linarith [hj.2],by linarith [hj.1]⟩
  · simp only [freeze,if_neg hj,sub_self,abs_zero]
    exact hδ

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma freeze_mem (b : ι → ℝ) (a y center lo hi : ℝ)
    (hb : ∀ j,b j∈Icc lo hi) (hc : center∈Icc lo hi) (j : ι) :
    freeze b a y center j∈Icc lo hi := by
  unfold freeze
  split_ifs <;> first | exact hc | exact hb j

omit [Nonempty ι] in

theorem variation_tendsto_zero (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W,0< W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B eta v : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (i : ι) (fallback : CountLaw 2)
    (b d : ℕ → ι → ℝ) (x : ι → ℝ) (hx : ∀ j,0< x j)
    (hb : Tendsto b atTop (𝓝 x)) (hd : Tendsto d atTop (𝓝 x)) :
    Tendsto (fun n => variation (conditionalUtility P phi e0 B eta v he0 he1 i fallback)
      (b n) (d n)) atTop (𝓝 0) := by
  have hc (j : ι) : ContinuousAt
      (conditionalUtility P phi e0 B eta v he0 he1 i fallback · j) x := by
    have h := continuousAt_joint_conditionalTargetUtility P phi hphi e0 B eta he0 he1
      j i fallback (v,x) hx
    exact h.comp (continuousAt_const.prodMk continuousAt_id)
  have he (j : ι) := ((hc j).tendsto.comp hb).sub ((hc j).tendsto.comp hd)
  have hs := tendsto_finsetSum Finset.univ (fun j _ => (he j).abs)
  simpa only [Function.comp_def,sub_self,abs_zero,Finset.sum_const_zero,variation] using hs

end FCAppendix.Affine.Tail04.TypicalFinitePromotion
