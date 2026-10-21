import FCAppendix.Affine.Tail04.ZeroNoiseFallback
import FCAppendix.Affine.Tail04.UnequalPartialCountPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNoiseGuard
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open EqualPrivateSignal TypicalGuardStatistics AllNoiseFiniteSelector
open scoped BigOperators

section Parameters
variable {X : Type*} [TopologicalSpace X]

theorem continuousAt_phi (N H0 H1 c : ℕ) (ξ R width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (M : ℕ)
    (B V W : X→ℝ) (x : X) (hB : ContinuousAt B x) (hV : ContinuousAt V x)
    (hW : ContinuousAt W x) (hW0 : 0< W x) :
    ContinuousAt (fun y=>(TypicalGuardStatistics.phi N H0 H1 c ξ (B y) R (V y)
      width reg ν0 ν1 M (W y):ℝ)) x := by
  let P:=NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  have hlam (H ell : ℕ) (z : Marks H) : ContinuousAt
      (fun y=> multiplier H c ell M ξ reg (W y) z) x :=
    continuousAt_const.div hW hW0.ne'
  have hm (H ell : ℕ) (ν : FiniteLaw (Marks H)) : ContinuousAt
      (fun y=> meanMultiplier H c ell M ξ reg ν (W y)) x := by
    unfold meanMultiplier FiniteLaw.expect
    exact tendsto_finsetSum _ (fun z _=> continuousAt_const.mul (hlam H ell z))
  have hr (H ell : ℕ) : ContinuousAt
      (fun y=> realizationMargin H c ell M ξ (B y) reg (W y)) x := by
    apply continuousAt_finiteMinimum
    intro z
    exact ((hlam H ell z).sub (continuousAt_const.mul hB)).min
      (continuousAt_const.sub (hlam H ell z))
  have hp : ContinuousAt
      (fun y=> partialMargin H0 H1 c (P.owner0 M) (P.owner1 M) M ξ R (V y)
        reg ν0 ν1 (W y)) x := by
    cases reg
    · exact (continuousAt_const.sub (hm H0 (P.owner0 M) ν0)).min
        (continuousAt_const.sub (hm H1 (P.owner1 M) ν1))
    · exact ((hm H0 (P.owner0 M) ν0).sub hV).min
        ((hm H1 (P.owner1 M) ν1).sub hV)
  have hmargin : ContinuousAt
      (fun y=> margin H0 H1 c (P.owner0 M) (P.owner1 M) M ξ (B y) R (V y)
        reg ν0 ν1 (W y)) x :=
    ((hr H0 (P.owner0 M)).min (hr H1 (P.owner1 M))).min hp
  by_cases hs : Structural H0 H1 c (P.owner0 M) (P.owner1 M) M
  · dsimp only [P] at hs
    simp only [TypicalGuardStatistics.phi,weight,if_pos hs]
    exact continuous_probabilityClip.continuousAt.comp (hmargin.div_const width)
  · dsimp only [P] at hs
    simp only [TypicalGuardStatistics.phi,weight,if_neg hs]
    exact continuousAt_const

theorem continuousAt_targetWeight {N : ℕ} (H0 H1 c : ℕ) (ξ R width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B V : X→ℝ) (b : X→ Fin N→ℝ) (x : X)
    (hB : ContinuousAt B x) (hV : ContinuousAt V x)
    (hb : ContinuousAt b x) (hpos : ∀ i,0< b x i)
    (target : Fin N) (flags : Fin N→ Bool) :
    ContinuousAt (fun y=> targetTypicalWeight
      (TypicalGuardStatistics.phi N H0 H1 c ξ (B y) R (V y) width reg ν0 ν1)
      (b y) target flags) x := by
  let I:=targetMixedSet target flags
  by_cases hI : I.Nonempty
  · apply continuousAt_phi N H0 H1 c ξ R width reg ν0 ν1 I.card B V
      (fun y=> mixedReciprocalSum I (b y)) x hB hV
    · exact (continuousAt_mixedReciprocalSum I (b x) (fun i _=>(hpos i).ne')).comp hb
    · simpa only [mixedReciprocalSum,one_div] using Hybrid.reciprocal_sum_pos (b x) I hI (fun i _=> hpos i)
  · have he : I=∅:=Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [targetTypicalWeight,show targetMixedSet target flags=∅ from he,
      Finset.card_empty,TypicalGuardStatistics.phi_zero_mixed]
    exact continuousAt_const

theorem continuousAt_rawWeight (N H0 H1 c : ℕ) (ξ R width e0 F : ℝ)
    (reg low : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B V : X→ℝ) (b : X→ Fin N→ℝ) (x : X)
    (hB : ContinuousAt B x) (hV : ContinuousAt V x) (hb : ContinuousAt b x)
    (hpos : ∀ i,0< b x i) (hno : ∀ i j,i≠j→ b x i≠b x j) :
    ContinuousAt (fun y=> UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ (B y) R (V y)
      width e0 F reg low ν0 ν1 (b y)) x := by
  by_cases hN : N=0
  · simp only [UnequalPartialCountPayoff.rawWeight,dif_pos hN]
    exact continuousAt_const
  · letI : Nonempty (Fin N):=Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    cases low
    · simp only [UnequalPartialCountPayoff.rawWeight,dif_neg hN,Bool.false_eq_true,ite_false]
      exact continuousAt_const
    · simp only [UnequalPartialCountPayoff.rawWeight,dif_neg hN,ite_true]
      apply Hybrid.continuousAt_rankLaw_expect (fun i=>(continuous_apply i).continuousAt.comp hb)
      · intro target
        unfold FiniteLaw.expect
        apply tendsto_finsetSum
        intro flags _
        exact ((continuousAt_sourceFlagLaw_mass e0 F (b x) flags).comp hb).mul
          (continuousAt_targetWeight H0 H1 c ξ R width reg ν0 ν1 B V b x
            hB hV hb hpos target flags)
      · intro i j he
        have hij : i=j:=by_contra (fun h=> hno i j h he)
        subst j
        rfl

theorem continuousAt_rawCount_mass {N : ℕ} [Nonempty (Fin N)] (H0 H1 c : ℕ)
    (ξ R width e0 F : ℝ) (reg low : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B V : X→ℝ) (b : X→ Fin N→ℝ) (x : X)
    (hB : ContinuousAt B x) (hV : ContinuousAt V x) (hb : ContinuousAt b x)
    (hbad : b x∉ZeroNoiseFallback.bad N ξ) (i : Fin N) (r : Fin 3) :
    ContinuousAt (fun y=>(UnequalNoisyCountPayoff.rawCount H0 H1 c ξ (B y) R (V y)
      width e0 F reg low ν0 ν1 (b y) i).mass r) x := by
  obtain ⟨hpos,hno,hscore⟩:=ZeroNoiseFallback.regular_of_not_bad ξ (b x) hbad
  let fallback:=SortedAllNoise.sortedFallback N H0 H1 c ξ ν0 ν1 (b x) i
  have hsame : ∀ᶠ y in 𝓝 x,
      SortedAllNoise.sortedFallback N H0 H1 c ξ ν0 ν1 (b y) i=fallback :=
    (hb.tendsto.eventually (ZeroNoiseFallback.sortedFallback_eventually_eq N H0 H1 c ξ ν0 ν1
      (b x) hbad)).mono (fun _ h=> h i)
  cases low
  · change ContinuousAt (fun y : X=>(SortedAllNoise.sortedFallback N H0 H1 c ξ ν0 ν1 (b y) i).mass r) x
    have he : (fun _ : X=>fallback.mass r)=ᶠ[𝓝 x]
        (fun y : X=>(SortedAllNoise.sortedFallback N H0 H1 c ξ ν0 ν1 (b y) i).mass r) :=
      hsame.mono (fun _ h=>congrArg (fun q : CountLaw 2=>q.mass r) h.symm)
    exact (continuousAt_const : ContinuousAt (fun _ : X=>fallback.mass r) x).congr_of_eventuallyEq he.symm
  · let P:=NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
    have hcond (target : Fin N) : ContinuousAt (fun y=>
        (conditionalTargetCount P.mixedCount
          (TypicalGuardStatistics.phi N H0 H1 c ξ (B y) R (V y) width reg ν0 ν1)
          (b y) (sourceFlagProb e0 F (b y)) (sourceFlagProb_nonneg e0 F (b y))
          (sourceFlagProb_le_one e0 F (b y)) target i fallback).mass r) x := by
      unfold conditionalTargetCount FiniteLaw.finiteMix FiniteLaw.expect FiniteLaw.mixture
      apply tendsto_finsetSum
      intro flags _
      have hw:=continuousAt_targetWeight H0 H1 c ξ R width reg ν0 ν1 B V b x
        hB hV hb hpos target flags
      exact ((continuousAt_sourceFlagLaw_mass e0 F (b x) flags).comp hb).mul
        ((hw.mul ((continuousAt_targetStateCount_mass P (b x) hpos target flags i r).comp hb)).add
          ((continuousAt_const.sub hw).mul continuousAt_const))
    have hc:=Hybrid.continuousAt_rankLaw_expect
      (fun j=>(continuous_apply j).continuousAt.comp hb) hcond (by
        intro j k he
        have hjk : j=k:=by_contra (fun h=> hno j k h he)
        subst k
        rfl)
    apply hc.congr_of_eventuallyEq
    filter_upwards [hsame] with y hy
    change (typicalRankCount P.mixedCount
      (TypicalGuardStatistics.phi N H0 H1 c ξ (B y) R (V y) width reg ν0 ν1)
      (b y) (sourceFlagProb e0 F (b y)) _ _ i
      (SortedAllNoise.sortedFallback N H0 H1 c ξ ν0 ν1 (b y) i)).mass r=_
    rw [hy]
    rfl

end Parameters

section Measurability
variable {X : Type*} [MeasurableSpace X]

theorem measurable_phi (N H0 H1 c : ℕ) (ξ R width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (M : ℕ)
    (B V W : X→ℝ) (hB : Measurable B) (hV : Measurable V) (hW : Measurable W) :
    Measurable (fun y=>(TypicalGuardStatistics.phi N H0 H1 c ξ (B y) R (V y)
      width reg ν0 ν1 M (W y):ℝ)) := by
  have hlam (H ell : ℕ) (z : Marks H) : Measurable
      (fun y=> multiplier H c ell M ξ reg (W y) z) := measurable_const.div hW
  have hm (H ell : ℕ) (ν : FiniteLaw (Marks H)) : Measurable
      (fun y=> meanMultiplier H c ell M ξ reg ν (W y)) := by
    unfold meanMultiplier FiniteLaw.expect
    exact Finset.measurable_sum _ (fun z _=> measurable_const.mul (hlam H ell z))
  have hr (H ell : ℕ) : Measurable
      (fun y=> realizationMargin H c ell M ξ (B y) reg (W y)) := by
    apply UnequalNoisyCountPayoff.measurable_finiteMinimum
    intro z
    exact ((hlam H ell z).sub (measurable_const.mul hB)).min
      (measurable_const.sub (hlam H ell z))
  unfold TypicalGuardStatistics.phi weight
  dsimp only
  split_ifs
  · apply continuous_probabilityClip.measurable.comp
    apply Measurable.div_const
    unfold margin partialMargin
    apply ((hr _ _).min (hr _ _)).min
    cases reg
    · exact (measurable_const.sub (hm _ _ ν0)).min (measurable_const.sub (hm _ _ ν1))
    · exact ((hm _ _ ν0).sub hV).min ((hm _ _ ν1).sub hV)
  · exact measurable_const

theorem measurable_rawWeight (N H0 H1 c : ℕ) (ξ R width e0 F : ℝ)
    (reg low : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B V : X→ℝ) (b : X→ Fin N→ℝ) (hB : Measurable B) (hV : Measurable V)
    (hb : Measurable b) :
    Measurable (fun y=> UnequalPartialCountPayoff.rawWeight N H0 H1 c ξ (B y) R (V y)
      width e0 F reg low ν0 ν1 (b y)) := by
  by_cases hN : N=0
  · simp only [UnequalPartialCountPayoff.rawWeight,dif_pos hN]
    exact measurable_const
  · letI : Nonempty (Fin N):=Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    cases low
    · simp only [UnequalPartialCountPayoff.rawWeight,dif_neg hN,Bool.false_eq_true,ite_false]
      exact measurable_const
    · simp only [UnequalPartialCountPayoff.rawWeight,dif_neg hN,ite_true,FiniteLaw.expect]
      apply Finset.measurable_sum
      intro target _
      apply ((Hybrid.measurable_rankLaw_mass target).comp hb).mul
      apply Finset.measurable_sum
      intro flags _
      apply (((continuous_iff_continuousAt.mpr
        (fun b=> continuousAt_sourceFlagLaw_mass e0 F b flags)).measurable).comp hb).mul
      exact measurable_phi N H0 H1 c ξ R width reg ν0 ν1 _ B V _ hB hV
        ((UnequalNoisyCountPayoff.measurable_mixedReciprocalSum _).comp hb)

theorem measurable_rawCount_mass {N : ℕ} [Nonempty (Fin N)] (H0 H1 c : ℕ)
    (ξ R width e0 F : ℝ) (reg low : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B V : X→ℝ) (b : X→ Fin N→ℝ) (hB : Measurable B) (hV : Measurable V)
    (hb : Measurable b) (i : Fin N) (r : Fin 3) :
    Measurable (fun y=>(UnequalNoisyCountPayoff.rawCount H0 H1 c ξ (B y) R (V y)
      width e0 F reg low ν0 ν1 (b y) i).mass r) := by
  have hf:=(SortedAllNoise.measurable_sortedFallback_mass N H0 H1 c ξ ν0 ν1 i r).comp hb
  cases low
  · exact hf
  · simp only [UnequalNoisyCountPayoff.rawCount,ite_true,typicalRankCount,
      FiniteLaw.finiteMix,FiniteLaw.expect]
    apply Finset.measurable_sum
    intro target _
    apply ((Hybrid.measurable_rankLaw_mass target).comp hb).mul
    unfold conditionalTargetCount FiniteLaw.finiteMix FiniteLaw.expect FiniteLaw.mixture
    apply Finset.measurable_sum
    intro flags _
    apply (((continuous_iff_continuousAt.mpr
      (fun b=> continuousAt_sourceFlagLaw_mass e0 F b flags)).measurable).comp hb).mul
    have hw := measurable_phi N H0 H1 c ξ R width reg ν0 ν1 (targetMixedSet target flags).card B V
      (fun y=>mixedReciprocalSum (targetMixedSet target flags) (b y)) hB hV
      ((UnequalNoisyCountPayoff.measurable_mixedReciprocalSum (targetMixedSet target flags)).comp hb)
    apply (hw.mul ?_).add ((measurable_const.sub hw).mul hf)
    unfold targetStateCount
    split_ifs
    · exact (UnequalNoisyCountPayoff.measurable_meanCountLaw_mass _ _ _ i r).comp hb
    · exact measurable_const

end Measurability
end FCAppendix.Affine.Tail04.ZeroNoiseGuard
