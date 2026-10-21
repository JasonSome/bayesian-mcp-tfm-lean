import FCAppendix.Affine.Tail04.UniformFallbackVariation
import FCAppendix.Affine.Tail04.TypicalGuardStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04.MovingGuardVariation
open MeasureTheory Set Filter Topology Classical
open EqualPrivateSignal TypicalGuardStatistics TypicalFinitePromotion
open ActualFallbackPromotion UniformFallbackVariation
open scoped BigOperators

variable {X : Type*} [TopologicalSpace X]

theorem continuousAt_phi_moving (N H0 H1 c : ℕ) (ξ R width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (M : ℕ)
    (B Rp W : X → ℝ) (x : X)
    (hB : ContinuousAt B x) (hRp : ContinuousAt Rp x) (hW : ContinuousAt W x)
    (hW0 : 0< W x) :
    ContinuousAt (fun y => (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1 M (W y):ℝ)) x := by
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  have hm (H ell : ℕ) (z : Marks H) : ContinuousAt
      (fun y => multiplier H c ell M ξ reg (W y) z) x :=
    (continuousAt_multiplier H c ell M ξ reg (W x) hW0.ne' z).comp hW
  have havg (H ell : ℕ) (ν : FiniteLaw (Marks H)) : ContinuousAt
      (fun y => meanMultiplier H c ell M ξ reg ν (W y)) x :=
    (continuousAt_meanMultiplier H c ell M ξ reg ν (W x) hW0.ne').comp hW
  have hr (H ell : ℕ) : ContinuousAt
      (fun y => realizationMargin H c ell M ξ (B y) reg (W y)) x := by
    apply continuousAt_finiteMinimum
    intro z
    exact ((hm H ell z).sub (continuousAt_const.mul hB)).min
      (continuousAt_const.sub (hm H ell z))
  have hp : ContinuousAt (fun y => partialMargin H0 H1 c (P.owner0 M) (P.owner1 M) M
      ξ R (Rp y) reg ν0 ν1 (W y)) x := by
    cases reg
    · exact (continuousAt_const.sub (havg H0 (P.owner0 M) ν0)).min
        (continuousAt_const.sub (havg H1 (P.owner1 M) ν1))
    · exact ((havg H0 (P.owner0 M) ν0).sub hRp).min
        ((havg H1 (P.owner1 M) ν1).sub hRp)
  have hmargin : ContinuousAt (fun y => margin H0 H1 c (P.owner0 M) (P.owner1 M) M
      ξ (B y) R (Rp y) reg ν0 ν1 (W y)) x :=
    ((hr H0 (P.owner0 M)).min (hr H1 (P.owner1 M))).min hp
  dsimp only [P] at hmargin
  by_cases hs : Structural H0 H1 c (P.owner0 M) (P.owner1 M) M
  · dsimp only [P] at hs
    simp only [phi,weight,if_pos hs]
    exact continuous_probabilityClip.continuousAt.comp (hmargin.div_const width)
  · dsimp only [P] at hs
    simp only [phi,weight,if_neg hs]
    exact continuousAt_const

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in

theorem continuousAt_targetWeight_moving (N H0 H1 c : ℕ) (ξ R width : ℝ)
    (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B Rp : X → ℝ) (b : X → ι → ℝ) (x : X)
    (hB : ContinuousAt B x) (hRp : ContinuousAt Rp x) (hb : ContinuousAt b x)
    (hpos : ∀ j,0< b x j) (target : ι) (flags : ι → Bool) :
    ContinuousAt (fun y => targetTypicalWeight
      (effectivePhi lowPresent (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1))
      (b y) target flags) x := by
  cases lowPresent
  · change ContinuousAt (fun _ : X => (0:ℝ)) x
    exact continuousAt_const
  · let I := targetMixedSet target flags
    by_cases hI : I.Nonempty
    · have hW : 0< mixedReciprocalSum I (b x) :=
        by simpa only [mixedReciprocalSum,one_div] using
          Hybrid.reciprocal_sum_pos (b x) I hI (fun j _ => hpos j)
      exact continuousAt_phi_moving N H0 H1 c ξ R width reg ν0 ν1 I.card B Rp
        (fun y => mixedReciprocalSum I (b y)) x hB hRp
        ((continuousAt_mixedReciprocalSum I (b x) (fun j _ => (hpos j).ne')).comp hb) hW
    · have hI0 : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      have hz (y : X) : targetTypicalWeight
          (effectivePhi true (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1))
          (b y) target flags=0 := by
        change (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1 I.card
          (mixedReciprocalSum I (b y)):ℝ)=0
        rw [hI0,Finset.card_empty]
        exact phi_zero_mixed N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1 _
      simpa only [hz] using (continuousAt_const : ContinuousAt (fun _ : X => (0:ℝ)) x)

omit [Nonempty ι] in
theorem continuousAt_conditionalUtility_moving (N H0 H1 c : ℕ)
    (ξ R width e0 F eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (B Rp v : X → ℝ) (b : X → ι → ℝ) (x : X)
    (hB : ContinuousAt B x) (hRp : ContinuousAt Rp x) (hv : ContinuousAt v x)
    (hb : ContinuousAt b x) (hpos : ∀ j,0< b x j)
    (i target : ι) (K : CountLaw 2) :
    ContinuousAt (fun y => conditionalUtility
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1))
      e0 F eta (v y) he0 he1 i K (b y) target) x := by
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  have hm (r : Fin 3) : ContinuousAt (fun y =>
      (conditionalTargetCount P.mixedCount
        (effectivePhi lowPresent (phi N H0 H1 c ξ (B y) R (Rp y) width reg ν0 ν1))
        (b y) (sourceFlagProb e0 F (b y)) (sourceFlagProb_nonneg e0 F (b y))
        (sourceFlagProb_le_one e0 F (b y)) target i K).mass r) x := by
    unfold conditionalTargetCount FiniteLaw.finiteMix FiniteLaw.expect FiniteLaw.mixture
    apply tendsto_finsetSum
    intro flags _
    have hw := continuousAt_targetWeight_moving N H0 H1 c ξ R width reg lowPresent
      ν0 ν1 B Rp b x hB hRp hb hpos target flags
    exact ((continuousAt_sourceFlagLaw_mass e0 F (b x) flags).comp hb).mul
      ((hw.mul ((continuousAt_targetStateCount_mass P (b x) hpos target flags i r).comp hb)).add
        ((continuousAt_const.sub hw).mul continuousAt_const))
  unfold conditionalUtility affineCountUtility CountLaw.utility FiniteLaw.expect
  apply tendsto_finsetSum
  intro r _
  apply (hm r).mul
  unfold userPayoff
  exact ((hv.mul continuousAt_const).sub
    ((((continuous_apply i).continuousAt.comp hb)).mul continuousAt_const)).sub continuousAt_const

abbrev Environment (ι : Type*) := (ℝ×ℝ)×(ℝ×(ι → ℝ))

omit [Nonempty ι] in
set_option maxHeartbeats 800000 in

theorem dirac_variation_moving_tendsto_zero (N H0 H1 c : ℕ)
    (ξ R width e0 F eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : ι) (r : Fin 3)
    (B Rp v : ℕ → ℝ) (b d : ℕ → ι → ℝ) (B0 Rp0 v0 : ℝ) (x : ι → ℝ)
    (hB : Tendsto B atTop (𝓝 B0)) (hRp : Tendsto Rp atTop (𝓝 Rp0))
    (hv : Tendsto v atTop (𝓝 v0)) (hb : Tendsto b atTop (𝓝 x))
    (hd : Tendsto d atTop (𝓝 x)) (hx : ∀ j,0< x j) :
    Tendsto (fun n => variation (conditionalUtility
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ (B n) R (Rp n) width reg ν0 ν1))
      e0 F eta (v n) he0 he1 i (FiniteLaw.dirac r)) (b n) (d n)) atTop (𝓝 0) := by
  have hc (j : ι) : ContinuousAt (fun y : Environment ι => conditionalUtility
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ y.1.1 R y.1.2 width reg ν0 ν1))
      e0 F eta y.2.1 he0 he1 i (FiniteLaw.dirac r) y.2.2 j) ((B0,Rp0),(v0,x)) :=
    continuousAt_conditionalUtility_moving N H0 H1 c ξ R width e0 F eta he0 he1
      reg lowPresent ν0 ν1 (fun y : Environment ι => y.1.1) (fun y : Environment ι => y.1.2)
      (fun y : Environment ι => y.2.1) (fun y : Environment ι => y.2.2)
      ((B0,Rp0),(v0,x)) continuous_fst.fst.continuousAt continuous_fst.snd.continuousAt
      continuous_snd.fst.continuousAt continuous_snd.snd.continuousAt hx i j _
  have ha := (hB.prodMk_nhds hRp).prodMk_nhds (hv.prodMk_nhds hb)
  have hz := (hB.prodMk_nhds hRp).prodMk_nhds (hv.prodMk_nhds hd)
  have hs := tendsto_finsetSum Finset.univ (fun j _ =>
    (((hc j).tendsto.comp ha).sub ((hc j).tendsto.comp hz)).abs)
  simpa only [variation,Function.comp_apply,sub_self,abs_zero,Finset.sum_const_zero] using hs

omit [Nonempty ι] in

theorem arbitrary_fallback_moving_tendsto_zero (N H0 H1 c : ℕ)
    (ξ R width e0 F eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : ι) (K : ℕ → CountLaw 2)
    (B Rp v : ℕ → ℝ) (b d : ℕ → ι → ℝ) (B0 Rp0 v0 : ℝ) (x : ι → ℝ)
    (hB : Tendsto B atTop (𝓝 B0)) (hRp : Tendsto Rp atTop (𝓝 Rp0))
    (hv : Tendsto v atTop (𝓝 v0)) (hb : Tendsto b atTop (𝓝 x))
    (hd : Tendsto d atTop (𝓝 x)) (hx : ∀ j,0< x j) :
    Tendsto (fun n => variation (conditionalUtility
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ (B n) R (Rp n) width reg ν0 ν1))
      e0 F eta (v n) he0 he1 i (K n)) (b n) (d n)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => variation_nonneg _ _ _)
    (fun n => variation_le_uniformVariation _ _ e0 F eta (v n) he0 he1 i (K n) (b n) (d n))
  have hs := tendsto_finsetSum Finset.univ (fun r _ =>
    dirac_variation_moving_tendsto_zero N H0 H1 c ξ R width e0 F eta he0 he1 reg lowPresent
      ν0 ν1 i r B Rp v b d B0 Rp0 v0 x hB hRp hv hb hd hx)
  simpa only [uniformVariation,Finset.sum_const_zero] using hs

end FCAppendix.Affine.Tail04.MovingGuardVariation
