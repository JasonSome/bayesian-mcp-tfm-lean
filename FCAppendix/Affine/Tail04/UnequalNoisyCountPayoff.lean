import FCAppendix.Affine.Tail04.SortedAllNoise
import FCAppendix.Affine.Tail04.TypicalGuardStatistics
import FCAppendix.Affine.Tail04.OriginalOwnerCount

noncomputable section
namespace FCAppendix.Affine.Tail04.UnequalNoisyCountPayoff
open MeasureTheory Set Filter Topology Classical
open EqualPrivateSignal AllNoiseFiniteSelector SortedAllNoise
open scoped BigOperators

variable {N : ℕ} [Nonempty (Fin N)]

lemma typicalRankCount_relabel {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Q : ℕ → ℝ → ℝ → CountLaw 2) (phi : ℕ → ℝ → unitInterval)
    (b p : ι → ℝ) (hp0 : ∀ i,0≤ p i) (hp1 : ∀ i,p i≤1)
    (e : Equiv.Perm ι) (i : ι) (fallback : CountLaw 2) :
    typicalRankCount Q phi (b ∘ e.symm) (p ∘ e.symm)
      (fun j => hp0 (e.symm j)) (fun j => hp1 (e.symm j)) (e i) fallback=
        typicalRankCount Q phi b p hp0 hp1 i fallback := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [typicalRankCount,FiniteLaw.expect_finiteMix]
  rw [Hybrid.rankLaw_relabel,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro target
  rw [conditionalTargetCount_relabel]

lemma typicalRankCount_sorted (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 B : ℝ) (b : Fin N → ℝ)
    (i : Fin N) (fallback : CountLaw 2) :
    typicalRankCount P.mixedCount phi (sorted b) (sourceFlagProb e0 B (sorted b))
      (sourceFlagProb_nonneg e0 B (sorted b)) (sourceFlagProb_le_one e0 B (sorted b))
      (focalRank b i) fallback=
    typicalRankCount P.mixedCount phi b (sourceFlagProb e0 B b)
      (sourceFlagProb_nonneg e0 B b) (sourceFlagProb_le_one e0 B b) i fallback := by
  convert!
    typicalRankCount_relabel P.mixedCount phi b (sourceFlagProb e0 B b)
      (sourceFlagProb_nonneg e0 B b) (sourceFlagProb_le_one e0 B b)
      (PrivateRowSorting.permutation b).symm i fallback using 1

def rawCount (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (i : Fin N) : CountLaw 2 :=
  if lowPresent then
    typicalRankCount (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1).mixedCount
      (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      b (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)
      i (sortedFallback N H0 H1 c ξ ν0 ν1 b i)
  else sortedFallback N H0 H1 c ξ ν0 ν1 b i

lemma measurable_listMinimum {A X : Type*} [MeasurableSpace X]
    (as : List A) (f : X → A → ℝ) (hf : ∀ a∈as,Measurable (fun x => f x a)) :
    Measurable (fun x => TypicalGuard.listMinimum as (f x)) := by
  induction as with
  | nil => exact measurable_const
  | cons a as ih => exact (hf a (by simp)).min (ih (fun b hb => hf b (by simp [hb])))

lemma measurable_finiteMinimum {A X : Type*} [Fintype A] [MeasurableSpace X]
    (f : X → A → ℝ) (hf : ∀ a,Measurable (fun x => f x a)) :
    Measurable (fun x => TypicalGuard.finiteMinimum (f x)) :=
  measurable_listMinimum _ f (fun a _ => hf a)

omit [Nonempty (Fin N)] in
lemma measurable_phi (H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (M : ℕ) :
    Measurable (fun W : ℝ =>
      (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1 M W:ℝ)) := by
  have hlam (H ell : ℕ) (z : Marks H) : Measurable
      (fun W : ℝ => TypicalGuardStatistics.multiplier H c ell M ξ reg W z) := by
    unfold TypicalGuardStatistics.multiplier
    fun_prop
  have hmean (H ell : ℕ) (ν : FiniteLaw (Marks H)) : Measurable
      (fun W : ℝ => TypicalGuardStatistics.meanMultiplier H c ell M ξ reg ν W) := by
    unfold TypicalGuardStatistics.meanMultiplier FiniteLaw.expect
    exact Finset.measurable_sum _ (fun z _ => measurable_const.mul (hlam H ell z))
  have hreal (H ell : ℕ) : Measurable
      (fun W : ℝ => TypicalGuardStatistics.realizationMargin H c ell M ξ B reg W) := by
    apply measurable_finiteMinimum
    intro z
    exact ((hlam H ell z).sub measurable_const).min (measurable_const.sub (hlam H ell z))
  unfold TypicalGuardStatistics.phi TypicalGuardStatistics.weight
  dsimp only
  split_ifs
  · apply continuous_probabilityClip.measurable.comp
    apply Measurable.div_const
    unfold TypicalGuardStatistics.margin TypicalGuardStatistics.partialMargin
    apply ((hreal _ _).min (hreal _ _)).min
    cases reg
    · exact (measurable_const.sub (hmean _ _ ν0)).min (measurable_const.sub (hmean _ _ ν1))
    · exact ((hmean _ _ ν0).sub measurable_const).min ((hmean _ _ ν1).sub measurable_const)
  · exact measurable_const

omit [Nonempty (Fin N)] in
lemma measurable_mixedReciprocalSum (I : Finset (Fin N)) :
    Measurable (fun b : Fin N → ℝ => mixedReciprocalSum I b) := by
  unfold mixedReciprocalSum
  exact Finset.measurable_sum _ (fun i _ => measurable_const.div (measurable_pi_apply i))

omit [Nonempty (Fin N)] in
lemma measurable_meanCountLaw_mass (P : TypicalCountParameters) (M : ℕ)
    (I : Finset (Fin N)) (i : Fin N) (r : Fin 3) :
    Measurable (fun b : Fin N → ℝ => (P.mixedCount M (mixedReciprocalSum I b) (b i)).mass r) := by
  have hm (ell : ℕ) (mean : ℝ) : Measurable (fun b : Fin N → ℝ =>
      meanMarginal P.xi P.c ell mean M (mixedReciprocalSum I b) (b i)) := by
    unfold meanMarginal rawMeanMarginal
    exact continuous_probabilityClip.measurable.comp
      ((measurable_const.sub ((measurable_const.div (measurable_mixedReciprocalSum I)).div
        (measurable_pi_apply i))).div_const P.xi)
  unfold TypicalCountParameters.mixedCount meanCountLaw
  exact measurable_twoCoinCountLaw_mass _ _ _ _ _ _
    (hm (P.owner0 M) P.privateMean0) (hm (P.owner1 M) P.privateMean1) r

lemma measurable_rawCount_mass (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3) :
    Measurable (fun b : Fin N → ℝ => (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b i).mass r) := by
  have hf := measurable_sortedFallback_mass N H0 H1 c ξ ν0 ν1 i r
  cases lowPresent
  · exact hf
  · unfold rawCount
    simp only [ite_true,typicalRankCount,FiniteLaw.finiteMix,FiniteLaw.expect]
    apply Finset.measurable_sum
    intro t _
    apply (Hybrid.measurable_rankLaw_mass t).mul
    unfold conditionalTargetCount FiniteLaw.finiteMix FiniteLaw.expect FiniteLaw.mixture
    apply Finset.measurable_sum
    intro z _
    have hflag : Measurable (fun b : Fin N → ℝ =>
        (independentFlagLaw (sourceFlagProb e0 F b)
          (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)).mass z) :=
      (continuous_iff_continuousAt.mpr (fun b => continuousAt_sourceFlagLaw_mass e0 F b z)).measurable
    apply hflag.mul
    have hw : Measurable (fun b : Fin N → ℝ =>
        targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1) b t z) :=
      (measurable_phi H0 H1 c ξ B R Rp width reg ν0 ν1 _).comp (measurable_mixedReciprocalSum _)
    apply (hw.mul ?_).add ((measurable_const.sub hw).mul hf)
    unfold targetStateCount
    split_ifs
    · exact measurable_meanCountLaw_mass _ _ _ i r
    · exact measurable_const

lemma continuousAt_constantFallback_mass (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval)
    (hphi : ∀ M W,0< W → ContinuousAt (fun W' => (phi M W':ℝ)) W)
    (e0 B : ℝ) (fallback : CountLaw 2) (b : Fin N → ℝ) (hb : ∀ j,0< b j)
    (hn : ∀ j k,j≠k → b j≠b k) (i : Fin N) (r : Fin 3) :
    ContinuousAt (fun a : Fin N → ℝ =>
      (typicalRankCount P.mixedCount phi a (sourceFlagProb e0 B a)
        (sourceFlagProb_nonneg e0 B a) (sourceFlagProb_le_one e0 B a) i fallback).mass r) b := by
  change ContinuousAt (fun a : Fin N → ℝ => (Hybrid.rankLaw a).expect
    (fun t => (conditionalTargetCount P.mixedCount phi a (sourceFlagProb e0 B a)
      (sourceFlagProb_nonneg e0 B a) (sourceFlagProb_le_one e0 B a) t i fallback).mass r)) b
  apply Hybrid.continuousAt_rankLaw_expect
    (fun j => (continuous_apply j).continuousAt)
    (fun t => continuousAt_conditionalTargetCount_mass P phi hphi e0 B b hb t i fallback r)
  intro j k hjk
  have he : j=k := by_contra (fun h => hn j k h hjk)
  rw [he]

lemma ae_continuousAt_noisy_mass (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ j,0< b j) (i : Fin N) (r : Fin 3) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ContinuousAt (fun a : Fin N → ℝ =>
        (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps a z) i).mass r) b := by
  filter_upwards [ae_sortedFallback_locally_constant N H0 H1 c ξ heps ν0 ν1 b hb,
    AtypicalActiveNoisy.ae_noisyBids_distinct heps.ne' b (fun j => (hb j).ne')] with z hz hn
  cases lowPresent
  · apply (continuousAt_const : ContinuousAt (fun _ : Fin N → ℝ =>
      (sortedFallback N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i).mass r) b).congr
    exact hz.mono (fun a ha => (congrArg (fun μ : CountLaw 2 => μ.mass r) (ha i)).symm)
  · let K := sortedFallback N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i
    have hpos (j : Fin N) : 0< noisyBids eps b z j := by
      unfold noisyBids
      exact mul_pos (hb j) (by nlinarith [mul_nonneg heps.le (z j).2.1])
    have hnoisy : Continuous (fun a : Fin N → ℝ => noisyBids eps a z) :=
      (continuous_noisyBids eps).comp
        (show Continuous (fun a : Fin N → ℝ => (a,z)) from continuous_id.prodMk continuous_const)
    have hc := (continuousAt_constantFallback_mass
      (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      (TypicalGuardStatistics.continuousAt_phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      e0 F K (noisyBids eps b z) hpos hn i r).comp
        (f := fun a : Fin N → ℝ => noisyBids eps a z) hnoisy.continuousAt
    apply hc.congr_of_eventuallyEq
    exact hz.mono (fun a ha => by simp only [rawCount,ite_true,ha i,K,Function.comp_def])

def smoothedMass (H0 H1 c : ℕ) (ξ B R Rp width e0 F eps : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3)
    (b : Fin N → ℝ) : ℝ :=
  ∫ z : Fin N → unitInterval,
    (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps b z) i).mass r
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

def smoothedPaymentMass (H0 H1 c : ℕ) (ξ B R Rp width e0 F eps : ℝ) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N) (r : Fin 3)
    (b : Fin N → ℝ) : ℝ :=
  ∫ z : Fin N → unitInterval, (1+eps*(z i:ℝ))*
    (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps b z) i).mass r
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

theorem continuousAt_smoothedMass (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ j,0< b j) (i : Fin N) (r : Fin 3) :
    ContinuousAt (smoothedMass H0 H1 c ξ B R Rp width e0 F eps reg lowPresent ν0 ν1 i r) b := by
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a z => (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1
      (noisyBids eps a z) i).mass r) (bound:=fun _ => (1:ℝ))
  · exact Eventually.of_forall (fun a => ((measurable_rawCount_mass H0 H1 c ξ B R Rp width e0 F
      reg lowPresent ν0 ν1 i r).comp
        ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable).aestronglyMeasurable)
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (AtypicalActiveNoisy.mass_bounds _ r).1]
      exact (AtypicalActiveNoisy.mass_bounds _ r).2))
  · exact integrable_const 1
  · exact ae_continuousAt_noisy_mass H0 H1 c ξ B R Rp width e0 F reg lowPresent heps ν0 ν1 b hb i r

theorem continuousAt_smoothedPaymentMass (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (hb : ∀ j,0< b j) (i : Fin N) (r : Fin 3) :
    ContinuousAt (smoothedPaymentMass H0 H1 c ξ B R Rp width e0 F eps reg lowPresent ν0 ν1 i r) b := by
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun a z => (1+eps*(z i:ℝ))*(rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1
      (noisyBids eps a z) i).mass r) (bound:=fun _ => 1+eps)
  · exact Eventually.of_forall (fun a => Measurable.aestronglyMeasurable
      ((by fun_prop : Measurable (fun z : Fin N → unitInterval => 1+eps*(z i:ℝ))).mul
      ((measurable_rawCount_mass H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 i r).comp
        ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable)))
  · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => by
      have h0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps.le (z i).2.1]
      have h1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
      have hm := AtypicalActiveNoisy.mass_bounds
        (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps a z) i) r
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 hm.1)]
      exact (mul_le_of_le_one_right h0 hm.2).trans h1))
  · exact integrable_const _
  · filter_upwards [ae_continuousAt_noisy_mass H0 H1 c ξ B R Rp width e0 F reg lowPresent
      heps ν0 ν1 b hb i r] with z hz
    exact continuousAt_const.mul hz

def utility (H0 H1 c : ℕ) (ξ B R Rp width e0 F eps eta : ℝ) (reg lowPresent : Bool)
    (heta0 : 0≤ eta) (heta1 : eta≤1)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N)
    (x : ℝ×(Fin N → ℝ)) : ℝ :=
  ∑ r : Fin 3,
    (x.1*successIndicator r.val*
      smoothedMass H0 H1 c ξ B R Rp width e0 F eps reg lowPresent ν0 ν1 i r x.2-
    x.2 i*(Schedule.affine 2 eta heta0 heta1).charge r.val*
      smoothedPaymentMass H0 H1 c ξ B R Rp width e0 F eps reg lowPresent ν0 ν1 i r x.2)

theorem continuousAt_utility (H0 H1 c : ℕ) (ξ B R Rp width e0 F eta : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (heta0 : 0≤ eta) (heta1 : eta≤1)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N)
    (x : ℝ×(Fin N → ℝ)) (hb : ∀ j,0< x.2 j) :
    ContinuousAt (utility H0 H1 c ξ B R Rp width e0 F eps eta reg lowPresent heta0 heta1 ν0 ν1 i) x := by
  unfold utility
  apply tendsto_finsetSum
  intro r _
  exact (((continuousAt_fst.mul continuousAt_const).mul
    ((continuousAt_smoothedMass H0 H1 c ξ B R Rp width e0 F reg lowPresent heps ν0 ν1 x.2 hb i r).comp
      continuousAt_snd)).sub
    ((((continuous_apply i).continuousAt.comp continuousAt_snd).mul continuousAt_const).mul
      ((continuousAt_smoothedPaymentMass H0 H1 c ξ B R Rp width e0 F reg lowPresent heps ν0 ν1 x.2 hb i r).comp
        continuousAt_snd)))

theorem utility_eq_integral (H0 H1 c : ℕ) (ξ B R Rp width e0 F eta : ℝ) (reg lowPresent : Bool)
    {eps : ℝ} (heps : 0< eps) (heta0 : 0≤ eta) (heta1 : eta≤1)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N)
    (v : ℝ) (b : Fin N → ℝ) :
    utility H0 H1 c ξ B R Rp width e0 F eps eta reg lowPresent heta0 heta1 ν0 ν1 i (v,b)=
      ∫ z : Fin N → unitInterval,
        affineCountUtility (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1
          (noisyBids eps b z) i) v (noisyBids eps b z i) eta heta0 heta1
          ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)) := by
  let μ : Measure (Fin N → unitInterval) := Measure.pi (fun _ : Fin N => volume)
  let mass : Fin 3 → (Fin N → unitInterval) → ℝ := fun r z =>
    (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (noisyBids eps b z) i).mass r
  have hmeas (r : Fin 3) : Measurable (mass r) :=
    (measurable_rawCount_mass H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 i r).comp
      ((continuous_noisyBids eps).comp (continuous_const.prodMk continuous_id)).measurable
  have hm (r : Fin 3) : Integrable (mass r) μ :=
    Integrable.of_bound (hmeas r).aestronglyMeasurable 1 (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (AtypicalActiveNoisy.mass_bounds _ r).1]
      exact (AtypicalActiveNoisy.mass_bounds _ r).2))
  have hp (r : Fin 3) : Integrable (fun z => (1+eps*(z i:ℝ))*mass r z) μ :=
    Integrable.of_bound
      (((by fun_prop : Measurable (fun z : Fin N → unitInterval => 1+eps*(z i:ℝ))).mul
        (hmeas r)).aestronglyMeasurable) (1+eps) (ae_of_all _ (fun z => by
      have h0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps.le (z i).2.1]
      have h1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 (AtypicalActiveNoisy.mass_bounds _ r).1)]
      exact (mul_le_of_le_one_right h0 (AtypicalActiveNoisy.mass_bounds _ r).2).trans h1))
  have hr (r : Fin 3) : Integrable (fun z =>
      v*successIndicator r.val*mass r z-
        b i*(Schedule.affine 2 eta heta0 heta1).charge r.val*((1+eps*(z i:ℝ))*mass r z)) μ :=
    ((hm r).const_mul _).sub ((hp r).const_mul _)
  have he (z : Fin N → unitInterval) :
      affineCountUtility (rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1
        (noisyBids eps b z) i) v (noisyBids eps b z i) eta heta0 heta1=
      ∑ r : Fin 3, (v*successIndicator r.val*mass r z-
        b i*(Schedule.affine 2 eta heta0 heta1).charge r.val*((1+eps*(z i:ℝ))*mass r z)) := by
    unfold affineCountUtility CountLaw.utility FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro r _
    dsimp [mass,userPayoff,noisyBids]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun r _ => hr r)]
  unfold utility smoothedMass smoothedPaymentMass
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_sub ((hm r).const_mul _) ((hp r).const_mul _),integral_const_mul,integral_const_mul]

end FCAppendix.Affine.Tail04.UnequalNoisyCountPayoff
