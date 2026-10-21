import FCAppendix.Affine.Tail04.SourceMenuError

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

section Original
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X×unitInterval)
  (hrow : MeasurePreserving row ν
    (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))))
  (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
  (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)

def commonEmpiricalError (x : Ω) : ℝ :=
  (∑ k : Fin 5,sourceEmpiricalError μ N row active private0 private1 p bid k x)+4/(N:ℝ)

omit [MeasurableSpace Ω] [IsProbabilityMeasure μ] in
lemma commonEmpiricalError_nonnegative (x : Ω) :
    0≤ commonEmpiricalError μ N row active private0 private1 p bid x := by
  exact add_nonneg (Finset.sum_nonneg fun k _ => abs_nonneg _) (by positivity)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
include hrow hactive hprivate0 hprivate1 hp hbid in
lemma measurable_commonEmpiricalError :
    Measurable (commonEmpiricalError μ N row active private0 private1 p bid) := by
  apply Measurable.add_const
  apply Finset.measurable_sum
  intro k _
  exact (((measurable_empiricalMean N (sourceBasis active private0 private1 p bid k)
    (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)).comp
      hrow.measurable).sub_const _).abs

omit [IsProbabilityMeasure μ] in
include hN hrow hactive hprivate0 hprivate1 hp hbid in
lemma integrable_sourceEmpiricalError (k : Fin 5) :
    Integrable (sourceEmpiricalError μ N row active private0 private1 p bid k) ν :=
  ((integrable_empiricalMean (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
    (sourceBasis active private0 private1 p bid k)
    (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)
    (sourceBasis_bounds active private0 private1 p bid k)).sub (integrable_const _)).abs

omit [IsProbabilityMeasure μ] in
include hN hrow hactive hprivate0 hprivate1 hp hbid in
lemma integrable_commonEmpiricalError :
    Integrable (commonEmpiricalError μ N row active private0 private1 p bid) ν :=
  (integrable_finsetSum _ fun k _ => integrable_sourceEmpiricalError μ ν N hN row hrow
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k).add (integrable_const _)

include hN hrow hactive hprivate0 hprivate1 hp hbid in
theorem commonEmpiricalError_L1 :
    (∫ x,commonEmpiricalError μ N row active private0 private1 p bid x ∂ν)≤
      5/Real.sqrt N+4/(N:ℝ) := by
  have hi (k : Fin 5) := integrable_sourceEmpiricalError μ ν N hN row hrow
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k
  have hrate (k : Fin 5) :
      (∫ x,sourceEmpiricalError μ N row active private0 private1 p bid k x ∂ν)≤1/Real.sqrt N :=
    original_empirical_L1 (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (sourceBasis active private0 private1 p bid k)
      (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)
      (sourceBasis_bounds active private0 private1 p bid k)
  unfold commonEmpiricalError
  rw [integral_add (integrable_finsetSum _ fun k _ => hi k) (integrable_const _),
    integral_finsetSum _ (fun k _ => hi k)]
  have hs := Finset.sum_le_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 5))) => hrate k)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  rw [integral_const]
  have hν : ν.real univ = 1 := by simp
  rw [hν,one_smul]
  norm_num only [Nat.cast_ofNat] at hs
  convert! add_le_add_right hs (4/(N:ℝ)) using 1 <;> ring

omit [MeasurableSpace Ω] in
include hN hactive hprivate0 hprivate1 hp hbid in
theorem flaggedGuardError_le_common (b : ℝ) (hb : 1≤ b) (focal : Bool)
    (target : Ω→ Fin (N+1))
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) (x : Ω) :
    flaggedGuardError N row target active private0 private1 p bid b
      (∫ y,indicator active y ∂μ) (∫ y,(p y:ℝ)*indicator active y ∂μ)
      (∫ y,indicator private0 y ∂μ) (∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ) focal x≤
        commonEmpiricalError μ N row active private0 private1 p bid x := by
  let abar := ∫ y,indicator active y ∂μ
  let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
  let hbar := ∫ y,indicator private0 y ∂μ
  let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
  have hA : |(activeCount N row active x:ℝ)/N-abar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 0 x+1/(N:ℝ) := by
    rw [activeCount_normalized]
    have hh := abs_add_le
      (empiricalMean N (fun z : X×unitInterval => indicator active z.1) (row x)-abar) (1/(N:ℝ))
    have hm := integral_indicator_fst μ active hactive
    simp only [abs_of_nonneg (by positivity : 0≤1/(N:ℝ))] at hh
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 0 x=
        |empiricalMean N (fun z : X×unitInterval => indicator active z.1) (row x)-abar| := by
      simp only [sourceEmpiricalError,sourceBasis,Matrix.cons_val_zero,hm]
      rfl
    rw [hs]
    convert! hh using 1; first | rfl | (unfold insertedMean;ring)
  have hfocal : (if focal then (1:ℝ) else 0)∈Icc (0:ℝ) 1 := by cases focal <;> norm_num
  have hM : |(flaggedMixedCount N row target active p focal x:ℝ)/N-mbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 1 x+1/(N:ℝ) := by
    rw [flaggedMixedCount_normalized]
    have he := forcedMean_error_pointwise N hN row
      (Empirical.markedStatistic p (indicator active))
      (Empirical.markedStatistic_bounds p (indicator active) (indicator_bounds active))
      (if focal then 1 else 0) hfocal target x
    have ht := abs_sub_le
      (forcedMean N (Empirical.markedStatistic p (indicator active)) (if focal then 1 else 0) row target x)
      (empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)) mbar
    have hm := Empirical.integral_markedStatistic μ p hp (indicator active)
      (measurable_indicator active hactive) (indicator_bounds active)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 1 x=
        |empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)-mbar| := by
      change |empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)-
        ∫ z,Empirical.markedStatistic p (indicator active) z ∂μ.prod volume|=_
      rw [hm]
    rw [hs]
    linarith
  have hW : |flaggedReciprocal N row target active p bid b focal x-wbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 4 x+1/(N:ℝ) := by
    have he := forcedMean_error_pointwise N hN row
      (Empirical.markedStatistic p (reciprocalWeight active bid))
      (Empirical.markedStatistic_bounds p (reciprocalWeight active bid) (reciprocalWeight_bounds active bid))
      (if focal then 1/b else 0) (focalReciprocal_bounds hb focal) target x
    have ht := abs_sub_le (flaggedReciprocal N row target active p bid b focal x)
      (empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)) wbar
    have hm := Empirical.integral_markedStatistic μ p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid) (reciprocalWeight_bounds active bid)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 4 x=
        |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-wbar| := by
      change |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-
        ∫ z,Empirical.markedStatistic p (reciprocalWeight active bid) z ∂μ.prod volume|=_
      rw [hm]
    rw [hs]
    change |flaggedReciprocal N row target active p bid b focal x-
      empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)|≤1/(N:ℝ) at he
    exact ht.trans (by linarith only [he])
  have h0 : |(privateCount N row private0 x:ℝ)/N-hbar|=
      sourceEmpiricalError μ N row active private0 private1 p bid 2 x := by
    rw [privateCount_normalized]
    change |empiricalMean N (fun z : X×unitInterval => indicator private0 z.1) (row x)-hbar|=
      |empiricalMean N (fun z : X×unitInterval => indicator private0 z.1) (row x)-
        ∫ z,indicator private0 z.1 ∂μ.prod volume|
    rw [integral_indicator_fst μ private0 hprivate0]
  have h1 : |(privateCount N row private1 x:ℝ)/N-hbar|=
      sourceEmpiricalError μ N row active private0 private1 p bid 3 x := by
    rw [privateCount_normalized]
    change |empiricalMean N (fun z : X×unitInterval => indicator private1 z.1) (row x)-hbar|=
      |empiricalMean N (fun z : X×unitInterval => indicator private1 z.1) (row x)-
        ∫ z,indicator private1 z.1 ∂μ.prod volume|
    rw [integral_indicator_fst μ private1 hprivate1,←hfair]
  dsimp only [flaggedGuardError,guardError,commonEmpiricalError]
  rw [h0,h1]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  change |(activeCount N row active x:ℝ)/N-abar|+
      |(flaggedMixedCount N row target active p focal x:ℝ)/N-mbar|+
      sourceEmpiricalError μ N row active private0 private1 p bid 2 x+
      sourceEmpiricalError μ N row active private0 private1 p bid 3 x+
      |flaggedReciprocal N row target active p bid b focal x-wbar|+1/(N:ℝ)≤
    sourceEmpiricalError μ N row active private0 private1 p bid 0 x+
      (sourceEmpiricalError μ N row active private0 private1 p bid 1 x+
        (sourceEmpiricalError μ N row active private0 private1 p bid 2 x+
          (sourceEmpiricalError μ N row active private0 private1 p bid 3 x+
            (sourceEmpiricalError μ N row active private0 private1 p bid 4 x+0))))+4/(N:ℝ)
  rw [show (4:ℝ)/(N:ℝ)=4*(1/(N:ℝ)) by ring]
  linarith only [hA,hM,hW]

end Original

theorem meanCount_error_guard (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ b W abar mbar hbar wbar : ℝ)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hshare : share∈Icc (0:ℝ) 1)
    (hρ : ρ∈Icc (0:ℝ) 1) (hb : 1≤ b) (hwbar : 0< wbar)
    (hnbar : |populationNumerator ξ ρ abar mbar hbar share|≤ wbar) (f : Fin 3→ℝ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    let Z := guardError N A M H0 H1 W abar mbar hbar wbar
    |(meanCountLaw ξ (iidCapacity ρ N) Q (A-M-Q) (share*H0) (share*H1) M ((N:ℝ)*W) b).expect f-
      (clippedCount ξ b (populationNumerator ξ ρ abar mbar hbar share)
        (populationNumerator ξ ρ abar mbar hbar share) wbar).expect f|≤
      oscillation f*(12/(ξ*b*wbar)+4/wbar)*Z := by
  dsimp only
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  let Z := guardError N A M H0 H1 W abar mbar hbar wbar
  let nbar := populationNumerator ξ ρ abar mbar hbar share
  have hg := guardError_bounds N A M H0 H1 W abar mbar hbar wbar
  have hc := iidCapacity_error hρ N hN
  have he := balanced_numerator_error A M H0 H1 (iidCapacity ρ N) hMA hξ.le hξ1 hshare.1 hn
    ρ abar mbar hbar
  have hcent : (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar=nbar := by
    dsimp [nbar,populationNumerator]
    ring
  rw [hcent] at he
  have he2 : (1-ξ/2)*|(M:ℝ)/N-mbar|+ξ*|(iidCapacity ρ N:ℝ)/N-ρ|+
      (ξ/2)*|(A:ℝ)/N-abar|+ξ*share*(|(H0:ℝ)/N-hbar|+|(H1:ℝ)/N-hbar|)+ξ/(2*N)≤2*Z := by
    have hmul : ξ*share≤1 := by nlinarith [hshare.1,hshare.2]
    have hnonneg := abs_nonneg ((M:ℝ)/N-mbar)
    have hs := abs_nonneg ((A:ℝ)/N-abar)
    have hh := add_nonneg (abs_nonneg ((H0:ℝ)/N-hbar)) (abs_nonneg ((H1:ℝ)/N-hbar))
    have hn' : 0≤1/(N:ℝ) := by positivity
    have hcap := mul_le_mul_of_nonneg_left hc hξ.le
    dsimp [Z,guardError]
    have hlast : ξ/(2*N)=(ξ/2)*(1/(N:ℝ)) := by ring
    rw [hlast]
    nlinarith [abs_nonneg (W-wbar)]
  have h0 := he.1.trans he2
  have h1 := he.2.trans he2
  rw [meanCountLaw_normalized ξ b N hn.ne',mul_div_cancel_left₀ _ hn.ne']
  have hh := clippedCount_error
    (n0:=((M:ℝ)-ξ*((iidCapacity ρ N:ℝ)-share*H0-clampedOwner (A-M) (share*H0) (share*H1)))/N)
    (n1:=((M:ℝ)-ξ*((iidCapacity ρ N:ℝ)-share*H1-(A-M-clampedOwner (A-M) (share*H0) (share*H1):ℕ)))/N)
    (w:=W) f hξ ((by norm_num : (0:ℝ)<1).trans_le hb) hwbar hnbar
  have hW := hg.2.2.2.2.2.1
  have hk0 : 0≤2/(ξ*b*wbar) := by positivity
  have hk1 : 0≤4/wbar := by positivity
  have hmono := mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul_of_nonneg_left (show
        |((M:ℝ)-ξ*((iidCapacity ρ N:ℝ)-share*H0-clampedOwner (A-M) (share*H0) (share*H1)))/N-nbar|+
        |((M:ℝ)-ξ*((iidCapacity ρ N:ℝ)-share*H1-(A-M-clampedOwner (A-M) (share*H0) (share*H1):ℕ)))/N-nbar|+
        2*|W-wbar|≤6*Z by linarith) hk0)
      (mul_le_mul_of_nonneg_left hW hk1)) (oscillation_nonneg f)
  exact hh.trans (by convert! hmono using 1; ring)

end FCAppendix.Affine.Tail04.MenuError
