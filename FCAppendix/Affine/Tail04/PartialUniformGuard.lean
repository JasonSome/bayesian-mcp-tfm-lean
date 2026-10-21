import FCAppendix.Affine.Tail04.PartialFocalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

section Original
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ]
variable (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X×unitInterval)
variable (active private0 private1 : X→ Bool)
variable (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
variable (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)

omit [MeasurableSpace Ω] in
include hN hactive hprivate0 hprivate1 hp hbid in
theorem partialGuardError_le_unforced (target : Ω→ Fin (N+1)) (side : Fin 2)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) (x : Ω) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    partialGuardError N row target active private0 private1 p bid abar mbar hbar wbar side x≤
      (∑ k : Fin 5,sourceEmpiricalError μ N row active private0 private1 p bid k x)+4/(N:ℝ) := by
  dsimp only
  let abar := ∫ y,indicator active y ∂μ
  let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
  let hbar := ∫ y,indicator private0 y ∂μ
  let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
  have hA : |(privateCount N row active x:ℝ)/N-abar|=
      sourceEmpiricalError μ N row active private0 private1 p bid 0 x := by
    rw [privateCount_normalized]
    simp only [sourceEmpiricalError,sourceBasis,Matrix.cons_val_zero,
      integral_indicator_fst μ active hactive]
    rfl
  have hM : |(flaggedMixedCount N row target active p false x:ℝ)/N-mbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 1 x+1/(N:ℝ) := by
    rw [flaggedMixedCount_normalized]
    have he := forcedMean_error_pointwise N hN row
      (Empirical.markedStatistic p (indicator active))
      (Empirical.markedStatistic_bounds p (indicator active) (indicator_bounds active))
      0 (by norm_num) target x
    have ht := abs_sub_le
      (forcedMean N (Empirical.markedStatistic p (indicator active)) 0 row target x)
      (empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)) mbar
    have hm := Empirical.integral_markedStatistic μ p hp (indicator active)
      (measurable_indicator active hactive) (indicator_bounds active)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 1 x=
        |empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)-mbar| := by
      change |empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)-
        ∫ z,Empirical.markedStatistic p (indicator active) z ∂μ.prod (volume : Measure unitInterval)|=_
      rw [hm]
    simp only [Bool.false_eq_true,ite_false]
    rw [hs]
    linarith
  have hW : |flaggedReciprocal N row target active p bid 1 false x-wbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 4 x+1/(N:ℝ) := by
    have he := forcedMean_error_pointwise N hN row
      (Empirical.markedStatistic p (reciprocalWeight active bid))
      (Empirical.markedStatistic_bounds p (reciprocalWeight active bid) (reciprocalWeight_bounds active bid))
      0 (by norm_num) target x
    have ht := abs_sub_le (flaggedReciprocal N row target active p bid 1 false x)
      (empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)) wbar
    have hm := Empirical.integral_markedStatistic μ p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid) (reciprocalWeight_bounds active bid)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 4 x=
        |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-wbar| := by
      change |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-
        ∫ z,Empirical.markedStatistic p (reciprocalWeight active bid) z ∂μ.prod (volume : Measure unitInterval)|=_
      rw [hm]
    rw [hs]
    change |forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid))
      0 row target x-wbar|≤_
    change |forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid))
      0 row target x-wbar|≤
      |forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid))
        0 row target x-empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)|+
      |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-wbar| at ht
    linarith
  have hP (q : X→ Bool) (hq : Measurable q) (j : Fin 2) :
      |(partialPrivateCount N row q side j x:ℝ)/N-∫ y,indicator q y ∂μ|≤
        |empiricalMean N (fun z : X×unitInterval => indicator q z.1) (row x)-
          ∫ y,indicator q y ∂μ|+(partialOffset side j:ℝ)/N := by
    rw [partialPrivateCount_normalized]
    have hh := abs_add_le
      (empiricalMean N (fun z : X×unitInterval => indicator q z.1) (row x)-∫ y,indicator q y ∂μ)
      ((partialOffset side j:ℝ)/N)
    simp only [abs_of_nonneg (by positivity : 0≤(partialOffset side j:ℝ)/N)] at hh
    convert! hh using 1
    simp only [insertedMean]
    ring
  have h0 : |(partialPrivateCount N row private0 side 0 x:ℝ)/N-hbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 2 x+(partialOffset side 0:ℝ)/N := by
    have h := hP private0 hprivate0 0
    change |(partialPrivateCount N row private0 side 0 x:ℝ)/N-hbar|≤
      |empiricalMean N (fun z : X×unitInterval => indicator private0 z.1) (row x)-
        ∫ z,indicator private0 z.1 ∂μ.prod (volume : Measure unitInterval)|+
        (partialOffset side 0:ℝ)/N
    simpa only [integral_indicator_fst μ private0 hprivate0,hbar] using h
  have h1 : |(partialPrivateCount N row private1 side 1 x:ℝ)/N-hbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 3 x+(partialOffset side 1:ℝ)/N := by
    have h := hP private1 hprivate1 1
    change |(partialPrivateCount N row private1 side 1 x:ℝ)/N-hbar|≤
      |empiricalMean N (fun z : X×unitInterval => indicator private1 z.1) (row x)-
        ∫ z,indicator private1 z.1 ∂μ.prod (volume : Measure unitInterval)|+
        (partialOffset side 1:ℝ)/N
    simpa only [integral_indicator_fst μ private1 hprivate1,←hfair,hbar] using h
  have hoff : (partialOffset side 0:ℝ)/N+(partialOffset side 1:ℝ)/N=1/(N:ℝ) := by
    rw [←add_div,partialOffset_sum]
  dsimp only [partialGuardError,guardError]
  rw [hA]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at ⊢
  change _ ≤ sourceEmpiricalError μ N row active private0 private1 p bid 0 x+
    (sourceEmpiricalError μ N row active private0 private1 p bid 1 x+
    (sourceEmpiricalError μ N row active private0 private1 p bid 2 x+
    (sourceEmpiricalError μ N row active private0 private1 p bid 3 x+
    (sourceEmpiricalError μ N row active private0 private1 p bid 4 x+0))))+4/(N:ℝ)
  dsimp only [mbar,hbar,wbar] at hM h0 h1 hW
  simp only [div_eq_mul_inv,one_mul] at hoff hM hW h0 h1 ⊢
  linarith

omit [MeasurableSpace Ω] in
include hN hactive hprivate0 hprivate1 hp hbid in
theorem partialGuardError_lt_of_not_bad {δ : ℝ} (hroom : 8/(N:ℝ)≤ δ)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
    (x : Ω) (hx : x∉sourceFiveBad μ N row active private0 private1 p bid δ) :
    ∀ target : Ω→ Fin (N+1),∀ side : Fin 2,
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    partialGuardError N row target active private0 private1 p bid abar mbar hbar wbar side x< δ := by
  intro target side
  dsimp only
  have hh := partialGuardError_le_unforced μ N hN row active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid target side hfair x
  have hk (k : Fin 5) : sourceEmpiricalError μ N row active private0 private1 p bid k x< δ/10 :=
    lt_of_not_ge fun h => hx ⟨k,h⟩
  have hs : (∑ k : Fin 5,sourceEmpiricalError μ N row active private0 private1 p bid k x)< δ/2 := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
    change sourceEmpiricalError μ N row active private0 private1 p bid 0 x+
      (sourceEmpiricalError μ N row active private0 private1 p bid 1 x+
      (sourceEmpiricalError μ N row active private0 private1 p bid 2 x+
      (sourceEmpiricalError μ N row active private0 private1 p bid 3 x+
      (sourceEmpiricalError μ N row active private0 private1 p bid 4 x+0))))<δ/2
    linarith [hk 0,hk 1,hk 2,hk 3,hk 4]
  dsimp only at hh
  simp only [div_eq_mul_inv] at hroom hh hs ⊢
  linarith

omit [MeasurableSpace Ω] in
include hN hactive hprivate0 hprivate1 hp hbid in
theorem partial_weight_eq_one_on_common_good
    (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ)
    (hroom : 8/(N:ℝ)≤ δ)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    δ≤ mbar/2 → δ≤ wbar/2 → 4*δ≤ ρ-(abar-mbar)/2-hbar → 10*δ≤ γ*wbar →
    (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar →
    populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1 →
    (if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R) →
    ∀ x,x∉sourceFiveBad μ N row active private0 private1 p bid δ →
      ∀ target : Ω→ Fin (N+1),∀ side : Fin 2,
      partialGuardWeight N row target active private0 private1 p bid
        ξ share ρ B R Rp width hshare reg side x=1 := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean x hx target side
  exact partial_weight_eq_one_of_good μ N hN row target active private0 private1 p bid
    ξ share ρ B R Rp width γ δ reg hξ hshare hshareLo hρ hB hw hwγ hγ1 hδ
    hδm hδw hδc hδγ hlo hhi hmean side x
    (partialGuardError_lt_of_not_bad μ N hN row active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid hroom hfair x hx target side)

end Original
end FCAppendix.Affine.Tail04.MenuError
