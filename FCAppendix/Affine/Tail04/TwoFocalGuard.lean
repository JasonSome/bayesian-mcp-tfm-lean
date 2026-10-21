import FCAppendix.Affine.Tail04.IidTypicalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open EqualPrivateSignal NativeTypicalCount TypicalGuardEndpoints
open scoped BigOperators

section Probability
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X)
variable (hrow : MeasurePreserving row ν (Measure.pi (fun _ : Fin N => μ)))

include hN hrow in
omit [IsProbabilityMeasure ν] in
theorem original_empirical_tail (f : X→ℝ) (hf : Measurable f)
    (hfb : ∀ x,f x∈Icc (0:ℝ) 1) {ε : ℝ} (hε : 0≤ ε) :
    ν.real {x | ε≤|empiricalMean N f (row x)-∫ y,f y ∂μ|}≤
      2*Real.exp (-2*(N:ℝ)*ε^2) := by
  have hbad : MeasurableSet {r : Fin N→ X | ε≤|empiricalMean N f r-∫ y,f y ∂μ|} :=
    measurableSet_le measurable_const (((measurable_empiricalMean N f hf).sub_const _).abs)
  have he : ν.real {x | ε≤|empiricalMean N f (row x)-∫ y,f y ∂μ|}=
      (Measure.pi (fun _ : Fin N => μ)).real
        {r | ε≤|empiricalMean N f r-∫ y,f y ∂μ|} := by
    change (ν (row ⁻¹' {r | ε≤|empiricalMean N f r-∫ y,f y ∂μ|})).toReal=_
    rw [←Measure.map_apply hrow.measurable hbad,hrow.map_eq]
    rfl
  rw [he]
  exact Probability.iid_empiricalMean_two_sided_le μ hf.aemeasurable
    (Eventually.of_forall hfb) N hN hε

end Probability

theorem measureReal_exists_fin_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (K : ℕ) (E : Fin K→ Set Ω) :
    ν.real {x | ∃ k,x∈E k}≤∑ k,ν.real (E k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have he : {x | ∃ k : Fin (K+1),x∈E k}=
        E 0∪{x | ∃ k : Fin K,x∈E k.succ} := by
      ext x
      constructor
      · rintro ⟨k,hk⟩
        have hh : ∀ j : Fin (K+1),x∈E j→ x∈E 0∪{x | ∃ i : Fin K,x∈E i.succ} :=
          Fin.cases (fun h => Or.inl h) (fun i h => Or.inr ⟨i,h⟩)
        exact hh k hk
      · rintro (h | ⟨k,h⟩)
        · exact ⟨0,h⟩
        · exact ⟨k.succ,h⟩
    rw [he,Fin.sum_univ_succ]
    exact (measureReal_union_le _ _).trans (add_le_add le_rfl (ih (fun k => E k.succ)))

section TwoPrefix
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X) (weight : X→ℝ)

def twoPrefixWeight (f0 f1 : ℝ) (x : Ω) : Fin (N+2)→ℝ :=
  Fin.cases f0 (Fin.cases f1 (fun i : Fin N => weight (row x i)))

def twoForcedMean (f0 f1 : ℝ) (target : Ω→ Fin (N+2)) (x : Ω) : ℝ :=
  (∑ i : Fin (N+2),if i=target x then 0 else twoPrefixWeight N row weight f0 f1 x i)/(N:ℝ)

theorem twoPrefixWeight_bounds (hw : ∀ x,weight x∈Icc (0:ℝ) 1)
    (f0 f1 : ℝ) (h0 : f0∈Icc (0:ℝ) 1) (h1 : f1∈Icc (0:ℝ) 1)
    (x : Ω) (i : Fin (N+2)) : twoPrefixWeight N row weight f0 f1 x i∈Icc (0:ℝ) 1 := by
  refine Fin.cases h0 (fun j => ?_) i
  exact Fin.cases h1 (fun k => hw (row x k)) j

theorem twoForcedMean_identity (f0 f1 : ℝ) (target : Ω→ Fin (N+2)) (x : Ω) :
    twoForcedMean N row weight f0 f1 target x=empiricalMean N weight (row x)+
      (f0+f1-twoPrefixWeight N row weight f0 f1 x (target x))/(N:ℝ) := by
  have hi (i : Fin (N+2)) :
      (if i=target x then (0:ℝ) else twoPrefixWeight N row weight f0 f1 x i)=
      twoPrefixWeight N row weight f0 f1 x i-
        (if i=target x then twoPrefixWeight N row weight f0 f1 x i else 0) := by
    split_ifs <;> ring
  unfold twoForcedMean
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Fin.sum_univ_succ,
    twoPrefixWeight,Fin.cases_zero,Fin.cases_succ]
  unfold empiricalMean
  simp only [div_eq_mul_inv]
  ring

theorem twoForcedMean_error (hN : 0< N) (hw : ∀ x,weight x∈Icc (0:ℝ) 1)
    (f0 f1 : ℝ) (h0 : f0∈Icc (0:ℝ) 1) (h1 : f1∈Icc (0:ℝ) 1)
    (target : Ω→ Fin (N+2)) (x : Ω) :
    |twoForcedMean N row weight f0 f1 target x-empiricalMean N weight (row x)|≤2/(N:ℝ) := by
  rw [twoForcedMean_identity,add_sub_cancel_left,abs_div,
    abs_of_pos (show (0:ℝ)<(N:ℝ) from Nat.cast_pos.mpr hN)]
  have ht := twoPrefixWeight_bounds N row weight hw f0 f1 h0 h1 x (target x)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact abs_le.mpr ⟨by linarith [h0.1,h1.1,ht.2],by linarith [h0.2,h1.2,ht.1]⟩

end TwoPrefix

section LiteralCounts
variable {X Ω : Type*} (N : ℕ) (row : Ω→ Fin N→ X×unitInterval)
variable (active : X→ Bool) (p : X→ unitInterval)

def twoActiveCount (x : Ω) : ℕ :=
  boolCount (Fin.cases true (Fin.cases true (fun i : Fin N => active (row x i).1)))

def twoMixedBit (f0 f1 : Bool) (target : Ω→ Fin (N+2)) (x : Ω) (i : Fin (N+2)) : Bool :=
  if i=target x then false else
    Fin.cases f0 (Fin.cases f1 (fun j : Fin N => activeFlag active p (row x j))) i

def twoMixedCount (f0 f1 : Bool) (target : Ω→ Fin (N+2)) (x : Ω) : ℕ :=
  boolCount (twoMixedBit N row active p f0 f1 target x)

theorem twoMixedCount_le_active (f0 f1 : Bool) (target : Ω→ Fin (N+2)) (x : Ω) :
    twoMixedCount N row active p f0 f1 target x≤ twoActiveCount N row active x := by
  unfold twoMixedCount twoActiveCount boolCount
  apply Finset.sum_le_sum
  intro i _
  have hle (j : Fin (N+2)) :
      (if (Fin.cases f0 (Fin.cases f1 (fun k : Fin N => activeFlag active p (row x k))) j : Bool)
        then (1:ℕ) else 0) ≤
      if (Fin.cases true (Fin.cases true (fun k : Fin N => active (row x k).1)) j : Bool)
        then 1 else 0 := by
    refine Fin.cases ?_ (fun j => ?_) j
    · change (if f0 then (1:ℕ) else 0) ≤ 1
      cases f0 <;> norm_num
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (if f1 then (1:ℕ) else 0) ≤ 1
        cases f1 <;> norm_num
      · cases ha : active (row x k).1 <;>
          cases hf : Empirical.flag (p (row x k).1) (row x k).2 <;>
          simp [activeFlag,ha,hf]
  unfold twoMixedBit
  by_cases hi : i = target x
  · simp only [if_pos hi, Bool.false_eq_true, ↓reduceIte]
    exact Nat.zero_le _
  · simpa only [if_neg hi] using hle i

theorem twoActiveCount_normalized (x : Ω) :
    (twoActiveCount N row active x:ℝ)/N=
      empiricalMean N (fun z : X×unitInterval => indicator active z.1) (row x)+2/(N:ℝ) := by
  rw [twoActiveCount,boolCount_real]
  simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,ite_true]
  unfold empiricalMean indicator
  simp only [div_eq_mul_inv]
  ring

theorem twoMixedCount_normalized (f0 f1 : Bool) (target : Ω→ Fin (N+2)) (x : Ω) :
    (twoMixedCount N row active p f0 f1 target x:ℝ)/N=
      twoForcedMean N row (Empirical.markedStatistic p (indicator active))
        (if f0 then 1 else 0) (if f1 then 1 else 0) target x := by
  rw [twoMixedCount,boolCount_real]
  unfold twoForcedMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=target x
  · simp [twoMixedBit,hi]
  · simp only [twoMixedBit,if_neg hi]
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if f0 then (1:ℝ) else 0)=(if f0 then 1 else 0)
      rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · change (if f1 then (1:ℝ) else 0)=(if f1 then 1 else 0)
        rfl
      · exact activeFlag_weight active p (row x k)

def twoReciprocal (bid : X→ℝ) (b0 b1 : ℝ) (f0 f1 : Bool)
    (target : Ω→ Fin (N+2)) : Ω→ℝ :=
  twoForcedMean N row (Empirical.markedStatistic p (reciprocalWeight active bid))
    (if f0 then 1/b0 else 0) (if f1 then 1/b1 else 0) target

theorem focalReciprocal_bounds {b : ℝ} (hb : 1≤ b) (f : Bool) :
    (if f then 1/b else 0)∈Icc (0:ℝ) 1 := by
  cases f
  · norm_num
  · simp only [ite_true]
    have hb0 : 0< b := (by norm_num : (0:ℝ)<1).trans_le hb
    exact ⟨div_nonneg (by norm_num) hb0.le,(div_le_one hb0).mpr hb⟩

def twoGuardError (private0 private1 : X→ Bool) (bid : X→ℝ)
    (b0 b1 : ℝ) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (abar mbar hbar wbar : ℝ) (x : Ω) : ℝ :=
  guardError N (twoActiveCount N row active x) (twoMixedCount N row active p f0 f1 target x)
    (privateCount N row private0 x) (privateCount N row private1 x)
    (twoReciprocal N row active p bid b0 b1 f0 f1 target x) abar mbar hbar wbar+1/(N:ℝ)

def twoCapacity (ρ : ℝ) (N : ℕ) : ℕ := ⌊ρ*((N:ℝ)+2)⌋₊

theorem twoCapacity_error {ρ : ℝ} (hρ : ρ∈Icc (0:ℝ) 1) (N : ℕ) (hN : 0< N) :
    |(twoCapacity ρ N:ℝ)/(N:ℝ)-ρ|≤2/(N:ℝ) := by
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hlo : (twoCapacity ρ N:ℝ)≤ ρ*((N:ℝ)+2) :=
    Nat.floor_le (mul_nonneg hρ.1 (by positivity))
  have hhi : ρ*((N:ℝ)+2)<(twoCapacity ρ N:ℝ)+1 := Nat.lt_floor_add_one _
  have he : (twoCapacity ρ N:ℝ)/(N:ℝ)-ρ=((twoCapacity ρ N:ℝ)-ρ*N)/(N:ℝ) := by
    field_simp [hn.ne']
  rw [he,abs_div,abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  exact abs_le.mpr ⟨by nlinarith [hρ.1],by nlinarith [hρ.2]⟩

end LiteralCounts

section OriginalFive
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X×unitInterval)
variable (hrow : MeasurePreserving row ν
  (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))))
variable (active private0 private1 : X→ Bool)
variable (hactive : Measurable active) (hprivate0 : Measurable private0) (hprivate1 : Measurable private1)
variable (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)

def sourceBasis : Fin 5→(X×unitInterval)→ℝ :=
  ![fun z => indicator active z.1,Empirical.markedStatistic p (indicator active),
    fun z => indicator private0 z.1,fun z => indicator private1 z.1,
    Empirical.markedStatistic p (reciprocalWeight active bid)]

include hactive hprivate0 hprivate1 hp hbid in
theorem measurable_sourceBasis (k : Fin 5) :
    Measurable (sourceBasis active private0 private1 p bid k) := by
  fin_cases k
  · exact (measurable_indicator active hactive).comp measurable_fst
  · exact Empirical.measurable_markedStatistic p hp (indicator active) (measurable_indicator active hactive)
  · exact (measurable_indicator private0 hprivate0).comp measurable_fst
  · exact (measurable_indicator private1 hprivate1).comp measurable_fst
  · exact Empirical.measurable_markedStatistic p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid)

omit [MeasurableSpace X] in
theorem sourceBasis_bounds (k : Fin 5) (z : X×unitInterval) :
    sourceBasis active private0 private1 p bid k z∈Icc (0:ℝ) 1 := by
  fin_cases k
  · exact indicator_bounds active z.1
  · exact Empirical.markedStatistic_bounds p (indicator active) (indicator_bounds active) z
  · exact indicator_bounds private0 z.1
  · exact indicator_bounds private1 z.1
  · exact Empirical.markedStatistic_bounds p (reciprocalWeight active bid)
      (reciprocalWeight_bounds active bid) z

def sourceEmpiricalError (k : Fin 5) (x : Ω) : ℝ :=
  |empiricalMean N (sourceBasis active private0 private1 p bid k) (row x)-
    ∫ z,sourceBasis active private0 private1 p bid k z ∂μ.prod (volume : Measure unitInterval)|

def sourceFiveBad (δ : ℝ) : Set Ω :=
  {x | ∃ k : Fin 5,δ/10≤ sourceEmpiricalError μ N row active private0 private1 p bid k x}

include hrow hactive hprivate0 hprivate1 hp hbid in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurableSet_sourceFiveBad (δ : ℝ) :
    MeasurableSet (sourceFiveBad μ N row active private0 private1 p bid δ) := by
  have hk (k : Fin 5) : MeasurableSet {x : Ω | δ/10≤
      sourceEmpiricalError μ N row active private0 private1 p bid k x} :=
    measurableSet_le measurable_const
      ((((measurable_empiricalMean N (sourceBasis active private0 private1 p bid k)
        (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)).comp
          hrow.measurable).sub_const _).abs)
  have he : sourceFiveBad μ N row active private0 private1 p bid δ=
      ⋃ k : Fin 5,{x | δ/10≤ sourceEmpiricalError μ N row active private0 private1 p bid k x} := by
    ext x
    simp [sourceFiveBad]
  rw [he]
  exact MeasurableSet.iUnion hk

include hN hrow hactive hprivate0 hprivate1 hp hbid in
theorem sourceFiveBad_probability {δ : ℝ} (hδ : 0≤ δ) :
    ν.real (sourceFiveBad μ N row active private0 private1 p bid δ)≤
      10*Real.exp (-(N:ℝ)*δ^2/50) := by
  have hk (k : Fin 5) : ν.real {x | δ/10≤
      sourceEmpiricalError μ N row active private0 private1 p bid k x}≤
      2*Real.exp (-2*(N:ℝ)*(δ/10)^2) :=
    original_empirical_tail (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (sourceBasis active private0 private1 p bid k)
      (measurable_sourceBasis active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid k)
      (sourceBasis_bounds active private0 private1 p bid k) (by positivity)
  have hsum := (measureReal_exists_fin_le ν 5
    (fun k => {x | δ/10≤ sourceEmpiricalError μ N row active private0 private1 p bid k x})).trans
      (Finset.sum_le_sum (fun k _ => hk k))
  have he : -2*(N:ℝ)*(δ/10)^2= -(N:ℝ)*δ^2/50 := by ring
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,he] at hsum
  change ν.real (sourceFiveBad μ N row active private0 private1 p bid δ)≤_ at hsum
  convert! hsum using 1; ring

include hN hactive hprivate0 hprivate1 hp hbid in
omit [MeasurableSpace Ω] in
theorem twoGuardError_le_unforced (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1)
    (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) (x : Ω) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    twoGuardError N row active p private0 private1 bid b0 b1 f0 f1 target abar mbar hbar wbar x≤
      (∑ k : Fin 5,sourceEmpiricalError μ N row active private0 private1 p bid k x)+8/(N:ℝ) := by
  dsimp only
  let abar := ∫ y,indicator active y ∂μ
  let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
  let hbar := ∫ y,indicator private0 y ∂μ
  let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
  have hA : |(twoActiveCount N row active x:ℝ)/N-abar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 0 x+2/(N:ℝ) := by
    rw [twoActiveCount_normalized]
    have hh := abs_add_le
      (empiricalMean N (fun z : X×unitInterval => indicator active z.1) (row x)-abar) (2/(N:ℝ))
    have hm := integral_indicator_fst μ active hactive
    simp only [abs_of_nonneg (by positivity : 0≤2/(N:ℝ))] at hh
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 0 x=
        |empiricalMean N (fun z : X×unitInterval => indicator active z.1) (row x)-abar| := by
      simp [sourceEmpiricalError,sourceBasis,hm,abar]
    rw [hs]
    convert! hh using 1; ring
  have hf0 : (if f0 then (1:ℝ) else 0)∈Icc (0:ℝ) 1 := by cases f0 <;> norm_num
  have hf1 : (if f1 then (1:ℝ) else 0)∈Icc (0:ℝ) 1 := by cases f1 <;> norm_num
  have hM : |(twoMixedCount N row active p f0 f1 target x:ℝ)/N-mbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 1 x+2/(N:ℝ) := by
    rw [twoMixedCount_normalized]
    have he := twoForcedMean_error N row (Empirical.markedStatistic p (indicator active)) hN
      (Empirical.markedStatistic_bounds p (indicator active) (indicator_bounds active))
      (if f0 then 1 else 0) (if f1 then 1 else 0) hf0 hf1 target x
    have ht := abs_sub_le
      (twoForcedMean N row (Empirical.markedStatistic p (indicator active))
        (if f0 then 1 else 0) (if f1 then 1 else 0) target x)
      (empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)) mbar
    have hm := Empirical.integral_markedStatistic μ p hp (indicator active)
      (measurable_indicator active hactive) (indicator_bounds active)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 1 x=
        |empiricalMean N (Empirical.markedStatistic p (indicator active)) (row x)-mbar| := by
      simp [sourceEmpiricalError,sourceBasis,hm,mbar]
    rw [hs]
    linarith
  have hW : |twoReciprocal N row active p bid b0 b1 f0 f1 target x-wbar|≤
      sourceEmpiricalError μ N row active private0 private1 p bid 4 x+2/(N:ℝ) := by
    have he := twoForcedMean_error N row (Empirical.markedStatistic p (reciprocalWeight active bid)) hN
      (Empirical.markedStatistic_bounds p (reciprocalWeight active bid) (reciprocalWeight_bounds active bid))
      (if f0 then 1/b0 else 0) (if f1 then 1/b1 else 0)
      (focalReciprocal_bounds hb0 f0) (focalReciprocal_bounds hb1 f1) target x
    have ht := abs_sub_le (twoReciprocal N row active p bid b0 b1 f0 f1 target x)
      (empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)) wbar
    have hm := Empirical.integral_markedStatistic μ p hp (reciprocalWeight active bid)
      (measurable_reciprocalWeight active hactive bid hbid) (reciprocalWeight_bounds active bid)
    have hs : sourceEmpiricalError μ N row active private0 private1 p bid 4 x=
        |empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)-wbar| := by
      simp [sourceEmpiricalError,sourceBasis,Matrix.cons_val_four,hm,wbar]
    rw [hs]
    change |twoReciprocal N row active p bid b0 b1 f0 f1 target x -
      empiricalMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (row x)| ≤ 2/(N:ℝ) at he
    exact ht.trans (by linarith)
  have h0 : |(privateCount N row private0 x:ℝ)/N-hbar|=
      sourceEmpiricalError μ N row active private0 private1 p bid 2 x := by
    rw [privateCount_normalized]
    simp [sourceEmpiricalError,sourceBasis,Matrix.cons_val_two,
      integral_indicator_fst μ private0 hprivate0,hbar]
  have h1 : |(privateCount N row private1 x:ℝ)/N-hbar|=
      sourceEmpiricalError μ N row active private0 private1 p bid 3 x := by
    rw [privateCount_normalized]
    simp [sourceEmpiricalError,sourceBasis,Matrix.cons_val_three,
      integral_indicator_fst μ private1 hprivate1,←hfair,hbar]
  dsimp only [twoGuardError,guardError]
  rw [h0,h1]
  norm_num only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.succ] at ⊢
  change _ ≤ (sourceEmpiricalError μ N row active private0 private1 p bid 0 x + (sourceEmpiricalError μ N row active private0 private1 p bid 1 x +
    (sourceEmpiricalError μ N row active private0 private1 p bid 2 x + (sourceEmpiricalError μ N row active private0 private1 p bid 3 x + (sourceEmpiricalError μ N row active private0 private1 p bid 4 x + 0))))) + 8/(N:ℝ)
  dsimp only [abar,mbar,hbar,wbar] at hA hM hW h0 h1 ⊢
  simp only [div_eq_mul_inv,one_mul] at hA hM hW ⊢
  linarith

include hN hactive hprivate0 hprivate1 hp hbid in
omit [MeasurableSpace Ω] in
theorem twoGuardError_lt_of_not_bad {δ : ℝ} (hroom : 16/(N:ℝ)≤ δ)
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ))
    (x : Ω) (hx : x∉sourceFiveBad μ N row active private0 private1 p bid δ) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    twoGuardError N row active p private0 private1 bid b0 b1 f0 f1 target abar mbar hbar wbar x< δ := by
  dsimp only
  have hh := twoGuardError_le_unforced μ N hN row active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid b0 b1 hb0 hb1 f0 f1 target hfair x
  have hk (k : Fin 5) : sourceEmpiricalError μ N row active private0 private1 p bid k x< δ/10 := by
    exact lt_of_not_ge fun h => hx ⟨k,h⟩
  have hsum : (∑ k : Fin 5,sourceEmpiricalError μ N row active private0 private1 p bid k x)< δ/2 := by
    have hs := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset (Fin 5)).Nonempty)
      (fun k _ => hk k)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    convert! hs using 1; ring
  dsimp only at hh
  simp only [div_eq_mul_inv] at hh hroom ⊢
  linarith

include hN hrow hactive hprivate0 hprivate1 hp hbid in
theorem two_fixed_guard_error_probability {δ : ℝ} (hδ : 0≤ δ) (hroom : 16/(N:ℝ)≤ δ)
    (b0 b1 : ℝ) (hb0 : 1≤ b0) (hb1 : 1≤ b1) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    ν.real {x | δ≤ twoGuardError N row active p private0 private1 bid
      b0 b1 f0 f1 target abar mbar hbar wbar x}≤10*Real.exp (-(N:ℝ)*δ^2/50) := by
  dsimp only
  have hsub : {x | δ≤ twoGuardError N row active p private0 private1 bid b0 b1 f0 f1 target
      (∫ y,indicator active y ∂μ) (∫ y,(p y:ℝ)*indicator active y ∂μ)
      (∫ y,indicator private0 y ∂μ) (∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ) x}⊆
      sourceFiveBad μ N row active private0 private1 p bid δ := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx) (twoGuardError_lt_of_not_bad μ N hN row active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid hroom b0 b1 hb0 hb1 f0 f1 target hfair x hn)
  exact (measureReal_mono hsub).trans (sourceFiveBad_probability μ ν N hN row hrow
    active private0 private1 hactive hprivate0 hprivate1 p hp bid hbid hδ)

include hN hactive hprivate0 hprivate1 hp hbid in
omit [MeasurableSpace Ω] in
theorem two_fixed_weight_eq_one_on_common_good
    (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ)
    (hroom : 16/(N:ℝ)≤ δ)
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
      ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target : Ω→ Fin (N+2),
      ∀ ν0 : FiniteLaw (Marks (privateCount N row private0 x)),
      ∀ ν1 : FiniteLaw (Marks (privateCount N row private1 x)),
      privateMean (privateCount N row private0 x) reg ν0=share*privateCount N row private0 x →
      privateMean (privateCount N row private1 x) reg ν1=share*privateCount N row private1 x →
      let A := twoActiveCount N row active x
      let M := twoMixedCount N row active p f0 f1 target x
      let H0 := privateCount N row private0 x
      let H1 := privateCount N row private1 x
      let Q := clampedOwner (A-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity ρ N) Q (A-M-Q) M
        ξ B R Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N row active p bid b0 b1 f0 f1 target x)=1 := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean x hx b0 b1 hb0 hb1 f0 f1 target ν0 ν1 hmean0 hmean1
  let A := twoActiveCount N row active x
  let M := twoMixedCount N row active p f0 f1 target x
  let H0 := privateCount N row private0 x
  let H1 := privateCount N row private1 x
  let W := twoReciprocal N row active p bid b0 b1 f0 f1 target x
  let abar := ∫ y,indicator active y ∂μ
  let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
  let hbar := ∫ y,indicator private0 y ∂μ
  let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
  have hgood := twoGuardError_lt_of_not_bad μ N hN row active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid hroom b0 b1 hb0 hb1 f0 f1 target hfair x hx
  have hhbar : 0≤ hbar := integral_nonneg fun y => (indicator_bounds private0 y).1
  apply source_weight_eq_one_of_guardError_capacity N A M H0 H1 (twoCapacity ρ N) hN
    (twoMixedCount_le_active N row active p f0 f1 target x)
    ξ share ρ B R Rp width γ δ (1/(N:ℝ)) W abar mbar hbar wbar reg ν0 ν1
    hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ hδm hδw hδc hδγ
    hmean0 hmean1 hlo hhi hmean (by positivity)
  · have hc := twoCapacity_error hρ N hN
    have hz := (guardError_bounds N A M H0 H1 W abar mbar hbar wbar).2.2.2.2.2.2
    simp only [div_eq_mul_inv,one_mul] at hc hz ⊢
    linarith
  · exact hgood

include hN hrow hactive hprivate0 hprivate1 hp hbid in
theorem two_fixed_common_policy_guard
    (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ)
    (hroom : 16/(N:ℝ)≤ δ)
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
    ∃ bad : Set Ω,MeasurableSet bad ∧ ν.real bad≤10*Real.exp (-(N:ℝ)*δ^2/50) ∧
      ∀ x,x∉bad → ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target : Ω→ Fin (N+2),
      ∀ ν0 : FiniteLaw (Marks (privateCount N row private0 x)),
      ∀ ν1 : FiniteLaw (Marks (privateCount N row private1 x)),
      privateMean (privateCount N row private0 x) reg ν0=share*privateCount N row private0 x →
      privateMean (privateCount N row private1 x) reg ν1=share*privateCount N row private1 x →
      let A := twoActiveCount N row active x
      let M := twoMixedCount N row active p f0 f1 target x
      let H0 := privateCount N row private0 x
      let H1 := privateCount N row private1 x
      let Q := clampedOwner (A-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity ρ N) Q (A-M-Q) M
        ξ B R Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N row active p bid b0 b1 f0 f1 target x)=1 := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean
  refine ⟨sourceFiveBad μ N row active private0 private1 p bid δ,
    measurableSet_sourceFiveBad μ ν N row hrow active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid δ,
    sourceFiveBad_probability μ ν N hN row hrow active private0 private1
      hactive hprivate0 hprivate1 p hp bid hbid hδ.le,?_⟩
  exact two_fixed_weight_eq_one_on_common_good μ N hN row active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid ξ share ρ B R Rp width γ δ reg
    hξ hshare hshareLo hρ hB hw hwγ hγ1 hδ hroom hfair
    hδm hδw hδc hδγ hlo hhi hmean

end OriginalFive
end FCAppendix.Affine.Tail04.MenuError
