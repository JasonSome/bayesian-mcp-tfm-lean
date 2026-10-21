import FCAppendix.Affine.Tail04.IidMenuStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

def boolCount {ι : Type*} [Fintype ι] (b : ι→ Bool) : ℕ := ∑ i,if b i then 1 else 0

theorem boolCount_le_card {ι : Type*} [Fintype ι] (b : ι→ Bool) : boolCount b≤ Fintype.card ι := by
  unfold boolCount
  calc
    _ ≤ ∑ _i : ι,(1:ℕ) := Finset.sum_le_sum (fun i _ => by cases b i <;> simp)
    _ = _ := by simp

theorem boolCount_real {ι : Type*} [Fintype ι] (b : ι→ Bool) :
    (boolCount b:ℝ)=∑ i,if b i then (1:ℝ) else 0 := by
  simp only [boolCount,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem measurable_boolCount {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (b : Ω→ ι→ Bool) (hb : ∀ i,Measurable (fun x => b x i)) : Measurable (fun x => boolCount (b x)) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_eq_fun (hb i) measurable_const) measurable_const measurable_const

def indicator {X : Type*} (a : X→ Bool) (x : X) : ℝ := if a x then 1 else 0

theorem indicator_bounds {X : Type*} (a : X→ Bool) (x : X) :
    indicator a x∈Icc (0:ℝ) 1 := by cases h : a x <;> simp [indicator,h]

theorem measurable_indicator {X : Type*} [MeasurableSpace X] (a : X→ Bool) (ha : Measurable a) :
    Measurable (indicator a) :=
  Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const measurable_const

def activeFlag {X : Type*} (active : X→ Bool) (p : X→ unitInterval) (z : X×unitInterval) : Bool :=
  if active z.1 then Empirical.flag (p z.1) z.2 else false

theorem activeFlag_weight {X : Type*} (active : X→ Bool) (p : X→ unitInterval) (z : X×unitInterval) :
    (if activeFlag active p z then (1:ℝ) else 0)=Empirical.markedStatistic p (indicator active) z := by
  cases ha : active z.1 <;> cases hf : Empirical.flag (p z.1) z.2 <;>
    simp [activeFlag,Empirical.markedStatistic,indicator,ha,hf]

theorem measurable_activeFlag {X : Type*} [MeasurableSpace X]
    (active : X→ Bool) (ha : Measurable active) (p : X→ unitInterval) (hp : Measurable p) :
    Measurable (activeFlag active p) :=
  Measurable.ite (measurableSet_eq_fun (ha.comp measurable_fst) measurable_const)
    (Empirical.measurable_flag.comp ((hp.comp measurable_fst).prodMk measurable_snd)) measurable_const

def reciprocalWeight {X : Type*} (active : X→ Bool) (bid : X→ℝ) (x : X) : ℝ :=
  if active x then 1/max 1 (bid x) else 0

theorem reciprocalWeight_bounds {X : Type*} (active : X→ Bool) (bid : X→ℝ) (x : X) :
    reciprocalWeight active bid x∈Icc (0:ℝ) 1 := by
  by_cases ha : active x=true
  · simp only [reciprocalWeight,ha,ite_true]
    have hpos : 0< max 1 (bid x) := (by norm_num : (0:ℝ)<1).trans_le (le_max_left _ _)
    exact ⟨div_nonneg (by norm_num) hpos.le,(div_le_one hpos).mpr (le_max_left _ _)⟩
  · simp [reciprocalWeight,ha]

theorem reciprocalWeight_physical {X : Type*} (active : X→ Bool) (bid : X→ℝ)
    (x : X) (ha : active x=true) (hb : 1≤ bid x) : reciprocalWeight active bid x=1/bid x := by
  simp [reciprocalWeight,ha,max_eq_right hb]

theorem measurable_reciprocalWeight {X : Type*} [MeasurableSpace X]
    (active : X→ Bool) (ha : Measurable active) (bid : X→ℝ) (hb : Measurable bid) :
    Measurable (reciprocalWeight active bid) :=
  Measurable.ite (measurableSet_eq_fun ha measurable_const)
    (measurable_const.div (measurable_const.max hb)) measurable_const

section Counts
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (N : ℕ) (row : Ω→ Fin N→ X×unitInterval) (target : Ω→ Fin (N+1))
variable (active private0 private1 : X→ Bool) (p : X→ unitInterval)

def activeCount (x : Ω) : ℕ :=
  boolCount (Fin.cases true (fun i : Fin N => active (row x i).1))

def privateCount (privateCategory : X→ Bool) (x : Ω) : ℕ :=
  boolCount (fun i : Fin N => privateCategory (row x i).1)

def mixedBit (x : Ω) (i : Fin (N+1)) : Bool :=
  if i=target x then false else Fin.cases true (fun j : Fin N => activeFlag active p (row x j)) i

def mixedCount (x : Ω) : ℕ := boolCount (mixedBit N row target active p x)

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem mixedCount_le_activeCount (x : Ω) : mixedCount N row target active p x≤ activeCount N row active x := by
  unfold mixedCount activeCount boolCount
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = target x
  · simp only [mixedBit, if_pos hi, Bool.false_eq_true, ite_false]
    positivity
  · simp only [mixedBit, if_neg hi]
    refine Fin.cases ?_ (fun j => ?_) i
    · norm_num
    · cases ha : active (row x j).1 <;> cases hf : Empirical.flag (p (row x j).1) (row x j).2 <;>
        simp [activeFlag,ha,hf]

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem activeCount_normalized (x : Ω) : (activeCount N row active x:ℝ)/(N:ℝ)=
    insertedMean N (fun z : X×unitInterval => indicator active z.1) 1 row x := by
  rw [activeCount,boolCount_real,Fin.sum_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,ite_true,insertedMean,empiricalMean,indicator]
  simp only [div_eq_mul_inv]
  ring

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem privateCount_normalized (privateCategory : X→ Bool) (x : Ω) :
    (privateCount N row privateCategory x:ℝ)/(N:ℝ)=
      empiricalMean N (fun z : X×unitInterval => indicator privateCategory z.1) (row x) := by
  rw [privateCount,boolCount_real]
  rfl

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem mixedCount_normalized (x : Ω) : (mixedCount N row target active p x:ℝ)/(N:ℝ)=
    forcedMean N (Empirical.markedStatistic p (indicator active)) 1 row target x := by
  rw [mixedCount,boolCount_real]
  unfold forcedMean
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=target x
  · simp [mixedBit,hi]
  · simp only [mixedBit,if_neg hi]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [prefixWeight]
    · exact activeFlag_weight active p (row x j)

theorem measurable_activeCount (hrow : Measurable row) (ha : Measurable active) :
    Measurable (activeCount N row active) := by
  apply measurable_boolCount
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact ha.comp (measurable_fst.comp ((measurable_pi_apply j).comp hrow))

theorem measurable_privateCount (privateCategory : X→ Bool) (hrow : Measurable row) (ha : Measurable privateCategory) :
    Measurable (privateCount N row privateCategory) := by
  apply measurable_boolCount
  intro i
  exact ha.comp (measurable_fst.comp ((measurable_pi_apply i).comp hrow))

theorem measurable_mixedCount (hrow : Measurable row) (htarget : Measurable target)
    (ha : Measurable active) (hp : Measurable p) :
    Measurable (mixedCount N row target active p) := by
  apply measurable_boolCount
  intro i
  apply Measurable.ite (measurableSet_eq_fun measurable_const htarget) measurable_const
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact (measurable_activeFlag active ha p hp).comp ((measurable_pi_apply j).comp hrow)

end Counts

section SourceRates
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω → Fin N→ X×unitInterval)
variable (hrow : MeasurePreserving row ν
  (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))))

theorem integral_indicator_fst (active : X→ Bool) (ha : Measurable active) :
    (∫ z : X×unitInterval,indicator active z.1 ∂μ.prod (volume : Measure unitInterval))=
      ∫ x,indicator active x ∂μ := by
  have hi : Integrable (fun z : X×unitInterval => indicator active z.1)
      (μ.prod (volume : Measure unitInterval)) := by
    apply Integrable.of_bound ((measurable_indicator active ha).comp measurable_fst).aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by
      change ‖indicator active z.1‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (indicator_bounds active z.1).1]
      exact (indicator_bounds active z.1).2)
  rw [integral_prod _ hi]
  simp

include hN hrow in
theorem actual_active_count_L1 (active : X→ Bool) (ha : Measurable active) :
    (∫ x,|(activeCount N row active x:ℝ)/(N:ℝ)-∫ y,indicator active y ∂μ| ∂ν)≤
      1/Real.sqrt N+1/(N:ℝ) := by
  simp_rw [activeCount_normalized]
  simpa only [integral_indicator_fst μ active ha] using
    original_inserted_L1 (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (fun z : X×unitInterval => indicator active z.1)
      ((measurable_indicator active ha).comp measurable_fst)
      (fun z => indicator_bounds active z.1) 1 (by norm_num)

omit [IsProbabilityMeasure ν] in
include hN hrow in
theorem actual_private_count_L1 (privateCategory : X→ Bool) (ha : Measurable privateCategory) :
    (∫ x,|(privateCount N row privateCategory x:ℝ)/(N:ℝ)-∫ y,indicator privateCategory y ∂μ| ∂ν)≤
      1/Real.sqrt N := by
  simp_rw [privateCount_normalized]
  simpa only [integral_indicator_fst μ privateCategory ha] using
    original_empirical_L1 (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (fun z : X×unitInterval => indicator privateCategory z.1)
      ((measurable_indicator privateCategory ha).comp measurable_fst)
      (fun z => indicator_bounds privateCategory z.1)

include hN hrow in
theorem actual_mixed_count_L1 (active : X→ Bool) (ha : Measurable active)
    (p : X→ unitInterval) (hp : Measurable p) (target : Ω→ Fin (N+1)) (htarget : Measurable target) :
    (∫ x,|(mixedCount N row target active p x:ℝ)/(N:ℝ)-
      ∫ y,(p y:ℝ)*indicator active y ∂μ| ∂ν)≤1/Real.sqrt N+1/(N:ℝ) := by
  simp_rw [mixedCount_normalized]
  exact original_marked_forced_L1 μ ν N hN row hrow p hp (indicator active)
    (measurable_indicator active ha) (indicator_bounds active) 1 (by norm_num) target htarget

include hN hrow in
theorem actual_reciprocal_L1 (active : X→ Bool) (ha : Measurable active)
    (p : X→ unitInterval) (hp : Measurable p) (bid : X→ℝ) (hbid : Measurable bid)
    (b : ℝ) (hb : 1≤ b) (target : Ω→ Fin (N+1)) (htarget : Measurable target) :
    (∫ x,|forcedMean N (Empirical.markedStatistic p (reciprocalWeight active bid)) (1/b) row target x-
      ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ| ∂ν)≤1/Real.sqrt N+1/(N:ℝ) := by
  have hb0 : 0< b := lt_of_lt_of_le (by norm_num) hb
  exact original_marked_forced_L1 μ ν N hN row hrow p hp (reciprocalWeight active bid)
    (measurable_reciprocalWeight active ha bid hbid) (reciprocalWeight_bounds active bid)
    (1/b) ⟨div_nonneg (by norm_num) hb0.le,(div_le_one hb0).mpr hb⟩ target htarget

end SourceRates
end FCAppendix.Affine.Tail04.MenuError
