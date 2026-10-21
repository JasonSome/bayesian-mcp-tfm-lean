import FCAppendix.Affine.Tail04.AllCountOwnerError
import FCAppendix.Affine.Tail04.EmpiricalStatistics

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

section RowStatistics
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ]
variable (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω → Fin N → X)
variable (hrow : MeasurePreserving row ν (Measure.pi (fun _ : Fin N => μ)))
variable (weight : X→ℝ) (hweight : Measurable weight) (hw : ∀ x,weight x∈Icc (0:ℝ) 1)

def empiricalMean (weight : X→ℝ) (x : Fin N→ X) : ℝ := (∑ i,weight (x i))/(N:ℝ)

include hweight in
theorem measurable_empiricalMean : Measurable (empiricalMean N weight) :=
  (Finset.measurable_sum _ (fun i _ => hweight.comp (measurable_pi_apply i))).div_const N

include hN hw in
omit [MeasurableSpace X] in
theorem empiricalMean_bounds (x : Fin N→ X) : empiricalMean N weight x∈Icc (0:ℝ) 1 := by
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hlo : 0≤∑ i,weight (x i) := Finset.sum_nonneg (fun i _ => (hw _).1)
  have hhi : (∑ i,weight (x i))≤(N:ℝ) := by
    simpa using Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin N))) => (hw (x i)).2)
  exact ⟨div_nonneg hlo hn.le,(div_le_one hn).mpr hhi⟩

include hN hrow hweight hw in
omit [IsProbabilityMeasure μ] in
theorem integrable_empiricalMean : Integrable (fun x => empiricalMean N weight (row x)) ν := by
  apply Integrable.of_bound ((measurable_empiricalMean N weight hweight).comp hrow.measurable).aestronglyMeasurable 1
  exact Eventually.of_forall (fun x => by
    change ‖empiricalMean N weight (row x)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (empiricalMean_bounds N hN weight hw (row x)).1]
    exact (empiricalMean_bounds N hN weight hw (row x)).2)

include hN hrow hweight hw in
omit [IsProbabilityMeasure ν] in
theorem original_empirical_L1 :
    (∫ x,|empiricalMean N weight (row x)-∫ y,weight y ∂μ| ∂ν)≤1/Real.sqrt N := by
  have hh := Probability.iid_empiricalMean_L1_le μ hweight.aestronglyMeasurable
    1 (by norm_num) (Eventually.of_forall (fun x => by
      rw [abs_of_nonneg (hw x).1];exact (hw x).2)) N hN
  have hm : Measurable (fun x : Fin N→ X => |empiricalMean N weight x-∫ y,weight y ∂μ|) :=
    ((measurable_empiricalMean N weight hweight).sub_const _).abs
  have hmap := integral_map (μ := ν) hrow.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hrow.map_eq] at hmap
  change (∫ x,|empiricalMean N weight x-∫ y,weight y ∂μ|
      ∂Measure.pi (fun _ : Fin N => μ))≤_ at hh
  exact hmap ▸ hh

def prefixWeight (N : ℕ) (weight : X→ℝ) (focal : ℝ) (x : Fin N→ X) : Fin (N+1)→ℝ :=
  Fin.cases focal (fun i => weight (x i))

include hw in
omit [MeasurableSpace X] in
theorem prefixWeight_bounds (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1)
    (x : Fin N→ X) (i : Fin (N+1)) : prefixWeight N weight focal x i∈Icc (0:ℝ) 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hfocal
  · exact hw (x j)

include hrow hweight in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_prefixWeight (focal : ℝ) (i : Fin (N+1)) :
    Measurable (fun x => prefixWeight N weight focal (row x) i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact hweight.comp ((measurable_pi_apply j).comp hrow.measurable)

def forcedMean (N : ℕ) (weight : X→ℝ) (focal : ℝ)
    (row : Ω → Fin N→ X) (target : Ω → Fin (N+1)) (x : Ω) : ℝ :=
  (∑ i : Fin (N+1),if i=target x then 0 else prefixWeight N weight focal (row x) i)/(N:ℝ)

omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem forcedMean_identity (focal : ℝ) (target : Ω → Fin (N+1)) (x : Ω) :
    forcedMean N weight focal row target x=
      empiricalMean N weight (row x)+
        (focal-prefixWeight N weight focal (row x) (target x))/(N:ℝ) := by
  have hi (i : Fin (N+1)) : (if i=target x then (0:ℝ) else prefixWeight N weight focal (row x) i)=
      prefixWeight N weight focal (row x) i-
        (if i=target x then prefixWeight N weight focal (row x) i else 0) := by
    split_ifs <;> ring
  unfold forcedMean
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,Fin.sum_univ_succ,
    prefixWeight,Fin.cases_zero,Fin.cases_succ]
  unfold empiricalMean
  simp only [div_eq_mul_inv]
  ring

include hN hw in
omit [MeasurableSpace X] [MeasurableSpace Ω] in
theorem forcedMean_error_pointwise (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1)
    (target : Ω → Fin (N+1)) (x : Ω) :
    |forcedMean N weight focal row target x-empiricalMean N weight (row x)|≤1/(N:ℝ) := by
  rw [forcedMean_identity]
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have he : empiricalMean N weight (row x)+
      (focal-prefixWeight N weight focal (row x) (target x))/(N:ℝ)-empiricalMean N weight (row x)=
      (focal-prefixWeight N weight focal (row x) (target x))/(N:ℝ) := by ring
  rw [he,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right
    (unit_abs_sub_le_one hfocal (prefixWeight_bounds N weight hw focal hfocal (row x) (target x))) hn.le

include μ ν hrow hweight in
omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
theorem measurable_forcedMean (focal : ℝ) (target : Ω → Fin (N+1)) (htarget : Measurable target) :
    Measurable (forcedMean N weight focal row target) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_eq_fun measurable_const htarget)
    measurable_const (measurable_prefixWeight μ ν N row hrow weight hweight focal i)

include μ hN hrow hweight hw in
omit [IsProbabilityMeasure μ] in
theorem integrable_forcedMean (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1)
    (target : Ω → Fin (N+1)) (htarget : Measurable target) :
    Integrable (forcedMean N weight focal row target) ν := by
  apply Integrable.of_bound (measurable_forcedMean μ ν N row hrow weight hweight focal target htarget).aestronglyMeasurable
    (1+1/(N:ℝ))
  exact Eventually.of_forall (fun x => by
    have hp := forcedMean_error_pointwise N hN row weight hw focal hfocal target x
    have hb := empiricalMean_bounds N hN weight hw (row x)
    have htri := abs_add_le (forcedMean N weight focal row target x-empiricalMean N weight (row x))
      (empiricalMean N weight (row x))
    rw [sub_add_cancel,abs_of_nonneg hb.1] at htri
    rw [Real.norm_eq_abs]
    linarith [hb.2])

include hN hrow hweight hw in
theorem original_forced_L1 (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1)
    (target : Ω → Fin (N+1)) (htarget : Measurable target) :
    (∫ x,|forcedMean N weight focal row target x-∫ y,weight y ∂μ| ∂ν)≤
      1/Real.sqrt N+1/(N:ℝ) := by
  exact Empirical.edited_mean_L1 ν (fun x => empiricalMean N weight (row x))
    (forcedMean N weight focal row target)
    (integrable_empiricalMean μ ν N hN row hrow weight hweight hw)
    (integrable_forcedMean μ ν N hN row hrow weight hweight hw focal hfocal target htarget)
    (∫ y,weight y ∂μ) (1/(N:ℝ)) (1/Real.sqrt N)
    (Eventually.of_forall (forcedMean_error_pointwise N hN row weight hw focal hfocal target))
    (original_empirical_L1 μ ν N hN row hrow weight hweight hw)

def insertedMean (N : ℕ) (weight : X→ℝ) (focal : ℝ) (row : Ω → Fin N→ X) (x : Ω) : ℝ :=
  empiricalMean N weight (row x)+focal/(N:ℝ)

include hN hrow hweight hw in
theorem original_inserted_exact_L1 (focal : ℝ) (hfocal : 0≤ focal) :
    (∫ x,|insertedMean N weight focal row x-∫ y,weight y ∂μ| ∂ν)≤
      1/Real.sqrt N+focal/(N:ℝ) := by
  have hold := integrable_empiricalMean μ ν N hN row hrow weight hweight hw
  have hf : Integrable (insertedMean N weight focal row) ν := hold.add (integrable_const _)
  apply Empirical.edited_mean_L1 ν (fun x => empiricalMean N weight (row x))
    (insertedMean N weight focal row) hold hf (∫ y,weight y ∂μ)
      (focal/(N:ℝ)) (1/Real.sqrt N)
  · exact ae_of_all _ (fun x => by
      have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
      simp only [insertedMean,add_sub_cancel_left,abs_div,abs_of_pos hn,abs_of_nonneg hfocal]
      exact le_rfl)
  · exact original_empirical_L1 μ ν N hN row hrow weight hweight hw

include hN hrow hweight hw in
theorem original_inserted_L1 (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1) :
    (∫ x,|insertedMean N weight focal row x-∫ y,weight y ∂μ| ∂ν)≤
      1/Real.sqrt N+1/(N:ℝ) := by
  have hold := integrable_empiricalMean μ ν N hN row hrow weight hweight hw
  have hf : Integrable (insertedMean N weight focal row) ν := hold.add (integrable_const _)
  apply Empirical.edited_mean_L1 ν (fun x => empiricalMean N weight (row x))
    (insertedMean N weight focal row) hold hf (∫ y,weight y ∂μ) (1/(N:ℝ)) (1/Real.sqrt N)
  · exact Eventually.of_forall (fun x => by
      have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
      simp only [insertedMean,add_sub_cancel_left,abs_div,abs_of_pos hn,abs_of_nonneg hfocal.1]
      exact div_le_div_of_nonneg_right hfocal.2 hn.le)
  · exact original_empirical_L1 μ ν N hN row hrow weight hweight hw

end RowStatistics

section ActualFlags
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
variable (N : ℕ) (hN : 0< N) (row : Ω → Fin N→ X×unitInterval)
variable (hrow : MeasurePreserving row ν
  (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))))
variable (p : X→ unitInterval) (hp : Measurable p)
variable (h : X→ℝ) (hh : Measurable h) (hb : ∀ x,h x∈Icc (0:ℝ) 1)

include hN hrow hp hh hb in
theorem original_marked_forced_L1 (focal : ℝ) (hfocal : focal∈Icc (0:ℝ) 1)
    (target : Ω → Fin (N+1)) (htarget : Measurable target) :
    (∫ x,|forcedMean N (Empirical.markedStatistic p h) focal row target x-
      ∫ y,(p y:ℝ)*h y ∂μ| ∂ν)≤1/Real.sqrt N+1/(N:ℝ) := by
  simpa only [Empirical.integral_markedStatistic μ p hp h hh hb] using
    original_forced_L1 (μ.prod (volume : Measure unitInterval)) ν N hN row hrow
      (Empirical.markedStatistic p h) (Empirical.measurable_markedStatistic p hp h hh)
      (Empirical.markedStatistic_bounds p h hb) focal hfocal target htarget

end ActualFlags
end FCAppendix.Affine.Tail04.MenuError
