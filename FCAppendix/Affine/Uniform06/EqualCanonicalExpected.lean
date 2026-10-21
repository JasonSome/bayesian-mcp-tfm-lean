import FCAppendix.Affine.Uniform06.EqualCanonicalRegularity
import FCAppendix.Affine.Uniform06.PureRankCounts

noncomputable section
namespace FCAppendix.Affine.Uniform06.EqualCanonicalRegularity

open MeasureTheory ProbabilityTheory Set Filter
open LowBody PureRankCounts
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07
open scoped BigOperators

variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem measurable_equalMarginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) : Measurable (equalMarginal (N := N) ξ c b) := by
  have hk : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst)
  have hr : Measurable (fun ω : Fin N → RowRival => rowResidual c 0 ω) :=
    (measurable_of_countable
      (fun k : Fin N → Fin 4 => (patternTemplate c k).residual₀)).comp hk
  have hb : Measurable (fun ω : Fin N → RowRival => rowBids b ω) :=
    measurable_rowBids.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun q : ℕ × (Fin (N+1) → ℝ) =>
      EqualCapacity.positiveMarginal ξ q.1 q.2 0) := by
    apply measurable_from_prod_countable_right
    intro k
    exact (measurable_pi_apply 0).comp
      (EqualCapacity.measurable_positiveMarginal ξ k hξ hξ1)
  exact hf.comp (hr.prodMk hb)

theorem measurableSet_equalResidual (c : ℕ) :
    MeasurableSet {ω : Fin N → RowRival | rowResidual c 0 ω=rowResidual c 1 ω} := by
  have hk : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ (fun j => (measurable_pi_apply j).fst)
  have h₀ := (measurable_of_countable
    (fun k : Fin N → Fin 4 => (patternTemplate c k).residual₀)).comp hk
  have h₁ := (measurable_of_countable
    (fun k : Fin N → Fin 4 => (patternTemplate c k).residual₁)).comp hk
  exact measurableSet_eq_fun h₀ h₁

theorem measurable_equalDuplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) : Measurable (equalDuplicate (N := N) ξ c b) :=
  Measurable.ite (measurableSet_equalResidual c)
    ((measurable_equalMarginal hξ hξ1 c b).pow_const 2) measurable_const

theorem equalDuplicate_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) :
    equalDuplicate ξ c b ω ∈ Icc (0:ℝ) 1 := by
  have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω)
    hξ hξ1 (rowBids b ω)
  unfold equalDuplicate equalMarginal
  split_ifs
  · constructor
    · exact sq_nonneg _
    · nlinarith [hp.1 (0:Fin (N+1)),hp.2.1 (0:Fin (N+1))]
  · norm_num

theorem integrable_equalDuplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (equalDuplicate ξ c b) P := by
  apply Integrable.of_bound (C := 1)
    (measurable_equalDuplicate hξ hξ1 c b).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (equalDuplicate_bounds hξ hξ1 c b ω).1]
    exact (equalDuplicate_bounds hξ hξ1 c b ω).2

theorem measurable_rivalStatistic {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    Measurable (rivalStatistic ξ z) :=
  Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    ((continuous_exposure hξ hz).measurable.comp measurable_snd) measurable_const

def scalarTailEvent (ξ z : ℝ) (c : ℕ) : Set (Fin N → RowRival) :=
  {ω | (∑ j, rivalStatistic ξ z (ω j)) < c}

theorem measurableSet_scalarTailEvent {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (c : ℕ) : MeasurableSet (scalarTailEvent (N := N) ξ z c) := by
  apply measurableSet_lt _ measurable_const
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_rivalStatistic hξ hz).comp (measurable_pi_apply j))

def expectedEqualDuplicate (P : Measure (Fin N → RowRival))
    (ξ : ℝ) (c : ℕ) (b : ℝ) : ℝ := ∫ ω, equalDuplicate ξ c b ω ∂P

theorem expected_equal_duplicate_increment
    {ξ z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (c : ℕ) (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P]
    (hrows : ∀ᵐ ω ∂P, (∀ j, (ω j).1=0 → 0 ≤ (ω j).2) ∧
      (∀ j, (ω j).1 ≠ 1)) :
    ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ z →
      expectedEqualDuplicate P ξ c y-expectedEqualDuplicate P ξ c x ≤
        (2/(ξ*x))*P.real (scalarTailEvent ξ z c)*(y-x) := by
  intro x y hx hxy hyz
  let C : ℝ := 2*(y-x)/(ξ*x)
  have hpoint : ∀ᵐ ω ∂P, equalDuplicate ξ c y ω-equalDuplicate ξ c x ω ≤
      (scalarTailEvent ξ z c).indicator (fun _ => C) ω := by
    filter_upwards [hrows] with ω hω
    simpa only [scalarTailEvent,Set.indicator_apply,mem_setOf_eq,C] using
      equal_duplicate_increment_with_tail hξ hξ1 hz c ω hω.1 hω.2 hx hxy hyz
  have hi := integral_mono_ae
    ((integrable_equalDuplicate hξ hξ1 c y P).sub
      (integrable_equalDuplicate hξ hξ1 c x P))
    ((integrable_const C).indicator (measurableSet_scalarTailEvent hξ hz c)) hpoint
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_equalDuplicate hξ hξ1 c y P)
    (integrable_equalDuplicate hξ hξ1 c x P),integral_indicator
      (measurableSet_scalarTailEvent hξ hz c),integral_const] at hi
  change expectedEqualDuplicate P ξ c y-expectedEqualDuplicate P ξ c x ≤
    (P.restrict (scalarTailEvent ξ z c)).real univ * C at hi
  rw [Measure.real,Measure.restrict_apply_univ] at hi
  change expectedEqualDuplicate P ξ c y-expectedEqualDuplicate P ξ c x ≤
    P.real (scalarTailEvent ξ z c)*C at hi
  convert! hi using 1
  dsimp only [C]
  ring

theorem expected_equal_duplicate_le_tail
    {ξ z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (c : ℕ) (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P]
    (hno : ∀ᵐ ω ∂P, ∀ j, (ω j).1 ≠ 1) :
    ∀ b : ℝ, 0 < b → b ≤ z →
      expectedEqualDuplicate P ξ c b ≤ P.real (scalarTailEvent ξ z c) := by
  intro b hb hbz
  have hpoint : ∀ᵐ ω ∂P, equalDuplicate ξ c b ω ≤
      (scalarTailEvent ξ z c).indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [hno] with ω hω
    by_cases ht : ω ∈ scalarTailEvent ξ z c
    · rw [Set.indicator_of_mem ht]
      exact (equalDuplicate_bounds hξ hξ1 c b ω).2
    · rw [Set.indicator_of_notMem ht]
      unfold equalDuplicate
      split_ifs with heq
      · have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω)
          hξ hξ1 (rowBids b ω)
        have hzero : equalMarginal ξ c b ω=0 := by
          apply le_antisymm _ (hp.1 0)
          apply le_of_not_gt
          intro hpos
          exact ht (equal_positive_implies_scalar_tail hξ hξ1 hz c ω hb hbz hω heq hpos)
        rw [hzero]
        norm_num
      · exact le_rfl
  have hi := integral_mono_ae (integrable_equalDuplicate hξ hξ1 c b P)
    ((integrable_const (1:ℝ)).indicator (measurableSet_scalarTailEvent hξ hz c)) hpoint
  rw [integral_indicator (measurableSet_scalarTailEvent hξ hz c),integral_const] at hi
  simpa [expectedEqualDuplicate,Measure.real] using hi

theorem source_statistic_map (i : Row) (G : Measure (ℝ × ℝ)) :
    (sourceRivalLaw (cutoff i) (G.map Prod.snd)).map
      (rivalStatistic (xi i) ((501/1000:ℝ)*cutoff i)) =
        LowChernoff.originalStatisticLaw i G := by
  let f := rivalStatistic (xi i) ((501/1000:ℝ)*cutoff i)
  have hf : Measurable f := measurable_rivalStatistic (xi_pos i)
    (mul_pos (by norm_num) (cutoff_pos i))
  have hlow : Measurable (fun b : ℝ => ((0:Fin 4),b)) :=
    measurable_const.prodMk measurable_id
  have hmap : ((G.map Prod.snd).map (fun b : ℝ => ((0:Fin 4),b))).map f =
      LowChernoff.lowerStatisticLaw i G := by
    rw [Measure.map_map hf hlow,Measure.map_map (hf.comp hlow) measurable_snd]
    rfl
  have hcoeff : ENNReal.ofReal ((1-cutoff i)/2)+ENNReal.ofReal ((1-cutoff i)/2) =
      ENNReal.ofReal (1-cutoff i) := by
    rw [← ENNReal.ofReal_add (by linarith [cutoff_lt_one i])
      (by linarith [cutoff_lt_one i])]
    congr 1
    ring
  change (sourceRivalLaw (cutoff i) (G.map Prod.snd)).map f = _
  rw [sourceRivalLaw,rivalLaw,Measure.map_add _ _ hf,
    Measure.map_add _ _ hf,Measure.map_add _ _ hf]
  simp only [Measure.map_smul,ENNReal.ofReal_zero,zero_smul,Measure.map_zero,add_zero]
  rw [hmap,Measure.map_dirac' hf,Measure.map_dirac' hf]
  have he2 : f ((2:Fin 4),(0:ℝ))=1/2 := by norm_num [f,rivalStatistic,Fin.ext_iff]
  have he3 : f ((3:Fin 4),(0:ℝ))=1/2 := by norm_num [f,rivalStatistic,Fin.ext_iff]
  rw [he2,he3,add_assoc,← add_smul,hcoeff,add_comm]
  rfl

theorem source_equal_tail_chernoff (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 2 ≤ m) :
    (Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) (G.map Prod.snd)).real
      (scalarTailEvent (xi i) ((501/1000:ℝ)*cutoff i) (capacity m)) ≤
        Real.exp ((LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
          (m-1:ℕ)*((LowChernoff.thetaQ i:ℝ)*rho+
            LowChernoff.rankI0 i+LowChernoff.sourceGap i)) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := sourceRivalLaw (cutoff i) Gb
  letI : IsProbabilityMeasure μ := sourceRivalLaw_probability
    ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  let P := Measure.pi fun _ : Fin (m-1) => μ
  let f := rivalStatistic (xi i) ((501/1000:ℝ)*cutoff i)
  let Y := fun (j : Fin (m-1)) (ω : Fin (m-1) → RowRival) => f (ω j)
  have hf : Measurable f := measurable_rivalStatistic (xi_pos i)
    (mul_pos (by norm_num) (cutoff_pos i))
  have hY : ∀ j, Measurable (Y j) := fun j => hf.comp (measurable_pi_apply j)
  have hind : iIndepFun Y P := iIndepFun_pi (fun _ => hf.aemeasurable)
  have hlaw (j : Fin (m-1)) : IdentDistrib (Y j) id P (LowChernoff.originalStatisticLaw i G) := by
    refine ⟨(hY j).aemeasurable,measurable_id.aemeasurable,?_⟩
    rw [Measure.map_id]
    change P.map (f ∘ (fun ω => ω j)) = _
    rw [← Measure.map_map hf (measurable_pi_apply j),
      (measurePreserving_eval (fun _ : Fin (m-1) => μ) j).map_eq]
    exact source_statistic_map i G
  have hh := LowChernoff.original_iid_row_bound i G hvalue hfloor P hm Y hY hind hlaw
  apply (measureReal_mono (μ := P) (show scalarTailEvent (xi i)
    ((501/1000:ℝ)*cutoff i) (capacity m) ⊆
      {ω | FCAppendix.ExponentialTilt.rowSum Y ω ≤ (capacity m:ℝ)} from
        fun ω hω => show FCAppendix.ExponentialTilt.rowSum Y ω ≤ (capacity m:ℝ) from le_of_lt hω)).trans hh

theorem source_single_row_no_active (t : ℝ) (G : Measure ℝ) :
    ∀ᵐ r ∂sourceRivalLaw t G, r.1 ≠ 1 := by
  have hinj : Measurable (fun v : ℝ => ((0:Fin 4),v)) :=
    measurable_const.prodMk measurable_id
  have hlow : ∀ᵐ r ∂G.map (fun v : ℝ => ((0:Fin 4),v)), r.1 ≠ 1 := by
    apply (ae_map_iff hinj.aemeasurable (by measurability)).mpr
    exact Filter.Eventually.of_forall fun v => by norm_num [Fin.ext_iff]
  simp only [sourceRivalLaw,rivalLaw,ENNReal.ofReal_zero,zero_smul,add_zero,
    ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure hlow _,?_⟩,?_⟩ <;>
    apply Measure.ae_smul_measure <;> rw [ae_dirac_eq] <;> norm_num [Fin.ext_iff]

theorem source_iid_row_no_active {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] :
    ∀ᵐ ω : Fin N → RowRival ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G),
      ∀ j, (ω j).1 ≠ 1 := by
  letI := sourceRivalLaw_probability ht G
  apply ae_all_iff.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => sourceRivalLaw t G) (i := j))
    (source_single_row_no_active t G)

theorem source_floor_bid_nonnegative (i : Row) (G : Measure (ℝ × ℝ))
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) :
    ∀ᵐ b ∂G.map Prod.snd, 0 ≤ b := by
  apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr
  filter_upwards [hfloor] with p hp
  have hf : 0 ≤ LowChernoff.physicalFloor i p.1 := by
    unfold LowChernoff.physicalFloor
    positivity
  exact hf.trans hp

theorem source_equal_duplicate_level_and_increment (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 2 ≤ m) :
    let P := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) (G.map Prod.snd)
    let e := Real.exp ((LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
      (m-1:ℕ)*((LowChernoff.thetaQ i:ℝ)*rho+
        LowChernoff.rankI0 i+LowChernoff.sourceGap i))
    (∀ b : ℝ, 0 < b → b ≤ (501/1000:ℝ)*cutoff i →
      expectedEqualDuplicate P (xi i) (capacity m) b ≤ e) ∧
    (∀ x y : ℝ, 0 < x → x ≤ y → y ≤ (501/1000:ℝ)*cutoff i →
      expectedEqualDuplicate P (xi i) (capacity m) y-
        expectedEqualDuplicate P (xi i) (capacity m) x ≤
          (2/(xi i*x))*e*(y-x)) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := sourceRivalLaw (cutoff i) Gb
  letI : IsProbabilityMeasure μ := sourceRivalLaw_probability
    ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  let P := Measure.pi fun _ : Fin (m-1) => μ
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hz : 0 < (501/1000:ℝ)*cutoff i := mul_pos (by norm_num) (cutoff_pos i)
  have hno : ∀ᵐ ω ∂P, ∀ j, (ω j).1 ≠ 1 :=
    source_iid_row_no_active ⟨(cutoff_pos i).le,(cutoff_lt_one i).le⟩ Gb
  have hnon : ∀ᵐ ω ∂P, ∀ j, 0 ≤ (ω j).2 :=
    iid_rows_ae_bid_nonnegative μ
      (rivalLaw_ae_bid_nonnegative (cutoff i) 0 (1-cutoff i) Gb
        (source_floor_bid_nonnegative i G hfloor))
  have hrows : ∀ᵐ ω ∂P, (∀ j, (ω j).1=0 → 0 ≤ (ω j).2) ∧
      (∀ j, (ω j).1 ≠ 1) := by
    filter_upwards [hnon,hno] with ω hn hz
    exact ⟨fun j _ => hn j,hz⟩
  have htail := source_equal_tail_chernoff i G hvalue hfloor hm
  constructor
  · intro b hb hbz
    exact (expected_equal_duplicate_le_tail (xi_pos i) hξ1 hz
      (capacity m) P hno b hb hbz).trans htail
  · intro x y hx hxy hyz
    have hbound := expected_equal_duplicate_increment (xi_pos i) hξ1 hz
      (capacity m) P hrows x y hx hxy hyz
    apply hbound.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htail (div_nonneg (by norm_num) (mul_pos (xi_pos i) hx).le)) (sub_nonneg.mpr hxy)

end FCAppendix.Affine.Uniform06.EqualCanonicalRegularity
