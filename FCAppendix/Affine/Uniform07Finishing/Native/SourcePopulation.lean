import FCAppendix.Affine.Uniform07Finishing.Native.UniformUpperLimits
import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.PopulationGame

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open Existence.RankEnvelope

local instance : Nonempty (JointAction 2) := ⟨Interim.abstain 2⟩

def sourceBandValueLaw (a b : ℝ) (hab : a < b) : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Icc a b), by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sub_pos.mpr hab).le),
      inv_mul_cancel₀ (sub_pos.mpr hab).ne', ENNReal.ofReal_one]⟩

theorem sourceBandValueLaw_weighted (a b : ℝ) (hab : a < b) :
    ENNReal.ofReal (b-a) • (sourceBandValueLaw a b hab : Measure ℝ) =
      volume.restrict (Icc a b) := by
  change ENNReal.ofReal (b-a) •
    (ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Icc a b)) = _
  rw [smul_smul, ← ENNReal.ofReal_mul (sub_pos.mpr hab).le,
    mul_inv_cancel₀ (sub_pos.mpr hab).ne', ENNReal.ofReal_one, one_smul]

theorem sourceBandValueLaw_support (a b : ℝ) (hab : a < b) :
    ∀ᵐ v ∂(sourceBandValueLaw a b hab : Measure ℝ), v ∈ Icc a b :=
  Measure.ae_smul_measure (ae_restrict_mem (μ := volume) measurableSet_Icc) _

instance sourceBandValueLaw_atomless (a b : ℝ) (hab : a < b) :
    NullSingletonClass (sourceBandValueLaw a b hab : Measure ℝ) := by
  constructor
  intro v
  change (ENNReal.ofReal ((b-a)⁻¹) • volume.restrict (Icc a b)) {v} = 0
  simp only [Measure.smul_apply, smul_eq_mul, measure_singleton, mul_zero]

def sourceLowerValueLaw (i : Uniform07.Row) : ProbabilityMeasure ℝ :=
  sourceBandValueLaw 0 (Uniform07.cutoff i) (Uniform07.cutoff_pos i)

def sourceUpperValueLaw (i : Uniform07.Row) : ProbabilityMeasure ℝ :=
  sourceBandValueLaw (Uniform07.cutoff i) 1 (Uniform07.cutoff_lt_one i)

theorem sourceLowerValueLaw_literal (i : Uniform07.Row) :
    (sourceLowerValueLaw i : Measure ℝ) =
      ENNReal.ofReal (1 / Uniform07.cutoff i) •
        volume.restrict (Icc 0 (Uniform07.cutoff i)) := by
  simp only [sourceLowerValueLaw, sourceBandValueLaw, sub_zero, one_div]
  rfl

theorem sourceUpperValueLaw_literal (i : Uniform07.Row) :
    (sourceUpperValueLaw i : Measure ℝ) =
      ENNReal.ofReal (1 / (1-Uniform07.cutoff i)) •
        volume.restrict (Icc (Uniform07.cutoff i) 1) := by
  simp only [sourceUpperValueLaw, sourceBandValueLaw, one_div]
  rfl

instance sourceLowerValueLaw_atomless (i : Uniform07.Row) :
    NullSingletonClass (sourceLowerValueLaw i : Measure ℝ) := by
  unfold sourceLowerValueLaw
  infer_instance

instance sourceUpperValueLaw_atomless (i : Uniform07.Row) :
    NullSingletonClass (sourceUpperValueLaw i : Measure ℝ) := by
  unfold sourceUpperValueLaw
  infer_instance

theorem sourceLowerValueLaw_weighted (i : Uniform07.Row) :
    ENNReal.ofReal (Uniform07.cutoff i) • (sourceLowerValueLaw i : Measure ℝ) =
      volume.restrict (Icc 0 (Uniform07.cutoff i)) := by
  simpa only [sub_zero, sourceLowerValueLaw] using
    sourceBandValueLaw_weighted 0 (Uniform07.cutoff i) (Uniform07.cutoff_pos i)

theorem sourceUpperValueLaw_weighted (i : Uniform07.Row) :
    ENNReal.ofReal (1-Uniform07.cutoff i) • (sourceUpperValueLaw i : Measure ℝ) =
      upperValueMeasure i :=
  sourceBandValueLaw_weighted (Uniform07.cutoff i) 1 (Uniform07.cutoff_lt_one i)

theorem sourceLowerValueLaw_support (i : Uniform07.Row) :
    ∀ᵐ v ∂(sourceLowerValueLaw i : Measure ℝ), v ∈ Icc 0 (Uniform07.cutoff i) :=
  sourceBandValueLaw_support 0 (Uniform07.cutoff i) (Uniform07.cutoff_pos i)

theorem sourceUpperValueLaw_support (i : Uniform07.Row) :
    ∀ᵐ v ∂(sourceUpperValueLaw i : Measure ℝ), v ∈ Icc (Uniform07.cutoff i) 1 :=
  sourceBandValueLaw_support (Uniform07.cutoff i) 1 (Uniform07.cutoff_lt_one i)

theorem source_uniform_value_partition (i : Uniform07.Row) :
    volume.restrict (Icc 0 (Uniform07.cutoff i)) + upperValueMeasure i =
      Uniform07.uniformLaw := by
  have hne : ∀ᵐ v ∂(volume : Measure ℝ), v ≠ Uniform07.cutoff i :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton (Uniform07.cutoff i))
  have hupper : upperValueMeasure i = volume.restrict (Ioc (Uniform07.cutoff i) 1) := by
    apply Measure.restrict_congr_set
    filter_upwards [hne] with v hv
    apply propext
    change v∈Icc (Uniform07.cutoff i) 1 ↔ v∈Ioc (Uniform07.cutoff i) 1
    constructor
    · intro h
      exact ⟨lt_of_le_of_ne h.1 (Ne.symm hv), h.2⟩
    · exact fun h => ⟨h.1.le, h.2⟩
  have hd : Disjoint (Icc 0 (Uniform07.cutoff i)) (Ioc (Uniform07.cutoff i) 1) := by
    apply Set.disjoint_left.mpr
    intro v hl hh
    exact not_lt_of_ge hl.2 hh.1
  have hu : Icc 0 (Uniform07.cutoff i) ∪ Ioc (Uniform07.cutoff i) 1 = Icc 0 1 := by
    ext v
    simp only [mem_union, mem_Icc, mem_Ioc]
    constructor
    · rintro (h | h)
      · exact ⟨h.1, h.2.trans (Uniform07.cutoff_lt_one i).le⟩
      · exact ⟨(Uniform07.cutoff_pos i).le.trans h.1.le, h.2⟩
    · intro h
      by_cases hv : v ≤ Uniform07.cutoff i
      · exact Or.inl ⟨h.1, hv⟩
      · exact Or.inr ⟨lt_of_not_ge hv, h.2⟩
  rw [hupper, ← Measure.restrict_union hd measurableSet_Ioc, hu]
  rfl

def sourceUpperBid (i : Uniform07.Row) (m : ℕ) (R : ℝ) : ℝ → ℝ :=
  bid (source_upper_rank i m) (Uniform07.cutoff i) R

theorem sourceUpperBid_measurable (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ) :
    Measurable (sourceUpperBid i m R) :=
  (continuous_bid (continuous_rank (upperValueMeasure i) (m-1)
    (Uniform07.capacity m) 2)
    (fun v => (source_upper_rank_pos i m hc v).ne') (Uniform07.cutoff i) R).measurable

def sourceUpperJoint (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ) : ProbabilityMeasure (ℝ × JointAction 2) :=
  Hybrid.upperJoint (sourceUpperValueLaw i) (sourceUpperBid i m R)
    (sourceUpperBid_measurable i m hc R)

theorem source_upper_joint_value_marginal (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ) :
    (sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceUpperValueLaw i : Measure ℝ) :=
  Hybrid.upperJoint_value_marginal _ _ _

theorem source_upper_envelope (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ} (hR : 0 < R)
    (hRt : R < Uniform07.cutoff i) :
    UpperEnvelopeProperties (upperValueMeasure i) (m-2) (Uniform07.capacity m)
      (source_upper_rank i m) (sourceUpperBid i m R)
      (utility (source_upper_rank i m) (Uniform07.cutoff i) R)
      (Uniform07.cutoff i) R (error (source_upper_rank i m) (Uniform07.cutoff i) R) := by
  have hcm := source_capacity_lt_population m (by omega)
  have he : m-2+1 = m-1 := by omega
  have hs : ∀ᵐ v ∂upperValueMeasure i, v ∈ Icc (Uniform07.cutoff i) 1 :=
    ae_restrict_mem (μ := volume) measurableSet_Icc
  have heq : source_upper_rank i m = rank (upperValueMeasure i) (m-1) (Uniform07.capacity m) 2 := by
    funext v
    rfl
  dsimp only [sourceUpperBid]
  rw [heq]
  simpa only [he] using
    upper_envelope_bounded (upperValueMeasure i) (m-2) (Uniform07.capacity m)
      hc (by omega) (upperValueMeasure_mass_le_one i) (Uniform07.cutoff i) R 1 hR hRt hs

theorem source_upper_joint_properties (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ} (hR : 0 < R)
    (hRt : R < Uniform07.cutoff i) :
    (sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
        (sourceUpperValueLaw i : Measure ℝ).map (sourceUpperBid i m R) ∧
    (∀ᵐ x ∂(sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2)),
      x.1 ∈ Icc (Uniform07.cutoff i) 1 ∧ x.2.bid = sourceUpperBid i m R x.1 ∧
      R ≤ x.2.bid ∧ x.2.bid ≤ x.1 ∧ x.2.routeCount = 1) ∧
    (∀ y : ℝ, (sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2))
      {x | x.2.bid = y} = 0) := by
  have hp := source_upper_envelope i m hm hc hR hRt
  have hfloor : ∀ᵐ v ∂(sourceUpperValueLaw i : Measure ℝ), R ≤ sourceUpperBid i m R v :=
    (sourceUpperValueLaw_support i).mono (fun v hv => (hp.bid_bounds v hv.1).1)
  have hpos : ∀ᵐ v ∂(sourceUpperValueLaw i : Measure ℝ), 0 ≤ sourceUpperBid i m R v :=
    hfloor.mono (fun _ hv => hR.le.trans hv)
  letI : NullSingletonClass ((sourceUpperValueLaw i : Measure ℝ).map (sourceUpperBid i m R)) := by
    constructor
    intro y
    have hz := hp.atomless.measure_singleton y
    change ((upperValueMeasure i).map (sourceUpperBid i m R)) {y} = 0 at hz
    rw [← sourceUpperValueLaw_weighted i, Measure.map_smul,
      Measure.smul_apply, smul_eq_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr (Uniform07.cutoff_lt_one i)))
  refine ⟨Hybrid.upperJoint_bid_marginal _ _ _ hpos, ?_,
    Hybrid.upperJoint_atomless _ _ _ hpos⟩
  change ∀ᵐ x ∂((sourceUpperValueLaw i : Measure ℝ).map
    (fun v => (v, Hybrid.upperAction (sourceUpperBid i m R) v))), _
  apply (ae_map_iff (measurable_id.prodMk
    (Hybrid.measurable_upperAction _ (sourceUpperBid_measurable i m hc R))).aemeasurable
    (by
      exact (measurable_fst measurableSet_Icc).inter
        ((measurableSet_eq_fun ((measurable_bid 2).comp measurable_snd)
          ((sourceUpperBid_measurable i m hc R).comp measurable_fst)).inter
        ((measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
        ((measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_fst).inter
          (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const)))))).mpr
  filter_upwards [sourceUpperValueLaw_support i] with v hv
  have hb := hp.bid_bounds v hv.1
  have hb0 := hR.le.trans hb.1
  simpa only [Hybrid.upperAction, max_eq_left hb0,id_eq] using
    (show v ∈ Icc (Uniform07.cutoff i) 1 ∧ sourceUpperBid i m R v = sourceUpperBid i m R v ∧
      R ≤ sourceUpperBid i m R v ∧ sourceUpperBid i m R v ≤ v ∧ (1 : ℕ) = 1 from
      ⟨hv, rfl, hb.1, hb.2, rfl⟩)

theorem joint_value_ne_of_marginal (P : ProbabilityMeasure (ℝ × JointAction 2))
    (F : ProbabilityMeasure ℝ) [NullSingletonClass (F : Measure ℝ)]
    (hF : (P : Measure (ℝ × JointAction 2)).map Prod.fst = (F : Measure ℝ)) (v : ℝ) :
    ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), x.1 ≠ v := by
  apply measure_eq_zero_iff_ae_notMem.mp
  have hz := measure_singleton (μ := (F : Measure ℝ)) v
  rw [← hF, Measure.map_apply measurable_fst (measurableSet_singleton v)] at hz
  exact hz

def sourceLowerBroadcastAction (U : ℝ) (b : Icc (0 : ℝ) U) : JointAction 2 :=
  ⟨b.1, b.2.1, 2, le_rfl⟩

theorem sourceLowerBroadcastAction_measurable (U : ℝ) :
    Measurable (sourceLowerBroadcastAction U) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  exact (measurable_subtype_coe.prodMk measurable_const).comap_le

def sourceLowerBroadcastJoint (U : ℝ) (Q : ProbabilityMeasure (ℝ × Icc (0 : ℝ) U)) :
    ProbabilityMeasure (ℝ × JointAction 2) :=
  Q.map (measurable_fst.prodMk
    ((sourceLowerBroadcastAction_measurable U).comp measurable_snd)).aemeasurable

theorem sourceLowerBroadcastJoint_value_marginal (U : ℝ)
    (Q : ProbabilityMeasure (ℝ × Icc (0 : ℝ) U)) :
    (sourceLowerBroadcastJoint U Q : Measure (ℝ × JointAction 2)).map Prod.fst =
      (Q : Measure (ℝ × Icc (0 : ℝ) U)).map Prod.fst := by
  change ((Q : Measure (ℝ × Icc (0 : ℝ) U)).map
    (fun x => (x.1, sourceLowerBroadcastAction U x.2))).map Prod.fst = _
  rw [Measure.map_map measurable_fst (show Measurable
    (fun x : ℝ×Icc (0:ℝ) U => (x.1,sourceLowerBroadcastAction U x.2)) from
    measurable_fst.prodMk ((sourceLowerBroadcastAction_measurable U).comp measurable_snd))]
  rfl

theorem sourceLowerBroadcastJoint_bid_marginal (U : ℝ)
    (Q : ProbabilityMeasure (ℝ × Icc (0 : ℝ) U)) :
    (sourceLowerBroadcastJoint U Q : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid) =
      (Q : Measure (ℝ × Icc (0 : ℝ) U)).map (fun x => (x.2 : ℝ)) := by
  change ((Q : Measure (ℝ × Icc (0 : ℝ) U)).map
    (fun x => (x.1, sourceLowerBroadcastAction U x.2))).map (fun x => x.2.bid) = _
  rw [Measure.map_map (show Measurable (fun x : ℝ×JointAction 2 => x.2.bid) from
      (measurable_bid 2).comp measurable_snd)
    (show Measurable (fun x : ℝ×Icc (0:ℝ) U => (x.1,sourceLowerBroadcastAction U x.2)) from
      measurable_fst.prodMk ((sourceLowerBroadcastAction_measurable U).comp measurable_snd))]
  rfl

theorem sourceLowerBroadcastJoint_support (U : ℝ)
    (Q : ProbabilityMeasure (ℝ × Icc (0 : ℝ) U)) :
    ∀ᵐ x ∂(sourceLowerBroadcastJoint U Q : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ U ∧ x.2.routeCount = 2 := by
  change ∀ᵐ x ∂((Q : Measure (ℝ × Icc (0 : ℝ) U)).map
    (fun x => (x.1, sourceLowerBroadcastAction U x.2))), _
  apply (ae_map_iff (measurable_fst.prodMk
    ((sourceLowerBroadcastAction_measurable U).comp measurable_snd)).aemeasurable
    ((measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))).mpr
  exact Filter.Eventually.of_forall (fun x => ⟨x.2.2.2, rfl⟩)

theorem sourceLowerBroadcastJoint_atomless (U : ℝ)
    (Q : ProbabilityMeasure (ℝ × Icc (0 : ℝ) U))
    [NullSingletonClass ((Q : Measure (ℝ × Icc (0 : ℝ) U)).map (fun x => (x.2 : ℝ)))] :
    ∀ y : ℝ, (sourceLowerBroadcastJoint U Q : Measure (ℝ × JointAction 2))
      {x | x.2.bid = y} = 0 := by
  intro y
  have hz := measure_singleton (μ :=
    (Q : Measure (ℝ × Icc (0 : ℝ) U)).map (fun x => (x.2 : ℝ))) y
  rw [← sourceLowerBroadcastJoint_bid_marginal U Q,
    Measure.map_apply (show Measurable (fun x : ℝ×JointAction 2 => x.2.bid) from
      (measurable_bid 2).comp measurable_snd) (measurableSet_singleton y)] at hz
  exact hz

def sourcePopulation (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) : ProbabilityMeasure (ℝ × JointAction 2) :=
  Hybrid.populationLaw (Uniform07.cutoff i) 0 (1-Uniform07.cutoff i)
    (Uniform07.cutoff_pos i).le (by norm_num) (sub_pos.mpr (Uniform07.cutoff_lt_one i)).le
    (by ring) PL PL (sourceUpperJoint i m hc R)

theorem sourcePopulation_literal (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)) =
      ENNReal.ofReal (Uniform07.cutoff i) • (PL : Measure (ℝ × JointAction 2)) +
      ENNReal.ofReal (1-Uniform07.cutoff i) •
        (sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2)) := by
  simp only [sourcePopulation, Hybrid.populationLaw, Hybrid.populationJoint,
    ENNReal.ofReal_zero, zero_smul, add_zero]
  rfl

theorem source_lower_weighted_marginal (i : Uniform07.Row)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ)) :
    ENNReal.ofReal (Uniform07.cutoff i) • (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      volume.restrict (Icc 0 (Uniform07.cutoff i)) := by
  rw [hL, sourceLowerValueLaw_weighted]

theorem source_lower_normalized_marginal_of_weighted (i : Uniform07.Row)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ENNReal.ofReal (Uniform07.cutoff i) •
      (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
        volume.restrict (Icc 0 (Uniform07.cutoff i))) :
    (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ) := by
  ext s hs
  have h := congrArg (fun μ : Measure ℝ => μ s) hL
  simp only [Measure.smul_apply, smul_eq_mul] at h
  calc
    _ = ENNReal.ofReal (1 / Uniform07.cutoff i) *
        (ENNReal.ofReal (Uniform07.cutoff i) *
          ((PL : Measure (ℝ × JointAction 2)).map Prod.fst) s) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul
        (div_nonneg zero_le_one (Uniform07.cutoff_pos i).le),
        one_div_mul_cancel (Uniform07.cutoff_pos i).ne', ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (1 / Uniform07.cutoff i) *
        (volume.restrict (Icc 0 (Uniform07.cutoff i))) s := by rw [h]
    _ = _ := by rw [sourceLowerValueLaw_literal, Measure.smul_apply, smul_eq_mul]

theorem source_population_value_marginal (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ)) :
    (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      Uniform07.uniformLaw := by
  rw [sourcePopulation_literal, Measure.map_add _ _ measurable_fst]
  simp only [Measure.map_smul, hL, source_upper_joint_value_marginal,
    sourceLowerValueLaw_weighted, sourceUpperValueLaw_weighted]
  exact source_uniform_value_partition i

theorem source_population_support (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {U R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount = 2) :
    ∀ᵐ x ∂(sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)),
      (0 ≤ x.1 ∧ x.1 < Uniform07.cutoff i ∧ x.2.bid ≤ U ∧ x.2.routeCount = 2) ∨
      (Uniform07.cutoff i < x.1 ∧ x.1 ≤ 1 ∧ x.2.bid = sourceUpperBid i m R x.1 ∧
        R ≤ x.2.bid ∧ x.2.bid ≤ x.1 ∧ x.2.routeCount = 1) := by
  have hLvalues : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.1 ∈ Icc 0 (Uniform07.cutoff i) := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
    rw [hLvalue]
    exact sourceLowerValueLaw_support i
  have hLne := joint_value_ne_of_marginal PL (sourceLowerValueLaw i) hLvalue (Uniform07.cutoff i)
  have hHne := joint_value_ne_of_marginal (sourceUpperJoint i m hc R) (sourceUpperValueLaw i)
    (source_upper_joint_value_marginal i m hc R) (Uniform07.cutoff i)
  rw [sourcePopulation_literal, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    filter_upwards [hLvalues, hLroute, hLne] with x hx ha hne
    exact Or.inl ⟨hx.1, lt_of_le_of_ne hx.2 hne, ha.1, ha.2⟩
  · apply Measure.ae_smul_measure
    filter_upwards [(source_upper_joint_properties i m hm hc hR hRt).2.1, hHne] with x hx hne
    exact Or.inr ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne), hx.1.2,
      hx.2.1, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2⟩

theorem source_population_bid_atomless (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLatom : ∀ y : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0) :
    NullSingletonClass ((sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)).map
      (fun x => x.2.bid)) := by
  constructor
  intro y
  rw [Measure.map_apply (show Measurable (fun x : ℝ×JointAction 2 => x.2.bid) from
      (measurable_bid 2).comp measurable_snd) (measurableSet_singleton y),
    sourcePopulation_literal, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul]
  change ENNReal.ofReal (Uniform07.cutoff i) * (PL : Measure (ℝ × JointAction 2))
      {x | x.2.bid = y} + ENNReal.ofReal (1-Uniform07.cutoff i) *
      (sourceUpperJoint i m hc R : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0
  rw [hLatom y, (source_upper_joint_properties i m hm hc hR hRt).2.2 y]
  simp only [mul_zero, add_zero]

theorem source_population_bid_positive (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLatom : ∀ y : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0) :
    ∀ᵐ x ∂(sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)), 0 < x.2.bid := by
  letI := source_population_bid_atomless i m hm hc hR hRt PL hLatom
  have hz := measure_singleton (μ :=
    (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)).map
      (fun x => x.2.bid)) (0 : ℝ)
  rw [Measure.map_apply (show Measurable (fun x : ℝ×JointAction 2 => x.2.bid) from
    (measurable_bid 2).comp measurable_snd) (measurableSet_singleton 0)] at hz
  have hne : ∀ᵐ x ∂(sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)), x.2.bid ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hz
  exact hne.mono (fun x hx => lt_of_le_of_ne x.2.bid_nonneg (Ne.symm hx))

theorem source_population_action_shape (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {U R : ℝ} (hR : 0 < R)
    (hUR : U < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount = 2) :
    ∀ᵐ x ∂(sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)),
      (x.2.bid ≤ U ∧ x.2.routeCount = 2) ∨ (U < x.2.bid ∧ x.2.routeCount = 1) := by
  filter_upwards [source_population_support i m hm hc hR hRt PL hLvalue hLroute] with x hx
  rcases hx with hl | hh
  · exact Or.inl hl.2.2
  · exact Or.inr ⟨hUR.trans_le hh.2.2.2.1, hh.2.2.2.2.2⟩

def sourcePopulationKernel (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) : Kernel ℝ (JointAction 2) :=
  (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)).condKernel

instance sourcePopulationKernel_markov (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    IsMarkovKernel (sourcePopulationKernel i m hc R PL) := by
  unfold sourcePopulationKernel
  infer_instance

theorem source_population_disintegration (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ)) :
    Uniform07.uniformLaw ⊗ₘ sourcePopulationKernel i m hc R PL =
      (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)) := by
  have hmarg := source_population_value_marginal i m hc R PL hLvalue
  change (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)).fst =
    Uniform07.uniformLaw at hmarg
  rw [← hmarg]
  unfold sourcePopulationKernel
  exact Measure.disintegrate _ _

theorem source_population_conditional_support (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {U R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount = 2) :
    ∀ᵐ v ∂Uniform07.uniformLaw, ∀ᵐ a ∂sourcePopulationKernel i m hc R PL v,
      (0 ≤ v ∧ v < Uniform07.cutoff i ∧ a.bid ≤ U ∧ a.routeCount = 2) ∨
      (Uniform07.cutoff i < v ∧ v ≤ 1 ∧ a.bid = sourceUpperBid i m R v ∧
        R ≤ a.bid ∧ a.bid ≤ v ∧ a.routeCount = 1) := by
  apply Measure.ae_ae_of_ae_compProd (p:=fun x : ℝ×JointAction 2 =>
    (0≤x.1 ∧ x.1<Uniform07.cutoff i ∧ x.2.bid≤U ∧ x.2.routeCount=2) ∨
    (Uniform07.cutoff i<x.1 ∧ x.1≤1 ∧ x.2.bid=sourceUpperBid i m R x.1 ∧
      R≤x.2.bid ∧ x.2.bid≤x.1 ∧ x.2.routeCount=1))
  rw [source_population_disintegration i m hc R PL hLvalue]
  exact source_population_support i m hm hc hR hRt PL hLvalue hLroute

def sourcePopulationVersion (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) : Kernel ℝ (JointAction 2) :=
  Kernel.piecewise (show MeasurableSet (Iio (Uniform07.cutoff i)) from measurableSet_Iio)
    (sourcePopulationKernel i m hc R PL)
    (Kernel.deterministic (Hybrid.upperAction (sourceUpperBid i m R))
      (Hybrid.measurable_upperAction _ (sourceUpperBid_measurable i m hc R)))

instance sourcePopulationVersion_markov (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) :
    IsMarkovKernel (sourcePopulationVersion i m hc R PL) := by
  unfold sourcePopulationVersion
  infer_instance

theorem sourcePopulationVersion_lower (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) {v : ℝ} (hv : v < Uniform07.cutoff i) :
    sourcePopulationVersion i m hc R PL v = sourcePopulationKernel i m hc R PL v := by
  simp only [sourcePopulationVersion, Kernel.piecewise_apply, mem_Iio, if_pos hv]

theorem sourcePopulationVersion_upper (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (R : ℝ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) {v : ℝ} (hv : Uniform07.cutoff i ≤ v) :
    sourcePopulationVersion i m hc R PL v =
      Measure.dirac (Hybrid.upperAction (sourceUpperBid i m R) v) := by
  simp only [sourcePopulationVersion, Kernel.piecewise_apply, mem_Iio,
    if_neg (not_lt_of_ge hv), Kernel.deterministic_apply]

private theorem jointAction_eq_upperAction (a : JointAction 2) (b : ℝ → ℝ) (v : ℝ)
    (hb : 0 ≤ b v) (hbid : a.bid = b v) (hroute : a.routeCount = 1) :
    a = Hybrid.upperAction b v := by
  rcases a with ⟨ab, hab, ar, har⟩
  change ab = b v at hbid
  change ar = 1 at hroute
  subst ab
  subst ar
  simp only [Hybrid.upperAction, max_eq_left hb]

theorem source_population_version_ae (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {U R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount = 2) :
    sourcePopulationVersion i m hc R PL =ᵐ[Uniform07.uniformLaw]
      sourcePopulationKernel i m hc R PL := by
  filter_upwards [source_population_conditional_support i m hm hc hR hRt PL hLvalue hLroute]
    with v hv
  by_cases hvt : v < Uniform07.cutoff i
  · exact sourcePopulationVersion_lower i m hc R PL hvt
  · have htv := le_of_not_gt hvt
    have hb : 0 ≤ sourceUpperBid i m R v :=
      hR.le.trans ((source_upper_envelope i m hm hc hR hRt).bid_bounds v htv).1
    have ha : ∀ᵐ a ∂sourcePopulationKernel i m hc R PL v,
        a = Hybrid.upperAction (sourceUpperBid i m R) v := by
      filter_upwards [hv] with a ha
      rcases ha with hl | hh
      · exact (hvt hl.2.1).elim
      · exact jointAction_eq_upperAction a _ v hb hh.2.2.1 hh.2.2.2.2.2
    have he := (Measure.map_congr ha :
      (sourcePopulationKernel i m hc R PL v).map (id : JointAction 2 → JointAction 2) =
      (sourcePopulationKernel i m hc R PL v).map
        (fun _ => Hybrid.upperAction (sourceUpperBid i m R) v))
    simp only [Measure.map_id, Measure.map_const, measure_univ, one_smul] at he
    rw [sourcePopulationVersion_upper i m hc R PL htv, he]

theorem source_population_version_disintegration (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m)
    (hc : 1 ≤ Uniform07.capacity m) {U R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw i : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount = 2) :
    Uniform07.uniformLaw ⊗ₘ sourcePopulationVersion i m hc R PL =
      (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2)) := by
  rw [Measure.compProd_congr (source_population_version_ae i m hm hc hR hRt PL hLvalue hLroute)]
  exact source_population_disintegration i m hc R PL hLvalue

theorem source_population_visible_atomless {Seed : Type*} [MeasurableSpace Seed]
    (i : Uniform07.Row) (m : ℕ) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R : ℝ} (hR : 0 < R) (hRt : R < Uniform07.cutoff i)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLatom : ∀ y : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = y} = 0)
    (Γ : FiniteGame m 2 (Uniform07.capacity m) Seed)
    (hΓ : Γ.F ⊗ₘ Γ.σ = (sourcePopulation i m hc R PL : Measure (ℝ × JointAction 2))) :
    VisibleAtomless Γ := by
  letI : NullSingletonClass (submittedBidMeasure Γ) := by
    unfold submittedBidMeasure
    rw [hΓ]
    exact source_population_bid_atomless i m hm hc hR hRt PL hLatom
  exact visibleAtomless_of_submitted Γ

end FCAppendix.Affine.Uniform07Finishing
