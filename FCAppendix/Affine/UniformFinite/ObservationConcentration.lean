import FCAppendix.Affine.UniformFinite.SourceGuards
import FCAppendix.Probability.EmpiricalConcentration
import FCAppendix.Probability.EmpiricalMean

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Source
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators
open Uniform05

abbrev Observation (i : Row) := (ℝ × Bid i) ⊕ Fin 2

instance observationMeasurableSingleton (i : Row) : MeasurableSingletonClass (Observation i) := by
  constructor
  rintro (p | j)
  · simpa only [Set.image_singleton] using
      ((measurableSet_singleton p).inl_image :
        MeasurableSet (Sum.inl '' ({p} : Set (ℝ × Bid i)) : Set (Observation i)))
  · simpa only [Set.image_singleton] using
      ((measurableSet_singleton j).inr_image :
        MeasurableSet (Sum.inr '' ({j} : Set (Fin 2)) : Set (Observation i)))

def lowerObservationLaw (i : Row) (G : RestrictedLaw i) : Measure (Observation i) :=
  (G.1 : Measure (ℝ × Bid i)).map Sum.inl

instance lowerObservationLaw_probability (i : Row) (G : RestrictedLaw i) :
    IsProbabilityMeasure (lowerObservationLaw i G) :=
  Measure.isProbabilityMeasure_map measurable_inl.aemeasurable

def observationLaw (i : Row) (G : RestrictedLaw i) : Measure (Observation i) :=
  ENNReal.ofReal (t i) • lowerObservationLaw i G +
    ENNReal.ofReal ((1-t i)/2) • Measure.dirac (Sum.inr 0) +
    ENNReal.ofReal ((1-t i)/2) • Measure.dirac (Sum.inr 1)

instance observationLaw_probability (i : Row) (G : RestrictedLaw i) :
    IsProbabilityMeasure (observationLaw i G) := by
  constructor
  have ht := (t_pos i).le
  have hu : 0 ≤ (1-t i)/2 := by linarith [t_lt_one i]
  simp only [observationLaw, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ht hu, ← ENNReal.ofReal_add (by positivity) hu]
  convert! ENNReal.ofReal_one using 1
  congr 1
  ring

def fullObservationLaw {U : Type*} [MeasurableSpace U]
    (i : Row) (G : RestrictedLaw i) (upper : ProbabilityMeasure U) :
    Measure ((ℝ × Bid i) ⊕ (U × Fin 2)) :=
  ENNReal.ofReal (t i) • (G.1 : Measure (ℝ × Bid i)).map Sum.inl +
    ENNReal.ofReal ((1-t i)/2) •
      (upper : Measure U).map (fun u => Sum.inr (u,0)) +
    ENNReal.ofReal ((1-t i)/2) •
      (upper : Measure U).map (fun u => Sum.inr (u,1))

def collapseUpper {U : Type*} (i : Row) :
    ((ℝ × Bid i) ⊕ (U × Fin 2)) → Observation i :=
  Sum.elim Sum.inl (fun p => Sum.inr p.2)

theorem measurable_collapseUpper {U : Type*} [MeasurableSpace U] (i : Row) :
    Measurable (collapseUpper (U := U) i) :=
  measurable_inl.sumElim (measurable_inr.comp measurable_snd)

theorem observationLaw_projection {U : Type*} [MeasurableSpace U]
    (i : Row) (G : RestrictedLaw i) (upper : ProbabilityMeasure U) :
    (fullObservationLaw i G upper).map (collapseUpper i) = observationLaw i G := by
  have hc := measurable_collapseUpper (U := U) i
  have hu0 : Measurable (fun u : U =>
      (Sum.inr (u,(0 : Fin 2)) : (ℝ × Bid i) ⊕ (U × Fin 2))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  have hu1 : Measurable (fun u : U =>
      (Sum.inr (u,(1 : Fin 2)) : (ℝ × Bid i) ⊕ (U × Fin 2))) :=
    measurable_inr.comp (measurable_id.prodMk measurable_const)
  rw [fullObservationLaw, Measure.map_add _ _ hc, Measure.map_add _ _ hc,
    Measure.map_smul, Measure.map_smul, Measure.map_smul,
    Measure.map_map hc measurable_inl, Measure.map_map hc hu0, Measure.map_map hc hu1]
  simp only [collapseUpper, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    Measure.map_const, measure_univ, one_smul, observationLaw, lowerObservationLaw]

theorem integral_observationLaw (i : Row) (G : RestrictedLaw i)
    {f : Observation i → ℝ} (hf : Measurable f)
    (hb : ∀ x, f x ∈ Icc (0 : ℝ) 1) :
    (∫ x, f x ∂observationLaw i G) =
      t i * (∫ p : ℝ × Bid i, f (Sum.inl p) ∂(G.1 : Measure (ℝ × Bid i))) +
        ((1-t i)/2) * f (Sum.inr 0) + ((1-t i)/2) * f (Sum.inr 1) := by
  have hl : Integrable f (lowerObservationLaw i G) :=
    integrable_of_unit_bounds _ hf (fun x => (hb x).1) (fun x => (hb x).2)
  have h0 : Integrable f (Measure.dirac (Sum.inr (0 : Fin 2))) :=
    integrable_dirac (by finiteness)
  have h1 : Integrable f (Measure.dirac (Sum.inr (1 : Fin 2))) :=
    integrable_dirac (by finiteness)
  have ht := (t_pos i).le
  have hu : 0 ≤ (1-t i)/2 := by linarith [t_lt_one i]
  rw [observationLaw, integral_add_measure
    ((hl.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h0.smul_measure ENNReal.ofReal_ne_top))
    (h1.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (hl.smul_measure ENNReal.ofReal_ne_top)
      (h0.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal ht,
    ENNReal.toReal_ofReal hu, lowerObservationLaw,
    integral_map measurable_inl.aemeasurable hf.aestronglyMeasurable]
  rfl

def lowerExtension (i : Row) (f : Bid i → ℝ) : Observation i → ℝ :=
  Sum.elim (fun p => f p.2) (fun _ => 0)

theorem measurable_lowerExtension (i : Row) {f : Bid i → ℝ} (hf : Measurable f) :
    Measurable (lowerExtension i f) :=
  (hf.comp measurable_snd).sumElim measurable_const

theorem lowerExtension_bounds (i : Row) {f : Bid i → ℝ}
    (hf : ∀ b, f b ∈ Icc (0 : ℝ) 1) :
    ∀ x, lowerExtension i f x ∈ Icc (0 : ℝ) 1 := by
  rintro (p | j)
  · exact hf p.2
  · exact ⟨le_rfl, zero_le_one⟩

theorem integral_lowerExtension (i : Row) (G : RestrictedLaw i)
    {f : Bid i → ℝ} (hf : Measurable f) (hb : ∀ b, f b ∈ Icc (0 : ℝ) 1) :
    (∫ x, lowerExtension i f x ∂observationLaw i G) =
      t i * (∫ b, f b ∂(G.bidLaw : Measure (Bid i))) := by
  rw [integral_observationLaw i G (measurable_lowerExtension i hf)
    (lowerExtension_bounds i hb), G.integral_bidLaw hf.aestronglyMeasurable]
  simp only [lowerExtension, Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero]

def upperIndicator (i : Row) (j : Fin 2) : Observation i → ℝ :=
  Sum.elim (fun _ => 0) (fun k => if k = j then 1 else 0)

theorem measurable_upperIndicator (i : Row) (j : Fin 2) :
    Measurable (upperIndicator i j) :=
  measurable_const.sumElim (measurable_of_countable _)

theorem upperIndicator_bounds (i : Row) (j : Fin 2) (x : Observation i) :
    upperIndicator i j x ∈ Icc (0 : ℝ) 1 := by
  rcases x with p | k
  · exact ⟨le_rfl, zero_le_one⟩
  · dsimp [upperIndicator]
    split_ifs <;> norm_num

theorem integral_upperIndicator (i : Row) (G : RestrictedLaw i) (j : Fin 2) :
    (∫ x, upperIndicator i j x ∂observationLaw i G) = (1-t i)/2 := by
  rw [integral_observationLaw i G (measurable_upperIndicator i j)
    (upperIndicator_bounds i j)]
  fin_cases j <;> simp [upperIndicator]

def seedIndicator (i : Row) (b : Bid i) : ℝ := if (b : ℝ) ≤ t i/2 then 1 else 0

theorem measurable_seedIndicator (i : Row) : Measurable (seedIndicator i) :=
  Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    measurable_const measurable_const

theorem seedIndicator_bounds (i : Row) (b : Bid i) :
    seedIndicator i b ∈ Icc (0 : ℝ) 1 := by
  unfold seedIndicator
  split_ifs <;> norm_num

def sourceStatistic (i : Row) (G : RestrictedLaw i) : Fin 8 → Observation i → ℝ :=
  ![lowerExtension i (fun b => exposure (xi i) (rootLo i G) b),
    lowerExtension i (fun b => exposure (xi i) (rootHi i G) b),
    lowerExtension i (fun b => lawWeight i G b),
    lowerExtension i (fun b => rejectionExposure (rejectionScale i) G.rejectionRoot b),
    lowerExtension i (fun _ => 1), upperIndicator i 0, upperIndicator i 1,
    lowerExtension i (seedIndicator i)]

theorem measurable_sourceStatistic (i : Row) (G : RestrictedLaw i) (k : Fin 8) :
    Measurable (sourceStatistic i G k) := by
  fin_cases k
  · exact measurable_lowerExtension i
      ((continuous_exposure (xi_range i).1 (rootBounds i G).1).comp
        continuous_subtype_val).measurable
  · exact measurable_lowerExtension i
      ((continuous_exposure (xi_range i).1
        ((rootBounds i G).1.trans (rootBounds i G).2.1)).comp continuous_subtype_val).measurable
  · exact measurable_lowerExtension i
      ((continuous_lawWeight_bid i G).comp continuous_subtype_val).measurable
  · exact measurable_lowerExtension i
      ((continuous_rejectionExposure (rejectionScale_pos i)).comp
        (continuous_const.prodMk continuous_subtype_val)).measurable
  · exact measurable_lowerExtension i measurable_const
  · exact measurable_upperIndicator i 0
  · exact measurable_upperIndicator i 1
  · exact measurable_lowerExtension i (measurable_seedIndicator i)

theorem sourceStatistic_bounds (i : Row) (G : RestrictedLaw i) (k : Fin 8) :
    ∀ x, sourceStatistic i G k x ∈ Icc (0 : ℝ) 1 := by
  fin_cases k
  · exact lowerExtension_bounds i (fun _ =>
      ⟨exposure_nonneg (xi_range i).1 (rootBounds i G).1, exposure_le_one _ _ _⟩)
  · exact lowerExtension_bounds i (fun _ =>
      ⟨exposure_nonneg (xi_range i).1
        ((rootBounds i G).1.trans (rootBounds i G).2.1), exposure_le_one _ _ _⟩)
  · exact lowerExtension_bounds i (fun b => lawWeight_range i G b)
  · exact lowerExtension_bounds i (fun _ =>
      ⟨rejectionExposure_nonneg (rejectionScale_pos i),
        rejectionExposure_le_one (rejectionScale_pos i)⟩)
  · exact lowerExtension_bounds i (fun _ => ⟨zero_le_one, le_rfl⟩)
  · exact upperIndicator_bounds i 0
  · exact upperIndicator_bounds i 1
  · exact lowerExtension_bounds i (seedIndicator_bounds i)

def sourceMean (i : Row) (G : RestrictedLaw i) : Fin 8 → ℝ :=
  ![t i*lawDemand i G.bidLaw (rootLo i G),
    t i*lawDemand i G.bidLaw (rootHi i G),
    t i*(∫ b : Bid i, lawWeight i G b ∂(G.bidLaw : Measure (Bid i))),
    3*meanResidual i, t i, (1-t i)/2, (1-t i)/2,
    t i*(G.bidLaw : Measure (Bid i)).real {b | (b : ℝ) ≤ t i/2}]

theorem sourceStatistic_mean (i : Row) (G : RestrictedLaw i) (k : Fin 8) :
    (∫ x, sourceStatistic i G k x ∂observationLaw i G) = sourceMean i G k := by
  have hLo := (rootBounds i G).1
  have hHi := hLo.trans (rootBounds i G).2.1
  fin_cases k
  · exact integral_lowerExtension i G
      ((continuous_exposure (xi_range i).1 hLo).comp continuous_subtype_val).measurable
      (fun _ => ⟨exposure_nonneg (xi_range i).1 hLo, exposure_le_one _ _ _⟩)
  · exact integral_lowerExtension i G
      ((continuous_exposure (xi_range i).1 hHi).comp continuous_subtype_val).measurable
      (fun _ => ⟨exposure_nonneg (xi_range i).1 hHi, exposure_le_one _ _ _⟩)
  · exact integral_lowerExtension i G
      ((continuous_lawWeight_bid i G).comp continuous_subtype_val).measurable
      (fun b => lawWeight_range i G b)
  · have h := integral_lowerExtension i G
      (f := fun b : Bid i => rejectionExposure (rejectionScale i) G.rejectionRoot b)
      (((continuous_rejectionExposure (rejectionScale_pos i)).comp
        (continuous_const.prodMk continuous_subtype_val)).measurable)
      (fun _ => ⟨rejectionExposure_nonneg (rejectionScale_pos i),
        rejectionExposure_le_one (rejectionScale_pos i)⟩)
    change (∫ x, sourceStatistic i G 3 x ∂observationLaw i G) =
      t i*lawRejection i G.bidLaw G.rejectionRoot at h
    rw [G.rejectionRoot_equation] at h
    change (∫ x, sourceStatistic i G 3 x ∂observationLaw i G) = 3*meanResidual i
    unfold meanResidual
    linarith
  · have h := integral_lowerExtension i G measurable_const
      (fun _ => (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one,le_rfl⟩))
    simpa [sourceStatistic, sourceMean] using h
  · exact integral_upperIndicator i G 0
  · exact integral_upperIndicator i G 1
  · have h := integral_lowerExtension i G (measurable_seedIndicator i)
      (seedIndicator_bounds i)
    have hind : (∫ b : Bid i, seedIndicator i b ∂(G.bidLaw : Measure (Bid i))) =
        (G.bidLaw : Measure (Bid i)).real {b | (b : ℝ) ≤ t i/2} := by
      exact integral_indicator_one
        (measurableSet_le measurable_subtype_coe measurable_const)
    change (∫ x, lowerExtension i (seedIndicator i) x ∂observationLaw i G) = _
    change (∫ x, lowerExtension i (seedIndicator i) x ∂observationLaw i G) =
      t i*(G.bidLaw : Measure (Bid i)).real {b | (b : ℝ) ≤ t i/2}
    simpa only [hind] using h

theorem sourceMean_bounds (i : Row) (G : RestrictedLaw i) (k : Fin 8) :
    sourceMean i G k ∈ Icc (0 : ℝ) 1 := by
  rw [← sourceStatistic_mean i G k]
  have hi := integrable_of_unit_bounds (observationLaw i G)
    (measurable_sourceStatistic i G k) (fun x => (sourceStatistic_bounds i G k x).1)
    (fun x => (sourceStatistic_bounds i G k x).2)
  refine ⟨integral_nonneg (fun x => (sourceStatistic_bounds i G k x).1), ?_⟩
  have hh := integral_mono hi (integrable_const (1 : ℝ))
    (fun x => (sourceStatistic_bounds i G k x).2)
  simpa using hh

theorem sourceMean_guard_bounds (i : Row) (G : RestrictedLaw i) :
    meanResidual i+demandMargin i ≤ sourceMean i G 0 ∧
    sourceMean i G 1 ≤ meanResidual i-demandMargin i ∧
    weightMargin i ≤ sourceMean i G 2 ∧
    sourceMean i G 3 = 3*meanResidual i ∧
    t i/2 ≤ sourceMean i G 7 := by
  have hd := shifted_lawDemand_slack i G
  have hw := mul_le_mul_of_nonneg_left (mean_lawWeight_lower i G) (t_pos i).le
  have hs := G.seed_mass_lower
  have hsR : (1 : ℝ)/2 ≤
      (G.bidLaw : Measure (Bid i)).real {b | (b : ℝ) ≤ t i/2} := by
    have h := ENNReal.toReal_mono (measure_ne_top (G.bidLaw : Measure (Bid i)) _) hs
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2)] at h
    simpa [Measure.real, div_eq_mul_inv, mul_comm] using h
  refine ⟨?_, ?_, hw, rfl, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hd.1 (t_pos i).le
    simpa only [sourceMean, Matrix.cons_val_zero, meanResidual, demandMargin,
      rootLo, mul_add] using h
  · have h := mul_le_mul_of_nonneg_left hd.2 (t_pos i).le
    change t i*lawDemand i G.bidLaw (rootHi i G) ≤ meanResidual i-demandMargin i
    simpa only [meanResidual, demandMargin, rootHi, mul_sub] using h
  · have h := mul_le_mul_of_nonneg_left hsR (t_pos i).le
    change t i/2 ≤ t i*(G.bidLaw : Measure (Bid i)).real {b | (b : ℝ) ≤ t i/2}
    simpa only [mul_one_div] using h

def observationKind (i : Row) : Observation i → Fin 3 :=
  Sum.elim (fun _ => 0) (fun j => if j = 0 then 1 else 2)

def observationBid (i : Row) : Observation i → ℝ :=
  Sum.elim (fun p => (p.2 : ℝ)) (fun _ => 0)

def observationCountRow {M : ℕ} (i : Row) (x : Fin M → Observation i) : CountRow M :=
  countRowOfKind (fun a => observationKind i (x a))

theorem observationBid_cap (i : Row) (x : Observation i) : observationBid i x ≤ cap i := by
  rcases x with p | j
  · exact p.2.2.2
  · exact (cap_pos i).le

theorem lowerBids_observation {M : ℕ} (i : Row) (x : Fin M → Observation i) :
    lowerBids (observationCountRow i x) (fun a => observationBid i (x a)) =
      fun a => observationBid i (x a) := by
  funext a
  rcases h : x a with p | j
  · simp [lowerBids, observationCountRow, countRowOfKind, observationKind, observationBid, h]
  · fin_cases j <;>
      simp [lowerBids, observationCountRow, countRowOfKind, observationKind, observationBid, h]

theorem sourceStatistic_sum {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (x : Fin M → Observation i) :
    (fun k => ∑ a, sourceStatistic i G k (x a)) =
      ![lowDemand i G (observationCountRow i x) (fun a => observationBid i (x a)),
        highDemand i G (observationCountRow i x) (fun a => observationBid i (x a)),
        WeightedSampling.totalWeight
          (sourceWeights i G (observationCountRow i x) (fun a => observationBid i (x a))),
        rejectionSum i G (observationCountRow i x) (fun a => observationBid i (x a)),
        ((observationCountRow i x).lower.card : ℝ),
        ((observationCountRow i x).upper0 : ℝ),
        ((observationCountRow i x).upper1 : ℝ),
        (seedCount i (observationCountRow i x) (fun a => observationBid i (x a)) : ℝ)] := by
  classical
  have hLo := (rootBounds i G).1
  have hHi := hLo.trans (rootBounds i G).2.1
  have hZ : 0 < G.rejectionRoot := (rejectionLo_pos i).trans G.rejectionRoot_guards.1
  funext k
  fin_cases k
  all_goals
    simp only [sourceStatistic,
      lowDemand, highDemand, rejectionSum, WeightedSampling.totalWeight,
      Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
      seedCount, observationCountRow, countRowOfKind]
    apply Finset.sum_congr rfl
    intro a _
    rcases h : x a with p | j
    · simp [sourceWeights, lowerBids, observationKind, observationBid, lowerExtension,
        upperIndicator, seedIndicator, h]
    · fin_cases j <;>
        simp [sourceWeights, lowerBids, observationKind, observationBid, lowerExtension,
          upperIndicator, seedIndicator, h, exposure_zero hLo.le, exposure_zero hHi.le,
          rejectionExposure_zero hZ.le]

theorem sourceStatistic_deviation_le (i : Row) (G : RestrictedLaw i)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => observationLaw i G)).real
      {x | ∃ k : Fin 8,
        ε ≤ |(∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k|} ≤
      16*Real.exp (-2*(N : ℝ)*ε^2) := by
  let E : Fin 8 → Set (Fin N → Observation i) := fun k =>
    {x | ε ≤ |(∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k|}
  have hE (k : Fin 8) :
      (Measure.pi (fun _ : Fin N => observationLaw i G)).real (E k) ≤
        2*Real.exp (-2*(N : ℝ)*ε^2) := by
    have h := Probability.iid_empiricalMean_two_sided_le (observationLaw i G)
      (measurable_sourceStatistic i G k).aemeasurable
      (Eventually.of_forall (sourceStatistic_bounds i G k)) N hN hε
    simpa only [sourceStatistic_mean, E] using h
  have heq : {x : Fin N → Observation i | ∃ k : Fin 8,
      ε ≤ |(∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k|} = ⋃ k, E k := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, E]
  rw [heq]
  calc
    _ ≤ ∑ k : Fin 8, (Measure.pi (fun _ : Fin N => observationLaw i G)).real (E k) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _k : Fin 8, 2*Real.exp (-2*(N : ℝ)*ε^2) := Finset.sum_le_sum (fun k _ => hE k)
    _ = _ := by simp; ring

def prepend {α : Type*} {N : ℕ} : {K : ℕ} → (Fin K → α) →
    (Fin N → α) → Fin (N+K) → α
  | 0, _, x => x
  | _+1, p, x => Fin.cons (p 0) (prepend (fun a => p a.succ) x)

theorem measurable_prepend {α : Type*} [MeasurableSpace α] {N K : ℕ}
    (p : Fin K → α) : Measurable (fun x : Fin N → α => prepend p x) := by
  induction K with
  | zero => exact measurable_id
  | succ K ih =>
      apply measurable_pi_lambda
      intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · exact measurable_const
      · exact (measurable_pi_apply a).comp (ih (fun a => p a.succ))

theorem sum_prepend {α : Type*} {N K : ℕ} (f : α → ℝ)
    (p : Fin K → α) (x : Fin N → α) :
    (∑ a, f (prepend p x a)) = (∑ a, f (p a)) + ∑ a, f (x a) := by
  induction K with
  | zero => simp [prepend]
  | succ K ih =>
      change (∑ a : Fin (N+K+1), f ((Fin.cons (p 0) (prepend (fun a => p a.succ) x) : Fin (N+K+1) → α) a)) = _
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      change f (p 0) + (∑ a, f (prepend (fun a => p a.succ) x a)) = _
      rw [ih]
      ring

theorem fixed_sourceStatistic_offset {K : ℕ} (i : Row) (G : RestrictedLaw i)
    (p : Fin K → Observation i) (k : Fin 8) :
    |(∑ a, sourceStatistic i G k (p a))-(K : ℝ)*sourceMean i G k| ≤ K := by
  have hμ := sourceMean_bounds i G k
  have h0 : 0 ≤ ∑ a, sourceStatistic i G k (p a) :=
    Finset.sum_nonneg (fun a _ => (sourceStatistic_bounds i G k (p a)).1)
  have h1 : (∑ a, sourceStatistic i G k (p a)) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _a : Fin K, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => (sourceStatistic_bounds i G k (p a)).2)
      _ = K := by simp
  rw [abs_le]
  constructor <;> nlinarith [hμ.1, hμ.2, show (0 : ℝ) ≤ K from Nat.cast_nonneg K]

theorem fixed_sourceStatistic_deviation_le {K : ℕ}
    (i : Row) (G : RestrictedLaw i) (p : Fin K → Observation i)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε)
    (hroom : (K : ℝ) ≤ N*ε/2) :
    (Measure.pi (fun _ : Fin N => observationLaw i G)).real
      {x | ∃ k : Fin 8,
        ε ≤ |(∑ a, sourceStatistic i G k (prepend p x a))/(N+K : ℕ)-sourceMean i G k|} ≤
      16*Real.exp (-(N : ℝ)*ε^2/2) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNK : 0 < ((N+K : ℕ) : ℝ) := by exact_mod_cast (show 0 < N+K by omega)
  have hh := sourceStatistic_deviation_le i G N hN (show 0 ≤ ε/2 by positivity)
  have hsub : {x : Fin N → Observation i | ∃ k : Fin 8,
      ε ≤ |(∑ a, sourceStatistic i G k (prepend p x a))/(N+K : ℕ)-sourceMean i G k|} ⊆
      {x | ∃ k : Fin 8,
        ε/2 ≤ |(∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k|} := by
    rintro x ⟨k,hk⟩
    refine ⟨k, ?_⟩
    rw [sum_prepend] at hk
    have ho := fixed_sourceStatistic_offset i G p k
    have hab := abs_add_le
      ((∑ a, sourceStatistic i G k (x a))-(N : ℝ)*sourceMean i G k)
      ((∑ a, sourceStatistic i G k (p a))-(K : ℝ)*sourceMean i G k)
    have he : (∑ a, sourceStatistic i G k (x a))-(N : ℝ)*sourceMean i G k+
        ((∑ a, sourceStatistic i G k (p a))-(K : ℝ)*sourceMean i G k) =
        (∑ a, sourceStatistic i G k (p a))+(∑ a, sourceStatistic i G k (x a))-
          (N+K : ℕ)*sourceMean i G k := by push_cast; ring
    rw [he] at hab
    have hnorm :
        |((∑ a, sourceStatistic i G k (p a))+(∑ a, sourceStatistic i G k (x a)))/
            (N+K : ℕ)-sourceMean i G k| =
        |(∑ a, sourceStatistic i G k (p a))+(∑ a, sourceStatistic i G k (x a))-
            (N+K : ℕ)*sourceMean i G k| / (N+K : ℕ) := by
      calc
        _ = |((∑ a, sourceStatistic i G k (p a))+(∑ a, sourceStatistic i G k (x a))-
            (N+K : ℕ)*sourceMean i G k)/(N+K : ℕ)| := by
          congr 1
          field_simp [hNK.ne']
        _ = _ := by rw [abs_div, abs_of_pos hNK]
    rw [hnorm] at hk
    have hk' := (le_div_iff₀ hNK).mp hk
    have hdev : |(∑ a, sourceStatistic i G k (x a))-(N : ℝ)*sourceMean i G k| =
        N*|(∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k| := by
      calc
        _ = |(N : ℝ)*((∑ a, sourceStatistic i G k (x a))/(N : ℝ)-sourceMean i G k)| := by
          congr 1
          field_simp [hNr.ne']
        _ = _ := by rw [abs_mul, abs_of_pos hNr]
    rw [hdev] at hab
    have hKε := mul_nonneg (show (0 : ℝ) ≤ K from Nat.cast_nonneg K) hε
    push_cast at hk' hab
    nlinarith
  have hm := measureReal_mono (μ := Measure.pi (fun _ : Fin N => observationLaw i G)) hsub
  have hexp : -2*(N : ℝ)*(ε/2)^2 = -(N : ℝ)*ε^2/2 := by ring
  rw [hexp] at hh
  exact hm.trans hh

theorem sourceStatistic_control_guardAlpha_one {M : ℕ}
    (i : Row) (G : RestrictedLaw i) (x : Fin M → Observation i) (hM : 0 < M)
    (hc : |(Uniform07.capacity M : ℝ)/M-rho| ≤ commonGuardMargin i)
    (hx : ∀ k : Fin 8,
      |(∑ a, sourceStatistic i G k (x a))/(M : ℝ)-sourceMean i G k| ≤ commonGuardMargin i) :
    guardAlpha i G (observationCountRow i x) (fun a => observationBid i (x a)) = 1 := by
  let row := observationCountRow i x
  let b := fun a => observationBid i (x a)
  have hs := sourceStatistic_sum i G x
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have h3 := hx 3
  have h4 := hx 4
  have h5 := hx 5
  have h6 := hx 6
  have h7 := hx 7
  rw [congrFun hs 0] at h0
  rw [congrFun hs 1] at h1
  rw [congrFun hs 2] at h2
  rw [congrFun hs 3] at h3
  rw [congrFun hs 4] at h4
  rw [congrFun hs 5] at h5
  rw [congrFun hs 6] at h6
  rw [congrFun hs 7] at h7
  have hseed : 0 < seedCount i row b := by
    have hμ := (sourceMean_guard_bounds i G).2.2.2.2
    have he := count_margin i
    have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
    have hseedR : 0 < (seedCount i row b : ℝ)/M := by
      have hp := (abs_le.mp h7).1
      change -commonGuardMargin i ≤ (seedCount i row b : ℝ)/M-sourceMean i G 7 at hp
      linarith [t_pos i]
    have hz : 0 < (seedCount i row b : ℝ) := (div_pos_iff_of_pos_right hMr).mp hseedR
    exact_mod_cast hz
  exact empirical_control_guardAlpha_one i G row b hM hc h4 h5 h6 h0 h1 h2 h3 hseed

theorem fixed_guard_failure_le {K : ℕ}
    (i : Row) (G : RestrictedLaw i) (p : Fin K → Observation i)
    (N : ℕ) (hN : 0 < N)
    (hc : |(Uniform07.capacity (N+K) : ℝ)/(N+K : ℕ)-rho| ≤ commonGuardMargin i)
    (hroom : (K : ℝ) ≤ N*commonGuardMargin i/2) :
    (Measure.pi (fun _ : Fin N => observationLaw i G)).real
      {x | guardAlpha i G (observationCountRow i (prepend p x))
        (fun a => observationBid i (prepend p x a)) ≠ 1} ≤
      16*Real.exp (-(N : ℝ)*(commonGuardMargin i)^2/2) := by
  have hb := fixed_sourceStatistic_deviation_le i G p N hN
    (common_guard_margin i).le hroom
  apply le_trans (measureReal_mono ?_) hb
  intro x hx
  by_contra hn
  apply hx
  apply sourceStatistic_control_guardAlpha_one i G (prepend p x) (by omega) hc
  intro k
  exact (lt_of_not_ge (fun hk => hn ⟨k, hk⟩)).le

theorem capacity_error_le (M : ℕ) (hM : 0 < M) :
    |(Uniform07.capacity M : ℝ)/M-rho| ≤ 1/(M : ℝ) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdiv := Nat.mod_add_div (999*M) 2000
  have hmod := Nat.mod_lt (999*M) (by norm_num : 0 < 2000)
  have hu : 2000*Uniform07.capacity M ≤ 999*M := by
    dsimp [Uniform07.capacity]
    omega
  have hl : 999*M < 2000*(Uniform07.capacity M+1) := by
    dsimp [Uniform07.capacity]
    omega
  have huR : (2000 : ℝ)*(Uniform07.capacity M : ℝ) ≤ 999*(M : ℝ) := by exact_mod_cast hu
  have hlR : (999 : ℝ)*(M : ℝ) < 2000*((Uniform07.capacity M : ℝ)+1) := by exact_mod_cast hl
  have hcu : (Uniform07.capacity M : ℝ)/M ≤ rho := by
    apply (div_le_iff₀ hMr).mpr
    dsimp [rho]
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hcu), neg_sub]
  apply (le_div_iff₀ hMr).mpr
  have hcancel : ((Uniform07.capacity M : ℝ)/M)*M = Uniform07.capacity M :=
    div_mul_cancel₀ _ hMr.ne'
  dsimp [rho]
  nlinarith

theorem fixed_guard_failure_le_of_size {K : ℕ}
    (i : Row) (G : RestrictedLaw i) (p : Fin K → Observation i)
    (N : ℕ) (hN : 0 < N)
    (hsize : 1/((N+K : ℕ) : ℝ) ≤ commonGuardMargin i)
    (hroom : (K : ℝ) ≤ N*commonGuardMargin i/2) :
    (Measure.pi (fun _ : Fin N => observationLaw i G)).real
      {x | guardAlpha i G (observationCountRow i (prepend p x))
        (fun a => observationBid i (prepend p x a)) ≠ 1} ≤
      16*Real.exp (-(N : ℝ)*(commonGuardMargin i)^2/2) :=
  fixed_guard_failure_le i G p N hN ((capacity_error_le (N+K) (by omega)).trans hsize) hroom

def upperSign (i : Row) (x : Observation i) : ℝ :=
  upperIndicator i 0 x-upperIndicator i 1 x

theorem measurable_upperSign (i : Row) : Measurable (upperSign i) :=
  (measurable_upperIndicator i 0).sub (measurable_upperIndicator i 1)

theorem upperSign_bound (i : Row) (x : Observation i) : |upperSign i x| ≤ 1 := by
  rcases x with p | j
  · norm_num [upperSign, upperIndicator]
  · fin_cases j <;> norm_num [upperSign, upperIndicator]

theorem upperSign_mean (i : Row) (G : RestrictedLaw i) :
    (∫ x, upperSign i x ∂observationLaw i G) = 0 := by
  have h0 := integrable_of_unit_bounds (observationLaw i G)
    (measurable_upperIndicator i 0) (fun x => (upperIndicator_bounds i 0 x).1)
    (fun x => (upperIndicator_bounds i 0 x).2)
  have h1 := integrable_of_unit_bounds (observationLaw i G)
    (measurable_upperIndicator i 1) (fun x => (upperIndicator_bounds i 1 x).1)
    (fun x => (upperIndicator_bounds i 1 x).2)
  change (∫ x, upperIndicator i 0 x-upperIndicator i 1 x ∂observationLaw i G) = 0
  rw [integral_sub h0 h1, integral_upperIndicator, integral_upperIndicator, sub_self]

theorem upperCountDifference_sum {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (x : Fin M → Observation i) :
    (∑ a, upperSign i (x a)) =
      ((observationCountRow i x).upper0 : ℝ)-(observationCountRow i x).upper1 := by
  have h0 := congrFun (sourceStatistic_sum i G x) 5
  have h1 := congrFun (sourceStatistic_sum i G x) 6
  change (∑ a, upperIndicator i 0 (x a)) = ((observationCountRow i x).upper0 : ℝ) at h0
  change (∑ a, upperIndicator i 1 (x a)) = ((observationCountRow i x).upper1 : ℝ) at h1
  simpa only [upperSign, Finset.sum_sub_distrib] using congrArg₂ (fun a b : ℝ => a-b) h0 h1

theorem integrable_upperSign_sum (i : Row) (G : RestrictedLaw i) (N : ℕ) :
    Integrable (fun x : Fin N → Observation i => ∑ a, upperSign i (x a))
      (Measure.pi (fun _ : Fin N => observationLaw i G)) := by
  apply integrable_finsetSum
  intro a _
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_upperSign i).comp (measurable_pi_apply a)).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using upperSign_bound i (x a))

theorem expected_upperCountDifference_le (i : Row) (G : RestrictedLaw i)
    (N : ℕ) (hN : 0 < N) :
    (∫ x : Fin N → Observation i,
      |((observationCountRow i x).upper0 : ℝ)-(observationCountRow i x).upper1|
      ∂Measure.pi (fun _ : Fin N => observationLaw i G)) ≤ Real.sqrt N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hh := Probability.iid_empiricalMean_L1_le (observationLaw i G)
    (measurable_upperSign i).aestronglyMeasurable (1 : ℝ) (by norm_num)
    (Eventually.of_forall (upperSign_bound i)) N hN
  rw [upperSign_mean] at hh
  simp only [sub_zero] at hh
  have he : (∫ x : Fin N → Observation i,
      |((observationCountRow i x).upper0 : ℝ)-(observationCountRow i x).upper1|
      ∂Measure.pi (fun _ : Fin N => observationLaw i G)) =
      (N : ℝ)*(∫ x : Fin N → Observation i,
        |(∑ a, upperSign i (x a))/(N : ℝ)|
        ∂Measure.pi (fun _ : Fin N => observationLaw i G)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      dsimp only
      rw [← upperCountDifference_sum i G x, abs_div, abs_of_pos hNr]
      field_simp [hNr.ne'])
  rw [he]
  have hmult := mul_le_mul_of_nonneg_left hh hNr.le
  have hratio : (N : ℝ)*(1/Real.sqrt N) = Real.sqrt N := by
    calc
      _ = (N : ℝ)/Real.sqrt N := by ring
      _ = Real.sqrt N := (div_eq_iff hs.ne').2 (by nlinarith [Real.sq_sqrt hNr.le])
  simpa only [hratio] using hmult

theorem fixed_expected_upperCountDifference_le {K : ℕ}
    (i : Row) (G : RestrictedLaw i) (p : Fin K → Observation i)
    (N : ℕ) (hN : 0 < N) :
    (∫ x : Fin N → Observation i,
      |((observationCountRow i (prepend p x)).upper0 : ℝ)-
        (observationCountRow i (prepend p x)).upper1|
      ∂Measure.pi (fun _ : Fin N => observationLaw i G)) ≤ K+Real.sqrt N := by
  have hp : |∑ a, upperSign i (p a)| ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ a, |upperSign i (p a)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin K, (1 : ℝ) := Finset.sum_le_sum (fun a _ => upperSign_bound i (p a))
      _ = K := by simp
  have hi := integrable_upperSign_sum i G N
  have hiF : Integrable (fun x : Fin N → Observation i =>
      |(∑ a, upperSign i (p a))+(∑ a, upperSign i (x a))|)
      (Measure.pi (fun _ : Fin N => observationLaw i G)) :=
    ((integrable_const _).add hi).abs
  have hmono := integral_mono hiF ((integrable_const (K : ℝ)).add hi.abs)
    (fun x => by
      dsimp only [Pi.add_apply]
      have ht := abs_add_le (∑ a, upperSign i (p a)) (∑ a, upperSign i (x a))
      linarith)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (integrable_const (K : ℝ)) hi.abs] at hmono
  simp only [integral_const, probReal_univ, one_smul] at hmono
  have he (x : Fin N → Observation i) :
      |((observationCountRow i (prepend p x)).upper0 : ℝ)-
        (observationCountRow i (prepend p x)).upper1| =
        |(∑ a, upperSign i (p a))+(∑ a, upperSign i (x a))| := by
    rw [← upperCountDifference_sum i G, sum_prepend]
  simp_rw [he]
  apply hmono.trans
  have h := expected_upperCountDifference_le i G N hN
  simp only [← upperCountDifference_sum i G] at h
  linarith

theorem imbalance_le_upperCountDifference {M : ℕ} (row : CountRow M) :
    (imbalance row : ℝ) ≤ |(row.upper0 : ℝ)-row.upper1| := by
  by_cases h : row.upper0 ≤ row.upper1
  · have hn : imbalance row ≤ row.upper1-row.upper0 := by
      dsimp [imbalance, large, small, residual, upperCount]
      omega
    have hR : (row.upper0 : ℝ) ≤ row.upper1 := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hR), neg_sub]
    have hh : (imbalance row : ℝ) ≤ ((row.upper1-row.upper0 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_sub h] using hh
  · have h' : row.upper1 ≤ row.upper0 := le_of_not_ge h
    have hn : imbalance row ≤ row.upper0-row.upper1 := by
      dsimp [imbalance, large, small, residual, upperCount]
      omega
    have hR : (row.upper1 : ℝ) ≤ row.upper0 := by exact_mod_cast h'
    rw [abs_of_nonneg (sub_nonneg.mpr hR)]
    have hh : (imbalance row : ℝ) ≤ ((row.upper0-row.upper1 : ℕ) : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_sub h'] using hh

theorem fixed_expected_imbalance_le {K : ℕ}
    (i : Row) (G : RestrictedLaw i) (p : Fin K → Observation i)
    (N : ℕ) (hN : 0 < N) :
    (∫ x : Fin N → Observation i, (imbalance (observationCountRow i (prepend p x)) : ℝ)
      ∂Measure.pi (fun _ : Fin N => observationLaw i G)) ≤ K+Real.sqrt N := by
  have hi : Integrable (fun x : Fin N → Observation i =>
      |((observationCountRow i (prepend p x)).upper0 : ℝ)-
        (observationCountRow i (prepend p x)).upper1|)
      (Measure.pi (fun _ : Fin N => observationLaw i G)) := by
    simp_rw [← upperCountDifference_sum i G, sum_prepend]
    exact ((integrable_const _).add (integrable_upperSign_sum i G N)).abs
  have hm := integral_mono_of_nonneg
    (Eventually.of_forall (fun x => (Nat.cast_nonneg (imbalance
      (observationCountRow i (prepend p x))) : (0 : ℝ) ≤ _))) hi
    (Eventually.of_forall (fun x => imbalance_le_upperCountDifference
      (observationCountRow i (prepend p x))))
  exact hm.trans (fixed_expected_upperCountDifference_le i G p N hN)

end FCAppendix.Affine.UniformFinite.Source
