import FCAppendix.Affine.Uniform06.EntryGoodVelocity

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySequence
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EntryEarlySourceLimits EntryLiteralResponseGeometry EntryLiteralCanonicalTransfer
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Row)

structure Source where
  value : Ω → ℝ
  bid : ℕ → Ω → ℝ
  value_measurable : Measurable value
  bid_measurable : ∀ m,Measurable (bid m)
  value_law : μ.map value=LowChernoff.conditionalValueLaw i
  admissible : ∀ m,∀ᵐ ω ∂μ,bid m ω≤ value ω
  active : ∀ᵐ ω ∂μ,entry i< value ω → Tendsto (fun m => bid m ω) atTop
    (𝓝 (ActiveGraphComponent.activeBid i (value ω)))
  focal : ℕ → ℝ
  focal_le_cutoff : ∀ m,focal m≤ cutoff i
  focal_tendsto : Tendsto focal atTop (𝓝 (entry i))
  guards : ℕ → LiteralExperiment.GuardData
  multiplier_tendsto : Tendsto (fun m => (guards m).multiplier) atTop (𝓝 (entry i))
  population : ℕ → ℕ
  population_ge_four : ∀ m,4≤ population m
  population_tendsto : Tendsto population atTop atTop
  epsilon : ℝ
  epsilon_pos : 0< epsilon
  stripDensity : ℝ
  lowerPrice : ℝ
  lowerPrice_lt_entry : lowerPrice< entry i
  stripBid : ℕ → ℝ
  demandMargin : ℕ → ℝ
  weightMargin : ℕ → ℝ
  seedMargin : ℕ → ℝ
  cap : ∀ m,∀ᵐ p ∂joint μ value (bid m),p.2≤ ReceiptGap.cap i
  finite : ∀ m,Inputs (RawMixedSource.source i (joint μ value (bid m))) i (guards m)
    (population m-1) (capacity (population m)) (focal m) (stripBid m) (ReceiptGap.cap i)
    epsilon (eligibleMass μ i value/2) stripDensity lowerPrice (demandMargin m)
    (weightMargin m) (seedMargin m)

namespace Source
variable {μ i} (s : Source μ i)

def jointLaw (m : ℕ) : Measure (ℝ × ℝ) := joint μ s.value (s.bid m)
instance jointLaw_probability (m : ℕ) : IsProbabilityMeasure (s.jointLaw m) :=
  Measure.isProbabilityMeasure_map (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable

def rivals (m : ℕ) : ℕ := s.population m-1
def raw (m : ℕ) : Measure RowRival := RawMixedSource.source i (s.jointLaw m)
instance raw_probability (m : ℕ) : IsProbabilityMeasure (s.raw m) := by
  unfold raw
  infer_instance

def law (m : ℕ) : Measure (EntryIIDCentral.Row (Ω := RowRival) (s.rivals m)) :=
  EntryIIDCentral.rowLaw (s.raw m) (s.rivals m)
instance law_probability (m : ℕ) : IsProbabilityMeasure (s.law m) := by
  unfold law
  infer_instance

def response (m : ℕ) : EntryIIDCentral.Row (Ω := RowRival) (s.rivals m) → ℝ :=
  EntryLiteralResponseGeometry.response (s.raw m) i (capacity (s.population m))
    (s.guards m) (s.focal m) (s.stripBid m) (ReceiptGap.cap i) s.epsilon

def success (m : ℕ) : ℝ := (s.law m).real {x | 0< s.response m x}
def first (m : ℕ) : ℝ := canonicalGoodMarginal i (s.jointLaw m) (capacity (s.population m))
  (s.rivals m) (s.guards m) (s.focal m) (s.stripBid m) (ReceiptGap.cap i) s.epsilon

def second (m : ℕ) : ℝ := canonicalGoodDuplicate i (s.jointLaw m) (capacity (s.population m))
  (s.rivals m) (s.guards m) (s.focal m) (s.stripBid m) (ReceiptGap.cap i) s.epsilon

def ratio (m : ℕ) : ℝ := s.first m^2/(s.success m*s.second m)
def conditionalMean (m : ℕ) : ℝ := s.first m/s.success m

def center (m : ℕ) : ℝ := EntryRawCentral.center i (s.jointLaw m) (s.rivals m)
  (capacity (s.population m)) (s.focal m)

omit [IsProbabilityMeasure μ] in
lemma rivals_pos (m : ℕ) : 0< s.rivals m := (s.finite m).rivals_pos
omit [IsProbabilityMeasure μ] in
lemma rivals_tendsto : Tendsto s.rivals atTop atTop :=
  PhysicalRates.rivals_tendsto.comp s.population_tendsto
omit [IsProbabilityMeasure μ] in
lemma focal_pos (m : ℕ) : 0< s.focal m := (s.finite m).lo_pos.trans_le
  ((s.finite m).lower_price.trans (s.finite m).bid_window.1)

lemma canonical_integrals (m : ℕ) :
    (∫ x,s.response m x ∂s.law m)=s.first m ∧
      (∫ x,(s.response m x)^2 ∂s.law m)=s.second m :=
  integrated_canonical_moments i (s.jointLaw m) (s.guards m) (s.finite m) (s.cap m)

omit [IsProbabilityMeasure μ] in
lemma response_measurable (m : ℕ) : Measurable (s.response m) :=
  measurable_response _ _ _ _ _ _ _ _
omit [IsProbabilityMeasure μ] in
lemma response_bounds (m : ℕ) (x : EntryIIDCentral.Row (Ω := RowRival) (s.rivals m)) :
    s.response m x∈Icc (0:ℝ) 1 := EntryLiteralModerate.response_bounds _ _ _ _ _ _ _ _

lemma first_nonneg (m : ℕ) : 0≤ s.first m := by
  rw [← (s.canonical_integrals m).1]
  exact integral_nonneg fun x => (s.response_bounds m x).1
lemma first_le_one (m : ℕ) : s.first m≤1 := by
  rw [← (s.canonical_integrals m).1]
  have hh := integral_mono (Integrable.of_mem_Icc 0 1 (s.response_measurable m).aemeasurable
    (ae_of_all _ (s.response_bounds m))) (integrable_const (μ := s.law m) (1:ℝ))
      (fun x => (s.response_bounds m x).2)
  simpa using hh
lemma second_nonneg (m : ℕ) : 0≤ s.second m := by
  rw [← (s.canonical_integrals m).2]
  exact integral_nonneg fun x => sq_nonneg _

lemma cauchy (m : ℕ) (hP : 0< s.success m) : s.first m^2≤ s.success m*s.second m := by
  have hh := EntryGoodVelocity.conditional_cauchy (s.law m) (s.response m)
    (s.response_measurable m) (s.response_bounds m) hP
  simpa only [success,(s.canonical_integrals m).1,(s.canonical_integrals m).2] using hh

def reindex (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) : Source μ i where
  value := s.value
  bid := fun m => s.bid (φ m)
  value_measurable := s.value_measurable
  bid_measurable := fun m => s.bid_measurable (φ m)
  value_law := s.value_law
  admissible := fun m => s.admissible (φ m)
  active := s.active.mono fun _ hω hv => (hω hv).comp hφ
  focal := s.focal ∘ φ
  focal_le_cutoff := fun m => s.focal_le_cutoff (φ m)
  focal_tendsto := s.focal_tendsto.comp hφ
  guards := s.guards ∘ φ
  multiplier_tendsto := s.multiplier_tendsto.comp hφ
  population := s.population ∘ φ
  population_ge_four := fun m => s.population_ge_four (φ m)
  population_tendsto := s.population_tendsto.comp hφ
  epsilon := s.epsilon
  epsilon_pos := s.epsilon_pos
  stripDensity := s.stripDensity
  lowerPrice := s.lowerPrice
  lowerPrice_lt_entry := s.lowerPrice_lt_entry
  stripBid := s.stripBid ∘ φ
  demandMargin := s.demandMargin ∘ φ
  weightMargin := s.weightMargin ∘ φ
  seedMargin := s.seedMargin ∘ φ
  cap := fun m => s.cap (φ m)
  finite := fun m => s.finite (φ m)

omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_center (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).center m=s.center (φ m) := rfl
omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_first (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).first m=s.first (φ m) := rfl
omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_second (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).second m=s.second (φ m) := rfl
omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_success (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).success m=s.success (φ m) := rfl
omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_ratio (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).ratio m=s.ratio (φ m) := rfl
omit [IsProbabilityMeasure μ] in
@[simp] lemma reindex_conditionalMean (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (m) :
    (s.reindex φ hφ).conditionalMean m=s.conditionalMean (φ m) := rfl

end Source

section Extraction
lemma unbounded_above_tail (f : ℕ → ℝ) (hf : ¬BddAbove (Set.range f)) (M : ℝ) (N : ℕ) :
    ∃ k,N≤ k ∧ M≤ f k := by
  classical
  by_contra hn
  have htail : ∀ k,N≤ k → f k< M := by
    intro k hk
    exact lt_of_not_ge fun hh => hn ⟨k,hk,hh⟩
  apply hf
  refine ⟨max M (∑ j ∈ Finset.range N,|f j|),?_⟩
  rintro _ ⟨k,rfl⟩
  by_cases hk : N≤ k
  · exact (htail k hk).le.trans (le_max_left _ _)
  · have hkN : k∈Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hk)
    have hsum : |f k|≤∑ j ∈ Finset.range N,|f j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (f j)) hkN
    exact ((le_abs_self _).trans hsum).trans (le_max_right _ _)

def aboveIndex (f : ℕ → ℝ) (hf : ¬BddAbove (Set.range f)) : ℕ → ℕ
  | 0 => Classical.choose (unbounded_above_tail f hf 1 0)
  | n+1 => Classical.choose (unbounded_above_tail f hf (((n+1:ℕ):ℝ)+1) (aboveIndex f hf n+1))

lemma aboveIndex_step (f : ℕ → ℝ) (hf : ¬BddAbove (Set.range f)) (n : ℕ) :
    aboveIndex f hf n< aboveIndex f hf (n+1) := by
  exact (Nat.lt_succ_self _).trans_le
    (Classical.choose_spec (unbounded_above_tail f hf (((n+1:ℕ):ℝ)+1) (aboveIndex f hf n+1))).1

lemma aboveIndex_value (f : ℕ → ℝ) (hf : ¬BddAbove (Set.range f)) (n : ℕ) :
    (n:ℝ)+1≤ f (aboveIndex f hf n) := by
  cases n with
  | zero => simpa only [Nat.cast_zero,zero_add,aboveIndex] using
      (Classical.choose_spec (unbounded_above_tail f hf 1 0)).2
  | succ n => exact (Classical.choose_spec
      (unbounded_above_tail f hf (((n+1:ℕ):ℝ)+1) (aboveIndex f hf n+1))).2

lemma unbounded_above_extraction (f : ℕ → ℝ) (hf : ¬BddAbove (Set.range f)) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧ (∀ m,0< f (φ m)) ∧ Tendsto (f ∘ φ) atTop atTop := by
  refine ⟨aboveIndex f hf,strictMono_nat_of_lt_succ (aboveIndex_step f hf),?_,?_⟩
  · intro m
    exact (by positivity : (0:ℝ)<(m:ℝ)+1).trans_le (aboveIndex_value f hf m)
  · exact tendsto_atTop_mono (fun m => by
      change (m:ℝ) ≤ f (aboveIndex f hf m)
      linarith only [aboveIndex_value f hf m])
      tendsto_natCast_atTop_atTop

theorem three_regime_exhaustion (f : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧
      (Tendsto (fun m => -f (φ m)) atTop atTop ∨
        (∃ z : ℝ,Tendsto (f ∘ φ) atTop (𝓝 z)) ∨
          ((∀ m,0< f (φ m)) ∧ Tendsto (f ∘ φ) atTop atTop)) := by
  classical
  by_cases hu : BddAbove (Set.range f)
  · by_cases hl : BddAbove (Set.range (fun m => -f m))
    · obtain ⟨U,hU⟩ := hu
      obtain ⟨L,hL⟩ := hl
      have hmem : ∀ m,f m∈Icc (-L) U := by
        intro m
        have h1 := hU (Set.mem_range_self m)
        have h2 := hL (Set.mem_range_self m)
        exact ⟨by linarith,h1⟩
      obtain ⟨z,hz,φ,hφ,hlim⟩ := (isCompact_Icc : IsCompact (Icc (-L) U)).tendsto_subseq hmem
      exact ⟨φ,hφ,Or.inr (Or.inl ⟨z,hlim⟩)⟩
    · obtain ⟨φ,hφ,hpos,hlim⟩ := unbounded_above_extraction (fun m => -f m) hl
      exact ⟨φ,hφ,Or.inl hlim⟩
  · obtain ⟨φ,hφ,hpos,hlim⟩ := unbounded_above_extraction f hu
    exact ⟨φ,hφ,Or.inr (Or.inr ⟨hpos,hlim⟩)⟩

end Extraction
end FCAppendix.Affine.Uniform06.EntrySequence
