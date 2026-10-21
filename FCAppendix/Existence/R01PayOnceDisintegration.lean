import FCAppendix.Existence.R01PayOnceImprovement

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

theorem allAction_iff_dense_positive {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (D : Set (PositiveBid W)) (hD : Dense D) (z : Value W × FloorAction 0 W) :
    (∀a : FloorAction 0 W,positivePayoff N n c π (z.1,a)≤positivePayoff N n c π z) ↔
      ((∀b∈D,positivePayoff N n c π (z.1,positiveAction b)≤positivePayoff N n c π z) ∧
        0≤positivePayoff N n c π z) := by
  constructor
  · intro h
    exact ⟨fun b _=>h (positiveAction b),by simpa only [positivePayoff_inactive N n c hn π] using h (.inl ())⟩
  · rintro ⟨hpos,h0⟩ a
    have hf : Continuous (fun b : PositiveBid W=>positivePayoff N n c π (z.1,positiveAction b)) := by
      convert ((continuous_const (y:=z.1.1)).sub continuous_subtype_val).mul
        (continuous_positiveQ_own N n c hn π) using 1
      funext b
      rfl
    have hc : IsClosed {b : PositiveBid W|positivePayoff N n c π (z.1,positiveAction b)≤
        positivePayoff N n c π z} := isClosed_le hf continuous_const
    have hall : ∀b : PositiveBid W,positivePayoff N n c π (z.1,positiveAction b)≤
        positivePayoff N n c π z := fun b=>(closure_minimal hpos hc) (hD.closure_eq ▸ mem_univ b)
    cases a with
    | inl u => cases u; simpa only [positivePayoff_inactive N n c hn π] using h0
    | inr b =>
      by_cases hb : b.1=0
      · change (z.1.1-b.1)*positiveQ N n c π (.inr b)≤_
        rw [positiveQ_zero_bid N n c hn π (.inr b) hb,mul_zero]
        exact h0
      · exact hall ⟨b.1,lt_of_le_of_ne b.2.1 (Ne.symm hb),b.2.2⟩

theorem measurableSet_zeroPayoff_allAction {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) :
    MeasurableSet {z : Value W × FloorAction 0 W|∀a : FloorAction 0 W,
      positivePayoff N n c π (z.1,a)≤positivePayoff N n c π z} := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (PositiveBid W)
  have hm (b : PositiveBid W) : Measurable (fun z : Value W × FloorAction 0 W=>
      positivePayoff N n c π (z.1,positiveAction b)) :=
    (measurable_positivePayoff N n c hn π).comp (measurable_fst.prodMk measurable_const)
  have hDenseMeas : MeasurableSet {z : Value W × FloorAction 0 W|∀b∈D,
      positivePayoff N n c π (z.1,positiveAction b)≤positivePayoff N n c π z} := by
    convert MeasurableSet.biInter hDc (fun b _=>measurableSet_le (hm b)
      (measurable_positivePayoff N n c hn π)) using 1
    ext z
    simp
  have he : {z : Value W × FloorAction 0 W|∀a : FloorAction 0 W,
      positivePayoff N n c π (z.1,a)≤positivePayoff N n c π z}=
      {z|∀b∈D,positivePayoff N n c π (z.1,positiveAction b)≤positivePayoff N n c π z} ∩
        {z|0≤positivePayoff N n c π z} := by
    ext z
    exact allAction_iff_dense_positive N n c hn π D hDd z
  rw [he]
  exact hDenseMeas.inter (measurableSet_le measurable_const (measurable_positivePayoff N n c hn π))

theorem disintegrate_zeroPayoff_allAction {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] (π : FloorLaw 0 W μ)
    (hIC : ∀ᵐz ∂(π.1 : Measure (Value W × FloorAction 0 W)),∀a : FloorAction 0 W,
      positivePayoff N n c π.1 (z.1,a)≤positivePayoff N n c π.1 z) :
    ∃σ : Kernel (Value W) (FloorAction 0 W),IsMarkovKernel σ ∧
      μ ⊗ₘ σ=(π.1 : Measure (Value W × FloorAction 0 W)) ∧
      (∀ᵐw ∂μ,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
        positivePayoff N n c π.1 (w,a')≤positivePayoff N n c π.1 (w,a)) := by
  let σ := (π.1 : Measure (Value W × FloorAction 0 W)).condKernel
  have hmarg : (π.1 : Measure (Value W × FloorAction 0 W)).fst=μ := π.2
  have hdis : μ ⊗ₘ σ=(π.1 : Measure (Value W × FloorAction 0 W)) := by
    calc
      _=(π.1 : Measure (Value W × FloorAction 0 W)).fst ⊗ₘ σ := by rw [hmarg]
      _=_ := Measure.disintegrate _ _
  refine ⟨σ,inferInstance,hdis,?_⟩
  rw [←hdis] at hIC
  exact (Measure.ae_compProd_iff (measurableSet_zeroPayoff_allAction N n c hn π.1)).mp hIC

end FCAppendix.Existence.PayOnceBounded
