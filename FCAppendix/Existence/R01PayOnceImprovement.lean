import FCAppendix.Existence.R01PayOnceZeroPayoff

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

abbrev PositiveBid (W : ℝ) := Ioc (0:ℝ) W

def positiveAction {W : ℝ} (b : PositiveBid W) : FloorAction 0 W :=
  .inr ⟨b.1,b.2.1.le,b.2.2⟩

theorem continuous_positiveAction {W : ℝ} : Continuous (positiveAction (W:=W)) :=
  continuous_inr.comp (continuous_subtype_val.subtype_mk _)

theorem continuous_positiveSuccess_own {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (r : Fin N→Value W × FloorAction 0 W) :
    Continuous (fun b : PositiveBid W=>positiveSuccess n c (insertFocal N (positiveAction b) r) 0) := by
  rw [continuous_iff_continuousAt]
  intro b
  let bids := fun b' : PositiveBid W=>fun i=>bid (insertFocal N (positiveAction b') r i)
  let S := positiveSupport (bids b)
  have hS (b' : PositiveBid W) : positiveSupport (bids b')=S := by
    ext i
    rw [mem_positiveSupport,mem_positiveSupport]
    refine Fin.cases ?_ (fun k=>?_) i
    · simpa [bids,insertFocal,positiveAction,bid] using (iff_of_true b'.2.1 b.2.1)
    · simp [bids,insertFocal]
  have hbids : Continuous bids := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun k=>?_) i
    · exact continuous_subtype_val
    · change Continuous (fun _ : PositiveBid W=>bid (r k).2)
      exact continuous_const
  have hpos : ∀i∈S,0<bids b i := fun i hi=>(mem_positiveSupport (bids b) i).mp hi
  have hcont : ContinuousAt (fun b' : PositiveBid W=>
      PayOnce.success n (onSupport n c S (bids b') 0)) b :=
    (PayOnce.continuous_success n).continuousAt.comp
    ((continuous_apply (0:Fin (N+1))).continuousAt.comp
      ((continuousAt_onSupport n c hn S (bids b) hpos).comp hbids.continuousAt))
  convert hcont using 1
  funext b'
  change PayOnce.success n (onSupport n c (positiveSupport (bids b')) (bids b') 0)=
    PayOnce.success n (onSupport n c S (bids b') 0)
  rw [hS]

theorem continuous_positiveQ_own {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) :
    Continuous (fun b : PositiveBid W=>positiveQ N n c π (positiveAction b)) := by
  apply continuous_of_dominated (bound:=fun _=>1)
  · intro b
    exact (integrable_positiveSuccess_insertFocal N n c hn π (positiveAction b)).aestronglyMeasurable
  · intro b
    exact Filter.Eventually.of_forall (fun r=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (positiveSuccess_bounds n c hn _ _).1]
      exact (positiveSuccess_bounds n c hn _ _).2)
  · exact integrable_const (1:ℝ)
  · exact Filter.Eventually.of_forall (continuous_positiveSuccess_own N n c hn)

def clippedImprovementMass {W : ℝ} (N n c : ℕ) (δ : ℝ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (b : FloorAction 0 W) : ℝ :=
  ∫z,max 0 (clippedPayoff N n c δ hδW π (z.1,b)-clippedPayoff N n c δ hδW π z)
    ∂(π : Measure (Value W × FloorAction 0 W))

theorem continuous_clippedImprovementMass {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W) :
    Continuous (fun p : ProbabilityMeasure (Value W × FloorAction 0 W) × FloorAction 0 W=>
      clippedImprovementMass N n c δ hδW p.1 p.2) := by
  let f : (ProbabilityMeasure (Value W × FloorAction 0 W) × FloorAction 0 W) ×
      (Value W × FloorAction 0 W)→ℝ := fun p=>
    max 0 (clippedPayoff N n c δ hδW p.1.1 (p.2.1,p.1.2)-
      clippedPayoff N n c δ hδW p.1.1 p.2)
  have hf : Continuous f := continuous_const.max
    (((continuous_clippedPayoff N n c hn δ hδ hδW).comp
      (continuous_fst.fst.prodMk (continuous_snd.fst.prodMk continuous_fst.snd))).sub
      ((continuous_clippedPayoff N n c hn δ hδ hδW).comp
        (continuous_fst.fst.prodMk continuous_snd)))
  exact (continuous_law_integral f hf).comp (continuous_id.prodMk continuous_fst)

theorem fixed_action_IC_of_improvementMass_zero {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hW : 0≤W) (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (b : FloorAction 0 W) (hM : improvementMass N n c π b=0) :
    ∀ᵐz ∂(π : Measure (Value W × FloorAction 0 W)),
      positivePayoff N n c π (z.1,b)≤positivePayoff N n c π z := by
  have hm : Measurable (fun z : Value W × FloorAction 0 W=>
      max 0 (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)) :=
    measurable_const.max (((measurable_positivePayoff N n c hn π).comp
      (measurable_fst.prodMk measurable_const)).sub (measurable_positivePayoff N n c hn π))
  have hi : Integrable (fun z : Value W × FloorAction 0 W=>
      max 0 (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)) (π : Measure _) := by
    apply Integrable.of_bound hm.aestronglyMeasurable (2*W)
    exact Filter.Eventually.of_forall (fun z=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      apply max_le (by positivity)
      have h1 := abs_le.mp (positivePayoff_abs_le N n c hn hW π (z.1,b))
      have h2 := abs_le.mp (positivePayoff_abs_le N n c hn hW π z)
      linarith [h1.2,h2.1])
  have hz := (integral_eq_zero_iff_of_nonneg (fun _=>le_max_left 0 _) hi).mp hM
  filter_upwards [hz] with z hz
  exact sub_nonpos.mp ((le_max_right 0 _).trans_eq hz)

theorem common_positive_IC_of_improvementMass_zero {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hW : 0≤W) (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hM : ∀b : PositiveBid W,improvementMass N n c π (positiveAction b)=0) :
    ∀ᵐz ∂(π : Measure (Value W × FloorAction 0 W)),∀b : PositiveBid W,
      positivePayoff N n c π (z.1,positiveAction b)≤positivePayoff N n c π z := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (PositiveBid W)
  have hfixed : ∀b∈D,∀ᵐz ∂(π : Measure (Value W × FloorAction 0 W)),
      positivePayoff N n c π (z.1,positiveAction b)≤positivePayoff N n c π z :=
    fun b _=>fixed_action_IC_of_improvementMass_zero N n c hn hW π _ (hM b)
  have hall := (ae_ball_iff hDc).mpr hfixed
  filter_upwards [hall] with z hz
  have hf : Continuous (fun b : PositiveBid W=>positivePayoff N n c π (z.1,positiveAction b)) := by
    convert ((continuous_const (y:=z.1.1)).sub continuous_subtype_val).mul
      (continuous_positiveQ_own N n c hn π) using 1
    funext b
    rfl
  have hclosed : IsClosed {b : PositiveBid W|positivePayoff N n c π (z.1,positiveAction b)≤
      positivePayoff N n c π z} := isClosed_le hf continuous_const
  have hs := closure_minimal (fun b hb=>hz b hb) hclosed
  intro b
  exact hs (hDd.closure_eq ▸ mem_univ b)

end FCAppendix.Existence.PayOnceBounded
