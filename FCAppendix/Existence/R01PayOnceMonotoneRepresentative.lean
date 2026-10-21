import FCAppendix.Existence.R01PayOncePurityActual

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory

def orderedBidSet {W : ℝ} (E : Set (Value W)) (f : Value W→ℝ) (v : ℝ) : Set ℝ :=
  insert 0 (f '' {w|w∈E ∧ w.1≤v})

def orderedBidExtension {W : ℝ} (E : Set (Value W)) (f : Value W→ℝ) (v : ℝ) : ℝ :=
  sSup (orderedBidSet E f v)

theorem orderedBidSet_nonempty {W : ℝ} (E : Set (Value W)) (f : Value W→ℝ) (v : ℝ) :
    (orderedBidSet E f v).Nonempty := ⟨0,mem_insert _ _⟩

theorem orderedBidSet_bddAbove {W : ℝ} (hW : 0≤W) (E : Set (Value W)) (f : Value W→ℝ)
    (hbound : ∀w∈E,0≤f w ∧ f w≤W) (v : ℝ) : BddAbove (orderedBidSet E f v) := by
  refine ⟨W,?_⟩
  rintro x (hx|⟨w,⟨hw,_⟩,rfl⟩)
  · exact hx ▸ hW
  · exact (hbound w hw).2

theorem orderedBidExtension_bounds {W : ℝ} (hW : 0≤W) (E : Set (Value W)) (f : Value W→ℝ)
    (hbound : ∀w∈E,0≤f w ∧ f w≤W) (v : ℝ) : orderedBidExtension E f v∈Icc 0 W := by
  refine ⟨le_csSup (orderedBidSet_bddAbove hW E f hbound v) (mem_insert _ _),?_⟩
  apply csSup_le (orderedBidSet_nonempty E f v)
  rintro x (hx|⟨w,⟨hw,_⟩,rfl⟩)
  · exact hx ▸ hW
  · exact (hbound w hw).2

theorem monotone_orderedBidExtension {W : ℝ} (hW : 0≤W) (E : Set (Value W)) (f : Value W→ℝ)
    (hbound : ∀w∈E,0≤f w ∧ f w≤W) : Monotone (orderedBidExtension E f) := by
  intro v v' hvv'
  apply csSup_le (orderedBidSet_nonempty E f v)
  intro x hx
  apply le_csSup (orderedBidSet_bddAbove hW E f hbound v')
  rcases hx with hx|⟨w,⟨hw,hwv⟩,rfl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨w,⟨hw,hwv.trans hvv'⟩,rfl⟩

theorem orderedBidExtension_eq {W : ℝ} (hW : 0≤W) (E : Set (Value W)) (f : Value W→ℝ)
    (hbound : ∀w∈E,0≤f w ∧ f w≤W) (hmono : MonotoneOn f E) (w : Value W) (hw : w∈E) :
    orderedBidExtension E f w.1=f w := by
  apply le_antisymm
  · apply csSup_le (orderedBidSet_nonempty E f w.1)
    rintro x (hx|⟨u,⟨hu,huw⟩,rfl⟩)
    · exact hx ▸ (hbound w hw).1
    · exact hmono hu hw huw
  · exact le_csSup (orderedBidSet_bddAbove hW E f hbound w.1) (Or.inr ⟨w,⟨hw,le_rfl⟩,rfl⟩)

theorem actual_bounded_monotone_bid_representative {W : ℝ} (hW : 0≤W)
    (N n c : ℕ) (hn : 2≤n) (μ : Measure (Value W))
    (hμ : ∀w : Value W,0<w.1→μ {w}=0)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ]
    (hIC : ∀ᵐw ∂μ,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
      positivePayoff N n c π (w,a')≤positivePayoff N n c π (w,a))
    (hpositive : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<bid a)
    (hservice : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0<w.1→0<positiveQ N n c π a) :
    ∃b : ℝ→ℝ,Measurable b ∧ Monotone b ∧ (∀v,b v∈Icc 0 W) ∧
      (∀ᵐw ∂μ,0<w.1→∃bp : PositiveBid W,b w.1=bp.1 ∧
        σ w=Measure.dirac (positiveAction bp) ∧ Purity.Best (boundedSuccessQ N n c π) w.1 bp.1) := by
  obtain ⟨E,hEnull,hmean,hmono,hpoint⟩ :=
    actual_bounded_measurable_ordered_purity N n c hn μ hμ π σ hIC hpositive hservice
  let Epos : Set (Value W) := E∩{w|0<w.1}
  have hbound : ∀w∈Epos,0 ≤ meanBoundedBid σ w ∧ meanBoundedBid σ w≤W := by
    intro w hw
    obtain ⟨bp,hbp,_,_⟩ := hpoint w hw.1 hw.2
    rw [hbp]
    exact ⟨bp.2.1.le,bp.2.2⟩
  let b := orderedBidExtension Epos (meanBoundedBid σ)
  have hmon : Monotone b := monotone_orderedBidExtension hW Epos (meanBoundedBid σ) hbound
  refine ⟨b,hmon.measurable,hmon,(orderedBidExtension_bounds hW Epos (meanBoundedBid σ) hbound),?_⟩
  have hEae : ∀ᵐw ∂μ,w∈E := by
    simpa only [mem_compl_iff,not_not] using measure_eq_zero_iff_ae_notMem.mp hEnull
  filter_upwards [hEae] with w hw
  intro hwp
  obtain ⟨bp,hbp,hσ,hbest⟩ := hpoint w hw hwp
  exact ⟨bp,(orderedBidExtension_eq hW Epos (meanBoundedBid σ) hbound hmono w ⟨hw,hwp⟩).trans hbp,hσ,hbest⟩

end FCAppendix.Existence.PayOnceBounded
