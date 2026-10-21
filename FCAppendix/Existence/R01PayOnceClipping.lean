import FCAppendix.Existence.R01PayOnceInactiveSupport
import FCAppendix.Existence.R01PayOnceCanonicalPolicy

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

def clipToFloor {W : ℝ} (δ : ℝ) (hδW : δ≤W) : FloorAction 0 W → FloorAction δ W
  | .inl u => .inl u
  | .inr b => .inr ⟨max δ b.1,le_max_left _ _,max_le hδW b.2.2⟩

theorem continuous_clipToFloor {W : ℝ} (δ : ℝ) (hδW : δ≤W) :
    Continuous (clipToFloor δ hδW) := by
  apply continuous_sum_dom.mpr
  constructor
  · exact continuous_inl
  · exact continuous_inr.comp ((continuous_const.max continuous_subtype_val).subtype_mk _)

@[simp] theorem present_clipToFloor {W : ℝ} (δ : ℝ) (hδW : δ≤W)
    (b : FloorAction 0 W) : present (clipToFloor δ hδW b)=present b := by cases b <;> rfl

def smallActive {W : ℝ} (δ : ℝ) : Set (Value W × FloorAction 0 W) :=
  {z|present z.2=true ∧ bid z.2≤δ}

theorem isClosed_smallActive {W : ℝ} (δ : ℝ) : IsClosed (smallActive (W:=W) δ) :=
  (isClosed_eq (continuous_present.comp continuous_snd) continuous_const).inter
    (isClosed_le (continuous_bid.comp continuous_snd) continuous_const)

theorem positiveSupport_bid_eq_activeSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε W : ℝ} (hε : 0<ε) (x : ι→FloorAction ε W) :
    positiveSupport (fun i=>bid (x i))=activeSet x := by
  ext i
  rw [mem_positiveSupport,mem_activeSet]
  cases h : x i with
  | inl u => simp [bid,present]
  | inr b => simpa [h,bid,present] using (hε.trans_le b.2.1)

theorem positiveMarginal_eq_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ε W : ℝ} (hε : 0<ε) (n c : ℕ) (x : ι→FloorAction ε W) :
    positiveMarginal n c (fun i=>bid (x i))=marginal n c x := by
  unfold positiveMarginal marginal
  rw [positiveSupport_bid_eq_activeSet hε]

def positiveSuccess {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ℝ}
    (n c : ℕ) (x : ι→FloorAction 0 W) (i : ι) : ℝ :=
  PayOnce.success n (positiveMarginal n c (fun j=>bid (x j)) i)

theorem measurable_positiveSuccess {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ℝ}
    (n c : ℕ) (hn : 2≤n) (i : ι) :
    Measurable (fun x : ι→FloorAction 0 W=>positiveSuccess n c x i) :=
  (PayOnce.continuous_success n).measurable.comp
    ((measurable_pi_apply i).comp ((measurable_positiveMarginal n c hn).comp
      (measurable_pi_iff.mpr (fun j=>continuous_bid.measurable.comp (measurable_pi_apply j)))))

theorem positiveSuccess_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ℝ}
    (n c : ℕ) (hn : 2≤n) (x : ι→FloorAction 0 W) (i : ι) :
    0≤positiveSuccess n c x i ∧ positiveSuccess n c x i≤1 := by
  have hp := positiveMarginal_spec n c hn (fun j=>bid (x j))
  refine ⟨?_,PayOnce.success_le_one n _ (hp.2.1 i)⟩
  rw [positiveSuccess,← PayOnce.H_mul n (by omega)]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp.1 i)) (PayOnce.H_nonneg n _ (hp.2.1 i))

theorem bid_clipToFloor_eq {W : ℝ} (δ : ℝ) (hδW : δ≤W)
    (a : FloorAction 0 W) (ha : present a=true→δ≤bid a) :
    bid (clipToFloor δ hδW a)=bid a := by
  cases a with
  | inl u => rfl
  | inr b => exact max_eq_right (ha rfl)

theorem clipped_success_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {W : ℝ}
    (n c : ℕ) (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W)
    (x : ι→FloorAction 0 W) (hx : ∀j,present (x j)=true→δ≤bid (x j)) (i : ι) :
    success n c (fun j=>clipToFloor δ hδW (x j)) i=positiveSuccess n c x i := by
  rw [success,← positiveMarginal_eq_marginal hδ]
  have he : (fun j=>bid (clipToFloor δ hδW (x j)))=(fun j=>bid (x j)) :=
    funext (fun j=>bid_clipToFloor_eq δ hδW (x j) (hx j))
  rw [he]
  rfl

def clippedInsertFocal {W : ℝ} (N : ℕ) (δ : ℝ) (hδW : δ≤W)
    (a : FloorAction 0 W) (r : Fin N→Value W × FloorAction 0 W) :
    Fin (N+1)→FloorAction δ W :=
  fun i=>clipToFloor δ hδW (insertFocal N a r i)

theorem continuous_clippedInsertFocal {W : ℝ} (N : ℕ) (δ : ℝ) (hδW : δ≤W) :
    Continuous (fun p : FloorAction 0 W × (Fin N→Value W × FloorAction 0 W)=>
      clippedInsertFocal N δ hδW p.1 p.2) := by
  apply continuous_pi
  intro i
  exact (continuous_clipToFloor δ hδW).comp ((continuous_apply i).comp (continuous_insertFocal N))

def clippedQ {W : ℝ} (N n c : ℕ) (δ : ℝ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (a : FloorAction 0 W) : ℝ :=
  ∫r,success n c (clippedInsertFocal N δ hδW a r) 0
    ∂(rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W))

theorem continuous_clippedQ {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W) :
    Continuous (fun p : ProbabilityMeasure (Value W × FloorAction 0 W) × FloorAction 0 W=>
      clippedQ N n c δ hδW p.1 p.2) := by
  letI : OpensMeasurableSpace (Fin N→Value W × FloorAction 0 W) := inferInstance
  let f : FloorAction 0 W × (Fin N→Value W × FloorAction 0 W)→ℝ :=
    fun p=>success n c (clippedInsertFocal N δ hδW p.1 p.2) 0
  have hf : Continuous f := (PayOnce.continuous_success n).comp ((continuous_apply 0).comp
    ((continuous_marginal n c hn hδ).comp (continuous_clippedInsertFocal N δ hδW)))
  exact (continuous_law_integral f hf).comp (continuous_snd.prodMk
    ((continuous_rowLaw (X:=Value W × FloorAction 0 W) N).comp continuous_fst))

def clippedPayoff {W : ℝ} (N n c : ℕ) (δ : ℝ) (hδW : δ≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) : ℝ :=
  (z.1.1-bid (clipToFloor δ hδW z.2))*clippedQ N n c δ hδW π z.2

theorem continuous_clippedPayoff {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (δ : ℝ) (hδ : 0<δ) (hδW : δ≤W) :
    Continuous (fun p : ProbabilityMeasure (Value W × FloorAction 0 W) ×
      (Value W × FloorAction 0 W)=>clippedPayoff N n c δ hδW p.1 p.2) := by
  have hq : Continuous (fun p : ProbabilityMeasure (Value W × FloorAction 0 W) ×
      (Value W × FloorAction 0 W)=>clippedQ N n c δ hδW p.1 p.2.2) :=
    (continuous_clippedQ N n c hn δ hδ hδW).comp
    (continuous_fst.prodMk continuous_snd.snd)
  exact (continuous_snd.fst.subtype_val.sub
    (continuous_bid.comp ((continuous_clipToFloor δ hδW).comp continuous_snd.snd))).mul hq

end FCAppendix.Existence.PayOnceBounded
