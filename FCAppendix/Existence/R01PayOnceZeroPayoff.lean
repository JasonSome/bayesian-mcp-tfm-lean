import FCAppendix.Existence.R01PayOnceWeakPayoff

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

theorem rowLaw_map {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [CompactSpace X] [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [BorelSpace Y]
    (N : ℕ) (π : ProbabilityMeasure X) (f : X→Y) (hf : Measurable f) :
    (rowLaw N (π.map hf.aemeasurable) : Measure (Fin N→Y)) =
      Measure.map (fun r i=>f (r i)) (rowLaw N π : Measure (Fin N→X)) := by
  rw [rowLaw_eq_pi,rowLaw_eq_pi]
  exact (Measure.pi_map_pi (fun _ : Fin N=>hf.aemeasurable)).symm

def positiveQ {W : ℝ} (N n c : ℕ) (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (a : FloorAction 0 W) : ℝ :=
  ∫r,positiveSuccess n c (insertFocal N a r) 0
    ∂(rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W))

theorem measurable_positiveQ {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) :
    Measurable (positiveQ N n c π) := by
  have hm : Measurable (fun p : FloorAction 0 W × (Fin N→Value W × FloorAction 0 W)=>
      positiveSuccess n c (insertFocal N p.1 p.2) 0) :=
    (measurable_positiveSuccess n c hn 0).comp (continuous_insertFocal N).measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem integrable_positiveSuccess_insertFocal {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (a : FloorAction 0 W) :
    Integrable (fun r=>positiveSuccess n c (insertFocal N a r) 0)
      (rowLaw N π : Measure (Fin N→Value W × FloorAction 0 W)) := by
  have hm : Measurable (fun r : Fin N→Value W × FloorAction 0 W=>
      positiveSuccess n c (insertFocal N a r) 0) := (measurable_positiveSuccess n c hn 0).comp
    ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id)).measurable
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun r=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (positiveSuccess_bounds n c hn _ _).1]
    exact (positiveSuccess_bounds n c hn _ _).2)

theorem positiveQ_bounds {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (a : FloorAction 0 W) :
    positiveQ N n c π a∈Icc 0 1 := by
  refine ⟨integral_nonneg (fun r=>(positiveSuccess_bounds n c hn _ _).1),?_⟩
  have hh := integral_mono (integrable_positiveSuccess_insertFocal N n c hn π a)
    (integrable_const (1:ℝ)) (fun r=>(positiveSuccess_bounds n c hn (insertFocal N a r) 0).2)
  simpa [positiveQ] using hh

def positivePayoff {W : ℝ} (N n c : ℕ)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) : ℝ :=
  (z.1.1-bid z.2)*positiveQ N n c π z.2

theorem measurable_positivePayoff {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) :
    Measurable (positivePayoff N n c π) :=
  (measurable_fst.subtype_val.sub (continuous_bid.measurable.comp measurable_snd)).mul
    ((measurable_positiveQ N n c hn π).comp measurable_snd)

theorem positivePayoff_abs_le {W : ℝ} (N n c : ℕ) (hn : 2≤n) (hW : 0≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (z : Value W × FloorAction 0 W) :
    |positivePayoff N n c π z|≤W :=
  abs_net_payoff_le W _ _ _ z.1.2 (floor_bid_bounds le_rfl hW z.2)
    (positiveQ_bounds N n c hn π z.2)

theorem positiveQ_embeddedFloor {ε W : ℝ} (N n c : ℕ) (hn : 2≤n) (hε : 0<ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (a : FloorAction ε W) :
    positiveQ N n c (embeddedFloorLaw hε.le π).1 (embedFloor hε.le a)=Qfloor N n c π a := by
  have hrow : (rowLaw N (embeddedFloorLaw hε.le π).1 : Measure (Fin N→Value W × FloorAction 0 W)) =
      Measure.map (fun r i=>embedFloorPair hε.le (r i))
        (rowLaw N π.1 : Measure (Fin N→Value W × FloorAction ε W)) :=
    rowLaw_map N π.1 (embedFloorPair hε.le) (continuous_embedFloorPair hε.le).measurable
  have hmeas : AEStronglyMeasurable (fun r : Fin N→Value W × FloorAction 0 W=>
      positiveSuccess n c (insertFocal N (embedFloor hε.le a) r) 0)
      (rowLaw N (embeddedFloorLaw hε.le π).1 : Measure _) :=
    (integrable_positiveSuccess_insertFocal N n c hn (embeddedFloorLaw hε.le π).1 _).aestronglyMeasurable
  unfold positiveQ
  rw [hrow] at hmeas ⊢
  have hmap : Measurable (fun r : Fin N→Value W × FloorAction ε W=>
      fun i=>embedFloorPair hε.le (r i)) :=
    measurable_pi_iff.mpr (fun i=>(continuous_embedFloorPair hε.le).measurable.comp (measurable_pi_apply i))
  rw [integral_map hmap.aemeasurable hmeas]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun r=>by
    have he : (fun j=>bid (insertFocal N (embedFloor hε.le a)
        (fun i=>embedFloorPair hε.le (r i)) j))=(fun j=>bid (insertFocal N a r j)) := by
      funext j
      refine Fin.cases ?_ (fun k=>?_) j
      · simp [insertFocal]
      · simp [insertFocal,embedFloorPair]
    change PayOnce.success n (positiveMarginal n c _ 0)=success n c (insertFocal N a r) 0
    rw [he,positiveMarginal_eq_marginal hε]
    rfl)

theorem positivePayoff_embeddedFloor {ε W : ℝ} (N n c : ℕ) (hn : 2≤n) (hε : 0<ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (z : Value W × FloorAction ε W) :
    positivePayoff N n c (embeddedFloorLaw hε.le π).1 (embedFloorPair hε.le z)=
      floorPayoff N n c (π,z) := by
  unfold positivePayoff floorPayoff
  simp only [embedFloorPair,bid_embedFloor,positiveQ_embeddedFloor N n c hn hε]

def improvementMass {W : ℝ} (N n c : ℕ)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (b : FloorAction 0 W) : ℝ :=
  ∫z,max 0 (positivePayoff N n c π (z.1,b)-positivePayoff N n c π z)
    ∂(π : Measure (Value W × FloorAction 0 W))

theorem improvementMass_embeddedFloor_eq_zero {ε W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hε : 0<ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) (b : Icc ε W) :
    improvementMass N n c (embeddedFloorLaw hε.le π).1 (embedFloor hε.le (.inr b))=0 := by
  let ν := (embeddedFloorLaw hε.le π).1
  have hM : Measurable (fun z : Value W × FloorAction 0 W=>
      max 0 (positivePayoff N n c ν (z.1,embedFloor hε.le (.inr b))-positivePayoff N n c ν z)) :=
    measurable_const.max (((measurable_positivePayoff N n c hn ν).comp
      (measurable_fst.prodMk measurable_const)).sub (measurable_positivePayoff N n c hn ν))
  unfold improvementMass
  change (∫z,max 0 (positivePayoff N n c ν (z.1,embedFloor hε.le (.inr b))-
    positivePayoff N n c ν z) ∂Measure.map (embedFloorPair hε.le)
      (π.1 : Measure (Value W × FloorAction ε W)))=0
  rw [integral_map (continuous_embedFloorPair hε.le).measurable.aemeasurable hM.aestronglyMeasurable]
  apply integral_eq_zero_of_ae
  filter_upwards [hIC] with z hz
  have hdev := positivePayoff_embeddedFloor N n c hn hε π (z.1,.inr b)
  have hinc := positivePayoff_embeddedFloor N n c hn hε π z
  change max 0 (positivePayoff N n c ν (embedFloorPair hε.le (z.1,.inr b))-
    positivePayoff N n c ν (embedFloorPair hε.le z))=0
  rw [hdev,hinc]
  exact max_eq_left (sub_nonpos.mpr (hz (.inr b)))

theorem improvementMass_embeddedFloor_inactive_eq_zero {ε W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hε : 0<ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) :
    improvementMass N n c (embeddedFloorLaw hε.le π).1 (.inl ())=0 := by
  let ν := (embeddedFloorLaw hε.le π).1
  have hM : Measurable (fun z : Value W × FloorAction 0 W=>
      max 0 (positivePayoff N n c ν (z.1,.inl ())-positivePayoff N n c ν z)) :=
    measurable_const.max (((measurable_positivePayoff N n c hn ν).comp
      (measurable_fst.prodMk measurable_const)).sub (measurable_positivePayoff N n c hn ν))
  unfold improvementMass
  change (∫z,max 0 (positivePayoff N n c ν (z.1,.inl ())-
    positivePayoff N n c ν z) ∂Measure.map (embedFloorPair hε.le)
      (π.1 : Measure (Value W × FloorAction ε W)))=0
  rw [integral_map (continuous_embedFloorPair hε.le).measurable.aemeasurable hM.aestronglyMeasurable]
  apply integral_eq_zero_of_ae
  filter_upwards [hIC] with z hz
  have hdev := positivePayoff_embeddedFloor N n c hn hε π (z.1,.inl ())
  have hinc := positivePayoff_embeddedFloor N n c hn hε π z
  change max 0 (positivePayoff N n c ν (embedFloorPair hε.le (z.1,.inl ()))-
    positivePayoff N n c ν (embedFloorPair hε.le z))=0
  rw [hdev,hinc]
  exact max_eq_left (sub_nonpos.mpr (hz (.inl ())))

theorem positiveQ_zero_bid {W : ℝ} (N n c : ℕ) (_hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (a : FloorAction 0 W)
    (ha : bid a=0) : positiveQ N n c π a=0 := by
  unfold positiveQ
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun r=>by
    let B := fun j=>bid (insertFocal N a r j)
    have hi : (0:Fin (N+1))∉positiveSupport B := by
      rw [mem_positiveSupport]
      simp [B,insertFocal,ha]
    have hm := onSupport_outside n c (positiveSupport B) B 0 hi
    change PayOnce.success n (onSupport n c (positiveSupport B) B 0)=0
    rw [hm]
    simp [PayOnce.success])

@[simp] theorem positivePayoff_inactive {W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W)) (w : Value W) :
    positivePayoff N n c π (w,.inl ())=0 := by
  unfold positivePayoff
  rw [positiveQ_zero_bid N n c hn π (.inl ()) rfl,mul_zero]

end FCAppendix.Existence.PayOnceBounded
