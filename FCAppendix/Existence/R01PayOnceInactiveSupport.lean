import FCAppendix.Existence.R01PayOnceFloorEmbedding

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional
attribute [local instance] Classical.propDecidable

theorem success_one_of_inactive_rivals {ε W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hc1 : 1≤c) (hε : 0<ε) (b : Icc ε W)
    (r : Fin N → Value W × FloorAction ε W) (hr : ∀j,present (r j).2=false) :
    success n c (insertFocal N (.inr b) r) 0=1 := by
  have hm := marginal_saturates n c hn hc1 hε (insertFocal N (.inr b) r) 0
    (by simp [insertFocal,present]) (fun j hj hact => by
      revert hj hact
      refine Fin.cases ?_ (fun k=>?_) j
      · intro hj _; exact False.elim (hj rfl)
      · intro _ hact
        have hh : present (r k).2=true := by simpa [insertFocal] using hact
        rw [hr k] at hh
        contradiction)
  simp [success,hm,PayOnce.success,Nat.ne_of_gt (show 0<n by omega)]

theorem Qfloor_ge_inactive_mass_pow {ε W : ℝ} (N n c : ℕ) (hn : 2≤n)
    (hc1 : 1≤c) (hε : 0<ε) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (b : Icc ε W) :
    ((π.1 : Measure (Value W × FloorAction ε W)).real {z|present z.2=false})^N ≤
      Qfloor N n c π (.inr b) := by
  let C : Set (Value W × FloorAction ε W) := {z|present z.2=false}
  have hC : MeasurableSet C := measurableSet_eq_fun
    (continuous_present.measurable.comp measurable_snd) measurable_const
  have hAll : MeasurableSet {r : Fin N → Value W × FloorAction ε W | ∀j,r j∈C} := by
    convert MeasurableSet.iInter (fun j=>hC.preimage (measurable_pi_apply j)) using 1
    · ext r; simp
    · infer_instance
  have hi : Integrable (fun r : Fin N → Value W × FloorAction ε W =>
      if ∀j,r j∈C then (1:ℝ) else 0) (rowLaw N π.1 : Measure _) := by
    convert (integrable_const (1:ℝ)).indicator (μ := (rowLaw N π.1 : Measure _)) hAll using 1
    all_goals first | rfl | (funext r; simp only [Set.indicator,mem_setOf_eq])
  have hs : Continuous (fun r : Fin N → Value W × FloorAction ε W =>
      success n c (insertFocal N (.inr b) r) 0) :=
    (PayOnce.continuous_success n).comp ((continuous_apply 0).comp
      ((continuous_marginal n c hn hε).comp
        ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id))))
  have his := (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,hs⟩).integrable
    (rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W))
  have hm : (∫ r : Fin N → Value W × FloorAction ε W,
      if ∀j,r j∈C then (1:ℝ) else 0 ∂(rowLaw N π.1 : Measure _)) =
      ((π.1 : Measure (Value W × FloorAction ε W)).real C)^N := by
    calc
      _=((rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W)) {r|∀j,r j∈C}).toReal := by
        convert integral_indicator_one (μ := (rowLaw N π.1 : Measure _)) hAll using 1
        all_goals first | rfl | (congr 1; funext r; simp only [Set.indicator,mem_setOf_eq,Pi.one_apply])
      _=_ := by rw [rowLaw_all N π.1 C hC,ENNReal.toReal_pow]; rfl
  rw [← hm]
  apply integral_mono hi his
  intro r
  change (if ∀j,r j∈C then (1:ℝ) else 0) ≤ success n c (insertFocal N (.inr b) r) 0
  split_ifs with hr
  · exact (success_one_of_inactive_rivals N n c hn hc1 hε b r hr).ge
  · exact (success_bounds n c hn hε _ _).1

theorem floor_inactive_value_le {ε W : ℝ} (N n c : ℕ) (hn : 2≤n) (hc1 : 1≤c)
    (hε : 0<ε) (hεW : ε≤W) {μ : Measure (Value W)} (π : FloorLaw ε W μ)
    (hIC : AllActionOptimal π (fun z=>floorPayoff N n c (π,z))) :
    ∀ᵐ z ∂(π.1 : Measure (Value W × FloorAction ε W)),
      present z.2=false → z.1.1≤ε := by
  let C : Set (Value W × FloorAction ε W) := {z|present z.2=false}
  by_cases hnull : (π.1 : Measure (Value W × FloorAction ε W)) C=0
  · have ha : ∀ᵐ z ∂(π.1 : Measure (Value W × FloorAction ε W)),z∉C :=
      measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [ha] with z hz hact
    exact False.elim (hz hact)
  · have hq : 0<(π.1 : Measure (Value W × FloorAction ε W)).real C :=
      ENNReal.toReal_pos hnull (measure_ne_top _ _)
    let b : Icc ε W := ⟨ε,le_rfl,hεW⟩
    have hQ : 0<Qfloor N n c π (.inr b) :=
      (pow_pos hq N).trans_le (Qfloor_ge_inactive_mass_pow N n c hn hc1 hε π b)
    filter_upwards [hIC] with z hz hact
    by_contra hw
    have hwε : ε<z.1.1 := lt_of_not_ge hw
    have hb : bid (.inr b : FloorAction ε W)=ε := rfl
    rcases ha : z.2 with u|bb
    · cases u
      have hp := hz (.inr b)
      have hpay : floorPayoff N n c (π,z)=0 := by
        simp [floorPayoff,ha]
      rw [hpay] at hp
      have hpos : 0<floorPayoff N n c (π,(z.1,.inr b)) := by
        exact mul_pos (sub_pos.mpr hwε) hQ
      linarith
    · simp [ha,present] at hact

theorem actual_floor_limit_no_positive_inactive (W : ℝ) (N n c : ℕ)
    (hn : 2≤n) (hc1 : 1≤c) (μ : Measure (Value W)) [IsProbabilityMeasure μ]
    (ε : ℕ→ℝ) (hε : ∀j,0<ε j) (hεW : ∀j,ε j≤W)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (π : (j:ℕ)→FloorLaw (ε j) W μ)
    (hIC : ∀j,AllActionOptimal (π j) (fun z=>floorPayoff N n c (π j,z)))
    (ν₀ : FloorLaw 0 W μ)
    (hν : Tendsto (fun j=>(embeddedFloorLaw (hε j).le (π j)).1) atTop (𝓝 ν₀.1)) :
    (ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z|0<z.1.1 ∧ present z.2=false}=0 := by
  have hcut : ∀a,0<a→(ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z|a<z.1.1 ∧ present z.2=false}=0 := by
    intro a ha
    let O : Set (Value W × FloorAction 0 W) := {z|a<z.1.1 ∧ present z.2=false}
    have hO : IsOpen O := (isOpen_lt continuous_const
      (continuous_subtype_val.comp continuous_fst)).inter
      ((isOpen_discrete {false}).preimage (continuous_present.comp continuous_snd))
    have hjnull (j:ℕ) (hj:ε j≤a) :
        ((embeddedFloorLaw (hε j).le (π j)).1 : Measure (Value W × FloorAction 0 W)) O=0 := by
      change (Measure.map (embedFloorPair (hε j).le)
        ((π j).1 : Measure (Value W × FloorAction (ε j) W))) O=0
      rw [Measure.map_apply (continuous_embedFloorPair (hε j).le).measurable hO.measurableSet]
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [floor_inactive_value_le N n c hn hc1 (hε j) (hεW j) (π j) (hIC j)] with z hz
      intro hmem
      have hm : a<z.1.1 ∧ present z.2=false := by
        simpa [O,embedFloorPair] using hmem
      exact not_lt_of_ge ((hz hm.2).trans hj) hm.1
    by_contra hmass
    let r := (ν₀.1 : Measure (Value W × FloorAction 0 W)).real O/2
    have hr : 0<r := div_pos (ENNReal.toReal_pos hmass (measure_ne_top _ _)) (by norm_num)
    have hεa : ∀ᶠj in atTop,ε j≤a :=
      (hε0.eventually (Iio_mem_nhds ha)).mono (fun _ h=>h.le)
    have hrO : r<(ν₀.1 : Measure (Value W × FloorAction 0 W)).real O := by
      dsimp [r] at hr ⊢
      linarith
    have hpos := eventually_open_mass_gt _ ν₀.1 hν O hO r hr.le hrO
    obtain ⟨j,hj,hpj⟩ := (hεa.and hpos).exists
    have hz := hjnull j hj
    have hzreal : ((embeddedFloorLaw (hε j).le (π j)).1 :
        Measure (Value W × FloorAction 0 W)).real O=0 := by simp [Measure.real,hz]
    rw [hzreal] at hpj
    linarith
  have hcover : {z : Value W × FloorAction 0 W | 0 <z.1.1 ∧ present z.2=false} ⊆
      ⋃ j : ℕ, {z | 1/(j+1:ℝ) <z.1.1 ∧ present z.2=false} := by
    rintro z ⟨hw,hp⟩
    obtain ⟨j,hj⟩ := exists_nat_gt (1/z.1.1)
    refine mem_iUnion.mpr ⟨j,?_,hp⟩
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<j+1)).mpr
    have hh := (div_lt_iff₀ hw).mp hj
    nlinarith [z.1.2.1]
  apply measure_mono_null hcover
  exact measure_iUnion_null (fun j=>hcut (1/(j+1:ℝ)) (by positivity))

end FCAppendix.Existence.PayOnceBounded
