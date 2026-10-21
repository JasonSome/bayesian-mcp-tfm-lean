import FCAppendix.Affine.UniformFinite.ConditionalFibers
import FCAppendix.Affine.UniformFinite.ConditionalCounts

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity WeightedSampling
open scoped BigOperators

namespace NativeSeed

def seedSet (i : Row) : Set (Bid i) := {b | (b:ℝ)≤ t i/2}

lemma measurableSet_seedSet (i : Row) : MeasurableSet (seedSet i) :=
  measurableSet_le measurable_subtype_coe measurable_const

lemma seedSet_pos (i : Row) (G : RestrictedLaw i) : 0<(G.bidLaw : Measure (Bid i)) (seedSet i) := by
  have h:=G.seed_mass_lower
  have he : (1:ℝ)/2*t i=t i/2 := by ring
  rw [he] at h
  exact (show (0:ENNReal)< ENNReal.ofReal ((1:ℝ)/2) by norm_num).trans_le h

def measure (i : Row) (G : RestrictedLaw i) : Measure ℝ :=
  (cond (G.bidLaw : Measure (Bid i)) (seedSet i)).map (fun b : Bid i=>(b:ℝ))

theorem measure_eq_real_cond (i : Row) (G : RestrictedLaw i) :
    measure i G=cond ((G.bidLaw : Measure (Bid i)).map (fun b : Bid i=>(b:ℝ)))
      (Iic (t i/2)) := by
  apply Measure.ext
  intro E hE
  rw [measure,Measure.map_apply measurable_subtype_coe hE,
    cond_apply (measurableSet_seedSet i),cond_apply measurableSet_Iic,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic,
    Measure.map_apply measurable_subtype_coe (measurableSet_Iic.inter hE)]
  rfl

instance measure_probability (i : Row) (G : RestrictedLaw i) : IsProbabilityMeasure (measure i G) := by
  haveI:=cond_isProbabilityMeasure (seedSet_pos i G).ne'
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem measure_singleton (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (z : ℝ) : measure i G {z}=0 := by
  apply Literal.conditional_seed_singletons (G.bidLaw : Measure (Bid i)) (seedSet i)
    (measurableSet_seedSet i) (fun b : Bid i=>(b:ℝ)) measurable_subtype_coe
  intro z
  apply measure_mono_null Set.inter_subset_right
  apply measure_eq_zero_iff_ae_notMem.mpr
  simpa only [Set.mem_preimage,Set.mem_singleton_iff] using
    LowBody.ae_injective_ne (G.bidLaw : Measure (Bid i))
      (fun b : Bid i=>(b:ℝ)) Subtype.val_injective z

variable {M : ℕ}

def seedList (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) : LocalList M :=
  fun a=> if a∈row.lower ∧ (b a:ℝ)≤ t i/2 then some (b a:ℝ) else none

lemma measurable_seedList (i : Row) (row : Source.CountRow M) : Measurable (seedList i row) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈row.lower
  · simp only [seedList,ha,true_and]
    exact Measurable.ite
      (measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply a)) measurable_const)
      (measurable_some.comp (measurable_subtype_coe.comp (measurable_pi_apply a))) measurable_const
  · simp only [seedList,ha,false_and,if_false]
    exact measurable_const

def common (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ Bid i) :
    unitInterval := (Hybrid.seedOnList (measure i G) (seedList i row b)).getD 0

lemma measurable_common (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) :
    Measurable (common i G row) := by
  have hg : Measurable (fun u : Option unitInterval=> u.getD 0) := by
    intro S hS
    change MeasurableSet S
    exact hS
  exact hg.comp ((Hybrid.measurable_seedOnList (measure i G)).comp (measurable_seedList i row))

def assignment (i : Row) (row : Source.CountRow M) (b : Fin M→ Bid i) : Fin M→ Bool :=
  fun a=> decide (a∈row.lower ∧ (b a:ℝ)≤ t i/2)

lemma measurable_assignment (i : Row) (row : Source.CountRow M) : Measurable (assignment i row) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈row.lower
  · simp only [assignment,ha,true_and]
    exact Measurable.ite
      (measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply a)) measurable_const)
      measurable_const measurable_const
  · simp only [assignment,ha,false_and,decide_false]
    exact measurable_const

def coordinateCell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool) (a : Fin M) :
    Set (Bid i) := {b | decide (a∈row.lower ∧ (b:ℝ)≤ t i/2)=k a}

lemma measurable_coordinateCell (i : Row) (row : Source.CountRow M)
    (k : Fin M→ Bool) (a : Fin M) : MeasurableSet (coordinateCell i row k a) := by
  by_cases ha : a∈row.lower <;> cases hk : k a <;>
    simp [coordinateCell,ha,hk] <;> measurability

lemma assignment_fiber (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool) :
    assignment i row ⁻¹' {k}=Set.univ.pi (coordinateCell i row k) := by
  ext b
  simp only [mem_preimage,mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies,
    assignment,coordinateCell,mem_setOf_eq,funext_iff]

def selectedSeeds (row : Source.CountRow M) (k : Fin M→ Bool) : Finset (Fin M) :=
  row.lower.filter (fun a=> k a=true)

lemma selected_cell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool)
    (a : Fin M) (ha : a∈selectedSeeds row k) : coordinateCell i row k a=seedSet i := by
  obtain ⟨hal,hk⟩:=Finset.mem_filter.mp ha
  ext b
  simp only [coordinateCell,hal,true_and,hk,decide_eq_true_eq,seedSet]

lemma list_on_cell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool)
    (b : Fin M→ Bid i) (hb : assignment i row b=k) :
    ∀a,seedList i row b a=if a∈selectedSeeds row k then some (b a:ℝ) else none := by
  intro a
  have h:=congrFun hb a
  have he : (a∈row.lower ∧ (b a:ℝ)≤ t i/2)↔a∈selectedSeeds row k := by
    rw [selectedSeeds,Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨ha.1,by simpa only [assignment,ha,true_and,decide_true] using h.symm⟩
    · rintro ⟨hal,hk⟩
      rw [hk] at h
      simpa only [assignment,decide_eq_true_eq] using h
  simp only [seedList,he]

lemma exists_enumeration (S : Finset (Fin M)) (hS : S.Nonempty) :
    ∃n : ℕ,Nonempty (Fin (n+1)≃{a : Fin M // a∈S}) := by
  refine ⟨S.card-1,⟨Fintype.equivOfCardEq ?_⟩⟩
  have hp:=Finset.card_pos.mpr hS
  simp only [Fintype.card_fin,Fintype.card_subtype]
  simpa using (show S.card-1+1=S.card by omega)

lemma common_on_cell (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (k : Fin M→ Bool) (b : Fin M→ Bid i) (hb : assignment i row b=k)
    (n : ℕ) (e : Fin (n+1)≃{a : Fin M // a∈selectedSeeds row k}) :
    common i G row b=Hybrid.conditionalMinimumSeed (measure i G) n (fun j=>(b (e j):ℝ)) := by
  rw [common,Hybrid.seedOnList_enumeration (measure i G) (fun a=> a∈selectedSeeds row k)
    e (fun a=>(b a:ℝ)) (seedList i row b) (list_on_cell i row k b hb)]
  rfl

lemma no_seed_on_empty_cell (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (k : Fin M→ Bool) (b : Fin M→ Bid i) (hb : assignment i row b=k)
    (hS : selectedSeeds row k=∅) : Source.seedCount i row (bids i (G,b))=0 := by
  have he : row.lower.filter (fun a=>(b a:ℝ)≤ t i/2)=selectedSeeds row k := by
    ext a
    have hh:=congrFun hb a
    simp only [assignment] at hh
    by_cases ha : a∈row.lower <;> simp [selectedSeeds,ha,← hh]
  simp only [Source.seedCount,bids,he,hS,Finset.card_empty]

variable [NeZero M]

def test (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (f : Allocation M→ℝ) (b : Fin M→ Bid i) : ℝ :=
  ∫s,f (NativeRow.draw i row (G,b) (common i G row b,s))
    ∂((volume : Measure unitInterval).prod volume)

lemma measurable_test (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (f : Allocation M→ℝ) : Measurable (test i G row f) := by
  have hm := (measurable_of_countable f).comp ((NativeRow.draw_joint_measurable i row).comp
    (((measurable_fixedLawState i G).comp measurable_fst).prodMk
      (((measurable_common i G row).comp measurable_fst).prodMk measurable_snd)))
  convert! hm.stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

lemma test_bound (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (f : Allocation M→ℝ) (b : Fin M→ Bid i) : |test i G row f b|≤∑P,|f P| := by
  simpa only [test,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (f:=fun s=>
      f (NativeRow.draw i row (G,b) (common i G row b,s))) (ae_of_all
      ((volume : Measure unitInterval).prod volume) (fun s=> by
        simpa only [Real.norm_eq_abs] using NativeRow.finite_bound f
          (NativeRow.draw i row (G,b) (common i G row b,s))))

lemma continuation_test_bound (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (f : Allocation M→ℝ) (b : Fin M→ Bid i) :
    |(continuationLaw i G row (bids i (G,b))).expect f|≤∑P,|f P| := by
  apply (WeightedSampling.abs_expect_le _ _).trans
  exact FiniteLaw.expect_le_const _ (NativeRow.finite_bound f)

theorem nonseed_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (row : Source.CountRow M) (a : Fin M) (_ha : a∈row.lower)
    (own : Bid i) (hown : t i/2<(own:ℝ))
    (ν : Fin M→ Measure (Bid i)) [∀j,IsProbabilityMeasure (ν j)]
    (hνa : ν a=Measure.dirac own)
    (hν : ∀j∈row.lower,j≠a→ν j=(G.bidLaw : Measure (Bid i)))
    (f : Allocation M→ℝ) :
    (∫b,test i G row f b ∂Measure.pi ν)=
      ∫b,(continuationLaw i G row (bids i (G,b))).expect f ∂Measure.pi ν := by
  have hi : Integrable (test i G row f) (Measure.pi ν) :=
    Integrable.of_bound (measurable_test i G row f).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (test_bound i G row f))
  have hj : Integrable (fun b=>(continuationLaw i G row (bids i (G,b))).expect f) (Measure.pi ν) :=
    Integrable.of_bound ((measurable_continuation_expect i row f).comp
      (measurable_fixedLawState i G)).aestronglyMeasurable
        (∑P,|f P|) (ae_of_all _ (continuation_test_bound i G row f))
  apply Literal.integral_eq_of_finite_conditional (Measure.pi ν)
    (assignment i row) (measurable_assignment i row) _ _ hi hj
  intro k hk
  let C:=coordinateCell i row k
  let νk : Fin M→ Measure (Bid i):=fun j=> cond (ν j) (C j)
  have hnonzero (j : Fin M) : ν j (C j)≠0 :=
    Literal.product_cell_coordinate_nonzero ν C (by rwa [← assignment_fiber i row k]) j
  letI (j : Fin M) : IsProbabilityMeasure (νk j):=cond_isProbabilityMeasure (hnonzero j)
  have hcond : cond (Measure.pi ν) (assignment i row ⁻¹' {k})=Measure.pi νk := by
    rw [assignment_fiber]
    exact Literal.conditional_product_cell ν C (measurable_coordinateCell i row k)
  have hcell : ∀ᵐb∂Measure.pi νk,assignment i row b=k := by
    rw [← hcond]
    exact ae_cond_mem ((measurable_assignment i row) (measurableSet_singleton k))
  rw [hcond]
  let S:=selectedSeeds row k
  have hnot : a∉S := by
    intro has
    have hCa : C a=seedSet i:=selected_cell i row k a has
    have hn:=hnonzero a
    rw [hνa,hCa,Measure.dirac_apply' _ (measurableSet_seedSet i)] at hn
    simp [seedSet,not_le_of_gt hown] at hn
  by_cases hS : S.Nonempty
  · obtain ⟨n,⟨e⟩⟩:=exists_enumeration S hS
    have hbox : ∀j∈S,∀ᵐ(b : Bid i)∂νk j,(b:ℝ)≤ t i/2 := by
      intro j hj
      have hcj : C j=seedSet i:=selected_cell i row k j hj
      have hh : ∀ᵐb∂νk j,b∈C j:=ae_cond_mem (measurable_coordinateCell i row k j)
      simpa only [hcj,seedSet,mem_setOf_eq] using hh
    have hseed : ∀j,(νk (e j)).map (fun b : Bid i=>(b:ℝ))=measure i G := by
      intro j
      have hj:= (e j).property
      have hja : (e j).val≠a:=fun he=> hnot (he ▸ hj)
      have hlow : (e j).val∈row.lower:=(Finset.mem_filter.mp hj).1
      change (cond (ν (e j)) (C (e j))).map _=_
      rw [hν (e j) hlow hja]
      change (cond (G.bidLaw : Measure (Bid i)) (coordinateCell i row k (e j))).map _=_
      rw [selected_cell i row k (e j) hj]
      rfl
    have heq := NativeRow.conditional_minimum_draw_integral i row G S νk hbox n e
      (measure i G) hseed (measure_singleton i G) f
    have hI : Integrable (fun x : (Fin M→ Bid i)×(unitInterval×unitInterval)=>
        f (NativeRow.draw i row (G,x.1)
          (Hybrid.conditionalMinimumSeed (measure i G) n (fun j=>(x.1 (e j):ℝ)),x.2)))
        ((Measure.pi νk).prod ((volume : Measure unitInterval).prod volume)) :=
      Integrable.of_bound
        ((measurable_of_countable f).comp ((NativeRow.draw_joint_measurable i row).comp
          (((measurable_fixedLawState i G).comp measurable_fst).prodMk
            (((Hybrid.measurable_conditionalMinimumSeed (measure i G) n).comp
              (measurable_pi_lambda _ (fun j=> measurable_subtype_coe.comp
                ((measurable_pi_apply (e j).val).comp measurable_fst)))).prodMk measurable_snd)))).aestronglyMeasurable
        (∑P,|f P|) (ae_of_all _ (fun x=> NativeRow.finite_bound f _))
    rw [integral_prod _ hI] at heq
    calc
      _=∫b,∫s,f (NativeRow.draw i row (G,b)
          (Hybrid.conditionalMinimumSeed (measure i G) n (fun j=>(b (e j):ℝ)),s))
          ∂((volume : Measure unitInterval).prod volume) ∂Measure.pi νk := by
        apply integral_congr_ae
        filter_upwards [hcell] with b hb
        simp only [test,common_on_cell i G row k b hb n e]
      _=_ := heq
  · have hS0 : selectedSeeds row k=∅:=Finset.not_nonempty_iff_eq_empty.mp hS
    apply integral_congr_ae
    filter_upwards [hcell] with b hb
    exact NativeRow.private_integral_common_irrelevant i row (G,b)
      (Or.inr (by simp only [Source.guardAlpha,no_seed_on_empty_cell i G row k b hb hS0,ite_true]))
      (common i G row b) f

theorem fixed_focal_trace_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower) (own : Bid i)
    (ν : Fin M→ Measure (Bid i)) [∀j,IsProbabilityMeasure (ν j)]
    (hνa : ν a=Measure.dirac own)
    (hν : ∀j∈row.lower,j≠a→ν j=(G.bidLaw : Measure (Bid i)))
    (g : Bool×Bool→ℝ) :
    (∫b,test i G row (fun P=> g (NativeRow.focalTrace a P)) b ∂Measure.pi ν)=
      ∫b,(continuationLaw i G row (bids i (G,b))).expect
        (fun P=> g (NativeRow.focalTrace a P)) ∂Measure.pi ν := by
  by_cases hown : (own:ℝ)≤ t i/2
  · have hownae : ∀ᵐb∂Measure.pi ν,b a=own := by
      have he : ∀ᵐb∂ν a,b=own := by rw [hνa]; simp
      exact (measurePreserving_eval ν a).quasiMeasurePreserving.ae he
    apply integral_congr_ae
    filter_upwards [hownae] with b hb
    exact NativeRow.fixed_seed_trace_integral i row (G,b) a ha
      (by simpa only [bids,hb] using hown) (common i G row b) g
  · exact nonseed_integral i G row a ha own (lt_of_not_ge hown) ν hνa hν _

end NativeSeed
end FCAppendix.Affine.UniformFinite
