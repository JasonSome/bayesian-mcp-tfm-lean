import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalSeed
import FCAppendix.Affine.UniformFinite.Late.NativeExceptional
import FCAppendix.Affine.UniformFinite.NativeConditional

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.ExceptionalSeed
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 WeightedSampling
open scoped BigOperators

def bidMeasure (i : Row) (G : RestrictedLaw i) : Measure ℝ :=
  (G.bidLaw : Measure (Bid i)).map (fun b : Bid i => (b:ℝ))

instance bidMeasure_probability (i : Row) (G : RestrictedLaw i) :
    IsProbabilityMeasure (bidMeasure i G) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem bidMeasure_box (i : Row) (G : RestrictedLaw i) :
    ∀ᵐb∂bidMeasure i G,0≤ b ∧ b≤ cap i := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun b => b.property)

theorem conditional_seed_measure (i : Row) (G : RestrictedLaw i) :
    cond (bidMeasure i G) (Iic (t i/2))=NativeSeed.measure i G :=
  (NativeSeed.measure_eq_real_cond i G).symm

variable {M : ℕ} [NeZero M]

def seedList (i : Row) (row : Source.CountRow M) (b : Fin M→ℝ) : LocalList M :=
  fun a=> if a∈row.lower ∧ b a≤ t i/2 then some (b a) else none

omit [NeZero M] in
theorem measurable_seedList (i : Row) (row : Source.CountRow M) : Measurable (seedList i row) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈row.lower
  · simp only [seedList,ha,true_and]
    exact Measurable.ite (measurableSet_le (measurable_pi_apply a) measurable_const)
      (measurable_some.comp (measurable_pi_apply a)) measurable_const
  · simp only [seedList,ha,false_and,if_false]
    exact measurable_const

def common (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (b : Fin M→ℝ) :
    unitInterval := (Hybrid.seedOnList (NativeSeed.measure i G) (seedList i row b)).getD 0

omit [NeZero M] in
theorem measurable_common (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) :
    Measurable (common i G row) := by
  have hg : Measurable (fun u : Option unitInterval=> u.getD 0) := by
    intro S hS
    change MeasurableSet S
    exact hS
  exact hg.comp ((Hybrid.measurable_seedOnList (NativeSeed.measure i G)).comp (measurable_seedList i row))

omit [NeZero M] in

theorem common_context (i : Row) (G : RestrictedLaw i) (X : Hybrid.ClassifiedContext M) :
    common i G (NativeContext.decode X) (NativeExceptional.rawBids X)=
      NativeContext.common i (NativeSeed.measure i G) X := by
  have he : seedList i (NativeContext.decode X) (NativeExceptional.rawBids X)=
      TaggedLocal.lowList (t i/2) (cap i) X.1 := by
    funext a
    cases ha : X.1 a with
    | none => simp [seedList,NativeContext.decode,NativeContext.present,NativeExceptional.rawBids,
        TaggedLocal.lowList,TaggedLocal.tag,ha]
    | some b =>
      by_cases hb : b≤ t i/2 <;> by_cases hU : b≤ cap i <;>
        simp [seedList,NativeContext.decode,NativeContext.present,NativeExceptional.rawBids,entryBid,
          TaggedLocal.lowList,TaggedLocal.tag,ha,hb,hU]
  simp only [common,NativeContext.common,Hybrid.observedLowSeed,he]

def assignment (i : Row) (row : Source.CountRow M) (b : Fin M→ℝ) : Fin M→ Bool :=
  fun a=> decide (a∈row.lower ∧ b a≤ t i/2)

omit [NeZero M] in
theorem measurable_assignment (i : Row) (row : Source.CountRow M) : Measurable (assignment i row) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈row.lower
  · simp only [assignment,ha,true_and]
    exact Measurable.ite (measurableSet_le (measurable_pi_apply a) measurable_const)
      measurable_const measurable_const
  · simp only [assignment,ha,false_and,decide_false]
    exact measurable_const

def coordinateCell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool) (a : Fin M) : Set ℝ :=
  {b | decide (a∈row.lower ∧ b≤ t i/2)=k a}

omit [NeZero M] in
theorem measurable_coordinateCell (i : Row) (row : Source.CountRow M)
    (k : Fin M→ Bool) (a : Fin M) : MeasurableSet (coordinateCell i row k a) := by
  by_cases ha : a∈row.lower <;> cases hk : k a <;>
    simp [coordinateCell,ha,hk] <;> measurability

omit [NeZero M] in
theorem assignment_fiber (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool) :
    assignment i row ⁻¹' {k}=Set.univ.pi (coordinateCell i row k) := by
  ext b
  simp only [mem_preimage,mem_singleton_iff,Set.mem_pi,Set.mem_univ,true_implies,
    assignment,coordinateCell,mem_setOf_eq,funext_iff]

abbrev selectedSeeds (row : Source.CountRow M) (k : Fin M→ Bool) := NativeSeed.selectedSeeds row k

omit [NeZero M] in
theorem selected_cell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool)
    (a : Fin M) (ha : a∈selectedSeeds row k) : coordinateCell i row k a=Iic (t i/2) := by
  obtain ⟨hal,hk⟩ := Finset.mem_filter.mp ha
  ext b
  simp only [coordinateCell,hal,true_and,hk,decide_eq_true_eq,mem_Iic,mem_setOf_eq]

omit [NeZero M] in
theorem list_on_cell (i : Row) (row : Source.CountRow M) (k : Fin M→ Bool)
    (b : Fin M→ℝ) (hb : assignment i row b=k) :
    ∀a,seedList i row b a=if a∈selectedSeeds row k then some (b a) else none := by
  intro a
  have h := congrFun hb a
  have he : (a∈row.lower ∧ b a≤ t i/2)↔a∈selectedSeeds row k := by
    change (a∈row.lower ∧ b a≤t i/2)↔a∈row.lower.filter (fun j=>k j=true)
    rw [Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨ha.1,by simpa only [assignment,ha.1,ha.2,and_self,decide_true] using h.symm⟩
    · rintro ⟨hal,hk⟩
      rw [hk] at h
      simpa only [assignment,decide_eq_true_eq] using h
  simp only [seedList,he]

omit [NeZero M] in
theorem common_on_cell (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (k : Fin M→ Bool) (b : Fin M→ℝ) (hb : assignment i row b=k)
    (n : ℕ) (e : Fin (n+1)≃{a : Fin M // a∈selectedSeeds row k}) :
    common i G row b=Hybrid.conditionalMinimumSeed (NativeSeed.measure i G) n (fun j=> b (e j)) := by
  rw [common,Hybrid.seedOnList_enumeration (NativeSeed.measure i G)
    (fun a=> a∈selectedSeeds row k) e b (seedList i row b) (list_on_cell i row k b hb)]
  rfl

omit [NeZero M] in

theorem alpha_zero_on_empty_cell (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (k : Fin M→ Bool) (b : Fin M→ℝ) (hb : assignment i row b=k)
    (hS : selectedSeeds row k=∅) : Exceptional.alpha i G row b a=0 := by
  have hnone (j : Fin M) (hj : j∈row.lower) : ¬ b j≤ t i/2 := by
    intro hbj
    have hk : k j=true := by simpa only [assignment,hj,hbj,and_self,decide_true] using (congrFun hb j).symm
    have hmem : j∈selectedSeeds row k := Finset.mem_filter.mpr ⟨hj,hk⟩
    rw [hS] at hmem
    exact Finset.notMem_empty j hmem
  have hsub : row.lower.filter (fun j=> Exceptional.ordinary row b a j≤ t i/2)⊆{a} := by
    intro j hj
    obtain ⟨hjl,hjb⟩ := Finset.mem_filter.mp hj
    by_contra hja
    have hne : j≠a := by simpa only [Finset.mem_singleton] using hja
    simp only [Exceptional.ordinary,Function.update_of_ne hne,Source.lowerBids_of_mem row b hjl] at hjb
    exact hnone j hjl hjb
  have hcount : Source.seedCount i row (Exceptional.ordinary row b a)≤1 := by
    simpa only [Source.seedCount,Finset.card_singleton] using Finset.card_le_card hsub
  unfold Exceptional.alpha
  rw [if_neg (by intro h; omega)]

def test (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (a : Fin M)
    (f : Allocation M→ℝ) (b : Fin M→ℝ) : ℝ :=
  ∫s,f (NativeExceptionalRow.draw i G row a b (common i G row b,s))
    ∂((volume : Measure unitInterval).prod volume)

theorem measurable_test (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (f : Allocation M→ℝ) : Measurable (test i G row a f) := by
  have hm := (measurable_of_countable f).comp ((NativeExceptionalRow.draw_joint_measurable i G row a).comp
    (measurable_fst.prodMk (((measurable_common i G row).comp measurable_fst).prodMk measurable_snd)))
  convert! hm.stronglyMeasurable.integral_prod_right'.measurable using 1
  infer_instance

theorem test_bound (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (f : Allocation M→ℝ) (b : Fin M→ℝ) : |test i G row a f b|≤∑P,|f P| := by
  simpa only [test,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (f:=fun s : unitInterval×unitInterval=>
        f (NativeExceptionalRow.draw i G row a b (common i G row b,s))) (ae_of_all
      ((volume : Measure unitInterval).prod volume) (fun s=> by
        simpa only [Real.norm_eq_abs] using NativeRow.finite_bound f
          (NativeExceptionalRow.draw i G row a b (common i G row b,s))))

theorem measurable_continuation_expect (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (a : Fin M) (f : Allocation M→ℝ) :
    Measurable (fun b=>(Exceptional.continuationLaw i G row b a).expect f) := by
  change Measurable (fun b=>∑P,(Exceptional.continuationLaw i G row b a).mass P*f P)
  exact Finset.measurable_sum _ (fun P _=>(Exceptional.measurable_continuationLaw_mass i G row a P).mul_const _)

theorem continuation_bound (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (f : Allocation M→ℝ) (b : Fin M→ℝ) :
    |(Exceptional.continuationLaw i G row b a).expect f|≤∑P,|f P| := by
  apply (WeightedSampling.abs_expect_le _ _).trans
  exact FiniteLaw.expect_le_const _ (NativeRow.finite_bound f)

omit [NeZero M] in
theorem product_good (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (ha : a∈row.lower) (own : ℝ) (hown : 0≤ own)
    (ν : Fin M→ Measure ℝ) [∀j,IsProbabilityMeasure (ν j)] (hνa : ν a=Measure.dirac own)
    (hν : ∀j∈row.lower,j≠a→ν j=bidMeasure i G) :
    ∀ᵐb∂Measure.pi ν,NativeExceptionalRow.Good i row a b := by
  have hcoord : ∀ᵐb∂Measure.pi ν,∀j,j∈row.lower → 0≤ b j ∧ (j≠a → b j≤ cap i) := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j∈row.lower
    · have hr : ∀ᵐ x ∂ν j,0≤x ∧ (j≠a→x≤cap i) := by
        by_cases hja : j=a
        · subst j
          rw [hνa]
          simp [hown]
        · rw [hν j hj hja]
          exact (bidMeasure_box i G).mono (fun b hb=>⟨hb.1,fun _=>hb.2⟩)
      exact ((measurePreserving_eval ν j).quasiMeasurePreserving.ae hr).mono
        (fun _ hb _=>hb)
    · exact ae_of_all _ (fun b h=> False.elim (hj h))
  filter_upwards [hcoord] with b hb
  exact ⟨ha,fun j hj=>(hb j hj).1,fun j hj hja=>(hb j hj).2 hja⟩

theorem fixed_exception_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (own : ℝ) (hown : cap i< own)
    (ν : Fin M→ Measure ℝ) [∀j,IsProbabilityMeasure (ν j)]
    (hνa : ν a=Measure.dirac own) (hν : ∀j∈row.lower,j≠a→ν j=bidMeasure i G)
    (f : Allocation M→ℝ) :
    (∫b,test i G row a f b ∂Measure.pi ν)=
      ∫b,(Exceptional.continuationLaw i G row b a).expect f ∂Measure.pi ν := by
  have hi : Integrable (test i G row a f) (Measure.pi ν) :=
    Integrable.of_bound (measurable_test i G row a f).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (test_bound i G row a f))
  have hj : Integrable (fun b=>(Exceptional.continuationLaw i G row b a).expect f) (Measure.pi ν) :=
    Integrable.of_bound (measurable_continuation_expect i G row a f).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (continuation_bound i G row a f))
  have hgood := product_good i G row a ha own ((cap_pos i).trans hown).le ν hνa hν
  apply Literal.integral_eq_of_finite_conditional (Measure.pi ν)
    (assignment i row) (measurable_assignment i row) _ _ hi hj
  intro k hk
  let C := coordinateCell i row k
  let νk : Fin M→ Measure ℝ := fun j=> cond (ν j) (C j)
  have hnonzero (j : Fin M) : ν j (C j)≠0 :=
    Literal.product_cell_coordinate_nonzero ν C (by rwa [← assignment_fiber i row k]) j
  letI (j : Fin M) : IsProbabilityMeasure (νk j) := cond_isProbabilityMeasure (hnonzero j)
  have hcond : cond (Measure.pi ν) (assignment i row ⁻¹' {k})=Measure.pi νk := by
    rw [assignment_fiber]
    exact Literal.conditional_product_cell ν C (measurable_coordinateCell i row k)
  have hcell : ∀ᵐb∂Measure.pi νk,assignment i row b=k := by
    rw [← hcond]
    exact ae_cond_mem ((measurable_assignment i row) (measurableSet_singleton k))
  have hgcell : ∀ᵐb∂Measure.pi νk,NativeExceptionalRow.Good i row a b := by
    rw [← hcond]
    exact ProbabilityTheory.cond_absolutelyContinuous.ae_le hgood
  rw [hcond]
  let S := selectedSeeds row k
  have hnot : a∉S := by
    intro has
    have hCa : C a=Iic (t i/2) := selected_cell i row k a has
    have hn := hnonzero a
    have hseedcap : t i/2< cap i := by
      have hc := chi_t_lt_cap i
      norm_num [chi] at hc
      nlinarith [t_pos i]
    have hcut : t i/2< own := hseedcap.trans hown
    rw [hνa,hCa,Measure.dirac_apply' _ measurableSet_Iic] at hn
    have hnotmem : own∉Iic (t i/2) := not_le_of_gt hcut
    have hz : (Iic (t i/2)).indicator (1 : ℝ→ENNReal) own=0 :=
      Set.indicator_of_notMem hnotmem _
    exact hn hz
  by_cases hS : S.Nonempty
  · obtain ⟨n,⟨e⟩⟩ := NativeSeed.exists_enumeration S hS
    have hbox : ∀j∈S,∀ᵐb∂νk j,b≤ t i/2 := by
      intro j hj
      have hcj : C j=Iic (t i/2) := selected_cell i row k j hj
      have hh : ∀ᵐb∂νk j,b∈C j := ae_cond_mem (measurable_coordinateCell i row k j)
      simpa only [hcj,mem_Iic] using hh
    have hseed : ∀j,νk (e j)=NativeSeed.measure i G := by
      intro j
      have hj := (e j).property
      have hja : (e j).val≠a := fun he=> hnot (he ▸ hj)
      have hlow : (e j).val∈row.lower := (Finset.mem_filter.mp hj).1
      change cond (ν (e j)) (C (e j))=_
      rw [hν (e j) hlow hja]
      change cond (bidMeasure i G) (coordinateCell i row k (e j))=_
      rw [selected_cell i row k (e j) hj,conditional_seed_measure]
    have heq := NativeExceptionalRow.conditional_minimum_draw_integral i G row a S νk hgcell hbox n e
      (NativeSeed.measure i G) hseed (NativeSeed.measure_singleton i G) f
    have hI : Integrable (fun x : (Fin M→ℝ)×(unitInterval×unitInterval)=>
        f (NativeExceptionalRow.draw i G row a x.1
          (Hybrid.conditionalMinimumSeed (NativeSeed.measure i G) n (fun j=> x.1 (e j)),x.2)))
        ((Measure.pi νk).prod ((volume : Measure unitInterval).prod volume)) :=
      Integrable.of_bound
        ((measurable_of_countable f).comp ((NativeExceptionalRow.draw_joint_measurable i G row a).comp
          (measurable_fst.prodMk
            (((Hybrid.measurable_conditionalMinimumSeed (NativeSeed.measure i G) n).comp
              (measurable_pi_lambda _ (fun j=>(measurable_pi_apply (e j).val).comp measurable_fst))).prodMk
                measurable_snd)))).aestronglyMeasurable
        (∑P,|f P|) (ae_of_all _ (fun x=> NativeRow.finite_bound f _))
    rw [integral_prod _ hI] at heq
    calc
      _=∫b,∫s,f (NativeExceptionalRow.draw i G row a b
          (Hybrid.conditionalMinimumSeed (NativeSeed.measure i G) n (fun j=> b (e j)),s))
          ∂((volume : Measure unitInterval).prod volume) ∂Measure.pi νk := by
        apply integral_congr_ae
        filter_upwards [hcell] with b hb
        simp only [test,common_on_cell i G row k b hb n e]
      _=_ := heq
  · have hS0 : selectedSeeds row k=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    apply integral_congr_ae
    filter_upwards [hcell] with b hb
    exact NativeExceptionalRow.private_integral_common_irrelevant i G row a b
      (Or.inr (alpha_zero_on_empty_cell i G row a k b hb hS0)) (common i G row b) f

end FCAppendix.Affine.UniformFinite.Late.ExceptionalSeed
