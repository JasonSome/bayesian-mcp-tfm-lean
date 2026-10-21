import FCAppendix.Affine.UniformFinite.OriginalDrawTransport
import FCAppendix.Affine.UniformFinite.ActualDuplicateEvent

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators ENNReal
namespace ActualAtoms

lemma zc_value_bounds (i : Row) : 0≤ Uniform05.zc i ∧ Uniform05.zc i≤ Uniform05.t i := by
  have ht := Uniform05.t_pos i
  have he : Uniform05.zc i=(Uniform05.x i+1/200)*Uniform05.t i := by
    dsimp [Uniform05.zc,Uniform05.lambda]; ring
  rw [he]
  constructor
  · have hx : 0≤ Uniform05.x i+1/200 := by cases i <;> norm_num [Uniform05.x]
    positivity
  · have hx : Uniform05.x i+1/200≤1 := by cases i <;> norm_num [Uniform05.x]
    nlinarith

lemma lower_value_Iic_probability (i : Row) (a : ℝ) (_ha : 0≤ a)
    (hat : a≤ Uniform05.t i) :
    lowerMeasure i {v | (v:ℝ)≤ a}=ENNReal.ofReal (a/Uniform05.t i) := by
  have hm := lowerMeasure_real i
  have he := congrArg (fun μ : Measure ℝ=>μ (Iic a)) hm
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic] at he
  change lowerMeasure i ((Subtype.val : Value i→ℝ) ⁻¹' Iic a)=_
  rw [he]
  have hs : Iic a∩Icc (0:ℝ) (Uniform05.t i)=Icc 0 a := by
    ext v
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hv,hv0,_⟩; exact ⟨hv0,hv⟩
    · rintro ⟨hv0,hv⟩; exact ⟨hv,hv0,hv.trans hat⟩
  simp only [Uniform05.lowerValueMeasure,Measure.smul_apply,
    Measure.restrict_apply measurableSet_Iic,hs,Real.volume_Icc,sub_zero,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (div_nonneg (by norm_num) (Uniform05.t_pos i).le)]
  congr 1
  ring

def originalLowEvent (i : Row) : Set (RivalDraw i) :=
  {x | x.1=0 ∧ (x.2.1.1:ℝ)≤ Uniform05.zc i}

lemma measurableSet_originalLowEvent (i : Row) : MeasurableSet (originalLowEvent i) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    (measurableSet_le (measurable_subtype_coe.comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))) measurable_const)

theorem originalLowEvent_probability (i : Row) (pi : Joint i) :
    (rivalDrawLaw i pi).real (originalLowEvent i)=Uniform05.zc i := by
  have hz := zc_value_bounds i
  have he := rival_lower_original_value_event i pi
    {v | (v:ℝ)≤ Uniform05.zc i}
    (measurableSet_le measurable_subtype_coe measurable_const)
  rw [lower_value_Iic_probability i _ hz.1 hz.2,
    ← ENNReal.ofReal_mul (Uniform05.t_pos i).le] at he
  have hp : Uniform05.t i*(Uniform05.zc i/Uniform05.t i)=Uniform05.zc i := by
    field_simp [(Uniform05.t_pos i).ne']
  rw [hp] at he
  exact (congrArg ENNReal.toReal he).trans (ENNReal.toReal_ofReal hz.1)

def originalClusterEvent (i : Row) (eps : unitInterval) (s : Set ℝ) : Set (RivalDraw i) :=
  {x | x.1=0 ∧ (drawBid i eps x.2:ℝ)∈s}

lemma measurableSet_originalClusterEvent (i : Row) (eps : unitInterval)
    (s : Set ℝ) (hs : MeasurableSet s) :
    MeasurableSet (originalClusterEvent i eps s) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter
    ((measurable_subtype_coe.comp ((measurable_drawBid i eps).comp measurable_snd)) hs)

theorem originalClusterEvent_probability (i : Row) (eps : unitInterval) (pi : Joint i)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (rivalDrawLaw i pi).real (originalClusterEvent i eps s)=
      Uniform05.t i*((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)).real
        ((Subtype.val : Bid i→ℝ) ⁻¹' s) := by
  have he := rival_lower_bid_event i eps pi
    ((Subtype.val : Bid i→ℝ) ⁻¹' s) (measurable_subtype_coe hs)
  apply_fun ENNReal.toReal at he
  simpa only [originalClusterEvent,Measure.real,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Uniform05.t_pos i).le,mem_preimage] using he

def deletedHarmfulEvent (i : Row) (N : ℕ) (eps : unitInterval)
    (s : Set ℝ) : Set (Fin (N+1)→ RivalDraw i) :=
  {ω | ∃j : Fin (N+1), ω j∈originalClusterEvent i eps s ∧
    N+2-2*Uniform07.capacity (N+2)≤ PiBinomial.count (originalLowEvent i)
      Finset.univ (fun k=>ω (j.succAbove k))}

lemma measurableSet_deletedHarmfulEvent (i : Row) (N : ℕ) (eps : unitInterval)
    (s : Set ℝ) (hs : MeasurableSet s) :
    MeasurableSet (deletedHarmfulEvent i N eps s) := by
  have he : deletedHarmfulEvent i N eps s =
      (⋃j : Fin (N+1),{ω : Fin (N+1)→RivalDraw i | ω j∈originalClusterEvent i eps s ∧
    N+2-2*Uniform07.capacity (N+2)≤ PiBinomial.count (originalLowEvent i)
      Finset.univ (fun k=>ω (j.succAbove k))}) := by
    ext ω
    simp [deletedHarmfulEvent]
  rw [he]
  apply MeasurableSet.iUnion
  intro j
  have h1 : MeasurableSet {ω : Fin (N+1)→RivalDraw i |
      ω j∈originalClusterEvent i eps s} :=
    (measurableSet_originalClusterEvent i eps s hs).preimage (measurable_pi_apply j)
  have hdel : Measurable (fun ω : Fin (N+1)→RivalDraw i =>
      fun k : Fin N => ω (j.succAbove k)) :=
    measurable_pi_lambda _ (fun k=>measurable_pi_apply (j.succAbove k))
  have h2 := (AtomEvents.measurableSet_count_upper N
    (N+2-2*Uniform07.capacity (N+2)) (originalLowEvent i)
    (measurableSet_originalLowEvent i)).preimage hdel
  convert! h1.inter h2 using 1

theorem deletedHarmfulEvent_probability (i : Row) (N : ℕ)
    (eps : unitInterval) (pi : Joint i) (s : Set ℝ) (hs : MeasurableSet s) :
    (Measure.pi (fun _ : Fin (N+1)=> rivalDrawLaw i pi)).real
      (deletedHarmfulEvent i N eps s) ≤
      ((N+1:ℕ):ℝ)*Uniform05.t i*
        ((restrictedLaw i (eps,pi)).bidLaw : Measure (Bid i)).real
          ((Subtype.val : Bid i→ℝ) ⁻¹' s)*
        AtomEvents.duplicateEvent (Uniform05.zc i) (Uniform05.zc_probability_bounds i).1
          (Uniform05.zc_probability_bounds i).2 (N+2) := by
  have h := AtomEvents.harmful_deleted_count_probability (rivalDrawLaw i pi)
    (originalClusterEvent i eps s) (originalLowEvent i)
    (measurableSet_originalClusterEvent i eps s hs) (measurableSet_originalLowEvent i)
    N (N+2-2*Uniform07.capacity (N+2))
  have hLow := originalLowEvent_probability i pi
  have htail : (IndependentCounts.binomial N ((rivalDrawLaw i pi).real (originalLowEvent i))
      measureReal_nonneg measureReal_le_one).prob
      (fun r=>N+2-2*Uniform07.capacity (N+2)≤r.val) =
      AtomEvents.duplicateEvent (Uniform05.zc i) (Uniform05.zc_probability_bounds i).1
        (Uniform05.zc_probability_bounds i).2 (N+2) := by
    rw [FiniteLaw.prob_eq_expect]
    unfold AtomEvents.duplicateEvent
    conv_rhs => rw [FiniteLaw.prob_eq_expect]
    change ActualBoundary.binomialMean N ((rivalDrawLaw i pi).real (originalLowEvent i)) _ _
      (fun n=>if N+2-2*Uniform07.capacity (N+2)≤n then (1:ℝ) else 0) =
      ActualBoundary.binomialMean (N+2-2) (Uniform05.zc i) _ _
        (fun n=>if N+2-2*Uniform07.capacity (N+2)≤n then (1:ℝ) else 0)
    rw [Nat.add_sub_cancel]
    congr 1
  rw [originalClusterEvent_probability i eps pi s hs,htail] at h
  simpa only [deletedHarmfulEvent,AtomEvents.duplicateEvent,Nat.add_sub_cancel,
    mul_assoc] using h

lemma lower_value_count_delete {N : ℕ} (i : Row) (ω : Fin (N+1)→ RivalDraw i)
    (j : Fin (N+1)) :
    (((focalRow (fun k=>(ω k).1)).lower.filter
      (fun a : Fin (N+2)=> a≠0 ∧
        ((Fin.cons (0:ℝ) (fun k : Fin (N+1)=>((ω k).2.1.1:ℝ)) : Fin (N+2)→ℝ) a)≤ Uniform05.zc i)).erase j.succ).card =
      PiBinomial.count (originalLowEvent i) Finset.univ (fun k=>ω (j.succAbove k)) := by
  classical
  rw [PiBinomial.count]
  symm
  apply Finset.card_bij (fun k _ => (j.succAbove k).succ)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨by intro he; exact Fin.succAbove_ne j k (Fin.succ_injective _ he),?_⟩
    apply Finset.mem_filter.mpr
    have hp := (Finset.mem_filter.mp hk).2
    refine ⟨by simpa [focalRow,Source.countRowOfKind] using hp.1,
      Fin.succ_ne_zero _,?_⟩
    simpa only [Fin.cons_succ] using hp.2
  · intro k hk l hl he
    exact Fin.succAbove_right_injective (Fin.succ_injective _ he)
  · intro a ha
    obtain ⟨haj,ha⟩ := Finset.mem_erase.mp ha
    obtain ⟨hal,ha0,hav⟩ := Finset.mem_filter.mp ha
    have hpred : Fin.pred a ha0≠j := by
      intro he
      apply haj
      rw [← Fin.succ_pred a ha0,he]
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hpred
    refine ⟨k,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rw [hk]
      have hcat : (ω (Fin.pred a ha0)).1 =
          (Fin.cons (0:Fin 3) (fun k : Fin (N+1)=>(ω k).1) : Fin (N+2)→Fin 3) a := by
        simpa only [Fin.cons_succ] using
          congrArg (Fin.cons (0:Fin 3) (fun k : Fin (N+1)=>(ω k).1) : Fin (N+2)→Fin 3)
            (Fin.succ_pred a ha0)
      have hval : ((ω (Fin.pred a ha0)).2.1.1:ℝ) =
          (Fin.cons (0:ℝ) (fun k : Fin (N+1)=>((ω k).2.1.1:ℝ)) : Fin (N+2)→ℝ) a :=
        congrArg (Fin.cons (0:ℝ) (fun k : Fin (N+1)=>((ω k).2.1.1:ℝ))) (Fin.succ_pred a ha0)
      exact ⟨hcat.trans (by simpa [focalRow,Source.countRowOfKind] using hal),
        hval.le.trans hav⟩
    · rw [hk,Fin.succ_pred a ha0]

theorem duplicate_subset_deletedHarmful (i : Row) (N : ℕ)
    (hM : 2*Uniform07.capacity (N+2)≤ N+2)
    (eps : unitInterval) (v : Value i) (q z : unitInterval)
    (ω : Fin (N+1)→ RivalDraw i) (target : ℝ)
    (hpos : 0<(drawBid i eps ((v,q),z):ℝ))
    (hraise : (drawBid i eps ((v,q),z):ℝ)< target)
    (hcap : target≤ Uniform05.cap i) (s : Set ℝ)
    (hI : Icc (drawBid i eps ((v,q),z):ℝ) target⊆s)
    (hK : Icc (Uniform05.kappa i*(drawBid i eps ((v,q),z):ℝ))
      (Uniform05.kappa i*target)⊆s)
    (hdup : let row:=focalRow (fun k=>(ω k).1)
      let b:=focalBids i (fun k=>(ω k).1) (drawBid i eps ((v,q),z))
        (fun k=> drawBid i eps (ω k).2)
      LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
        (Source.lowerBids row b)) 0≠2 ∧
      LowBody.focalCopy ((Source.lowerTemplate row).selection (Uniform05.kappa i)
        (Source.lowerBids row (Function.update b 0 target))) 0=2) :
    ω∈deletedHarmfulEvent i N eps s := by
  let row:=focalRow (fun k=>(ω k).1)
  let b:=focalBids i (fun k=>(ω k).1) (drawBid i eps ((v,q),z))
    (fun k=> drawBid i eps (ω k).2)
  let value : Fin (N+2)→ℝ:=Fin.cons (v:ℝ) (fun k=>((ω k).2.1.1:ℝ))
  have hf := ActualSurplus.focalRow_focal_mem (fun k=>(ω k).1)
  have hb (a : Fin (N+2)) : a∈row.lower → 0≤ b a := by
    refine Fin.cases ?_ (fun k=>?_) a
    · intro _; exact (drawBid i eps ((v,q),z)).property.1
    · intro ha
      have hk : (ω k).1=0 := by simpa [row,focalRow,Source.countRowOfKind] using ha
      simpa [b,focalBids,hk] using (drawBid i eps (ω k).2).property.1
  have hfloor (a : Fin (N+2)) : a∈row.lower →
      Uniform05.floorBid i (value a)≤ b a := by
    refine Fin.cases ?_ (fun k=>?_) a
    · intro _; convert! (noisyRealBid_bounds i eps v q z).1 using 1
    · intro ha
      have hk : (ω k).1=0 := by simpa [row,focalRow,Source.countRowOfKind] using ha
      convert! (noisyRealBid_bounds i eps (ω k).2.1.1 (ω k).2.1.2 (ω k).2.2).1 using 1
      simp [b,focalBids,hk,drawBid,noisyBid]
  obtain ⟨a,hal,ha0,hc,hcount⟩ := harmful_duplicate_original_value_count
    i row hM b value hb hfloor 0 hf hpos target hraise hcap hdup.1 hdup.2
  let j:=Fin.pred a ha0
  have he : a=j.succ := (Fin.succ_pred a ha0).symm
  have hj : (ω j).1=0 := by
    rw [he] at hal
    simpa [row,focalRow,Source.countRowOfKind] using hal
  refine ⟨j,⟨hj,?_⟩,?_⟩
  · rw [he] at hc
    have hc' : (drawBid i eps (ω j).2:ℝ)∈
        Icc (drawBid i eps ((v,q),z):ℝ) target ∨
      (drawBid i eps (ω j).2:ℝ)∈
        Icc (Uniform05.kappa i*(drawBid i eps ((v,q),z):ℝ))
          (Uniform05.kappa i*target) := by
      simpa [b,focalBids,hj] using hc
    exact hc'.elim (fun h=>hI h) (fun h=>hK h)
  · rw [he] at hcount
    have hcounts := lower_value_count_delete i ω j
    have hvset : (row.lower.filter (fun a=> a≠0 ∧ value a≤ Uniform05.zc i)).erase j.succ =
        ((focalRow (fun k=>(ω k).1)).lower.filter
          (fun a=> a≠0 ∧ ((Fin.cons (0:ℝ) (fun k : Fin (N+1)=>((ω k).2.1.1:ℝ)) : Fin (N+2)→ℝ) a)≤ Uniform05.zc i)).erase j.succ := by
      ext a
      refine Fin.cases ?_ (fun k=>?_) a <;> simp [value,row]
    rw [hvset,hcounts] at hcount
    exact hcount

end ActualAtoms
end FCAppendix.Affine.UniformFinite
