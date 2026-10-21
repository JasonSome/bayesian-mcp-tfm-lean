import FCAppendix.Affine.Uniform06.FullSourceSpecialization
import FCAppendix.Affine.Uniform06.EntryReciprocalLimit

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullBidGeometry

open MeasureTheory Set Filter Topology
open Uniform07 FullJointLaw EarlyJointCompactness

theorem active_strictMonoOn (i : Row) :
    StrictMonoOn (ActiveGraphComponent.activeBid i) (Ici (entry i)) := by
  intro v hv w hw hvw
  have hentry := EarlyMean.entry_pos i
  have hv0 := hentry.trans_le hv
  have hw0 := hentry.trans_le hw
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hξ := xi_pos i
  have hvd : 0 < kappa i*v+xi i*entry i :=
    add_pos (mul_pos hκ hv0) (mul_pos hξ hentry)
  have hwd : 0 < kappa i*w+xi i*entry i :=
    add_pos (mul_pos hκ hw0) (mul_pos hξ hentry)
  unfold ActiveGraphComponent.activeBid
  apply (div_lt_div_iff₀ hvd hwd).mpr
  have hp := mul_pos (mul_pos hξ (sq_pos_of_pos hentry)) (sub_pos.mpr hvw)
  nlinarith

theorem strictMonoOn_bid (i : Row) : StrictMonoOn (bid i) (Icc (0:ℝ) (cutoff i)) := by
  intro v hv w hw hvw
  by_cases hwL : w ≤ entry i
  · have hvL := hvw.le.trans hwL
    simp only [bid,if_pos hvL,if_pos hwL]
    exact hvw
  · have hwL' := lt_of_not_ge hwL
    unfold bid
    rw [if_neg hwL,extendedActive_eq i hw.1]
    by_cases hvL : v ≤ entry i
    · rw [if_pos hvL]
      exact hvL.trans_lt (EntryReciprocalLimit.entry_lt_activeBid i hwL')
    · rw [if_neg hvL,extendedActive_eq i hv.1]
      exact active_strictMonoOn i (le_of_lt (lt_of_not_ge hvL)) hwL'.le hvw

theorem full_bid_singleton_null (i : Row) (a : ℝ) :
    ((law i:Measure (ℝ × ℝ)).map Prod.snd) {a}=0 := by
  have hvalue : ∀ᵐ v ∂LowChernoff.conditionalValueLaw i,v ∈ Icc (0:ℝ) (cutoff i) := by
    rw [LowChernoff.conditionalValueLaw]
    exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _
  have he : ∀ᵐ v ∂LowChernoff.conditionalValueLaw i,bid i v ≠ a := by
    by_cases hex : ∃ v ∈ Icc (0:ℝ) (cutoff i),bid i v=a
    · obtain ⟨v,hv,hva⟩ := hex
      have hne : ∀ᵐ w ∂LowChernoff.conditionalValueLaw i,w ≠ v := by
        rw [LowChernoff.conditionalValueLaw]
        exact Measure.ae_smul_measure (ae_restrict_of_ae (volume.ae_ne v)) _
      filter_upwards [hvalue,hne] with w hw hwv hwa
      exact hwv ((strictMonoOn_bid i).injOn hw hv (hwa.trans hva.symm))
    · exact hvalue.mono fun v hv he => hex ⟨v,hv,he⟩
  change (((LowChernoff.conditionalValueLaw i).map (fun v => (v,bid i v))).map Prod.snd) {a}=0
  have hgraph : Measurable (fun v : ℝ=>(v,bid i v)) := by
    convert! measurable_id.prodMk (measurable_bid i) using 1
  rw [Measure.map_map measurable_snd hgraph]
  change ((LowChernoff.conditionalValueLaw i).map (bid i)) {a}=0
  rw [Measure.map_apply (measurable_bid i) (measurableSet_singleton a)]
  exact (measure_eq_zero_iff_ae_notMem).mpr he

theorem full_value_marginal (i : Row) :
    (law i:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i := by
  change (((LowChernoff.conditionalValueLaw i).map (fun v => (v,bid i v))).map Prod.fst)=_
  have hgraph : Measurable (fun v : ℝ=>(v,bid i v)) := by
    convert! measurable_id.prodMk (measurable_bid i) using 1
  rw [Measure.map_map measurable_fst hgraph]
  change (LowChernoff.conditionalValueLaw i).map id=LowChernoff.conditionalValueLaw i
  exact Measure.map_id

theorem bid_below_value (i : Row) {v : ℝ} (hv : 0 ≤ v) : bid i v ≤ v := by
  by_cases h : v ≤ entry i
  · simp only [bid,if_pos h,le_refl]
  · have hentry := EarlyMean.entry_pos i
    have hv0 := hentry.trans (lt_of_not_ge h)
    have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
    have hκξ : kappa i+xi i=1 := by cases i <;> norm_num [kappa,kappaQ,xi,xiQ]
    rw [bid,if_neg h,extendedActive_eq i hv,ActiveGraphComponent.activeBid]
    have hd : 0 < kappa i*v+xi i*entry i :=
      add_pos (mul_pos hκ hv0) (mul_pos (xi_pos i) hentry)
    apply (div_le_iff₀ hd).mpr
    have hfactor : v*(kappa i*v+xi i*entry i)-entry i*v=
        kappa i*v*(v-entry i) := by
      rw [show xi i=1-kappa i by linarith]
      ring
    nlinarith [mul_nonneg (mul_pos hv0 hκ).le (sub_nonneg.mpr (lt_of_not_ge h).le)]

theorem full_below_value (i : Row) : ∀ᵐ p ∂(law i:Measure (ℝ × ℝ)),p.2 ≤ p.1 := by
  apply (ae_map_iff (measurable_id.prodMk (measurable_bid i)).aemeasurable
    (measurableSet_le measurable_snd measurable_fst)).mpr
  have hv := EarlyMean.value_support i (law i:Measure (ℝ × ℝ)) (full_value_marginal i)
  have hval : ∀ᵐ v ∂LowChernoff.conditionalValueLaw i,0 ≤ v := by
    rw [LowChernoff.conditionalValueLaw]
    exact Measure.ae_smul_measure ((ae_restrict_mem measurableSet_Icc).mono fun _ h => h.1) _
  exact hval.mono fun v hv => bid_below_value i hv

theorem full_active_graph (i : Row) :
    ∀ᵐ p ∂(law i:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i) (cutoff i) →
      p.2=ActiveGraphComponent.activeBid i p.1 := by
  have hgraph : Measurable (fun v : ℝ=>(v,bid i v)) := by
    convert! measurable_id.prodMk (measurable_bid i) using 1
  have hab : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  have hE : MeasurableSet {p : (ℝ × ℝ) | p.1∈Ioc (entry i) (cutoff i)→
      p.2=ActiveGraphComponent.activeBid i p.1} :=
    ((measurableSet_Ioc.preimage measurable_fst).imp
      (measurableSet_eq_fun measurable_snd (hab.comp measurable_fst)))
  apply (ae_map_iff hgraph.aemeasurable hE).mpr
  exact ae_of_all _ fun v hv => by
    change v∈Ioc (entry i) (cutoff i) at hv
    change bid i v=ActiveGraphComponent.activeBid i v
    rw [bid,if_neg (not_le_of_gt hv.1),extendedActive_eq i ((EarlyMean.entry_pos i).trans hv.1).le]

end FCAppendix.Affine.Uniform06.FullBidGeometry
