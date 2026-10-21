import FCAppendix.Affine.LowBody.NoisyExpectedLoss

set_option maxHeartbeats 800000
noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
variable {N : ℕ}

lemma measurable_patternPayoff_variable_value {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) :
    Measurable (fun p : (Fin N→Fin 4)×(ℝ×(Fin (N+1)→ℝ))=>
      patternPayoff ξ c p.1 p.2.1 p.2.2) := by
  apply measurable_from_prod_countable_right
  intro kind
  unfold patternPayoff
  dsimp only
  split_ifs
  · let r:=(patternTemplate c kind).residual₀
    have hp : Measurable (fun p : ℝ×(Fin (N+1)→ℝ)=>EqualCapacity.positiveMarginal ξ r p.2 0):=
      ((measurable_pi_apply 0).comp (EqualCapacity.measurable_positiveMarginal ξ r hξ hξ1)).comp measurable_snd
    have hb : Measurable (fun p : ℝ×(Fin (N+1)→ℝ)=>p.2 0):=
      (measurable_pi_apply 0).comp measurable_snd
    unfold equalPayoff
    exact (measurable_fst.mul ((measurable_const.mul hp).sub (hp.pow_const 2))).sub
      (hb.mul ((measurable_const.mul hp).sub (measurable_const.mul (hp.pow_const 2))))
  · have hc : Measurable (fun p : ℝ×(Fin (N+1)→ℝ)=>focalCopy
        ((patternTemplate c kind).selection (1-ξ) p.2) 0):=
      (measurable_of_countable (fun P : Finset (Fin (N+1))×Finset (Fin (N+1))=>focalCopy P 0)).comp
        (((patternTemplate c kind).measurable_selection (1-ξ)).comp measurable_snd)
    have hb : Measurable (fun p : ℝ×(Fin (N+1)→ℝ)=>p.2 0):=
      (measurable_pi_apply 0).comp measurable_snd
    unfold purePayoff
    exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
      (measurable_fst.sub (measurable_const.mul hb))
      (Measurable.ite (measurableSet_eq_fun hc measurable_const)
        (measurable_fst.sub hb) measurable_const)

section General
variable {X : Type*} [MeasurableSpace X]

lemma measurable_patternPayoff_comp {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (k : X→Fin N→Fin 4) (hk : Measurable k)
    (w : X→ℝ) (hw : Measurable w) (b : X→Fin (N+1)→ℝ) (hb : Measurable b) :
    Measurable (fun t=>patternPayoff ξ c (k t) (w t) (b t)) :=
  (measurable_patternPayoff_variable_value hξ hξ1 c).comp (hk.prodMk (hw.prodMk hb))

lemma measurable_literalRowPayoff_comp {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (r : X→Fin N→RowRival) (hr : Measurable r)
    (w x : X→ℝ) (hw : Measurable w) (hx : Measurable x) :
    Measurable (fun t=>literalRowPayoff ξ c (w t) (x t,r t)) := by
  have hk : Measurable (fun t=>fun j=>(r t j).1):=
    measurable_pi_lambda _ (fun j=>((measurable_pi_apply j).comp hr).fst)
  have hb : Measurable (fun t=>rowBids (x t) (r t)):=measurable_rowBids.comp (hx.prodMk hr)
  change Measurable (fun t=>patternPayoff ξ c (fun j=>(r t j).1) (w t) (rowBids (x t) (r t)))
  exact measurable_patternPayoff_comp hξ hξ1 c _ hk w hw _ hb

lemma measurable_rowIntervalLoss_comp (c : ℕ) (κ : ℝ)
    (r : X→Fin N→RowRival) (hr : Measurable r)
    (x z : X→ℝ) (hx : Measurable x) (hz : Measurable z) :
    Measurable (fun t=>rowIntervalLoss c κ (x t) (z t) (r t)) := by
  have he : MeasurableSet {t | rowHarmfulInterval c κ (x t) (z t) (r t)}:=by
    simp only [rowHarmfulInterval,setOf_and,setOf_exists]
    apply ((measurableSet_rowBothUnderflow c).preimage hr).inter
    apply MeasurableSet.iUnion
    intro j
    have hj := (measurable_pi_apply j).comp hr
    exact (measurableSet_eq_fun hj.fst measurable_const).inter
      (((measurableSet_le hx hj.snd).inter (measurableSet_le hj.snd hz)).union
        ((measurableSet_le (measurable_const.mul hx) hj.snd).inter
          (measurableSet_le hj.snd (measurable_const.mul hz))))
  exact Measurable.ite he (measurable_const.mul hx) measurable_const

end General

section Carrier
variable {A : Type*} [MeasurableSpace A]

lemma measurable_cons_carrier_row :
    Measurable (fun q : (Fin N→RowRival)×(A×RowRival)=>(Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases measurable_snd.snd (fun j=>?_) i
  exact (measurable_pi_apply j).comp measurable_fst

lemma integrable_literalCarrierGain {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (Γ : Measure A) [IsFiniteMeasure Γ] (ρ : Measure RowRival) [IsProbabilityMeasure ρ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (W B Z : ℝ) (hbox : ∀ᵐt ∂Γ,|w t|≤W ∧ |x t|≤B ∧ |z t|≤Z) :
    Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>
      literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
        literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)) (ν.prod (Γ.prod ρ)) := by
  have hmz:=measurable_literalRowPayoff_comp hξ hξ1 c
    (fun q : (Fin N→RowRival)×(A×RowRival)=>Fin.cons q.2.2 q.1) measurable_cons_carrier_row
    (w ∘ Prod.fst ∘ Prod.snd) (z ∘ Prod.fst ∘ Prod.snd)
    (hw.comp measurable_snd.fst) (hz.comp measurable_snd.fst)
  have hmx:=measurable_literalRowPayoff_comp hξ hξ1 c
    (fun q : (Fin N→RowRival)×(A×RowRival)=>Fin.cons q.2.2 q.1) measurable_cons_carrier_row
    (w ∘ Prod.fst ∘ Prod.snd) (x ∘ Prod.fst ∘ Prod.snd)
    (hw.comp measurable_snd.fst) (hx.comp measurable_snd.fst)
  apply Integrable.of_bound (hmz.sub hmx).aestronglyMeasurable
    (2*W+(3+2*|1-ξ|)*(B+Z))
  have hboxP:=(measurePreserving_snd (μ:=ν) (ν:=Γ.prod ρ)).quasiMeasurePreserving.ae
    ((measurePreserving_fst (μ:=Γ) (ν:=ρ)).quasiMeasurePreserving.ae hbox)
  filter_upwards [hboxP] with q hq
  rw [Real.norm_eq_abs]
  have hnew:=abs_literalRowPayoff_le hξ hξ1 c (w q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)
  have hold:=abs_literalRowPayoff_le hξ hξ1 c (w q.2.1) (x q.2.1) (Fin.cons q.2.2 q.1)
  have hcost : 0≤3+2*|1-ξ|:=by positivity
  have hxB:=mul_le_mul_of_nonneg_left hq.2.1 hcost
  have hzZ:=mul_le_mul_of_nonneg_left hq.2.2 hcost
  have ht:=abs_sub (literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1))
    (literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1))
  change |literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
    literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)|≤_
  nlinarith [hq.1]

lemma integrable_literalCarrierLoss (c : ℕ) (κ : ℝ)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (Γ : Measure A) [IsFiniteMeasure Γ] (ρ : Measure RowRival) [IsProbabilityMeasure ρ]
    (x z : A→ℝ) (hx : Measurable x) (hz : Measurable z)
    (B : ℝ) (hB : 0≤B) (hbox : ∀ᵐt ∂Γ,|x t|≤B) :
    Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>
      rowIntervalLoss c κ (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)) (ν.prod (Γ.prod ρ)) := by
  have hm:=measurable_rowIntervalLoss_comp c κ
    (fun q : (Fin N→RowRival)×(A×RowRival)=>Fin.cons q.2.2 q.1) measurable_cons_carrier_row
    (x ∘ Prod.fst ∘ Prod.snd) (z ∘ Prod.fst ∘ Prod.snd)
    (hx.comp measurable_snd.fst) (hz.comp measurable_snd.fst)
  apply Integrable.of_bound hm.aestronglyMeasurable (|2*κ-1| * B)
  have hboxP:=(measurePreserving_snd (μ:=ν) (ν:=Γ.prod ρ)).quasiMeasurePreserving.ae
    ((measurePreserving_fst (μ:=Γ) (ν:=ρ)).quasiMeasurePreserving.ae hbox)
  filter_upwards [hboxP] with q hq
  rw [Real.norm_eq_abs]
  unfold rowIntervalLoss
  split_ifs
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hq (abs_nonneg _)
  · rw [abs_zero]
    positivity

lemma firstCopy_mixed_rows_nonnegative
    (ν : Measure (Fin N→RowRival)) (Γ : Measure A) (ρ : Measure RowRival)
    (hν : ∀ᵐomega ∂ν,∀j,(omega j).1=0→0≤(omega j).2)
    (hρ : ∀ᵐr ∂ρ,r.1=0→0≤r.2) :
    ∀ᵐq : (Fin N→RowRival)×(A×RowRival) ∂ν.prod (Γ.prod ρ),
      ∀j : Fin (N+1),((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).1=0→
        0≤((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).2 := by
  have hν':=(Measure.quasiMeasurePreserving_fst (μ:=ν) (ν:=Γ.prod ρ)).ae hν
  have hρ':=(Measure.quasiMeasurePreserving_snd (μ:=ν) (ν:=Γ.prod ρ)).ae
    ((Measure.quasiMeasurePreserving_snd (μ:=Γ) (ν:=ρ)).ae hρ)
  filter_upwards [hν',hρ'] with q hq hr
  intro j
  exact Fin.cases hr (fun k=>hq k) j

end Carrier

lemma rivalLaw_ae_bid_nonnegative (s a h : ℝ) (G : Measure ℝ)
    (hG : ∀ᵐb ∂G,0≤b) : ∀ᵐr ∂rivalLaw s a h G,0≤r.2 := by
  have hl : Measurable (fun b : ℝ=>((0:Fin 4),b)):=measurable_const.prodMk measurable_id
  have hlow : ∀ᵐr ∂G.map (fun b : ℝ=>((0:Fin 4),b)),0≤r.2:=
    (ae_map_iff hl.aemeasurable (measurableSet_le measurable_const measurable_snd)).mpr hG
  simp only [rivalLaw,ae_add_measure_iff]
  refine ⟨⟨⟨Measure.ae_smul_measure hlow _,?_⟩,?_⟩,?_⟩ <;>
    apply Measure.ae_smul_measure <;> rw [ae_dirac_eq] <;> norm_num

lemma iid_rows_ae_bid_nonnegative (ρ : Measure RowRival) [IsProbabilityMeasure ρ]
    (hρ : ∀ᵐr ∂ρ,0≤r.2) :
    ∀ᵐomega : Fin N→RowRival ∂Measure.pi (fun _ : Fin N=>ρ),∀j,0≤(omega j).2 := by
  apply ae_all_iff.mpr
  intro j
  exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin N=>ρ) (i:=j)) hρ
end FCAppendix.Affine.LowBody
