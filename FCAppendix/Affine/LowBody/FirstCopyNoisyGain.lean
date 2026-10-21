import FCAppendix.Affine.LowBody.FirstCopyTemplate
import FCAppendix.Affine.LowBody.FirstCopyIntegrated
import FCAppendix.Affine.LowBody.LiteralCarrierBounds

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators ENNReal
variable {N : ℕ}

lemma pairBids_pairRowBids (omega : Fin N→RowRival) (x y : ℝ) :
    pairBids (pairRowBids 0 0 omega) (0:Fin (N+2)) (0:Fin (N+1)).succ x y=
      pairRowBids x y omega := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [pairBids,pairRowBids]
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp [pairBids,pairRowBids]
    · have h1:k.succ.succ≠(0:Fin (N+1)).succ:=
        fun he=>Fin.succ_ne_zero k (Fin.succ_inj.mp he)
      have h1lit:k.succ.succ≠(1:Fin (N+2)):=by simpa using h1
      simp [pairBids,pairRowBids,h1lit]

theorem firstCopy_row_rejection_ge_half (c : ℕ) (hc : 0<c) (u κ : ℝ) (hu : 0≤u)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ : ∀ᵐx ∂μ,x≤u) :
    ν.real (firstCopyBoundary c u)/2≤∫omega in firstCopyBoundary c u,
      (μ.prod μ).real {p : ℝ×ℝ | (0:Fin (N+2))∉
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1} ∂ν := by
  have hij : (0:Fin (N+2))≠(0:Fin (N+1)).succ:=Ne.symm (Fin.succ_ne_zero _)
  have hh:=integrated_variable_pair_rejection_ge_half
    (fun kind : Fin (N+1)→Fin 4=>patternTemplate c kind) pairKinds measurable_pairKinds κ
    (pairRowBids 0 0) (measurable_pairRowBids 0 0)
    (0:Fin (N+2)) (0:Fin (N+1)).succ hij
    (fun omega=>(pairRowBids_support c omega).1)
    (fun omega=>(pairRowBids_support c omega).2)
    u (firstCopyBoundary c u) (measurableSet_firstCopyBoundary c u)
    (fun omega ho=>(firstCopy_residuals c u omega hc ho).2)
    (fun omega k hk=>pairRowBids_outside c omega 0 0 k hk)
    (fun omega ho=>by
      rw [pairRestAbove_pairRowBids_card u hu,(firstCopy_residuals c u omega hc ho).1]
      omega)
    ν μ hμ
  simpa only [pairBids_pairRowBids] using hh

lemma update_pairRowBids (omega : Fin N→RowRival) (x y z : ℝ) :
    Function.update (pairRowBids x y omega) (0:Fin (N+2)) z=pairRowBids z y omega := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [pairRowBids]
  · simp [pairRowBids]

def firstCopyPairGain (c : ℕ) (κ w x y z : ℝ) (omega : Fin N→RowRival) : ℝ :=
  let T:=patternTemplate c (pairKinds omega)
  purePayoff κ w (pairRowBids z y omega) (T.selection κ (pairRowBids z y omega)) 0-
    purePayoff κ w (pairRowBids x y omega) (T.selection κ (pairRowBids x y omega)) 0

theorem firstCopyPairGain_lower (c : ℕ) (hc : 0<c) (κ w l u x y z S : ℝ)
    (hu : 0≤u) (omega : Fin N→RowRival) (ho : omega∈firstCopyBoundary c u)
    (hy : y≤u) (hl : l≤x) (hz : u<z) (hz0 : 0<z) (hS : S≤w-x) :
    (if (0:Fin (N+2))∉((patternTemplate c (pairKinds omega)).selection κ
      (pairRowBids x y omega)).1 then S else 0)-(z-l)≤firstCopyPairGain c κ w x y z omega := by
  have hcounts:=firstCopy_template_counts c u omega hc hu ho x y hy
  have hh:=firstCopy_crossing_gain (patternTemplate c (pairKinds omega)) κ w
    (pairRowBids x y omega) hcounts.1 (pairRowBids_outside c omega x y)
    (0:Fin (N+2)) (pairRowBids_support c omega).1 l u z S
    (by simpa only [pairRowBids,Fin.cons_zero] using hl) hz hz0
    (by simpa only [pairRowBids,Fin.cons_zero] using hS) hcounts.2.2
  simpa only [firstCopyPairGain,update_pairRowBids] using hh

section Measurable
variable {X : Type*} [MeasurableSpace X]

lemma measurable_pairRowBids_comp (r : X→Fin N→RowRival) (hr : Measurable r)
    (x y : X→ℝ) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun t=>pairRowBids (x t) (y t) (r t)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases hx (fun j=>?_) i
  refine Fin.cases hy (fun k=>?_) j
  exact Measurable.ite
    (measurableSet_eq_fun (((measurable_pi_apply k).comp hr).fst) measurable_const)
    (((measurable_pi_apply k).comp hr).snd) measurable_const

lemma measurable_variable_selection
    {K ι : Type*} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype ι] [DecidableEq ι] (T : K→PureTemplate ι) (κ : ℝ) :
    Measurable (fun q : K×(ι→ℝ)=>(T q.1).selection κ q.2) :=
  measurable_from_prod_countable_right (fun k=>(T k).measurable_selection κ)

lemma measurable_variable_selection_comp
    {K ι : Type*} [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Fintype ι] [DecidableEq ι] (T : K→PureTemplate ι) (κ : ℝ)
    (kind : X→K) (hk : Measurable kind) (b : X→ι→ℝ) (hb : Measurable b) :
    Measurable (fun t=>(T (kind t)).selection κ (b t)) :=
  (measurable_variable_selection T κ).comp (hk.prodMk hb)

lemma measurable_pair_selection (c : ℕ) (κ : ℝ)
    (r : X→Fin N→RowRival) (hr : Measurable r)
    (x y : X→ℝ) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun t=>(patternTemplate c (pairKinds (r t))).selection κ
      (pairRowBids (x t) (y t) (r t))) := by
  exact measurable_variable_selection_comp
    (fun kind : Fin (N+1)→Fin 4=>patternTemplate c kind) κ
    (pairKinds ∘ r) (measurable_pairKinds.comp hr)
    (fun t=>pairRowBids (x t) (y t) (r t)) (measurable_pairRowBids_comp r hr x y hx hy)

lemma measurable_pair_purePayoff (c : ℕ) (κ : ℝ)
    (r : X→Fin N→RowRival) (hr : Measurable r)
    (w x y : X→ℝ) (hw : Measurable w) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun t=>purePayoff κ (w t) (pairRowBids (x t) (y t) (r t))
      ((patternTemplate c (pairKinds (r t))).selection κ (pairRowBids (x t) (y t) (r t))) 0) := by
  have hcopy:=((measurable_of_countable (fun P : Finset (Fin (N+2))×Finset (Fin (N+2))=>
    focalCopy P 0)).comp (measurable_pair_selection c κ r hr x y hx hy))
  unfold purePayoff
  simp only [pairRowBids,Fin.cons_zero]
  exact Measurable.ite (measurableSet_eq_fun hcopy measurable_const)
    (hw.sub (measurable_const.mul hx))
    (Measurable.ite (measurableSet_eq_fun hcopy measurable_const) (hw.sub hx) measurable_const)

lemma measurable_firstCopyPairGain (c : ℕ) (κ : ℝ)
    (r : X→Fin N→RowRival) (hr : Measurable r)
    (w x y z : X→ℝ) (hw : Measurable w) (hx : Measurable x)
    (hy : Measurable y) (hz : Measurable z) :
    Measurable (fun t=>firstCopyPairGain c κ (w t) (x t) (y t) (z t) (r t)) :=
  (measurable_pair_purePayoff c κ r hr w z y hw hz hy).sub
    (measurable_pair_purePayoff c κ r hr w x y hw hx hy)

end Measurable
section FocalCarrier
variable {A : Type*} [MeasurableSpace A]

theorem firstCopy_normalized_gain_lower (c : ℕ) (hc : 0<c)
    (κ l u S err W B : ℝ) (hu : 0≤u) (hS : 0≤S)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (Γ : Measure A) [IsProbabilityMeasure Γ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=μ) (hμ : ∀ᵐy ∂μ,y≤u)
    (hbox : ∀ᵐt ∂Γ,l≤x t ∧ x t≤u ∧ u<z t ∧ 0<z t ∧ S≤w t-x t ∧
      z t-l≤err ∧ |w t|≤W ∧ |x t|≤B ∧ |z t|≤B) :
    ν.real (firstCopyBoundary c u)*(S/2-err)≤
      ∫omega in firstCopyBoundary c u,∫p : A×ℝ,
        firstCopyPairGain c κ (w p.1) (x p.1) p.2 (z p.1) omega ∂Γ.prod μ ∂ν := by
  let F : (Fin N→RowRival)×(A×ℝ)→ℝ:=fun q=>
    firstCopyPairGain c κ (w q.2.1) (x q.2.1) q.2.2 (z q.2.1) q.1
  have hFm : Measurable F:=measurable_firstCopyPairGain c κ
    Prod.fst measurable_fst (w ∘ Prod.fst ∘ Prod.snd) (x ∘ Prod.fst ∘ Prod.snd)
    (Prod.snd ∘ Prod.snd) (z ∘ Prod.fst ∘ Prod.snd)
    (hw.comp measurable_snd.fst) (hx.comp measurable_snd.fst)
    measurable_snd.snd (hz.comp measurable_snd.fst)
  have hboxPair : ∀ᵐp : A×ℝ ∂Γ.prod μ,l≤x p.1 ∧ x p.1≤u ∧ u<z p.1 ∧ 0<z p.1 ∧
      S≤w p.1-x p.1 ∧ z p.1-l≤err ∧ |w p.1|≤W ∧ |x p.1|≤B ∧ |z p.1|≤B :=
    (measurePreserving_fst (μ:=Γ) (ν:=μ)).quasiMeasurePreserving.ae hbox
  have hbound (omega : Fin N→RowRival) : ∀ᵐp : A×ℝ ∂Γ.prod μ,
      |F (omega,p)|≤2*W+2*(1+2*|κ|)*B := by
    filter_upwards [hboxPair] with p hp
    have hnew:=abs_purePayoff_le κ (w p.1) (pairRowBids (z p.1) p.2 omega)
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (z p.1) p.2 omega)) 0
    have hold:=abs_purePayoff_le κ (w p.1) (pairRowBids (x p.1) p.2 omega)
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (x p.1) p.2 omega)) 0
    change |purePayoff κ (w p.1) (pairRowBids (z p.1) p.2 omega)
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (z p.1) p.2 omega)) 0|≤
      |w p.1|+(1+2*|κ|)*|z p.1| at hnew
    change |purePayoff κ (w p.1) (pairRowBids (x p.1) p.2 omega)
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (x p.1) p.2 omega)) 0|≤
      |w p.1|+(1+2*|κ|)*|x p.1| at hold
    have ht:=abs_sub
      (purePayoff κ (w p.1) (pairRowBids (z p.1) p.2 omega)
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (z p.1) p.2 omega)) 0)
      (purePayoff κ (w p.1) (pairRowBids (x p.1) p.2 omega)
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids (x p.1) p.2 omega)) 0)
    change |F (omega,p)|≤_ at ht
    have hn : 0≤1+2*|κ|:=by positivity
    have hbx:=mul_le_mul_of_nonneg_left hp.2.2.2.2.2.2.2.1 hn
    have hbz:=mul_le_mul_of_nonneg_left hp.2.2.2.2.2.2.2.2 hn
    linarith [hp.2.2.2.2.2.2.1]
  have hFi (omega : Fin N→RowRival) : Integrable (fun p=>F (omega,p)) (Γ.prod μ):=
    Integrable.of_bound ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (2*W+2*(1+2*|κ|)*B) (by simpa only [Real.norm_eq_abs] using hbound omega)
  have hFjoint : Integrable F (ν.prod (Γ.prod μ)):=Integrable.of_bound hFm.aestronglyMeasurable
    (2*W+2*(1+2*|κ|)*B) (by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      exact ae_of_all _ (fun omega=>by simpa only [Real.norm_eq_abs] using hbound omega))
  have hpoint (omega : Fin N→RowRival) (ho : omega∈firstCopyBoundary c u) :
      S/2-err≤∫p : A×ℝ,F (omega,p) ∂Γ.prod μ := by
    let T:=patternTemplate c (pairKinds omega)
    let R : Set (ℝ×ℝ):={p | (0:Fin (N+2))∉(T.selection κ (pairRowBids p.1 p.2 omega)).1}
    have hR : MeasurableSet R:=by
      have hh:=measurable_pair_selection c κ (fun _ : ℝ×ℝ=>omega) measurable_const
        Prod.fst Prod.snd measurable_fst measurable_snd
      exact (((measurable_of_countable (fun P : Finset (Fin (N+2))×Finset (Fin (N+2))=>
        (0:Fin (N+2))∉P.1)).comp hh).setOf)
    let R' : Set (A×ℝ):=(Prod.map x id) ⁻¹' R
    have hR' : MeasurableSet R':=hR.preimage (hx.prodMap measurable_id)
    have hmap : (Γ.prod μ).map (Prod.map x id)=μ.prod μ := by
      rw [←Measure.map_prod_map Γ μ hx measurable_id,hpush,Measure.map_id]
    have hmass : (Γ.prod μ).real R'=(μ.prod μ).real R := by
      rw [←hmap]
      change ((Γ.prod μ) R').toReal=((Γ.prod μ).map (Prod.map x id) R).toReal
      rw [Measure.map_apply (hx.prodMap measurable_id) hR]
    have hreject : 1/2≤(Γ.prod μ).real R' := by
      rw [hmass]
      have hcounts:=firstCopy_template_counts c u omega hc hu ho 0 0 (by linarith)
      have hh:=pair_rejection_probability_ge_half T κ (pairRowBids 0 0 omega)
        (0:Fin (N+2)) (0:Fin (N+1)).succ (Ne.symm (Fin.succ_ne_zero _))
        (pairRowBids_support c omega).1 (pairRowBids_support c omega).2 hcounts.1
        (pairRowBids_outside c omega 0 0) u (by exact hcounts.2.1.symm.le) μ hμ
      simpa only [pairBids_pairRowBids] using hh
    have hri : Integrable (R'.indicator (fun _=>S)) (Γ.prod μ):=
      (integrable_const S).indicator hR'
    have hinner:=integral_mono_ae (hri.sub (integrable_const err)) (hFi omega) (by
      have hy : ∀ᵐp : A×ℝ ∂Γ.prod μ,p.2≤u:=
        (measurePreserving_snd (μ:=Γ) (ν:=μ)).quasiMeasurePreserving.ae hμ
      filter_upwards [hboxPair,hy] with p hp hyp
      have hh:=firstCopyPairGain_lower c hc κ (w p.1) l u (x p.1) p.2 (z p.1) S hu
        omega ho hyp hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      have he : (R'.indicator (fun _=>S)) p=
          if (0:Fin (N+2))∉(T.selection κ (pairRowBids (x p.1) p.2 omega)).1 then S else 0:=by
        simp only [R',R,Set.indicator,Set.mem_preimage,Set.mem_setOf_eq]
        rfl
      change (R'.indicator (fun _=>S)) p-err≤F (omega,p)
      rw [he]
      change _≤F (omega,p) at hh
      linarith [hp.2.2.2.2.2.1])
    change (∫p : A×ℝ,(R'.indicator (fun _=>S)) p-err ∂Γ.prod μ)≤_ at hinner
    rw [integral_sub hri (integrable_const err),integral_indicator_const _ hR'] at hinner
    simp only [integral_const,probReal_univ,smul_eq_mul] at hinner
    nlinarith [mul_le_mul_of_nonneg_left hreject hS]
  have hh:=integral_mono_ae (integrable_const (S/2-err))
    hFjoint.integral_prod_left.restrict (by
      filter_upwards [ae_restrict_mem (measurableSet_firstCopyBoundary c u)] with omega ho
      exact hpoint omega ho)
  simpa only [integral_const,measureReal_def,Measure.restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul,F]
    using hh

theorem firstCopy_finite_gain_lower (c : ℕ) (hc : 0<c)
    (κ l u S err W B : ℝ) (hu : 0≤u) (hS : 0≤S)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (Γ : Measure A) [IsFiniteMeasure Γ] (hΓ : Γ univ≠0)
    (θ : Measure ℝ) [IsFiniteMeasure θ] [NullSingletonClass θ]
    (w x z : A→ℝ) (hw : Measurable w) (hx : Measurable x) (hz : Measurable z)
    (hpush : Γ.map x=θ) (hθ : ∀ᵐy ∂θ,y≤u)
    (hbox : ∀ᵐt ∂Γ,l≤x t ∧ x t≤u ∧ u<z t ∧ 0<z t ∧ S≤w t-x t ∧
      z t-l≤err ∧ |w t|≤W ∧ |x t|≤B ∧ |z t|≤B) :
    (Γ.real univ)^2*ν.real (firstCopyBoundary c u)*(S/2-err)≤
      ∫omega in firstCopyBoundary c u,∫p : A×ℝ,
        firstCopyPairGain c κ (w p.1) (x p.1) p.2 (z p.1) omega ∂Γ.prod θ ∂ν := by
  have hm : θ univ=Γ univ:=by
    rw [←hpush,Measure.map_apply hx MeasurableSet.univ,preimage_univ]
  let P : Measure A:=(Γ univ)⁻¹ • Γ
  let μ : Measure ℝ:=(Γ univ)⁻¹ • θ
  have hfinite : Γ univ≠⊤:=measure_ne_top Γ univ
  haveI : IsProbabilityMeasure P:=⟨by
    change (Γ univ)⁻¹*Γ univ=1
    exact ENNReal.inv_mul_cancel hΓ hfinite⟩
  haveI : IsProbabilityMeasure μ:=⟨by
    change (Γ univ)⁻¹*θ univ=1
    rw [hm]
    exact ENNReal.inv_mul_cancel hΓ hfinite⟩
  haveI : NullSingletonClass μ:=⟨by
    intro t
    simp only [μ,Measure.smul_apply,measure_singleton,smul_eq_mul,mul_zero]⟩
  have hp : P.map x=μ:=by
    simp only [P,μ,Measure.map_smul,hpush]
  have hnorm:=firstCopy_normalized_gain_lower c hc κ l u S err W B hu hS ν P μ w x z hw hx hz
    hp (Measure.ae_smul_measure hθ _) (Measure.ae_smul_measure hbox _)
  have hΓrec : Γ=(Γ univ) • P:=by
    dsimp [P]
    rw [smul_smul,ENNReal.mul_inv_cancel hΓ hfinite,one_smul]
  have hθrec : θ=(Γ univ) • μ:=by
    dsimp [μ]
    rw [smul_smul,ENNReal.mul_inv_cancel hΓ hfinite,one_smul]
  have hprod : Γ.prod θ=(Γ univ*Γ univ) • (P.prod μ):=by
    calc
      Γ.prod θ=((Γ univ) • P).prod ((Γ univ) • μ):=congrArg₂ Measure.prod hΓrec hθrec
      _=(Γ univ*Γ univ) • (P.prod μ):=by
        rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  have hint (omega : Fin N→RowRival) :
      (∫p : A×ℝ,firstCopyPairGain c κ (w p.1) (x p.1) p.2 (z p.1) omega ∂Γ.prod θ)=
      (Γ.real univ)^2*(∫p : A×ℝ,firstCopyPairGain c κ (w p.1) (x p.1) p.2 (z p.1) omega ∂P.prod μ):=by
    rw [hprod,integral_smul_measure]
    simp only [ENNReal.toReal_mul,smul_eq_mul,measureReal_def,pow_two]
  calc
    _=(Γ.real univ)^2*(ν.real (firstCopyBoundary c u)*(S/2-err)):=by ring
    _≤(Γ.real univ)^2*(∫omega in firstCopyBoundary c u,∫p : A×ℝ,
        firstCopyPairGain c κ (w p.1) (x p.1) p.2 (z p.1) omega ∂P.prod μ ∂ν):=
      mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
    _= _:=by simp_rw [hint]; rw [integral_const_mul]

end FocalCarrier

theorem firstCopy_finite_rejection_lower (c : ℕ) (hc : 0<c) (u κ : ℝ) (hu : 0≤u)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (θ : Measure ℝ) [IsFiniteMeasure θ] [NullSingletonClass θ]
    (hθ0 : θ univ≠0) (hθ : ∀ᵐx ∂θ,x≤u) :
    (θ.real univ)^2*ν.real (firstCopyBoundary c u)/2≤∫omega in firstCopyBoundary c u,
      (θ.prod θ).real {p : ℝ×ℝ | (0:Fin (N+2))∉
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1} ∂ν := by
  let μ : Measure ℝ:=(θ univ)⁻¹ • θ
  have ht : θ univ≠⊤:=measure_ne_top θ univ
  haveI : IsProbabilityMeasure μ:=⟨by
    change (θ univ)⁻¹*θ univ=1
    exact ENNReal.inv_mul_cancel hθ0 ht⟩
  haveI : NullSingletonClass μ:=⟨by
    intro t
    simp only [μ,Measure.smul_apply,measure_singleton,smul_eq_mul,mul_zero]⟩
  have hh:=firstCopy_row_rejection_ge_half c hc u κ hu ν μ (Measure.ae_smul_measure hθ _)
  have hrec : θ=(θ univ) • μ:=by
    dsimp [μ]
    rw [smul_smul,ENNReal.mul_inv_cancel hθ0 ht,one_smul]
  have hprod : θ.prod θ=(θ univ*θ univ) • (μ.prod μ):=by
    calc
      θ.prod θ=((θ univ) • μ).prod ((θ univ) • μ):=congrArg₂ Measure.prod hrec hrec
      _=(θ univ*θ univ) • (μ.prod μ):=by
        rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rw [hprod]
  simp only [measureReal_ennreal_smul_apply,ENNReal.toReal_mul,←measureReal_def]
  rw [integral_const_mul]
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (θ.real univ))]

def firstCopyLowRejection (c : ℕ) (κ u : ℝ) (omega : Fin N→RowRival) : Set (ℝ×RowRival):=
  {p | p.2.1=0 ∧ p.2.2≤u ∧ (0:Fin (N+2))∉((patternTemplate c (pairKinds omega)).selection κ
    (pairRowBids p.1 p.2.2 omega)).1}

lemma measurableSet_firstCopyLowRejection_joint (c : ℕ) (κ u : ℝ) :
    MeasurableSet {q : (Fin N→RowRival)×(ℝ×RowRival) | q.2∈firstCopyLowRejection c κ u q.1} := by
  have hsel:=measurable_pair_selection (N:=N) (X:=(Fin N→RowRival)×(ℝ×RowRival)) c κ
    Prod.fst measurable_fst (fun q=>q.2.1) (fun q=>q.2.2.2)
    measurable_snd.fst measurable_snd.snd.snd
  have hr:=((measurable_of_countable (fun P : Finset (Fin (N+2))×Finset (Fin (N+2))=>
    (0:Fin (N+2))∉P.1)).comp hsel).setOf
  exact (measurableSet_eq_fun measurable_snd.snd.fst measurable_const).inter
    ((measurableSet_le measurable_snd.snd.snd measurable_const).inter hr)

lemma measurableSet_firstCopyLowRejection (c : ℕ) (κ u : ℝ) (omega : Fin N→RowRival) :
    MeasurableSet (firstCopyLowRejection c κ u omega) :=
  (measurableSet_firstCopyLowRejection_joint c κ u).preimage (measurable_const.prodMk measurable_id)

theorem firstCopy_low_mixture_rejection (s a h : ℝ) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G θ : Measure ℝ) [IsProbabilityMeasure G] [IsFiniteMeasure θ] (hθG : θ ≤ G)
    (c : ℕ) (κ u : ℝ) (hθ : ∀ᵐy ∂θ,y≤u) (omega : Fin N→RowRival) :
    s*(θ.prod θ).real {p : ℝ×ℝ | (0:Fin (N+2))∉
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1}≤
      (θ.prod (rivalLaw s a h G)).real (firstCopyLowRejection c κ u omega) := by
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  let low : ℝ→RowRival:=fun y=>(0,y)
  have hl : Measurable low:=measurable_const.prodMk measurable_id
  have hdom : ENNReal.ofReal s • θ.map low≤rivalLaw s a h G:=by
    have hh : ENNReal.ofReal s • θ.map low≤ENNReal.ofReal s • G.map low:=by
      gcongr
    apply hh.trans
    unfold rivalLaw
    exact (Measure.le_add_right le_rfl).trans
      ((Measure.le_add_right le_rfl).trans (Measure.le_add_right le_rfl))
  have hpdom:=Measure.prod_mono (μ:=θ) le_rfl hdom
  have hpmap : θ.prod (θ.map low)=(θ.prod θ).map (Prod.map id low):=by
    simpa only [Measure.map_id] using Measure.map_prod_map θ θ measurable_id hl
  have hpre : (Prod.map id low) ⁻¹' firstCopyLowRejection c κ u omega=ᵐ[θ.prod θ]
      {p : ℝ×ℝ | (0:Fin (N+2))∉((patternTemplate c (pairKinds omega)).selection κ
        (pairRowBids p.1 p.2 omega)).1} := by
    have hy : ∀ᵐp : ℝ×ℝ ∂θ.prod θ,p.2≤u:=by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_snd measurable_const)).mpr
      exact ae_of_all _ (fun _=>hθ)
    filter_upwards [hy] with p hp
    apply propext
    change ((0:Fin 4)=0 ∧ p.2≤u ∧ (0:Fin (N+2))∉
      ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1)↔_
    simp only [hp,true_and]
    rfl
  have hcomp : (θ.prod (ENNReal.ofReal s • θ.map low)).real (firstCopyLowRejection c κ u omega)=
      s*(θ.prod θ).real {p : ℝ×ℝ | (0:Fin (N+2))∉
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1}:=by
    rw [Measure.prod_smul_right,measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal hs,hpmap]
    congr 1
    change (((θ.prod θ).map (Prod.map id low)) (firstCopyLowRejection c κ u omega)).toReal=
      ((θ.prod θ) {p : ℝ×ℝ | (0:Fin (N+2))∉
        ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1}).toReal
    rw [Measure.map_apply (measurable_id.prodMap hl)
      (measurableSet_firstCopyLowRejection c κ u omega)]
    exact congrArg ENNReal.toReal (measure_congr hpre)
  rw [←hcomp]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hpdom _)

lemma integrable_real_sections {Y : Type*} [MeasurableSpace Y]
    (P : Measure Y) [IsFiniteMeasure P]
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (f : (Fin N→RowRival)→Set Y)
    (hf : MeasurableSet {q : (Fin N→RowRival)×Y | q.2∈f q.1}) :
    Integrable (fun omega=>P.real (f omega)) ν := by
  have hm : Measurable (fun omega=>P.real (f omega)):=
    (measurable_measure_prodMk_left hf).ennreal_toReal
  apply Integrable.of_bound hm.aestronglyMeasurable (P.real univ)
  exact ae_of_all _ (fun omega=>by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (subset_univ _))

theorem firstCopy_actual_rejection_lower (s a h : ℝ) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G θ : Measure ℝ) [IsProbabilityMeasure G] [IsFiniteMeasure θ] [NullSingletonClass θ]
    (hθG : θ ≤ G) (hθ0 : θ univ≠0)
    (c : ℕ) (hc : 0<c) (u κ : ℝ) (hu : 0≤u) (hθ : ∀ᵐx ∂θ,x≤u)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν] :
    s*(θ.real univ)^2*ν.real (firstCopyBoundary c u)/2≤
      ∫omega in firstCopyBoundary c u,
        (θ.prod (rivalLaw s a h G)).real (firstCopyLowRejection c κ u omega) ∂ν := by
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  let R : (Fin N→RowRival)→Set (ℝ×ℝ):=fun omega=>{p | (0:Fin (N+2))∉
    ((patternTemplate c (pairKinds omega)).selection κ (pairRowBids p.1 p.2 omega)).1}
  have hR : MeasurableSet {q : (Fin N→RowRival)×(ℝ×ℝ) | q.2∈R q.1}:=by
    have hsel:=measurable_pair_selection (N:=N) (X:=(Fin N→RowRival)×(ℝ×ℝ)) c κ
      Prod.fst measurable_fst (fun q=>q.2.1) (fun q=>q.2.2) measurable_snd.fst measurable_snd.snd
    exact ((measurable_of_countable (fun P : Finset (Fin (N+2))×Finset (Fin (N+2))=>
      (0:Fin (N+2))∉P.1)).comp hsel).setOf
  have hi:=integrable_real_sections (θ.prod θ) ν R hR
  have hi':=integrable_real_sections (θ.prod (rivalLaw s a h G)) ν
    (firstCopyLowRejection c κ u) (measurableSet_firstCopyLowRejection_joint c κ u)
  have hmono:=integral_mono_ae (μ:=ν.restrict (firstCopyBoundary c u)) (hi.const_mul s).restrict hi'.restrict
    (ae_of_all _ (fun omega=>firstCopy_low_mixture_rejection s a h hs ha hh hsum G θ hθG c κ u hθ omega))
  rw [integral_const_mul] at hmono
  have hpair:=firstCopy_finite_rejection_lower c hc u κ hu ν θ hθ0 hθ
  calc
    _ = s *((θ.real univ)^2*ν.real (firstCopyBoundary c u)/2):=by ring
    _ ≤ s *(∫omega in firstCopyBoundary c u,(θ.prod θ).real (R omega) ∂ν):=
      mul_le_mul_of_nonneg_left hpair hs
    _≤_:=hmono

theorem firstCopy_actual_iid_rejection_lower (s a h : ℝ) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G θ : Measure ℝ) [IsProbabilityMeasure G] [IsFiniteMeasure θ] [NullSingletonClass θ]
    (hθG : θ ≤ G) (hθ0 : θ univ≠0)
    (c : ℕ) (hc : 0<c) (u κ : ℝ) (hu : 0≤u) (hθ : ∀ᵐx ∂θ,x≤u) :
    s*(θ.real univ)^2/2*(PiBinomial.pmf N (higherBidProbability s a h G u) (c-1)-
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c))≤
      ∫omega in firstCopyBoundary c u,
        (θ.prod (rivalLaw s a h G)).real (firstCopyLowRejection c κ u omega)
          ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h G) := by
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  have hmass:=firstCopyBoundary_probability_lower s a h hs ha hh hsum G N c u
  have hactual:=firstCopy_actual_rejection_lower s a h hs ha hh hsum G θ hθG hθ0 c hc u κ hu hθ
    (Measure.pi (fun _ : Fin N=>rivalLaw s a h G))
  have hcoef : 0 ≤ s*(θ.real univ)^2/2:=by positivity
  apply (mul_le_mul_of_nonneg_left hmass hcoef).trans
  calc
    _ = s *(θ.real univ)^2*(Measure.pi (fun _ : Fin N=>rivalLaw s a h G)).real
        (firstCopyBoundary c u)/2:=by ring
    _≤_:=hactual

section CarrierTransport
variable {A : Type*} [MeasurableSpace A]

theorem firstCopy_focal_rejection_transport
    (Γ : Measure A) [IsFiniteMeasure Γ] (θ : Measure ℝ) [IsFiniteMeasure θ]
    (ρ : Measure RowRival) [IsFiniteMeasure ρ]
    (x : A→ℝ) (hx : Measurable x) (hpush : Γ.map x=θ)
    (c : ℕ) (κ u : ℝ) (omega : Fin N→RowRival) :
    (Γ.prod ρ).real ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega)=
      (θ.prod ρ).real (firstCopyLowRejection c κ u omega) := by
  have hm : (Γ.prod ρ).map (Prod.map x id)=θ.prod ρ:=by
    rw [←Measure.map_prod_map Γ ρ hx measurable_id,hpush,Measure.map_id]
  rw [←hm]
  change ((Γ.prod ρ) ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega)).toReal=
    (((Γ.prod ρ).map (Prod.map x id)) (firstCopyLowRejection c κ u omega)).toReal
  rw [Measure.map_apply (hx.prodMap measurable_id) (measurableSet_firstCopyLowRejection c κ u omega)]

theorem firstCopy_actual_carrier_rejection_lower (s a h : ℝ) (hs : 0 ≤ s)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (G θ : Measure ℝ) [IsProbabilityMeasure G] [IsFiniteMeasure θ] [NullSingletonClass θ]
    (hθG : θ ≤ G) (hθ0 : θ univ≠0)
    (Γ : Measure A) [IsFiniteMeasure Γ] (x : A→ℝ) (hx : Measurable x) (hpush : Γ.map x=θ)
    (c : ℕ) (hc : 0<c) (u κ : ℝ) (hu : 0≤u) (hθ : ∀ᵐy ∂θ,y≤u)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν] :
    s*(Γ.real univ)^2*ν.real (firstCopyBoundary c u)/2≤
      ∫omega in firstCopyBoundary c u,(Γ.prod (rivalLaw s a h G)).real
        ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega) ∂ν := by
  letI : IsProbabilityMeasure (rivalLaw s a h G):=rivalLaw_isProbability s a h hs ha hh hsum G
  have hmass : Γ.real univ=θ.real univ:=by
    change (Γ univ).toReal=(θ univ).toReal
    rw [←hpush,Measure.map_apply hx MeasurableSet.univ,preimage_univ]
  have hh:=firstCopy_actual_rejection_lower s a h hs ha hh hsum G θ hθG hθ0 c hc u κ hu hθ ν
  rw [hmass]
  simpa only [firstCopy_focal_rejection_transport Γ θ (rivalLaw s a h G) x hx hpush c κ u] using hh

end CarrierTransport
lemma rowBids_cons_low (x y : ℝ) (omega : Fin N→RowRival) :
    rowBids x (Fin.cons ((0:Fin 4),y) omega)=pairRowBids x y omega := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [rowBids,pairRowBids]
  · refine Fin.cases ?_ (fun k=>?_) j
    · simp [rowBids,pairRowBids]
    · simp [rowBids,pairRowBids]

lemma pairKinds_cons_low (y : ℝ) (omega : Fin N→RowRival) :
    (fun i : Fin (N+1)=>((Fin.cons ((0:Fin 4),y) omega : Fin (N+1)→RowRival) i).1)=pairKinds omega := by
  funext i
  exact Fin.cases rfl (fun _=>rfl) i

theorem firstCopyPairGain_eq_literalRowGain (c : ℕ) (hc : 0<c) (ξ w u x y z : ℝ)
    (omega : Fin N→RowRival) (ho : omega∈firstCopyBoundary c u) :
    firstCopyPairGain c (1-ξ) w x y z omega=
      literalRowPayoff ξ c w (z,Fin.cons ((0:Fin 4),y) omega)-
        literalRowPayoff ξ c w (x,Fin.cons ((0:Fin 4),y) omega) := by
  have hr:=firstCopy_residuals c u omega hc ho
  have hne : (patternTemplate c (pairKinds omega)).residual₀≠
      (patternTemplate c (pairKinds omega)).residual₁:=by rw [hr.1,hr.2];omega
  simp only [literalRowPayoff,pairKinds_cons_low,rowBids_cons_low,patternPayoff,if_neg hne]
  rfl

theorem firstCopy_literalRowGain_bonus (c : ℕ) (hc : 0<c) (ξ w l u x z S : ℝ)
    (hu : 0≤u) (omega : Fin N→RowRival) (ho : omega∈firstCopyBoundary c u)
    (r : RowRival) (hb : (x,r)∈firstCopyLowRejection c (1-ξ) u omega)
    (hl : l≤x) (hz : u<z) (hz0 : 0<z) (hS : S≤w-x) :
    S-(z-l)≤literalRowPayoff ξ c w (z,Fin.cons r omega)-
      literalRowPayoff ξ c w (x,Fin.cons r omega) := by
  rcases r with ⟨k,y⟩
  obtain ⟨hk,hy,hreject⟩:=hb
  dsimp only at hk hy hreject
  subst k
  have hh:=firstCopyPairGain_lower c hc (1-ξ) w l u x y z S hu omega ho hy hl hz hz0 hS
  rw [if_pos hreject,firstCopyPairGain_eq_literalRowGain c hc ξ w u x y z omega ho] at hh
  exact hh

theorem firstCopy_literalRowGain_uniform {ξ a B W : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (ha : 0<a) (haB : a≤B) (hW : 0≤W) :
    ∀e>0,∃δ>0,∀(c : ℕ)(_hc : 0<c)(omega : Fin N→RowRival)(r : RowRival)
      (w l u x z S : ℝ),
      (∀j,((Fin.cons r omega : Fin (N+1)→RowRival) j).1=0→0≤((Fin.cons r omega : Fin (N+1)→RowRival) j).2)→|w|≤W→
      a≤x→x≤B→x≤w→x<z→z-x<δ→l≤x→0≤u→u<z→S≤w-x→
      (if omega∈firstCopyBoundary c u ∧ (x,r)∈firstCopyLowRejection c (1-ξ) u omega
        then S else 0)-(z-l)-
        (rowIntervalLoss c (1-ξ) x z (Fin.cons r omega)+2*(1-ξ)*(z-x)+e)≤
          literalRowPayoff ξ c w (z,Fin.cons r omega)-
            literalRowPayoff ξ c w (x,Fin.cons r omega) := by
  intro e he
  obtain ⟨δ,hδ,huniform⟩:=patternPayoff_uniform_raise (N:=N+1) hξ hξh ha haB hW e he
  refine ⟨δ,hδ,?_⟩
  intro c hc omega r w l u x z S hrow hw hax hxB hxw hxz hgap hl hu huz hS
  have hx : 0<x:=ha.trans_le hax
  have hz : 0<z:=hx.trans hxz
  have hwidth : 0≤z-l:=by linarith
  have hκ : 0≤1-ξ:=by linarith
  have hloss : 0≤rowIntervalLoss c (1-ξ) x z (Fin.cons r omega):=by
    unfold rowIntervalLoss
    split_ifs
    · exact mul_nonneg (by linarith) hx.le
    · exact le_rfl
  have hprice : 0≤2*(1-ξ)*(z-x):=mul_nonneg (by positivity) (sub_nonneg.mpr hxz.le)
  by_cases hb : omega∈firstCopyBoundary c u ∧ (x,r)∈firstCopyLowRejection c (1-ξ) u omega
  · rw [if_pos hb]
    have hh:=firstCopy_literalRowGain_bonus c hc ξ w l u x z S hu omega hb.1 r hb.2 hl huz hz hS
    linarith
  · rw [if_neg hb]
    have hh:=huniform c (Fin.cons r omega) w x z hrow hw hax hxB hxw hxz hgap
    change literalRowPayoff ξ c w (x,Fin.cons r omega)-
      literalRowPayoff ξ c w (z,Fin.cons r omega)≤_ at hh
    linarith

section IntegratedBonus
variable {A : Type*} [MeasurableSpace A]

def firstCopyCarrierBonus (c : ℕ) (κ u : ℝ) (x : A→ℝ) :
    Set ((Fin N→RowRival)×(A×RowRival)):=
  {q | q.1∈firstCopyBoundary c u ∧ (Prod.map x id q.2)∈firstCopyLowRejection c κ u q.1}

lemma measurableSet_firstCopyCarrierBonus (c : ℕ) (κ u : ℝ) (x : A→ℝ) (hx : Measurable x) :
    MeasurableSet (firstCopyCarrierBonus (N:=N) c κ u x) :=
  ((measurableSet_firstCopyBoundary c u).preimage measurable_fst).inter
    ((measurableSet_firstCopyLowRejection_joint c κ u).preimage
      (measurable_fst.prodMk ((hx.comp measurable_snd.fst).prodMk measurable_snd.snd)))

theorem integral_firstCopyCarrierBonus (c : ℕ) (κ u S : ℝ)
    (ν : Measure (Fin N→RowRival)) [IsProbabilityMeasure ν]
    (Γ : Measure A) [IsFiniteMeasure Γ] (ρ : Measure RowRival) [IsProbabilityMeasure ρ]
    (x : A→ℝ) (hx : Measurable x) :
    (∫q,(firstCopyCarrierBonus (N:=N) c κ u x).indicator (fun _=>S) q ∂ν.prod (Γ.prod ρ))=
      S*(∫omega in firstCopyBoundary c u,(Γ.prod ρ).real
        ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega) ∂ν) := by
  let E:=firstCopyBoundary (N:=N) c u
  let B:=firstCopyCarrierBonus (N:=N) c κ u x
  have hB : MeasurableSet B:=measurableSet_firstCopyCarrierBonus c κ u x hx
  have hi : Integrable (B.indicator (fun _=>S)) (ν.prod (Γ.prod ρ)):=
    (integrable_const S).indicator hB
  have hinner (omega : Fin N→RowRival) :
      (∫p : A×RowRival,B.indicator (fun _=>S) (omega,p) ∂Γ.prod ρ)=
      E.indicator (fun omega=>(Γ.prod ρ).real
        ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega)*S) omega := by
    by_cases ho:omega∈E
    · rw [Set.indicator_of_mem ho]
      have he : (fun p : A×RowRival=>B.indicator (fun _=>S) (omega,p))=
          ((Prod.map x id) ⁻¹' firstCopyLowRejection c κ u omega).indicator (fun _=>S):=by
        funext p
        simp only [B,firstCopyCarrierBonus,Set.indicator,Set.mem_setOf_eq,Set.mem_preimage,
          show omega∈firstCopyBoundary c u from ho,true_and]
      rw [he,integral_indicator_const _ ((measurableSet_firstCopyLowRejection c κ u omega).preimage
        (hx.prodMap measurable_id))]
      rfl
    · rw [Set.indicator_of_notMem ho]
      have he : (fun p : A×RowRival=>B.indicator (fun _=>S) (omega,p))=0:=by
        funext p
        simp only [B,firstCopyCarrierBonus,Set.indicator,Set.mem_setOf_eq,
          show omega∉firstCopyBoundary c u from ho,false_and,if_false,Pi.zero_apply]
      rw [he]
      exact integral_zero _ _
  change (∫q,B.indicator (fun _=>S) q ∂ν.prod (Γ.prod ρ))=_
  rw [integral_prod _ hi]
  simp_rw [hinner]
  rw [integral_indicator (measurableSet_firstCopyBoundary c u),integral_mul_const]
  ring

theorem firstCopy_integrated_literalGain_uniform_of_integrable {ξ a B W : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (ha : 0<a) (haB : a≤B) (hW : 0≤W) :
    ∀e>0,∃δ>0,∀(s a' h : ℝ)(_hs : 0 ≤ s)(_ha' : 0 ≤ a')(_hh : 0 ≤ h),s+a'+h=1→
    ∀(G θ : Measure ℝ)(_hG : IsProbabilityMeasure G)
      (_hθf : IsFiniteMeasure θ)(_hθa : NullSingletonClass θ),θ ≤ G→θ univ≠0→
    ∀(Γ : Measure A)(_hΓ : IsFiniteMeasure Γ)(ν : Measure (Fin N→RowRival))
      (_hν : IsProbabilityMeasure ν)(c : ℕ),0<c→
    ∀(l u S D : ℝ),0≤u→0≤S→
    ∀(w x z : A→ℝ),Measurable w→Measurable x→Measurable z→Γ.map x=θ→
      (∀ᵐy ∂θ,y≤u)→
      (∀ᵐt ∂Γ,l≤x t ∧ a≤x t ∧ x t≤B ∧ x t≤w t ∧ x t<z t ∧ z t-x t<δ ∧
        z t-l≤D ∧ u<z t ∧ S≤w t-x t ∧ |w t|≤W)→
      (∀ᵐq : (Fin N→RowRival)×(A×RowRival) ∂ν.prod (Γ.prod (rivalLaw s a' h G)),
        ∀j : Fin (N+1),((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).1=0→
          0≤((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).2)→
      Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>
        literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
          literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1))
        (ν.prod (Γ.prod (rivalLaw s a' h G)))→
      Integrable (fun q : (Fin N→RowRival)×(A×RowRival)=>
        rowIntervalLoss c (1-ξ) (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1))
        (ν.prod (Γ.prod (rivalLaw s a' h G)))→
      S*s*(Γ.real univ)^2*ν.real (firstCopyBoundary c u)/2-
        Γ.real univ*(D+2*(1-ξ)*D+e)-
        (∫q : (Fin N→RowRival)×(A×RowRival),
          rowIntervalLoss c (1-ξ) (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)
            ∂ν.prod (Γ.prod (rivalLaw s a' h G)))≤
        ∫q : (Fin N→RowRival)×(A×RowRival),
          literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
            literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)
              ∂ν.prod (Γ.prod (rivalLaw s a' h G)) := by
  intro e he
  obtain ⟨δ,hδ,huniform⟩:=firstCopy_literalRowGain_uniform (N:=N) hξ hξh ha haB hW e he
  refine ⟨δ,hδ,?_⟩
  intro s a' h hs ha' hh hsum G θ hG hθf hθa hθG hθ0 Γ hΓ ν hν c hc
    l u S D hu hS w x z hw hx hz hpush hθ hbox hrows hI hL
  letI:=hG
  letI:=hθf
  letI:=hθa
  letI:=hΓ
  letI:=hν
  let ρ:=rivalLaw s a' h G
  letI : IsProbabilityMeasure ρ:=rivalLaw_isProbability s a' h hs ha' hh hsum G
  let P:=ν.prod (Γ.prod ρ)
  let Bonus:=firstCopyCarrierBonus (N:=N) c (1-ξ) u x
  let L : (Fin N→RowRival)×(A×RowRival)→ℝ:=fun q=>
    rowIntervalLoss c (1-ξ) (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)
  let F : (Fin N→RowRival)×(A×RowRival)→ℝ:=fun q=>
    literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
      literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)
  have hBI : Integrable (Bonus.indicator (fun _=>S)) P:=
    (integrable_const S).indicator (measurableSet_firstCopyCarrierBonus c (1-ξ) u x hx)
  have hboxP:= (measurePreserving_snd (μ:=ν) (ν:=Γ.prod ρ)).quasiMeasurePreserving.ae
    ((measurePreserving_fst (μ:=Γ) (ν:=ρ)).quasiMeasurePreserving.ae hbox)
  have hκ : 0≤1-ξ:=by linarith
  have hpoint : ∀ᵐq ∂P,(Bonus.indicator (fun _=>S)) q-D-(L q+(2*(1-ξ)*D+e))≤F q:=by
    filter_upwards [hboxP,hrows] with q hq hr
    have hh:=huniform c hc q.1 q.2.2 (w q.2.1) l u (x q.2.1) (z q.2.1) S hr
      hq.2.2.2.2.2.2.2.2.2 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2.1
      hq.2.2.2.2.2.1 hq.1 hu hq.2.2.2.2.2.2.2.1 hq.2.2.2.2.2.2.2.2.1
    have hgap : z q.2.1-x q.2.1≤D:=by linarith [hq.1,hq.2.2.2.2.2.2.1]
    have hprice:=mul_le_mul_of_nonneg_left hgap (by positivity : 0≤2*(1-ξ))
    have hi : (Bonus.indicator (fun _=>S)) q=
        if q.1∈firstCopyBoundary c u ∧ (x q.2.1,q.2.2)∈firstCopyLowRejection c (1-ξ) u q.1
          then S else 0:=by
      simp only [Bonus,firstCopyCarrierBonus,Set.indicator,Set.mem_setOf_eq]
      rfl
    rw [hi]
    change _≤F q at hh
    change _-D-(L q+(2*(1-ξ)*D+e))≤F q
    linarith [hq.2.2.2.2.2.2.1]
  have hLI : Integrable L P:=hL
  have hFI : Integrable F P:=hI
  have hcompare:=integral_mono_ae ((hBI.sub (integrable_const D)).sub
    (hLI.add (integrable_const (2*(1-ξ)*D+e)))) hFI hpoint
  have hp : P.real univ=Γ.real univ:=by
    have hm₁ : P univ=(Γ.prod ρ) univ:=by
      simpa only [P,Set.univ_prod_univ,measure_univ,one_mul] using
        (Measure.prod_prod (μ:=ν) (ν:=Γ.prod ρ) univ univ)
    have hm₂ : (Γ.prod ρ) univ=Γ univ:=by
      simpa only [Set.univ_prod_univ,measure_univ,mul_one] using
        (Measure.prod_prod (μ:=Γ) (ν:=ρ) univ univ)
    exact congrArg ENNReal.toReal (hm₁.trans hm₂)
  change (∫q,(Bonus.indicator (fun _=>S)) q-D-(L q+(2*(1-ξ)*D+e)) ∂P)≤∫q,F q ∂P at hcompare
  have hEq : (∫q,(Bonus.indicator (fun _=>S)) q-D-(L q+(2*(1-ξ)*D+e)) ∂P)=
      (∫q,Bonus.indicator (fun _=>S) q ∂P)-Γ.real univ*D-
        ((∫q,L q ∂P)+Γ.real univ*(2*(1-ξ)*D+e)):=by
    calc
      _=(∫q,(Bonus.indicator (fun _=>S)) q-D ∂P)-(∫q,L q+(2*(1-ξ)*D+e) ∂P):=
        integral_sub (hBI.sub (integrable_const D)) (hLI.add (integrable_const (2*(1-ξ)*D+e)))
      _= _:=by
        rw [integral_sub hBI (integrable_const D),integral_add hLI (integrable_const (2*(1-ξ)*D+e))]
        simp only [integral_const,smul_eq_mul,hp]
  rw [hEq] at hcompare
  have hbonus:=firstCopy_actual_carrier_rejection_lower s a' h hs ha' hh hsum G θ hθG hθ0
    Γ x hx hpush c hc u (1-ξ) hu hθ ν
  have hbonus':=mul_le_mul_of_nonneg_left hbonus hS
  have hident:=integral_firstCopyCarrierBonus c (1-ξ) u S ν Γ ρ x hx
  change (∫q,Bonus.indicator (fun _=>S) q ∂P)=_ at hident
  rw [←hident] at hbonus'
  change _≤∫q,F q ∂P
  change S*(s*(Γ.real univ)^2*ν.real (firstCopyBoundary c u)/2)≤_ at hbonus'
  linarith

theorem firstCopy_integrated_literalGain_uniform {ξ a B W : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (ha : 0<a) (haB : a≤B) (hW : 0≤W) :
    ∀e>0,∃δ>0,∀(s a' h : ℝ)(_hs : 0 ≤ s)(_ha' : 0 ≤ a')(_hh : 0 ≤ h),s+a'+h=1→
    ∀(G θ : Measure ℝ)(_hG : IsProbabilityMeasure G)
      (_hθf : IsFiniteMeasure θ)(_hθa : NullSingletonClass θ),θ ≤ G→θ univ≠0→
    ∀(Γ : Measure A)(_hΓ : IsFiniteMeasure Γ)(ν : Measure (Fin N→RowRival))
      (_hν : IsProbabilityMeasure ν)(c : ℕ),0<c→
    ∀(l u S D : ℝ),0≤u→0≤S→
    ∀(w x z : A→ℝ),Measurable w→Measurable x→Measurable z→Γ.map x=θ→
      (∀ᵐy ∂θ,y≤u)→
      (∀ᵐt ∂Γ,l≤x t ∧ a≤x t ∧ x t≤B ∧ x t≤w t ∧ x t<z t ∧ z t-x t<δ ∧
        z t-l≤D ∧ u<z t ∧ S≤w t-x t ∧ |w t|≤W)→
      (∀ᵐq : (Fin N→RowRival)×(A×RowRival) ∂ν.prod (Γ.prod (rivalLaw s a' h G)),
        ∀j : Fin (N+1),((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).1=0→
          0≤((Fin.cons q.2.2 q.1 : Fin (N+1)→RowRival) j).2)→
      S*s*(Γ.real univ)^2*ν.real (firstCopyBoundary c u)/2-
        Γ.real univ*(D+2*(1-ξ)*D+e)-
        (∫q : (Fin N→RowRival)×(A×RowRival),
          rowIntervalLoss c (1-ξ) (x q.2.1) (z q.2.1) (Fin.cons q.2.2 q.1)
            ∂ν.prod (Γ.prod (rivalLaw s a' h G)))≤
        ∫q : (Fin N→RowRival)×(A×RowRival),
          literalRowPayoff ξ c (w q.2.1) (z q.2.1,Fin.cons q.2.2 q.1)-
            literalRowPayoff ξ c (w q.2.1) (x q.2.1,Fin.cons q.2.2 q.1)
              ∂ν.prod (Γ.prod (rivalLaw s a' h G)) := by
  intro e he
  obtain ⟨δ,hδ,hint⟩:=firstCopy_integrated_literalGain_uniform_of_integrable (N:=N) (A:=A) hξ hξh ha haB hW e he
  refine ⟨δ,hδ,?_⟩
  intro s a' h hs ha' hh hsum G θ hG hθf hθa hθG hθ0 Γ hΓ ν hν c hc
    l u S D hu hS w x z hw hx hz hpush hθ hbox hrows
  letI:=hG
  letI:=hθf
  letI:=hθa
  letI:=hΓ
  letI:=hν
  let ρ:=rivalLaw s a' h G
  letI : IsProbabilityMeasure ρ:=rivalLaw_isProbability s a' h hs ha' hh hsum G
  have hξ1 : ξ<1:=by linarith
  have hB : 0≤B:=(ha.trans_le haB).le
  have hbounds : ∀ᵐt ∂Γ,|w t|≤W ∧ |x t|≤B ∧ |z t|≤|l|+|D|:=by
    filter_upwards [hbox] with t ht
    have hx0 : 0<x t:=ha.trans_le ht.2.1
    have hz0 : 0<z t:=hx0.trans ht.2.2.2.2.1
    refine ⟨ht.2.2.2.2.2.2.2.2.2,?_,?_⟩
    · rw [abs_of_pos hx0]
      exact ht.2.2.1
    · rw [abs_of_pos hz0]
      have hwidth:=ht.2.2.2.2.2.2.1
      linarith [le_abs_self l,le_abs_self D]
  have hI:=integrable_literalCarrierGain hξ hξ1 c ν Γ ρ w x z hw hx hz W B (|l|+|D|) hbounds
  have hL:=integrable_literalCarrierLoss c (1-ξ) ν Γ ρ x z hx hz B hB
    (hbounds.mono (fun _ ht=>ht.2.1))
  exact hint s a' h hs ha' hh hsum G θ hG hθf hθa hθG hθ0 Γ hΓ ν hν c hc
    l u S D hu hS w x z hw hx hz hpush hθ hbox hrows hI hL

end IntegratedBonus
end FCAppendix.Affine.LowBody
