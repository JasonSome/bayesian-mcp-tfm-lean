import FCAppendix.Affine.Hybrid.Tail03.Rectangle
import FCAppendix.Affine.Hybrid.Tail03.Law
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

lemma count_two_success (C : CountLaw 2) : C.success=1-C.mass 0 := by
  have ht := C.total
  norm_num [Fin.sum_univ_succ] at ht
  norm_num [CountLaw.success,FiniteLaw.expect,Fin.sum_univ_succ,successIndicator]
  linarith

lemma count_two_load (C : CountLaw 2) : C.load=1-C.mass 0+C.mass 2 := by
  have ht := C.total
  norm_num [Fin.sum_univ_succ] at ht
  norm_num [CountLaw.load,FiniteLaw.expect,Fin.sum_univ_succ]
  linarith

lemma count_two_duplicates (C : CountLaw 2) : C.duplicates=C.mass 2 := by
  rw [CountLaw.duplicates,count_two_load,count_two_success]
  ring

lemma count_two_statistics_tendsto (C : ℕ→ CountLaw 2) (D : CountLaw 2)
    (h0 : Tendsto (fun m=>(C m).mass 0) atTop (𝓝 (D.mass 0)))
    (h2 : Tendsto (fun m=>(C m).mass 2) atTop (𝓝 (D.mass 2))) :
    Tendsto (fun m=>(C m).success) atTop (𝓝 D.success) ∧
    Tendsto (fun m=>(C m).load) atTop (𝓝 D.load) := by
  simp_rw [count_two_success,count_two_load]
  exact ⟨tendsto_const_nhds.sub h0,(tendsto_const_nhds.sub h0).add h2⟩

lemma measurable_count_success (C : ℝ→ CountLaw 2)
    (h : ∀r,Measurable (fun v=>(C v).mass r)) : Measurable (fun v=>(C v).success) := by
  simp_rw [count_two_success]
  exact measurable_const.sub (h 0)

lemma measurable_count_load (C : ℝ→ CountLaw 2)
    (h : ∀r,Measurable (fun v=>(C v).mass r)) : Measurable (fun v=>(C v).load) := by
  simp_rw [count_two_load]
  exact (measurable_const.sub (h 0)).add (h 2)

lemma integrable_count_success (mu : Measure ℝ) [IsFiniteMeasure mu]
    (C : ℝ→ CountLaw 2) (h : Measurable (fun v=>(C v).success)) :
    Integrable (fun v=>(C v).success) mu := by
  apply Integrable.of_bound h.aestronglyMeasurable 1
  exact Eventually.of_forall (fun v=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (CountLaw.success_nonneg _)]
    exact CountLaw.success_le_one _)

lemma integrable_count_load (mu : Measure ℝ) [IsFiniteMeasure mu]
    (C : ℝ→ CountLaw 2) (h : Measurable (fun v=>(C v).load)) :
    Integrable (fun v=>(C v).load) mu := by
  apply Integrable.of_bound h.aestronglyMeasurable 2
  exact Eventually.of_forall (fun v=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (CountLaw.load_nonneg _)]
    exact CountLaw.load_le_n _)

theorem bounded_count_aggregate_passage (F : ProbabilityMeasure ℝ)
    (C : ℕ→ℝ→ CountLaw 2) (D : ℝ→ CountLaw 2)
    (hmeas : ∀m r,Measurable (fun v=>(C m v).mass r))
    (hlim : ∀ᵐv ∂(F : Measure ℝ),∀r,
      Tendsto (fun m=>(C m v).mass r) atTop (𝓝 ((D v).mass r))) :
    Tendsto (fun m=>∫v,(C m v).success ∂(F : Measure ℝ)) atTop
      (𝓝 (∫v,(D v).success ∂(F : Measure ℝ))) ∧
    Tendsto (fun m=>∫v,(C m v).load ∂(F : Measure ℝ)) atTop
      (𝓝 (∫v,(D v).load ∂(F : Measure ℝ))) := by
  constructor
  · apply tendsto_integral_of_dominated_convergence (fun _ : ℝ=>(1:ℝ))
      (fun m=>(measurable_count_success _ (hmeas m)).aestronglyMeasurable)
      (integrable_const 1)
    · intro m
      exact Eventually.of_forall (fun v=> by
        rw [Real.norm_eq_abs,abs_of_nonneg (CountLaw.success_nonneg _)]
        exact CountLaw.success_le_one _)
    · filter_upwards [hlim] with v hv
      exact (count_two_statistics_tendsto (fun m=> C m v) (D v) (hv 0) (hv 2)).1
  · apply tendsto_integral_of_dominated_convergence (fun _ : ℝ=>(2:ℝ))
      (fun m=>(measurable_count_load _ (hmeas m)).aestronglyMeasurable)
      (integrable_const 2)
    · intro m
      exact Eventually.of_forall (fun v=> by
        rw [Real.norm_eq_abs,abs_of_nonneg (CountLaw.load_nonneg _)]
        exact CountLaw.load_le_n _)
    · filter_upwards [hlim] with v hv
      exact (count_two_statistics_tendsto (fun m=> C m v) (D v) (hv 0) (hv 2)).2

theorem strict_tail_menu_outcomes (p : Center) (rect : Rectangle p)
    (hr : ExplicitReceiptInequalities p rect) (lam : Fin 2→ℝ) (hlam : lam∈rect.box)
    (b : ℝ) (hb : b∈Ioo (1:ℝ) (B p)) :
    served p lam b < 1 ∧ 1 < load p lam b ∧ 0 < duplicates p lam b := by
  have hw (r : Fin 2) := regime_weights_positive p r
  have he (r : Fin 2) := mixed_prob_positive_before_B p r hb.2
  have hq (r : Fin 2) := hr.probabilities lam hlam r b ⟨hb.1.le,hb.2.le⟩
  have hf (r : Fin 2) : 0 < regimeWeight p r*mixedProb p r b*(1-exposure p lam r b)^2 := by
    apply mul_pos (mul_pos (hw r) (he r))
    exact sq_pos_of_pos (by linarith [(hq r).2])
  have hl (r : Fin 2) : 0 < regimeWeight p r*mixedProb p r b*(2*exposure p lam r b-1) := by
    apply mul_pos (mul_pos (hw r) (he r))
    linarith [(hq r).1]
  have hd (r : Fin 2) : 0 < regimeWeight p r*mixedProb p r b*(exposure p lam r b)^2 := by
    apply mul_pos (mul_pos (hw r) (he r))
    exact sq_pos_of_pos (by linarith [(hq r).1])
  refine ⟨?_,?_,?_⟩
  · unfold served
    rw [Fin.sum_univ_two]
    linarith [hf 0,hf 1]
  · rw [load_identity,Fin.sum_univ_two]
    linarith [hl 0,hl 1]
  · unfold duplicates
    rw [Fin.sum_univ_two]
    linarith [hd 0,hd 1]

theorem transfer_strict_outcomes (p : Center) (rect : Rectangle p)
    (hr : ExplicitReceiptInequalities p rect) (lam : Fin 2→ℝ) (hlam : lam∈rect.box)
    (b : ℝ) (hb : b∈Ioo (1:ℝ) (B p)) (C : CountLaw 2)
    (h0 : C.mass 0=1-served p lam b) (h2 : C.mass 2=duplicates p lam b) :
    0< C.success ∧ C.success<1 ∧ 1< C.load ∧ 1< C.load/C.success := by
  have hm := strict_tail_menu_outcomes p rect hr lam hlam b hb
  have hs : C.success=served p lam b := by rw [count_two_success,h0]; ring
  have hl : C.load=load p lam b := by rw [count_two_load,h0,h2]; unfold load; ring
  have hS1 : C.success<1 := by rw [hs]; exact hm.1
  have hL1 : 1< C.load := by rw [hl]; exact hm.2.1
  have hbound := CountLaw.load_le_mul_success C
  have hS0 : 0< C.success := by norm_num at hbound; linarith
  refine ⟨hS0,hS1,hL1,?_⟩
  apply (lt_div_iff₀ hS0).2
  linarith

theorem strict_inverse_coverage {Q1 Q2 beta : ℝ}
    (_hQ1 : 0< Q1) (hQ2 : 0< Q2) (hQ : Q2< Q1) (hb : 0< beta) :
    beta/Q1 < beta/Q2 := div_lt_div_of_pos_left hb hQ2 hQ

theorem integral_success_mixture (p : LawInput) (C : ℝ→ CountLaw 2)
    (hC : Measurable (fun v=>(C v).success)) :
    (∫v,(C v).success ∂(mixFourComponents p : Measure ℝ)) =
      p.s*(∫v,(C v).success ∂bandMeasure 0 p.d0)+
      p.h*(∫v,(C v).success ∂bandMeasure (2-p.w) (2+p.w))+
      p.a*(∫v,(C v).success ∂fixedUpperValueMeasure p) := by
  letI := bandMeasure_probability p.d0_pos
  letI := bandMeasure_probability (by linarith [p.w_pos] : 2-p.w<2+p.w)
  have h0 := integrable_count_success (bandMeasure 0 p.d0) C hC
  have h1 := integrable_count_success (bandMeasure (2-p.w) (2+p.w)) C hC
  have h2 := integrable_count_success (fixedUpperValueMeasure p) C hC
  change (∫v,(C v).success ∂mixtureMeasure p) = _
  rw [commonLaw_fixedUpper_decomposition p,fixedUpperMeasure]
  rw [integral_add_measure ((h0.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h1.smul_measure ENNReal.ofReal_ne_top)) (h2.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (h0.smul_measure ENNReal.ofReal_ne_top)
      (h1.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure,ENNReal.toReal_ofReal p.s_pos.le,
    ENNReal.toReal_ofReal p.h_pos.le,ENNReal.toReal_ofReal p.a_pos.le,smul_eq_mul]

theorem aggregate_coverage_gap (p : LawInput) (theta e : ℝ)
    (C1 C2 : ℝ→ CountLaw 2)
    (hm1 : Measurable (fun v=>(C1 v).success)) (hm2 : Measurable (fun v=>(C2 v).success))
    (hlow1 : ∀ᵐv ∂bandMeasure 0 p.d0,(C1 v).success=0)
    (hlow2 : ∀ᵐv ∂bandMeasure 0 p.d0,(C2 v).success=0)
    (hpart1 : ∀ᵐv ∂bandMeasure (2-p.w) (2+p.w),1-e≤(C1 v).success)
    (hpart2 : ∀ᵐv ∂bandMeasure (2-p.w) (2+p.w),(C2 v).success=1-theta)
    (hhigh1 : ∀ᵐv ∂fixedUpperValueMeasure p,(C1 v).success=1) :
    p.h*(theta-e) ≤
      (∫v,(C1 v).success ∂(mixFourComponents p : Measure ℝ))-
      (∫v,(C2 v).success ∂(mixFourComponents p : Measure ℝ)) := by
  letI := bandMeasure_probability p.d0_pos
  letI := bandMeasure_probability (by linarith [p.w_pos] : 2-p.w<2+p.w)
  have hloweq1 : (∫v,(C1 v).success ∂bandMeasure 0 p.d0)=0 := by
    rw [integral_congr_ae hlow1,integral_zero]
  have hloweq2 : (∫v,(C2 v).success ∂bandMeasure 0 p.d0)=0 := by
    rw [integral_congr_ae hlow2,integral_zero]
  have hpartge : 1-e≤∫v,(C1 v).success ∂bandMeasure (2-p.w) (2+p.w) := by
    have hh := integral_mono_ae (integrable_const (1-e))
      (integrable_count_success _ C1 hm1) hpart1
    simpa using hh
  have hparteq : (∫v,(C2 v).success ∂bandMeasure (2-p.w) (2+p.w))=1-theta := by
    rw [integral_congr_ae hpart2]
    simp
  have hhigheq : (∫v,(C1 v).success ∂fixedUpperValueMeasure p)=1 := by
    rw [integral_congr_ae hhigh1]
    simp
  have hhighle : (∫v,(C2 v).success ∂fixedUpperValueMeasure p)≤1 := by
    have hh := integral_mono_ae (integrable_count_success _ C2 hm2) (integrable_const (μ:=fixedUpperValueMeasure p) (1:ℝ))
      (Eventually.of_forall (fun v=> CountLaw.success_le_one (C2 v)))
    simpa using hh
  rw [integral_success_mixture p C1 hm1,integral_success_mixture p C2 hm2,
    hloweq1,hloweq2,hparteq,hhigheq]
  have hh := mul_le_mul_of_nonneg_left hpartge p.h_pos.le
  have ha := mul_le_mul_of_nonneg_left hhighle p.a_pos.le
  nlinarith

theorem positive_coverage_from_load (F : ProbabilityMeasure ℝ) (C : ℝ→ CountLaw 2)
    (hC : ∀r,Measurable (fun v=>(C v).mass r))
    (hL : (∫v,(C v).load ∂(F : Measure ℝ))=99/100) :
    0 < ∫v,(C v).success ∂(F : Measure ℝ) := by
  have hS := integrable_count_success (F : Measure ℝ) C (measurable_count_success C hC)
  have hload := integrable_count_load (F : Measure ℝ) C (measurable_count_load C hC)
  have hh := integral_mono_ae hload (hS.const_mul 2)
    (Eventually.of_forall (fun v=> CountLaw.load_le_mul_success (C v)))
  rw [integral_const_mul,hL] at hh
  linarith

end FCAppendix.Affine.Hybrid.Tail03
