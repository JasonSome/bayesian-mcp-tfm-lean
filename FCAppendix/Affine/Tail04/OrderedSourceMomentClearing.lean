import FCAppendix.Affine.Tail04.OrderedSourceOriginalMoments

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceMomentClearing
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity SourceMenuPopulation SourceMenuError
open SourceMomentRectangle SourceMovingScalarGuards OrderedSourceRestrictedNative
open OrderedSourceActiveCountData OrderedSourceActiveSpecified OrderedSourceOriginalMoments
open SourceTailOptimizer SourceBulkAnalyticAdapter MenuError

theorem conditional_bidTest_tendsto (P : ValueParameters) (ξ : ℝ) (rec reg : Bool)
    (σ : ℕ→ Measure (JointAction 2)) [∀j,IsProbabilityMeasure (σ j)] (b : ℝ)
    (hnear : ∀δ,0< δ→∀ᶠj in atTop,∀ᵐa ∂σ j,|a.bid-b|< δ) :
    Tendsto (fun j=>∫a,bidTest P ξ rec reg a.bid ∂σ j) atTop
      (𝓝 (bidTest P ξ rec reg b)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hg⟩:=Metric.continuousAt_iff.mp (continuous_bidTest P ξ rec reg).continuousAt
    (ε/2) (half_pos hε)
  filter_upwards [hnear δ hδ] with j hj
  have hb : ∀ᵐa ∂σ j,‖bidTest P ξ rec reg a.bid-bidTest P ξ rec reg b‖≤ ε/2 := by
    filter_upwards [hj] with a ha
    have hh:=hg (by simpa only [Real.dist_eq] using ha)
    simpa only [Real.dist_eq,Real.norm_eq_abs] using hh.le
  have hh:=norm_integral_le_of_norm_le_const (μ:=σ j) hb
  simp only [probReal_univ,mul_one] at hh
  rw [integral_sub (integrable_bidTest P ξ rec reg _) (integrable_const _)] at hh
  simpa only [integral_const,probReal_univ,one_smul,Real.norm_eq_abs,Real.dist_eq] using
    hh.trans_lt (half_lt_self hε)

def limitIntegrand (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ)
    (rec reg : Bool) (v : ℝ) : ℝ :=
  if v∈P.bulkValues then bidTest P ξ rec reg 1
  else if P.M≤ v then bidTest P ξ rec reg (beta P ξ hξ lam v) else 0

def limitMoment (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ) (rec reg : Bool) : ℝ :=
  ∫v,limitIntegrand P ξ hξ lam rec reg v ∂valueLaw P

lemma limitIntegrand_bounds (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ)
    (rec reg : Bool) (v : ℝ) : limitIntegrand P ξ hξ lam rec reg v∈Icc (0:ℝ) 1 := by
  unfold limitIntegrand
  split_ifs <;> first | exact bidTest_bounds _ _ _ _ _ | norm_num

lemma measurable_limitIntegrand (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ)
    (rec reg : Bool) : Measurable (limitIntegrand P ξ hξ lam rec reg) := by
  have hb : Measurable (fun v=>(beta P ξ hξ lam v:ℝ)) :=
    ((measurable_beta P ξ hξ).comp (measurable_const.prodMk measurable_id)).subtype_val
  exact measurable_const.piecewise measurableSet_Icc
    (((continuous_bidTest P ξ rec reg).measurable.comp hb).piecewise measurableSet_Ici measurable_const)

lemma integrable_limitIntegrand (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ) (lam : ℝ×ℝ)
    (rec reg : Bool) : Integrable (limitIntegrand P ξ hξ lam rec reg) (valueLaw P) :=
  Integrable.of_bound (measurable_limitIntegrand P ξ hξ lam rec reg).aestronglyMeasurable 1
    (ae_of_all _ fun v=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (limitIntegrand_bounds P ξ hξ lam rec reg v).1]
      exact (limitIntegrand_bounds P ξ hξ lam rec reg v).2)

theorem limitMoment_lower (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (rec reg : Bool) :
    P.bulkWeight*baseFlag P reg≤ limitMoment P ξ hξ lam rec reg := by
  have hi : Integrable (P.bulkValues.indicator (fun _ : ℝ=> baseFlag P reg)) (valueLaw P) :=
    (integrable_const _).indicator measurableSet_Icc
  have hh:=integral_mono hi (integrable_limitIntegrand P ξ hξ lam rec reg) (fun v=> by
    by_cases hv : v∈P.bulkValues
    · simpa only [indicator_of_mem hv,limitIntegrand,if_pos hv,bidTest_one P hξ] using (le_refl (baseFlag P reg))
    · simp only [indicator_of_notMem hv]
      exact (limitIntegrand_bounds P ξ hξ lam rec reg v).1)
  have he : (∫v,P.bulkValues.indicator (fun _ : ℝ=> baseFlag P reg) v ∂valueLaw P)=
      P.bulkWeight*baseFlag P reg := by
    rw [integral_indicator measurableSet_Icc]
    simp only [setIntegral_const,smul_eq_mul,P.bulk_mass]
  rw [he] at hh
  exact hh

lemma limitMoment_positive (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (rec reg : Bool) : 0< limitMoment P ξ hξ lam rec reg :=
  (mul_pos P.bulkWeight_pos (baseFlag_bounds P reg).1).trans_le
    (limitMoment_lower P ξ hξ lam rec reg)

theorem limitMoment_eq_bulk_tail (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (rec reg : Bool) :
    limitMoment P ξ hξ lam rec reg=P.bulkWeight*baseFlag P reg+
      ∫ v in Ici P.M,bidTest P ξ rec reg (beta P ξ hξ lam v) ∂valueLaw P := by
  let f : ℝ→ℝ:=fun v=> bidTest P ξ rec reg (beta P ξ hξ lam v)
  have hf : Measurable f := (continuous_bidTest P ξ rec reg).measurable.comp
    (((measurable_beta P ξ hξ).comp (measurable_const.prodMk measurable_id)).subtype_val)
  have hi : Integrable f (valueLaw P) := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun v=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (bidTest_bounds P ξ rec reg _).1]
      exact (bidTest_bounds P ξ rec reg _).2)
  have hiB : Integrable (P.bulkValues.indicator (fun _ : ℝ=> baseFlag P reg)) (valueLaw P) :=
    (integrable_const _).indicator measurableSet_Icc
  have hiT : Integrable ((Ici P.M).indicator f) (valueLaw P) := hi.indicator measurableSet_Ici
  have he (v : ℝ) : limitIntegrand P ξ hξ lam rec reg v=
      P.bulkValues.indicator (fun _ : ℝ=> baseFlag P reg) v+(Ici P.M).indicator f v := by
    by_cases hB : v∈P.bulkValues
    · have hT : v∉Ici P.M := by
        change ¬P.M≤ v
        linarith [hB.2,P.active_tail_gap]
      simp only [limitIntegrand,if_pos hB,indicator_of_mem hB,indicator_of_notMem hT,
        add_zero,bidTest_one P hξ]
    · by_cases hT : P.M≤ v
      · simp only [limitIntegrand,if_neg hB,if_pos hT,indicator_of_notMem hB,
          Set.indicator_of_mem (s:=Ici P.M) hT,zero_add,f]
      · simp only [limitIntegrand,if_neg hB,if_neg hT,indicator_of_notMem hB,
          Set.indicator_of_notMem (s:=Ici P.M) hT,add_zero]
  unfold limitMoment
  simp_rw [he]
  rw [integral_add hiB hiT,integral_indicator measurableSet_Icc,
    integral_indicator measurableSet_Ici]
  simp only [setIntegral_const,smul_eq_mul,P.bulk_mass,f]

theorem bidTest_beta_formula (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (rec reg : Bool) (v : ℝ) :
    bidTest P ξ rec reg (beta P ξ hξ lam v)=
      if rec then mixedProbability P ξ reg (beta P ξ hξ lam v)/(beta P ξ hξ lam v:ℝ)
      else mixedProbability P ξ reg (beta P ξ hξ lam v) := by
  have hb:=(beta P ξ hξ lam v).property
  have hp:=sourceFlag_eq_mixedProbability P hξ hb reg
  cases rec
  · exact hp
  · simpa only [bidTest,if_true,sourceReciprocalWeight,max_eq_right hb.1] using
      congrArg (fun z : ℝ=> z/(beta P ξ hξ lam v:ℝ)) hp

theorem limitMoment_eq_source (P : ValueParameters) (ξ : ℝ) (hξ : 0< ξ)
    (lam : ℝ×ℝ) (rec reg : Bool) :
    limitMoment P ξ hξ lam rec reg=P.bulkWeight*baseFlag P reg+
      ∫ v in Ici P.M,
        (if rec then mixedProbability P ξ reg (beta P ξ hξ lam v)/(beta P ξ hξ lam v:ℝ)
         else mixedProbability P ξ reg (beta P ξ hξ lam v)) ∂valueLaw P := by
  rw [limitMoment_eq_bulk_tail]
  simp_rw [bidTest_beta_formula]

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
  (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
  (A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (N j))

local notation "ls" => fun j=> lambda (A j) hlow
local notation "G" => fun j=> specified (A j) hlow

include hN in
theorem every_fixed_moment {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) (rec reg : Bool) :
    ∀v∈Icc (0:ℝ) P.d0∪P.partialValues∪P.bulkValues∪Ici P.M,
      Tendsto (fun j=> conditionalMoment (A j) hlow rec reg v) atTop
        (𝓝 (limitIntegrand P ξ hξ lam rec reg v)) := by
  intro v hv
  by_cases hB : v∈P.bulkValues
  · have hc : ∀j,v∈P.movingActiveValues (cutoff (N j)) := by
      intro j
      exact ⟨hB.1,hB.2.trans (P.active_tail_gap.le.trans (A j).point.range.cutoff_gt_M.le)⟩
    have hh:=conditional_bidTest_tendsto P ξ rec reg (fun j=>(G j).σ v) 1 (by
      intro δ hδ
      exact (OrderedSourceFixedCountLaws.bulk_bid_concentration P ξ Up u k width hξ hξh hu hRUp hUp hw
        hlow N hN A hκ hder lam hlam hls v hB δ hδ).mono fun j hj=> hj.mono fun a ha=> ha.2.2)
    simpa only [conditionalMoment,if_pos (hc _),limitIntegrand,if_pos hB] using hh
  by_cases hT : P.M≤ v
  · have hh:=conditional_bidTest_tendsto P ξ rec reg (fun j=>(G j).σ v)
      (beta P ξ hξ lam v) (by
        intro δ hδ
        exact (OrderedSourceFixedCountLaws.tail_bid_concentration P ξ Up u k width hξ hξh hu hRUp hUp hw
          hlow N hN A hgeom lam hlam hls v hT δ hδ).mono fun j hj=> hj.mono fun a ha=> ha.2.2)
    simp only [limitIntegrand,if_neg hB,if_pos hT]
    apply hh.congr'
    filter_upwards [(cutoff_tendsto.comp hN).eventually_ge_atTop v] with j hj
    have hc : v∈P.movingActiveValues (cutoff (N j)) :=
      ⟨(by linarith [P.active_tail_gap,P.w_pos] : P.vA-P.w≤ P.M).trans hT,hj⟩
    simp only [conditionalMoment,if_pos hc]
  · have hvlo : v< P.vA-P.w := by
      rcases hv with ((hv|hv)|hv)|hv
      · linarith [hv.2,P.low_partial_gap,P.partial_active_gap,P.w_pos]
      · exact hv.2.trans_lt P.partial_active_gap
      · exact (hB hv).elim
      · exact (hT hv).elim
    have hc (j : ℕ) : v∉P.movingActiveValues (cutoff (N j)) := fun h=> not_le.mpr hvlo h.1
    simpa only [conditionalMoment,if_neg (hc _),limitIntegrand,if_neg hB,if_neg hT] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0))

include hwγ hN in
theorem actualMoment_tendsto {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) (rec reg : Bool) :
    Tendsto (fun j=> actualMoment (A j) hlow rec reg) atTop
      (𝓝 (limitMoment P ξ hξ lam rec reg)) := by
  simp_rw [actualMoment_original (A _) hlow hwγ]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ=>(1:ℝ))
    (fun j=>(integrable_conditionalMoment (A j) hlow rec reg).aestronglyMeasurable)
    (integrable_const 1)
  · intro j
    exact ae_of_all _ fun v=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (conditionalMoment_bounds (A j) hlow rec reg v).1]
      exact (conditionalMoment_bounds (A j) hlow rec reg v).2
  · filter_upwards [P.fine_support] with v hv
    exact every_fixed_moment P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N hN A
      hκ hder hgeom lam hlam hls rec reg v hv

include Up u k width hξh hu hRUp hUp hw hlow hwγ N hN A in
theorem actual_clearing {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (hgeom : DerivativeGeometry P ξ Λ)
    (lam : ℝ×ℝ) (hlam : lam∈Λ) (hls : Tendsto ls atTop (𝓝 lam)) :
    ∀reg : Bool,(if reg then lam.2 else lam.1)=
      meanNumerator P ξ (limitMoment P ξ hξ lam false reg) reg/
        limitMoment P ξ hξ lam true reg := by
  intro reg
  have hM:=actualMoment_tendsto P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN A
    hκ hder hgeom lam hlam hls false reg
  have hW:=actualMoment_tendsto P ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ N hN A
    hκ hder hgeom lam hlam hls true reg
  have hnum : Tendsto (fun j=> meanNumerator P ξ (actualMoment (A j) hlow false reg) reg) atTop
      (𝓝 (meanNumerator P ξ (limitMoment P ξ hξ lam false reg) reg)) := by
    cases reg <;> exact (hM.const_mul (1-ξ/2)).sub_const _
  have hratio:=hnum.div hW (limitMoment_positive P ξ hξ lam true reg).ne'
  have hcoord : Tendsto (fun j=> if reg then (ls j).2 else (ls j).1) atTop
      (𝓝 (if reg then lam.2 else lam.1)) := by
    cases reg
    · exact continuous_fst.continuousAt.tendsto.comp hls
    · exact continuous_snd.continuousAt.tendsto.comp hls
  have hratio' := hratio.congr' (Eventually.of_forall fun j=>
    (lambda_eq_actualMoments (A j) hlow reg).symm)
  exact tendsto_nhds_unique hcoord hratio'

end FCAppendix.Affine.Tail04.OrderedSourceMomentClearing
