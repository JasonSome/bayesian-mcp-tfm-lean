import FCAppendix.Affine.Tail04.UnusedPublicMeasurable
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedRowAverage
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeHighExperiment NativeUnusedExperiment NativeUnusedReference
open PublicScenario EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy
open MenuError UnusedPublicLaw UnusedPublicPrices UnusedFiniteCountError UnusedPublicMeasurable
open scoped BigOperators

def publicValue (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (B y : ℝ)
    (f : Fin 3→ℝ) (b : Fin A→ Icc (1:ℝ) B) : ℝ :=
  (publicCount Q A H (TypicalGuard.bids (SortedAllNoise.sortedBox b)) y).expect f

def failure (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) (b : Fin A→ Icc (1:ℝ) B) : ℝ :=
  (scenarioLaw Q A H (TypicalGuard.bids (SortedAllNoise.sortedBox b))).prob
    (fun s=>¬StrongSafe Q A H B B0 R Rp width γ a
      (TypicalGuard.bids (SortedAllNoise.sortedBox b)) s)

lemma measurable_publicValue (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (B y : ℝ)
    (f : Fin 3→ℝ) : Measurable (publicValue Q A H B y f) :=
  (measurable_public_expect Q A H y f).comp measurable_sorted_real

lemma measurable_failure (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) : Measurable (failure Q A H B B0 R Rp width γ a) :=
  (UnusedPublicMeasurable.measurable_failure Q A H B B0 R Rp width γ a).comp
    measurable_sorted_real

lemma failure_bounds (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) (b : Fin A→ Icc (1:ℝ) B) :
    failure Q A H B B0 R Rp width γ a b∈Icc (0:ℝ) 1 :=
  ⟨FiniteLaw.prob_nonneg _ _,FiniteLaw.prob_le_one _ _⟩

lemma integrable_publicValue (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (B y : ℝ)
    (f : Fin 3→ℝ) (M : Measure (Fin A→ Icc (1:ℝ) B)) [IsFiniteMeasure M] :
    Integrable (publicValue Q A H B y f) M :=
  Integrable.of_bound (measurable_publicValue Q A H B y f).aestronglyMeasurable
    (∑r,‖f r‖) (ae_of_all _ fun _=> FiniteLaw.norm_expect_le_sum_norm _ f)

lemma integrable_failure (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) (M : Measure (Fin A→ Icc (1:ℝ) B)) [IsFiniteMeasure M] :
    Integrable (failure Q A H B B0 R Rp width γ a) M := by
  refine Integrable.of_bound
    (measurable_failure Q A H B B0 R Rp width γ a).aestronglyMeasurable 1 ?_
  exact ae_of_all _ fun b=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (failure_bounds Q A H B B0 R Rp width γ a b).1]
    exact (failure_bounds Q A H B B0 R Rp width γ a b).2

def totalError (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ)
    (b : Fin A→ Icc (1:ℝ) B) : ℝ :=
  |publicValue Q A H B y f b-target.expect f|+4*MenuError.oscillation f*failure Q A H B B0 R Rp width γ a b

lemma measurable_totalError (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ) :
    Measurable (totalError Q A H B B0 R Rp width γ a y target f) :=
  ((measurable_publicValue Q A H B y f).sub measurable_const).abs.add
    ((measurable_failure Q A H B B0 R Rp width γ a).const_mul _)

lemma totalError_bounds (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ)
    (b : Fin A→ Icc (1:ℝ) B) :
    totalError Q A H B B0 R Rp width γ a y target f b∈Icc (0:ℝ) (6*MenuError.oscillation f) := by
  have hp:=count_expect_difference_bound
    (publicCount Q A H (TypicalGuard.bids (SortedAllNoise.sortedBox b)) y) target f
  have hf:=failure_bounds Q A H B B0 R Rp width γ a b
  have ho:=oscillation_nonneg f
  unfold totalError publicValue
  constructor
  · exact add_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) ho) hf.1)
  · have hmul := mul_le_mul_of_nonneg_left hf.2 (mul_nonneg (by norm_num : (0:ℝ)≤4) ho)
    nlinarith

lemma integrable_totalError (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ)
    (M : Measure (Fin A→ Icc (1:ℝ) B)) [IsFiniteMeasure M] :
    Integrable (totalError Q A H B B0 R Rp width γ a y target f) M := by
  refine Integrable.of_bound
    (measurable_totalError Q A H B B0 R Rp width γ a y target f).aestronglyMeasurable
      (6*MenuError.oscillation f) ?_
  exact ae_of_all _ fun b=> by
    rw [Real.norm_eq_abs,abs_of_nonneg (totalError_bounds Q A H B B0 R Rp width γ a y target f b).1]
    exact (totalError_bounds Q A H B B0 R Rp width γ a y target f b).2

section OriginalPrivate
variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c) (H0 H1 : Fin (m+1))
  (Q : PublicScenario.Data) (hc : Q.c=c) (hξ : Q.ξ=K.ξ)
  (hν0 : Q.marksLaw H0.val=K.marksLaw H0) (hν1 : Q.marksLaw H1.val=K.marksLaw H1)
  (ρ : ProbabilityMeasure (Ici K.E.H⊕Icc K.E.R K.E.Rp))
  (hrows : ∀H : Fin (m+1),K.originalPrivateRow H=PrivateRowSorting.sortedOriginalIid K.E H.val ρ)
  (M : Measure (Fin A→ Icc (1:ℝ) K.E.U)) [IsProbabilityMeasure M]

def reference (y : ℝ) : CountLaw 2 :=
  FiniteLaw.ofMeasure (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))) (fun x : ((Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1))=> outcome K H0 H1 Q x.1 y x.2)
    (measurable_outcome_joint K H0 H1 Q y)

lemma reference_expect (y : ℝ) (f : Fin 3→ℝ) :
    (reference K H0 H1 Q ρ M y).expect f=
      ∫b,(NativeUnusedReference.rowCount K H0 H1 Q ρ b y).expect f ∂M := by
  rw [reference,FiniteLaw.expect_ofMeasure]
  rw [integral_prod _ (CountLaw.integrable_comp (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))) _ (measurable_outcome_joint K H0 H1 Q y) f)]
  apply integral_congr_ae
  exact ae_of_all _ fun b=>(FiniteLaw.expect_ofMeasure _ _ (measurable_outcome K H0 H1 Q b y) f).symm

lemma integrable_referenceRow (y : ℝ) (f : Fin 3→ℝ) :
    Integrable (fun b=>(NativeUnusedReference.rowCount K H0 H1 Q ρ b y).expect f) M := by
  have hi:=(CountLaw.integrable_comp (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))) _ (measurable_outcome_joint K H0 H1 Q y) f).integral_prod_left
  simpa only [NativeUnusedReference.rowCount,FiniteLaw.expect_ofMeasure] using hi

include hc hξ hν0 hν1 in
theorem native_failure_integral (B0 γ a : ℝ) :
    (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))).real {x : ((Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1)) | ¬Good K H0 H1 Q x.1 x.2.1}≤
      ∫b,failure Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a b ∂M := by
  let B : Set ((Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1)):={x | ¬Good K H0 H1 Q x.1 x.2.1}
  have hB : MeasurableSet B := (measurableSet_good K H0 H1 Q).compl.preimage
    (measurable_fst.prodMk measurable_snd.fst)
  have hi : Integrable (fun x : ((Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1))=> if x∈B then (1:ℝ) else 0) (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))) :=
    Integrable.of_bound (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable
      1 (ae_of_all _ fun x=> by split_ifs <;> norm_num)
  have he : (M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))).real B=(∫x : ((Fin A→ Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1)),if x∈B then (1:ℝ) else 0 ∂(M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1)))) := by
    simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ:=(M.prod ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1)))) hB).symm
  rw [he,integral_prod _ hi]
  apply integral_mono hi.integral_prod_left
    (integrable_failure Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a M)
  intro b
  have hBu : MeasurableSet {u : unitInterval | ¬Good K H0 H1 Q b u} :=
    (measurableSet_good K H0 H1 Q).compl.preimage (measurable_const.prodMk measurable_id)
  have hip : Integrable (fun z : unitInterval×RawPayload K H0 H1=>
      if ¬Good K H0 H1 Q b z.1 then (1:ℝ) else 0)
      ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1)) :=
    Integrable.of_bound (Measurable.ite (hBu.preimage measurable_fst)
      measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun z=> by split_ifs <;> norm_num)
  change (∫z : unitInterval×RawPayload K H0 H1,
    if ¬Good K H0 H1 Q b z.1 then (1:ℝ) else 0 ∂(volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))≤_
  have hprojection : (∫z : unitInterval×RawPayload K H0 H1,
      if ¬Good K H0 H1 Q b z.1 then (1:ℝ) else 0
        ∂(volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))=
      ∫u : unitInterval,if ¬Good K H0 H1 Q b u then (1:ℝ) else 0 :=
    (measurePreserving_fst (μ:=(volume:Measure unitInterval))
      (ν:=rawPayloadLaw K ρ H0 H1)).integral_comp_ae_real
        (Measurable.ite hBu measurable_const measurable_const).aestronglyMeasurable
  have huu : (∫u : unitInterval,if ¬Good K H0 H1 Q b u then (1:ℝ) else 0 ∂volume)=
      (volume:Measure unitInterval).real {u | ¬Good K H0 H1 Q b u} := by
    simpa only [Set.indicator,Pi.one_apply,Set.mem_setOf_eq] using! integral_indicator_one (μ:=(volume:Measure unitInterval)) hBu
  rw [hprojection,huu]
  exact NativeUnusedReference.native_failure K H0 H1 Q hc hξ hν0 hν1 B0 γ a b

include hc hξ hν0 hν1 hrows in
theorem reference_target_error (B0 γ a y : ℝ) (target : CountLaw 2) (f : Fin 3→ℝ) :
    |(reference K H0 H1 Q ρ M y).expect f-target.expect f|≤
      ∫b,|publicValue Q A (H0.val,H1.val) K.E.U y f b-target.expect f|+
        2*MenuError.oscillation f*failure Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a b ∂M := by
  have hi:=integrable_referenceRow K H0 H1 Q ρ M y f
  have hp:=integrable_publicValue Q A (H0.val,H1.val) K.E.U y f M
  have hb:=integrable_failure Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a M
  have hdiff : (reference K H0 H1 Q ρ M y).expect f-target.expect f=
      ∫b : Fin A→ Icc (1:ℝ) K.E.U,
        (NativeUnusedReference.rowCount K H0 H1 Q ρ b y).expect f-target.expect f ∂M := by
    rw [integral_sub hi (integrable_const _),reference_expect K H0 H1 Q ρ M y f]
    simp only [integral_const,probReal_univ,one_smul]
  rw [hdiff]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hi.sub (integrable_const _)).abs
    ((hp.sub (integrable_const _)).abs.add (hb.const_mul _))
  intro b
  have hh:=NativeUnusedReference.row_count_error K H0 H1 Q hc hξ hν0 hν1 ρ hrows B0 γ a b y f
  have ht:=abs_sub_le (NativeUnusedReference.rowCount K H0 H1 Q ρ b y |>.expect f)
    (publicValue Q A (H0.val,H1.val) K.E.U y f b) (target.expect f)
  change |_ - _|≤_ at hh
  change |(NativeUnusedReference.rowCount K H0 H1 Q ρ b y).expect f-target.expect f|≤
    |publicValue Q A (H0.val,H1.val) K.E.U y f b-target.expect f|+
      2*MenuError.oscillation f*failure Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a b
  dsimp only [publicValue,failure] at hh ht ⊢
  linarith

end OriginalPrivate
end FCAppendix.Affine.Tail04.UnusedRowAverage
