import FCAppendix.Affine.Tail04.NativeHighSeedProduct
import FCAppendix.Affine.Tail04.NativeNoisyBindings
import FCAppendix.Affine.Tail04.AllCountActiveFiniteGain
import FCAppendix.Affine.Tail04.EqualOriginalCountPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeHighExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeSamplerCountLaw NativeHighSeedProduct
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy PrivateRowSorting SortedAllNoise
open scoped BigOperators

section Numerical
variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c)
  (ρ : ProbabilityMeasure (Ici K.E.H ⊕ Icc K.E.R K.E.Rp))
  (hrows : ∀ H : Fin (m+1),K.originalPrivateRow H=sortedOriginalIid K.E H.val ρ)
  (H0 H1 : Fin (m+1))

abbrev RawPayload :=
  (Row H0.val K.E.R K.E.Rp K.E.H×Row H1.val K.E.R K.E.Rp K.E.H)×
    ((Fin 2 → Seed)×Equiv.Perm (Fin 2))

def rawPayloadLaw : Measure (RawPayload K H0 H1) :=
  (((originalIid K.E H0.val ρ : Measure _).prod (originalIid K.E H1.val ρ : Measure _)).prod
    ((Measure.pi (fun _ : Fin 2 => seedLaw)).prod (permLaw 2)))

instance rawPayloadLaw_probability : IsProbabilityMeasure (rawPayloadLaw K ρ H0 H1) := by
  unfold rawPayloadLaw
  infer_instance

def sortedPairs (z : RawPayload K H0 H1) :
    (Row H0.val K.E.R K.E.Rp K.E.H×unitInterval)×
      (Row H1.val K.E.R K.E.Rp K.E.H×unitInterval) :=
  ((sortRow K.E H0.val z.1.1,(z.2.1 0).1),
    (sortRow K.E H1.val z.1.2,(z.2.1 1).1))

lemma measurable_sortedPairs : Measurable (sortedPairs K H0 H1) :=
  (((measurable_sortRow K.E H0.val).comp measurable_fst.fst).prodMk
    (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd.fst))).prodMk
      (((measurable_sortRow K.E H1.val).comp measurable_fst.snd).prodMk
        (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd.fst)))

include hrows in
theorem sortedPairs_preserves : MeasurePreserving (sortedPairs K H0 H1)
    (rawPayloadLaw K ρ H0 H1) (pairLaw K H0 H1) := by
  have h0 : MeasurePreserving (sortRow K.E H0.val)
      (originalIid K.E H0.val ρ : Measure _) (K.originalPrivateRow H0) :=
    ⟨measurable_sortRow K.E H0.val,by rw [hrows H0];rfl⟩
  have h1 : MeasurePreserving (sortRow K.E H1.val)
      (originalIid K.E H1.val ρ : Measure _) (K.originalPrivateRow H1) :=
    ⟨measurable_sortRow K.E H1.val,by rw [hrows H1];rfl⟩
  exact (pairRows_preserves K H0 H1).comp
    ((h0.prod h1).prod (MeasurePreserving.id _))

variable (Q : PublicScenario.Data) (b : Fin A → Icc (1:ℝ) K.E.U) (i : Fin A)

def choice (lowPresent : Bool) (u : unitInterval) : Scenario A×unitInterval :=
  if lowPresent then
    PublicScenario.draw Q A (fun j => (sortedBox b j:ℝ),(H0.val,H1.val)) u
  else (PublicScenario.fallback A,1)

lemma measurable_choice (lowPresent : Bool) : Measurable (choice K H0 H1 Q b lowPresent) := by
  cases lowPresent
  · exact measurable_const
  · exact (PublicScenario.measurable_draw Q A).comp (measurable_const.prodMk measurable_id)

def outcome (lowPresent : Bool) (z : unitInterval×RawPayload K H0 H1) : Fin 3 :=
  let q := choice K H0 H1 Q b lowPresent z.1
  scenarioOutcome K A H0 H1 (sortedBox b) (focalRank (fun j => (b j:ℝ)) i)
    (q.1,(q.2,sortedPairs K H0 H1 z.2))

lemma measurable_outcome (lowPresent : Bool) :
    Measurable (outcome K H0 H1 Q b i lowPresent) :=
  (measurable_scenarioOutcome K A H0 H1 (sortedBox b) _).comp
    (((measurable_choice K H0 H1 Q b lowPresent).fst.comp measurable_fst).prodMk
      (((measurable_choice K H0 H1 Q b lowPresent).snd.comp measurable_fst).prodMk
        ((measurable_sortedPairs K H0 H1).comp measurable_snd)))

lemma measurable_outcome_joint (lowPresent : Bool) :
    Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×
      (unitInterval×RawPayload K H0 H1) =>
        outcome K H0 H1 Q z.1 i lowPresent z.2) := by
  let J := (Fin A → Icc (1:ℝ) K.E.U)×(unitInterval×RawPayload K H0 H1)
  let bs : J → Fin A → Icc (1:ℝ) K.E.U := fun z => sortedBox z.1
  let ix : J → Fin A := fun z => focalRank (fun j => (z.1 j:ℝ)) i
  let q : J → Scenario A×unitInterval := fun z =>
    choice K H0 H1 Q z.1 lowPresent z.2.1
  let rp : J → (Row H0.val K.E.R K.E.Rp K.E.H×unitInterval)×
      (Row H1.val K.E.R K.E.Rp K.E.H×unitInterval) :=
    fun z => sortedPairs K H0 H1 z.2.2
  let p : J → Parameters A H0.val K.E.R K.E.Rp K.E.U :=
    fun z => (((q z).1,bs z),(K.signalLaw H0,(q z).2))
  have hbs : Measurable bs := continuous_sortedBox.measurable.comp measurable_fst
  have hix : Measurable ix := (measurable_focalRank i).comp
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_fst).subtype_val)
  have hq : Measurable q := by
    cases lowPresent
    · exact measurable_const
    · exact (PublicScenario.measurable_draw Q A).comp
        (((measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp hbs).subtype_val).prodMk
          measurable_const).prodMk measurable_snd.fst)
  have hrp : Measurable rp := (measurable_sortedPairs K H0 H1).comp measurable_snd.snd
  have hp : Measurable p := (hq.fst.prodMk hbs).prodMk (measurable_const.prodMk hq.snd)
  have h0 := (K.zeroSampler_measurable A H0 H1).comp
    ((hp.prodMk hrp.fst.fst).prodMk hrp.fst.snd)
  have h1 := (K.oneSampler_measurable A H0 H1).comp
    ((hp.prodMk hrp.snd.fst).prodMk hrp.snd.snd)
  have ha0 : Measurable (fun z : J =>
      decide (Sum.inl (ix z)∈K.zeroSampler A H0 H1 (p z,(rp z).1.1) (rp z).1.2)) :=
    (measurable_of_countable (fun w : Fin A×Finset (Fin A⊕Fin H0.val) =>
      decide (Sum.inl w.1∈w.2))).comp (hix.prodMk h0)
  have ha1 : Measurable (fun z : J =>
      decide (Sum.inl (ix z)∈K.oneSampler A H0 H1 (p z,(rp z).2.1) (rp z).2.2)) :=
    (measurable_of_countable (fun w : Fin A×Finset (Fin A⊕Fin H1.val) =>
      decide (Sum.inl w.1∈w.2))).comp (hix.prodMk h1)
  exact (measurable_of_countable boolPairCount).comp (ha0.prodMk ha1)

lemma outcome_cast {B : ℕ} (h : A=B) (d : Fin B → Icc (1:ℝ) K.E.U) (j : Fin B)
    (lowPresent : Bool) (z : unitInterval×RawPayload K H0 H1) :
    outcome K H0 H1 Q (d ∘ Fin.cast h) (Fin.cast h.symm j) lowPresent z=
      outcome K H0 H1 Q d j lowPresent z := by
  cases h
  rfl

def law (lowPresent : Bool) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
    (outcome K H0 H1 Q b i lowPresent) (measurable_outcome K H0 H1 Q b i lowPresent)

include hrows in
theorem law_low : law K ρ H0 H1 Q b i true=
    scenarioExperimentLaw K A H0 H1 (sortedBox b)
      (PublicScenario.scenarioLaw Q A (H0.val,H1.val) (fun j => (sortedBox b j:ℝ)))
        (focalRank (fun j => (b j:ℝ)) i) := by
  let C := PublicScenario.scenarioLaw Q A (H0.val,H1.val) (fun j => (sortedBox b j:ℝ))
  let T : unitInterval×RawPayload K H0 H1 →
      Scenario A×(unitInterval×((Row H0.val K.E.R K.E.Rp K.E.H×unitInterval)×
        (Row H1.val K.E.R K.E.Rp K.E.H×unitInterval))) := fun z =>
    let q := PublicScenario.draw Q A (fun j => (sortedBox b j:ℝ),(H0.val,H1.val)) z.1
    (q.1,(q.2,sortedPairs K H0 H1 z.2))
  have hd : MeasurePreserving
      (PublicScenario.draw Q A (fun j => (sortedBox b j:ℝ),(H0.val,H1.val))) volume
      ((FiniteLaw.probabilityMeasure C).prod (volume : Measure unitInterval)) :=
    ⟨(PublicScenario.measurable_draw Q A).comp (measurable_const.prodMk measurable_id),
      PublicScenario.draw_law Q A _⟩
  have hT : MeasurePreserving T
      ((volume : Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
      ((FiniteLaw.probabilityMeasure C).prod ((volume : Measure unitInterval).prod (pairLaw K H0 H1))) :=
    (measurePreserving_prodAssoc (FiniteLaw.probabilityMeasure C)
      (volume : Measure unitInterval) (pairLaw K H0 H1)).comp
      (hd.prod (sortedPairs_preserves K ρ hrows H0 H1))
  exact FiniteLaw.ofMeasure_comp_measurePreserving _ _ T hT
    (scenarioOutcome K A H0 H1 (sortedBox b) _) (measurable_scenarioOutcome K A H0 H1 (sortedBox b) _)

include hrows in
theorem law_noLow : law K ρ H0 H1 Q b i false=
    samplerLaw K A H0 H1 (atScenario K A H0 (sortedBox b) (PublicScenario.fallback A))
      (focalRank (fun j => (b j:ℝ)) i) := by
  have hT := (sortedPairs_preserves K ρ hrows H0 H1).comp
    (measurePreserving_snd (μ:=(volume : Measure unitInterval))
      (ν:=rawPayloadLaw K ρ H0 H1))
  exact FiniteLaw.ofMeasure_comp_measurePreserving _ _ _ hT
    (originalPairCount (K.zeroSampler A H0 H1) (K.oneSampler A H0 H1)
      (atScenario K A H0 (sortedBox b) (PublicScenario.fallback A))
      (Sum.inl (focalRank (fun j => (b j:ℝ)) i)) (Sum.inl (focalRank (fun j => (b j:ℝ)) i)))
    (measurable_originalPairCount _ _ (K.zeroSampler_measurable A H0 H1)
      (K.oneSampler_measurable A H0 H1) _ _ _)

variable (hc : Q.c=c) (hξ : Q.ξ=K.ξ)
  (hν0 : Q.marksLaw H0.val=K.marksLaw H0) (hν1 : Q.marksLaw H1.val=K.marksLaw H1)
  [Nonempty (Fin A)]

def perRegime (reg lowPresent : Bool) : CountLaw 2 :=
  if H0=H1 then
    EqualPrivateCountPayoff.countLaw A H0.val c K.E.R K.E.Rp K.ξ 1 K.E.U
      (sortedBox b,K.signalLaw H0) (focalRank (fun j => (b j:ℝ)) i)
  else UnequalOriginalCountPayoff.originalCount H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp
    K.E.H K.width (PublicScenario.e0 Q reg) Q.B0 reg lowPresent (K.marksLaw H0) (K.marksLaw H1)
    b (K.signalLaw H0) (K.originalPrivateRow H0) (K.originalPrivateRow H1) i

include hrows hc hξ hν0 hν1 in
theorem law_regime (lowPresent : Bool) :
    law K ρ H0 H1 Q b i lowPresent=
      FiniteLaw.finiteMix (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one)
        (fun reg => perRegime K H0 H1 Q b i reg lowPresent) := by
  by_cases h : H0=H1
  · subst H1
    have hf : ∀ reg,perRegime K H0 H0 Q b i reg lowPresent=
        EqualPrivateCountPayoff.countLaw A H0.val c K.E.R K.E.Rp K.ξ 1 K.E.U
          (sortedBox b,K.signalLaw H0) (focalRank (fun j => (b j:ℝ)) i) := by
      intro reg
      simp only [perRegime,if_true]
    simp_rw [hf]
    have hm : ∀ (C : CountLaw 2),FiniteLaw.finiteMix
        (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) (fun _ => C)=C := by
      intro C
      apply FiniteLaw.ext_expect
      intro f
      rw [FiniteLaw.expect_finiteMix,FiniteLaw.expect_const]
    rw [hm]
    cases lowPresent
    · rw [law_noLow K ρ hrows,samplerLaw_equal K A H0 _ rfl]
      rfl
    · rw [law_low K ρ hrows,scenarioExperimentLaw_equal]
  · cases lowPresent
    · rw [law_noLow K ρ hrows,samplerLaw_noLow_unequal K A H0 H1 h]
      apply FiniteLaw.ext_expect
      intro f
      rw [FiniteLaw.expect_finiteMix]
      have he : ∀ reg,perRegime K H0 H1 Q b i reg false=
          NativeTypicalCount.fallbackCount A H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp K.E.H
            (atScenario K A H0 (sortedBox b) (PublicScenario.fallback A))
            (K.originalPrivateRow H0) (K.originalPrivateRow H1)
            (focalRank (fun j => (b j:ℝ)) i) := by
        intro reg
        simp only [perRegime,if_neg h,UnequalOriginalCountPayoff.originalCount,Bool.false_eq_true,
          if_false]
        unfold NativeTypicalCount.fallbackCount originalIndependentCountLaw
        apply FiniteLaw.ofMeasure_congr_ae
        exact ae_of_all _ fun z => by
          simp only [originalPairCount,localAccept,NativeTypicalCount.fallback0,
            NativeTypicalCount.fallback1,
            UnequalOriginalCountPayoff.parameter,atScenario,PublicScenario.fallback,
            publicBids]
          rfl
      simp_rw [he]
      exact (FiniteLaw.expect_const _ _).symm
    · rw [law_low K ρ hrows,scenarioExperimentLaw_unequal K Q hc hξ A H0 H1 h hν0 hν1]
      apply FiniteLaw.ext_expect
      intro f
      rw [FiniteLaw.expect_finiteMix,FiniteLaw.expect_finiteMix]
      apply FiniteLaw.expect_congr
      intro reg
      simp only [perRegime,if_neg h,UnequalOriginalCountPayoff.originalCount,
        if_true,UnequalOriginalCountPayoff.parameter,ownerScenarioLaw,atScenario,publicBids]
      rfl

theorem perRegime_physical (hgap : (1-K.ξ)*K.E.U< K.E.R)
    (hno : ∀ j k,j≠k → (b j:ℝ)≠(b k:ℝ)) (reg lowPresent : Bool) :
    perRegime K H0 H1 Q b i reg lowPresent=
      AllCountActiveFiniteGain.physicalCount H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp K.width
        (PublicScenario.e0 Q reg) Q.B0 reg lowPresent (K.marksLaw H0) (K.marksLaw H1)
        (K.signalLaw H0).val b i := by
  have hh : H0=H1 ↔ H0.val=H1.val := Fin.ext_iff
  by_cases h : H0=H1
  · simp only [perRegime,if_pos h,AllCountActiveFiniteGain.physicalCount,if_pos (hh.mp h)]
  · rw [perRegime,if_neg h,AllCountActiveFiniteGain.physicalCount,if_neg (h ∘ hh.mpr)]
    exact UnequalOriginalCountPayoff.originalCount_eq_raw H0.val H1.val c reg lowPresent
      (K.marksLaw H0) (K.marksLaw H1) b (K.signalLaw H0)
      (K.originalPrivateRow H0) (K.originalPrivateRow H1)
      (K.marksLaw_exact H0) (K.marksLaw_exact H1) ⟨K.xi_pos,K.xi_lt_one⟩ K.width_pos
      (K.E.d_nonneg.trans_lt K.E.d_lt_R) (K.E.R_le_Rp.trans K.E.Rp_lt_H.le)
      K.E.Rp_lt_one hgap K.E.U_lt_H hno i

end Numerical
end FCAppendix.Affine.Tail04.NativeHighExperiment
