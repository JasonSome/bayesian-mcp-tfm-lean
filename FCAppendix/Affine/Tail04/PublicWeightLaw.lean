import FCAppendix.Affine.Tail04.PublicScenario
import FCAppendix.Affine.Tail04.OriginalFlagMeasure

noncomputable section
namespace FCAppendix.Affine.Tail04.PublicWeightLaw
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon NativeTypicalCount JoinedHighPolicy
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

def weight (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B R Rp width : ℝ) (b : Fin A→ℝ) (s : Scenario A) : ℝ :=
  TypicalGuard.weight A H.1 H.2 Q.c Q.ξ B R Rp width (regime s)
    (mixed s) (owner0 s) (owner1 s) b (Q.marksLaw H.1) (Q.marksLaw H.2)

lemma output_weight (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B R Rp width : ℝ) (b : Fin A→ℝ) (reg : Bool)
    (target : Fin A) (flags : Fin A→ Bool) (AB : Finset (Fin A)×Finset (Fin A))
    (hAB : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      ((PublicScenario.ownerQuota Q) A H reg (target,flags))).mass AB≠0) :
    weight Q A H B R Rp width b (outputScenario reg ((target,flags),AB))=
      targetTypicalWeight
        (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
          (Q.marksLaw H.1) (Q.marksLaw H.2)) b target flags := by
  obtain ⟨hsub,hA,hB,hdis,hcover⟩ := Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty target flags) ((PublicScenario.ownerQuota_le Q) A H reg (target,flags)) AB.1 AB.2 hAB
  have hBcard : AB.2.card=(countParameters A H.1 H.2 Q.c Q.ξ reg
      (Q.marksLaw H.1) (Q.marksLaw H.2)).owner1 (targetMixedSet target flags).card := by
    rw [hB,Finset.card_sdiff_of_subset hsub,hA,OriginalOwnerCount.exclusive_card]
    rfl
  have hI : Disjoint (targetMixedSet target flags) (AB.1∪AB.2) := by
    rw [hcover]
    exact Finset.sdiff_disjoint.symm
  have hfull : targetMixedSet target flags∪(AB.1∪AB.2)=Finset.univ := by
    rw [hcover]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ _)
  exact TypicalGuardStatistics.actual_weight_phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
    (targetMixedSet target flags) AB.1 AB.2 b (Q.marksLaw H.1) (Q.marksLaw H.2)
    hdis hI hfull hA hBcard

lemma measurable_drawScenario (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (b : Fin A→ℝ) :
    Measurable (fun u : unitInterval => (draw Q A (b,H) u).1) :=
  ((measurable_draw Q A).comp (measurable_const.prodMk measurable_id)).fst

lemma drawScenario_law (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (b : Fin A→ℝ) :
    volume.map (fun u : unitInterval => (draw Q A (b,H) u).1)=
      FiniteLaw.probabilityMeasure (scenarioLaw Q A H b) := by
  have hp := measurePreserving_fst.comp
    (show MeasurePreserving (draw Q A (b,H)) (volume : Measure unitInterval)
      ((FiniteLaw.probabilityMeasure (scenarioLaw Q A H b)).prod (volume : Measure unitInterval)) from
      ⟨(measurable_draw Q A).comp (measurable_const.prodMk measurable_id),draw_law Q A (b,H)⟩)
  exact hp.map_eq

theorem draw_weight_failure (Q : PublicScenario.Data) (A : ℕ) (hA : 0< A)
    (H : ℕ×ℕ) (B R Rp width : ℝ) (b : Fin A→ℝ) :
    letI : Nonempty (Fin A) := ⟨⟨0,hA⟩⟩
    (volume : Measure unitInterval).real {u | weight Q A H B R Rp width b (draw Q A (b,H) u).1≠1}=
      (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one).expect (fun reg =>
        (Hybrid.rankLaw b).expect (fun target =>
          (independentFlagLaw (sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b)
            (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).prob (fun flags =>
              targetTypicalWeight
                (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
                  (Q.marksLaw H.1) (Q.marksLaw H.2)) b target flags≠1))) := by
  letI : Nonempty (Fin A) := ⟨⟨0,hA⟩⟩
  let f : Scenario A→ℝ := fun s => if weight Q A H B R Rp width b s≠1 then 1 else 0
  have hsam := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    (volume : Measure unitInterval) (fun u => (draw Q A (b,H) u).1)
    (measurable_drawScenario Q A H b) (scenarioLaw Q A H b) (drawScenario_law Q A H b)
  have hint := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval)
    (fun u => (draw Q A (b,H) u).1) (measurable_drawScenario Q A H b) f
  rw [hsam] at hint
  have hset : MeasurableSet {u : unitInterval | weight Q A H B R Rp width b (draw Q A (b,H) u).1≠1} :=
    ((Set.to_countable {s : Scenario A | weight Q A H B R Rp width b s≠1}).measurableSet).preimage
      (measurable_drawScenario Q A H b)
  have he : (volume : Measure unitInterval).real
      {u | weight Q A H B R Rp width b (draw Q A (b,H) u).1≠1}=
      (scenarioLaw Q A H b).expect f := by
    rw [hint]
    symm
    simpa only [f,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
      integral_indicator_one (μ:=(volume : Measure unitInterval)) hset
  rw [he,scenarioLaw,dif_pos hA,FiniteLaw.expect_map,latentLaw_expect]
  apply FiniteLaw.expect_congr
  intro reg
  apply FiniteLaw.expect_congr
  intro target
  apply FiniteLaw.expect_congr
  intro flags
  dsimp only
  calc
    _ = (Hybrid.ownerDivision (forcedExclusiveSet target flags)
        ((PublicScenario.ownerQuota Q) A H reg (target,flags))).expect (fun _ =>
          if targetTypicalWeight (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
            (Q.marksLaw H.1) (Q.marksLaw H.2)) b target flags≠1 then (1:ℝ) else 0) := by
      apply Hybrid.expect_congr_on_support
      intro AB hAB
      simp only [f,output_weight Q A H B R Rp width b reg target flags AB hAB]
    _ = _ := by
      convert! FiniteLaw.expect_const _ _ using 1
      split_ifs <;> rfl

theorem draw_weight_failure_le_full_flags
    {K : ℕ} (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B R Rp width : ℝ) (b : Fin A→ℝ)
    (active : Fin K→ Bool) (e : Fin A≃OriginalFlagCompression.Active active)
    (p : Bool→ Fin K→ unitInterval)
    (hp : ∀ reg j,sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b j=(p reg (e j).val:ℝ))
    (bad : Bool→ Set (Fin K→ unitInterval)) (hbad : ∀ reg,MeasurableSet (bad reg))
    (hgood : ∀ reg u,u∉bad reg → 0< A ∧ ∀ target : Fin A,
      targetTypicalWeight
        (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
          (Q.marksLaw H.1) (Q.marksLaw H.2)) b target
        (OriginalFlagCompression.compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))=1) :
    (volume : Measure unitInterval).real {u | weight Q A H B R Rp width b (draw Q A (b,H) u).1≠1}≤
      (1-Q.θ)*(Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))).real (bad false)+
        Q.θ*(Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))).real (bad true) := by
  let Z := Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))
  haveI : IsProbabilityMeasure Z := by dsimp [Z];infer_instance
  by_cases hA : 0< A
  · letI : Nonempty (Fin A) := ⟨⟨0,hA⟩⟩
    rw [draw_weight_failure Q A hA H B R Rp width b]
    have hreg (reg : Bool) :
        (Hybrid.rankLaw b).expect (fun target =>
          (independentFlagLaw (sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b)
            (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).prob (fun flags =>
              targetTypicalWeight (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
                (Q.marksLaw H.1) (Q.marksLaw H.2)) b target flags≠1))≤ Z.real (bad reg) := by
      apply FiniteLaw.expect_le_const_of_support
      intro target _
      let f : (Fin A→ Bool)→ℝ := fun flags => if
        targetTypicalWeight (TypicalGuardStatistics.phi A H.1 H.2 Q.c Q.ξ B R Rp width reg
          (Q.marksLaw H.1) (Q.marksLaw H.2)) b target flags≠1 then 1 else 0
      have he : sourceFlagProb ((PublicScenario.e0 Q) reg) Q.B0 b=(fun j => (p reg (e j).val:ℝ)) := funext (hp reg)
      have hf := (measurable_of_countable (fun flags : Fin K→ Bool =>
        f (OriginalFlagCompression.compressedFlags active e flags))).comp
          (OriginalFlagMeasure.measurable_flags (p reg))
      have hi : Integrable (fun u => f (OriginalFlagCompression.compressedFlags active e
          (OriginalFlagMeasure.flags (p reg) u))) Z :=
        Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun u => by
          dsimp only [f];split_ifs <;> norm_num)
      have hiB : Integrable (fun u : Fin K→ unitInterval => if u∈bad reg then (1:ℝ) else 0) Z :=
        Integrable.of_bound (Measurable.ite (hbad reg) measurable_const measurable_const).aestronglyMeasurable 1
          (ae_of_all _ fun u => by split_ifs <;> norm_num)
      have hpoint (u : Fin K→ unitInterval) :
          f (OriginalFlagCompression.compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))≤
            (if u∈bad reg then (1:ℝ) else 0) := by
        by_cases hu : u∈bad reg
        · simp only [if_pos hu,f];split_ifs <;> norm_num
        · simp only [f,(hgood reg u hu).2 target,ne_eq,not_true_eq_false,if_false,if_neg hu]
          exact le_rfl
      rw [FiniteLaw.prob_eq_expect]
      change (independentFlagLaw _ _ _).expect f≤_
      simp only [he]
      rw [OriginalFlagMeasure.flag_expect_compression active e (p reg) f]
      have hflag := OriginalFlagMeasure.flag_expect (p reg)
        (fun z => f (OriginalFlagCompression.compressedFlags active e z))
      have htransport : (independentFlagLaw (fun i => (p reg i:ℝ))
          (fun i => (p reg i).2.1) (fun i => (p reg i).2.2)).expect
          (fun z => f (OriginalFlagCompression.compressedFlags active e z)) =
            ∫ u : Fin K → unitInterval,
              f (OriginalFlagCompression.compressedFlags active e (OriginalFlagMeasure.flags (p reg) u)) ∂Z := by
        convert! hflag using 1
        congr 2 <;> exact Subsingleton.elim _ _
      rw [htransport]
      calc
        _ ≤ ∫ u : Fin K→ unitInterval,if u∈bad reg then (1:ℝ) else 0 ∂Z :=
          integral_mono_ae hi hiB (ae_of_all _ hpoint)
        _ = _ := by
          simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=Z) (hbad reg)
    have hh := FiniteLaw.expect_mono (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) hreg
    simpa only [IndependentCounts.expect_bernoulli,Z] using hh
  · have hB (reg : Bool) : bad reg=univ := by
      ext u
      simp only [mem_univ,iff_true]
      by_contra hu
      exact hA (hgood reg u hu).1
    simp only [hB,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] at ⊢
    have hle : (volume : Measure unitInterval).real
        {u | weight Q A H B R Rp width b (draw Q A (b,H) u).1≠1}≤1 :=
      (measureReal_mono (subset_univ _)).trans_eq (by simp [measureReal_def])
    calc
      _ ≤ 1 := hle
      _ = _ := by ring

end FCAppendix.Affine.Tail04.PublicWeightLaw
