import FCAppendix.Affine.Tail04.UnusedEmpiricalGuard
import FCAppendix.Affine.Tail04.NativeUnusedExperiment
import FCAppendix.Affine.Tail04.NativeCountGuards

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedPublicLaw
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open NativeTypicalCount NativeLocalPolicy NativeUnusedExperiment
open OriginalFlagCompression UnusedEmpiricalGuard
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

def Safe (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ : ℝ) (b : Fin A→ℝ) (s : Scenario A) : Prop :=
  FocalInsertion.Guard A H.1 H.2 Q.c Q.ξ B R Rp (regime s)
    (mixed s) (owner0 s) (owner1 s) b (Q.marksLaw H.1) (Q.marksLaw H.2) ∧
  PublicWeightLaw.weight Q A H B R Rp width b s=1 ∧
  γ≤ TypicalGuard.margin A H.1 H.2 Q.c Q.ξ B0 R Rp (regime s)
    (mixed s) (owner0 s) (owner1 s) b (Q.marksLaw H.1) (Q.marksLaw H.2)

theorem scenario_expect (Q : PublicScenario.Data) (A : ℕ) (hA : 0< A)
    (H : ℕ×ℕ) (b : Fin A→ℝ) (f : Scenario A→ℝ) :
    letI : Nonempty (Fin A):=⟨⟨0,hA⟩⟩
    (scenarioLaw Q A H b).expect f=
      (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one).expect (fun reg =>
        (Hybrid.rankLaw b).expect (fun target =>
          (independentFlagLaw (sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b)
            (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).expect (fun flags =>
              (Hybrid.ownerDivision (forcedExclusiveSet target flags)
                (PublicScenario.ownerQuota Q A H reg (target,flags))).expect
                  (fun AB => f (outputScenario reg ((target,flags),AB)))))) := by
  letI : Nonempty (Fin A):=⟨⟨0,hA⟩⟩
  rw [scenarioLaw,dif_pos hA,FiniteLaw.expect_map,latentLaw_expect]

theorem scenario_probability_le_full_flags {K : ℕ}
    (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (b : Fin A→ℝ)
    (active : Fin K→ Bool) (e : Fin A≃Active active)
    (p : Bool→ Fin K→ unitInterval)
    (hp : ∀ reg j,sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b j=(p reg (e j).val:ℝ))
    (good : Scenario A→ Prop) (bad : Bool→ Set (Fin K→ unitInterval))
    (hbad : ∀ reg,MeasurableSet (bad reg))
    (hpositive : ∀ reg u,u∉bad reg → 0< A)
    (hgood : ∀ reg u,u∉bad reg → ∀ target : Fin A,
      ∀ AB : Finset (Fin A)×Finset (Fin A),
      (Hybrid.ownerDivision
        (forcedExclusiveSet target (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u)))
        (PublicScenario.ownerQuota Q A H reg (target,compressedFlags active e
          (OriginalFlagMeasure.flags (p reg) u)))).mass AB≠0 →
      good (outputScenario reg ((target,compressedFlags active e
        (OriginalFlagMeasure.flags (p reg) u)),AB))) :
    (scenarioLaw Q A H b).prob (fun s => ¬good s)≤
      (1-Q.θ)*(Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))).real (bad false)+
        Q.θ*(Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))).real (bad true) := by
  let Z:=Measure.pi (fun _ : Fin K => (volume : Measure unitInterval))
  haveI : IsProbabilityMeasure Z := by dsimp [Z];infer_instance
  by_cases hA : 0< A
  · letI : Nonempty (Fin A):=⟨⟨0,hA⟩⟩
    rw [FiniteLaw.prob_eq_expect,scenario_expect Q A hA H b]
    have hr (reg : Bool) :
        (Hybrid.rankLaw b).expect (fun target =>
          (independentFlagLaw (sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b)
            (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).expect (fun flags =>
              (Hybrid.ownerDivision (forcedExclusiveSet target flags)
                (PublicScenario.ownerQuota Q A H reg (target,flags))).expect
                  (fun AB => if ¬good (outputScenario reg ((target,flags),AB)) then (1:ℝ) else 0)))≤
      Z.real (bad reg) := by
      apply FiniteLaw.expect_le_const_of_support
      intro target _
      let f : (Fin A→ Bool)→ℝ:=fun flags =>
        (Hybrid.ownerDivision (forcedExclusiveSet target flags)
          (PublicScenario.ownerQuota Q A H reg (target,flags))).expect
            (fun AB => if ¬good (outputScenario reg ((target,flags),AB)) then 1 else 0)
      have hf01 (flags : Fin A→ Bool) : f flags∈Icc (0:ℝ) 1 := by
        constructor
        · apply FiniteLaw.expect_nonneg;intro AB;split_ifs <;> norm_num
        · apply FiniteLaw.expect_le_const_of_support;intro AB _;split_ifs <;> norm_num
      have he : sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 b=(fun j => (p reg (e j).val:ℝ)) := funext (hp reg)
      have hf:=((measurable_of_countable (fun flags : Fin K→ Bool => f (compressedFlags active e flags))).comp
        (OriginalFlagMeasure.measurable_flags (p reg)))
      have hi : Integrable (fun u => f (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))) Z :=
        Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun u => by
          rw [Real.norm_eq_abs,abs_of_nonneg (hf01 _).1];exact (hf01 _).2)
      have hiB : Integrable (fun u : Fin K→ unitInterval => if u∈bad reg then (1:ℝ) else 0) Z :=
        Integrable.of_bound (Measurable.ite (hbad reg) measurable_const measurable_const).aestronglyMeasurable 1
          (ae_of_all _ fun u => by split_ifs <;> norm_num)
      have hpoint (u : Fin K→ unitInterval) :
          f (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u))≤
            (if u∈bad reg then (1:ℝ) else 0) := by
        by_cases hu : u∈bad reg
        · rw [if_pos hu];exact (hf01 _).2
        · rw [if_neg hu]
          apply FiniteLaw.expect_le_const_of_support
          intro AB hAB
          have hh:=hgood reg u hu target AB hAB
          simp only [hh,not_true_eq_false,if_false]
          exact le_rfl
      change (independentFlagLaw _ _ _).expect f≤_
      calc
        _=(∫ u : Fin K→unitInterval,
            f (compressedFlags active e (OriginalFlagMeasure.flags (p reg) u)) ∂Z) := by
          simpa only [he,Z] using!
            (@OriginalFlagMeasure.flag_expect_compression (Fin K) (Fin.fintype K)
              (fun a b => Classical.propDecidable (a=b)) active A e (p reg) f).trans
              (OriginalFlagMeasure.flag_expect (p reg) (fun z => f (compressedFlags active e z)))
        _≤∫ u : Fin K→ unitInterval,if u∈bad reg then (1:ℝ) else 0 ∂Z :=
          integral_mono_ae hi hiB (ae_of_all _ hpoint)
        _=_ := by simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=Z) (hbad reg)
    have hh:=FiniteLaw.expect_mono (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) hr
    simpa only [IndependentCounts.expect_bernoulli] using hh
  · have hb (reg : Bool) : bad reg=univ := by
      ext u
      simp only [mem_univ,iff_true]
      by_contra hu
      exact hA (hpositive reg u hu)
    simp only [hb,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one]
    have hh:=(scenarioLaw Q A H b).prob_le_one (fun s => ¬good s)
    linarith

section Native
variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c)
  (H0 H1 : Fin (m+1)) (Q : PublicScenario.Data)
  (hc : Q.c=c) (hξ : Q.ξ=K.ξ)
  (hν0 : Q.marksLaw H0.val=K.marksLaw H0) (hν1 : Q.marksLaw H1.val=K.marksLaw H1)

include hc hξ hν0 hν1 in
theorem native_use_failure (B0 γ : ℝ) (b : Fin A→ Icc (1:ℝ) K.E.U) :
    (volume : Measure unitInterval).real {u | ¬Good K H0 H1 Q b u}≤
      (scenarioLaw Q A (H0.val,H1.val) (TypicalGuard.bids (SortedAllNoise.sortedBox b))).prob
        (fun s => ¬Safe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ
          (TypicalGuard.bids (SortedAllNoise.sortedBox b)) s) := by
  let br:=TypicalGuard.bids (SortedAllNoise.sortedBox b)
  let S : Scenario A→ Prop:=Safe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ br
  let bad : Set unitInterval:={u | ¬S (draw Q A (br,(H0.val,H1.val)) u).1}
  let edge : Set unitInterval:={u | (PublicScenario.split u).2=(1:unitInterval)}
  have hsub : {u : unitInterval | ¬Good K H0 H1 Q b u}⊆bad∪edge := by
    intro u hu
    by_cases hb : u∈bad
    · exact Or.inl hb
    by_cases he : u∈edge
    · exact Or.inr he
    exfalso
    apply hu
    have hs : S (draw Q A (br,(H0.val,H1.val)) u).1 := not_not.mp hb
    have hlt : ((PublicScenario.split u).2:ℝ)<1 :=
      lt_of_le_of_ne ((PublicScenario.split u).2).2.2 (fun hz => he (Subtype.ext hz))
    refine ⟨?_,?_⟩
    · change ((PublicScenario.split u).2:ℝ)<_
      have hw:=hs.2.1
      simpa only [PublicWeightLaw.weight,hc,hξ,hν0,hν1,
        JoinedHighPolicy.publicWeight,NativeUnusedExperiment.parameter,
        PartialNativePublicWeight.drawnParameter,JoinedHighPolicy.publicBids,br] using! hlt.trans_le (le_of_eq hw.symm)
    · simpa only [Safe,FocalInsertion.PublicGuard,NativeUnusedExperiment.parameter,
        PartialNativePublicWeight.drawnParameter,hc,hξ,hν0,hν1,JoinedHighPolicy.publicBids,br] using! hs.1
  have hsam:=FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    (volume : Measure unitInterval) (fun u => (draw Q A (br,(H0.val,H1.val)) u).1)
    (PublicWeightLaw.measurable_drawScenario Q A (H0.val,H1.val) br)
    (scenarioLaw Q A (H0.val,H1.val) br)
    (PublicWeightLaw.drawScenario_law Q A (H0.val,H1.val) br)
  have hprob : (volume : Measure unitInterval).real bad=
      (scenarioLaw Q A (H0.val,H1.val) br).prob (fun s => ¬S s) := by
    rw [←hsam,NativeCountGuards.prob_ofMeasure]
  have hedge : (volume : Measure unitInterval).real edge=0 := by
    rw [measureReal_def,PartialNativeSeed.branch_endpoint_null,ENNReal.toReal_zero]
  have hh:=(measureReal_mono (μ:=(volume : Measure unitInterval)) hsub).trans (measureReal_union_le _ _)
  rw [hprob,hedge,add_zero] at hh
  exact hh

end Native
end FCAppendix.Affine.Tail04.UnusedPublicLaw
