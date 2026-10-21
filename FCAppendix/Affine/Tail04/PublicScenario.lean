import FCAppendix.Affine.Tail04.OriginalOwnerCount
import FCAppendix.Affine.Tail04.LocalCoordinates
import FCAppendix.Affine.Tail04.NativeFlagTransport
import FCAppendix.Affine.Hybrid.ObservedSeed
import FCAppendix.Affine.Tail04.HierarchicalFiniteSampler

noncomputable section
namespace FCAppendix.Affine.Tail04.PublicScenario
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open EqualPrivateSignal JoinedHighPolicy NativeTypicalCount
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

structure Data where
  c : ℕ
  ξ : ℝ
  θ : ℝ
  eA : ℝ
  eR : ℝ
  B0 : ℝ
  θ_nonneg : 0 ≤ θ
  θ_le_one : θ ≤ 1
  marksLaw : ∀ H : ℕ, FiniteLaw (Marks H)

abbrev OwnerOutput (N : ℕ) :=
  ((Fin N × (Fin N → Bool)) × (Finset (Fin N) × Finset (Fin N)))

def e0 (P : Data) (reg : Bool) : ℝ := if reg then P.eR else P.eA

def outputScenario {N : ℕ} (reg : Bool) (out : OwnerOutput N) : Scenario N :=
  (reg,(targetMixedSet out.1.1 out.1.2,out.2))

def fallback (N : ℕ) : Scenario N := (false,(∅,(Finset.univ,∅)))

def ownerQuota (P : Data) (N : ℕ) (H : ℕ × ℕ) (reg : Bool)
    (z : Fin N × (Fin N → Bool)) : ℕ :=
  (countParameters N H.1 H.2 P.c P.ξ reg
    (P.marksLaw H.1) (P.marksLaw H.2)).owner0
      (targetMixedSet z.1 z.2).card

lemma ownerQuota_le (P : Data) (N : ℕ) (H : ℕ × ℕ) (reg : Bool)
    (z : Fin N × (Fin N → Bool)) :
    ownerQuota P N H reg z ≤ (forcedExclusiveSet z.1 z.2).card := by
  rw [OriginalOwnerCount.exclusive_card]
  exact (countParameters N H.1 H.2 P.c P.ξ reg
    (P.marksLaw H.1) (P.marksLaw H.2)).owner0_le _

def latentLaw (P : Data) (N : ℕ) [Nonempty (Fin N)] (H : ℕ × ℕ)
    (b : Fin N → ℝ) : FiniteLaw (Bool × OwnerOutput N) :=
  FiniteLaw.finiteMix (IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
    (fun reg => (integerOwnerPlanLaw b (sourceFlagProb (e0 P reg) P.B0 b)
      (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)
      (ownerQuota P N H reg)).map (fun out => (reg,out)))

def scenarioLaw (P : Data) (N : ℕ) (H : ℕ × ℕ)
    (b : Fin N → ℝ) : FiniteLaw (Scenario N) :=
  if hn : 0 < N then
    letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
    (latentLaw P N H b).map (fun z => outputScenario z.1 z.2)
  else FiniteLaw.dirac (fallback N)

lemma latentLaw_expect (P : Data) (N : ℕ) [Nonempty (Fin N)] (H : ℕ × ℕ)
    (b : Fin N → ℝ) (f : Bool × OwnerOutput N → ℝ) :
    (latentLaw P N H b).expect f =
      (IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one).expect (fun reg =>
        (Hybrid.rankLaw b).expect (fun target =>
          (independentFlagLaw (sourceFlagProb (e0 P reg) P.B0 b)
            (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)).expect (fun flags =>
              (Hybrid.ownerDivision (forcedExclusiveSet target flags)
                (ownerQuota P N H reg (target,flags))).expect
                  (fun AB => f (reg,((target,flags),AB)))))) := by
  rw [latentLaw,FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro reg
  rw [FiniteLaw.expect_map,integerOwnerPlanLaw_expect]

lemma measurable_scenarioLaw_mass_fixed (P : Data) (N : ℕ) (H : ℕ × ℕ)
    (out : Scenario N) :
    Measurable (fun b : Fin N → ℝ => (scenarioLaw P N H b).mass out) := by
  classical
  by_cases hn : 0 < N
  · letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
    have hm (reg : Bool) (z : OwnerOutput N) : Measurable (fun b : Fin N → ℝ =>
        (integerOwnerPlanLaw b (sourceFlagProb (e0 P reg) P.B0 b)
          (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)
          (ownerQuota P N H reg)).mass z) :=
      measurable_integerOwnerPlanLaw_mass _ _ _
        (fun i => (continuous_sourceFlagProb (e0 P reg) P.B0 i).measurable)
        (fun _ => ownerQuota P N H reg) (fun _ => measurable_const) z
    simp only [scenarioLaw,dif_pos hn,latentLaw,FiniteLaw.map,
      FiniteLaw.finiteMix,FiniteLaw.expect]
    apply Finset.measurable_sum
    intro z _
    split_ifs
    · apply Finset.measurable_sum
      intro reg _
      apply Measurable.mul measurable_const
      apply Finset.measurable_sum
      intro v _
      split_ifs
      · exact hm reg v
      · exact measurable_const
    · exact measurable_const
  · simp only [scenarioLaw,dif_neg hn]
    exact measurable_const

lemma measurable_scenarioLaw_mass (P : Data) (N : ℕ) (out : Scenario N) :
    Measurable (fun z : (Fin N → ℝ) × (ℕ × ℕ) =>
      (scenarioLaw P N z.2 z.1).mass out) := by
  exact measurable_from_prod_countable_left
    (fun H => measurable_scenarioLaw_mass_fixed P N H out)

private theorem exists_split :
    ∃ f : unitInterval → unitInterval × unitInterval, Measurable f ∧
      volume.map f=(volume : Measure unitInterval).prod volume :=
  Measure.exists_measurable_map_eq _

def split : unitInterval → unitInterval × unitInterval := Classical.choose exists_split

lemma measurable_split : Measurable split := (Classical.choose_spec exists_split).1
lemma split_law : volume.map split=(volume : Measure unitInterval).prod volume :=
  (Classical.choose_spec exists_split).2

def regimeSample (P : Data) : unitInterval → Bool :=
  Classical.choose (Hybrid.exists_support_sampler
    (fun _ : Unit => IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
    (fun _ => measurable_const)) ()

lemma measurable_regimeSample (P : Data) : Measurable (regimeSample P) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun _ : Unit => IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
    (fun _ => measurable_const))).1.comp (measurable_const.prodMk measurable_id)

lemma regimeSample_support (P : Data) (u : unitInterval) :
    0<(IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one).mass (regimeSample P u) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun _ : Unit => IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
    (fun _ => measurable_const))).2.1 () u

lemma regimeSample_law (P : Data) : volume.map (regimeSample P)=
    FiniteLaw.probabilityMeasure (IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun _ : Unit => IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
    (fun _ => measurable_const))).2.2 ()

def conditionalScenarioLaw (P : Data) (N : ℕ) (H : ℕ×ℕ)
    (b : Fin N → ℝ) (reg : Bool) : FiniteLaw (Scenario N) :=
  if hn : 0< N then
    letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
    (integerOwnerPlanLaw b (sourceFlagProb (e0 P reg) P.B0 b)
      (sourceFlagProb_nonneg _ _ b) (sourceFlagProb_le_one _ _ b)
      (ownerQuota P N H reg)).map (outputScenario reg)
  else FiniteLaw.dirac (fallback N)

lemma scenarioLaw_conditional (P : Data) (N : ℕ) (hn : 0< N)
    (H : ℕ×ℕ) (b : Fin N → ℝ) :
    scenarioLaw P N H b=FiniteLaw.finiteMix
      (IndependentCounts.bernoulli P.θ P.θ_nonneg P.θ_le_one)
      (conditionalScenarioLaw P N H b) := by
  letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
  apply FiniteLaw.ext_expect
  intro f
  simp only [scenarioLaw,conditionalScenarioLaw,dif_pos hn,latentLaw,
    FiniteLaw.expect_map,FiniteLaw.expect_finiteMix]

set_option maxHeartbeats 600000 in
lemma measurable_conditionalScenarioLaw_mass (P : Data) (N : ℕ) (out : Scenario N) :
    Measurable (fun z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool =>
      (conditionalScenarioLaw P N z.1.2 z.1.1 z.2).mass out) := by
  have hm (H : (ℕ×ℕ)×Bool) : Measurable (fun b : Fin N → ℝ =>
      (conditionalScenarioLaw P N H.1 b H.2).mass out) := by
    by_cases hn : 0< N
    · letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
      simp only [conditionalScenarioLaw,dif_pos hn,FiniteLaw.map]
      apply Finset.measurable_sum
      intro v _
      split_ifs
      · exact measurable_integerOwnerPlanLaw_mass _ _ _
          (fun i => (continuous_sourceFlagProb (e0 P H.2) P.B0 i).measurable)
          (fun _ => ownerQuota P N H.1 H.2) (fun _ => measurable_const) v
      · exact measurable_const
    · simp only [conditionalScenarioLaw,dif_neg hn]
      exact measurable_const
  have h : Measurable (fun z : ((ℕ×ℕ)×Bool) × (Fin N → ℝ) =>
      (conditionalScenarioLaw P N z.1.1 z.2 z.1.2).mass out) :=
    measurable_from_prod_countable_right hm
  have hi : Measurable (fun z : ((Fin N → ℝ) × (ℕ×ℕ)) × Bool =>
      ((z.1.2,z.2),z.1.1)) :=
    (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have hc := h.comp hi
  simpa only [Function.comp_def] using hc

def conditionalSample (P : Data) (N : ℕ) :
    (((Fin N → ℝ)×(ℕ×ℕ))×Bool) → unitInterval → Scenario N :=
  Classical.choose (Hybrid.exists_support_sampler
    (fun z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool => conditionalScenarioLaw P N z.1.2 z.1.1 z.2)
    (measurable_conditionalScenarioLaw_mass P N))

lemma measurable_conditionalSample (P : Data) (N : ℕ) :
    Measurable (Function.uncurry (conditionalSample P N)) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool => conditionalScenarioLaw P N z.1.2 z.1.1 z.2)
    (measurable_conditionalScenarioLaw_mass P N))).1

lemma conditionalSample_support (P : Data) (N : ℕ)
    (z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool) (u : unitInterval) :
    0<(conditionalScenarioLaw P N z.1.2 z.1.1 z.2).mass (conditionalSample P N z u) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool => conditionalScenarioLaw P N z.1.2 z.1.1 z.2)
    (measurable_conditionalScenarioLaw_mass P N))).2.1 z u

lemma conditionalSample_law (P : Data) (N : ℕ) (z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool) :
    volume.map (conditionalSample P N z)=
      FiniteLaw.probabilityMeasure (conditionalScenarioLaw P N z.1.2 z.1.1 z.2) :=
  (Classical.choose_spec (Hybrid.exists_support_sampler
    (fun z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool => conditionalScenarioLaw P N z.1.2 z.1.1 z.2)
    (measurable_conditionalScenarioLaw_mass P N))).2.2 z

lemma conditionalSample_regime (P : Data) (N : ℕ) (hn : 0< N)
    (z : ((Fin N → ℝ)×(ℕ×ℕ))×Bool) (u : unitInterval) :
    (conditionalSample P N z u).1=z.2 := by
  letI : Nonempty (Fin N) := ⟨⟨0,hn⟩⟩
  have h := conditionalSample_support P N z u
  rw [conditionalScenarioLaw,dif_pos hn] at h
  obtain ⟨v,hv,_⟩ := HierarchicalFiniteSampler.map_support _ _ h
  exact (congrArg Prod.fst hv).symm

def sample (P : Data) (N : ℕ) (z : (Fin N → ℝ)×(ℕ×ℕ))
    (u : unitInterval) : Scenario N :=
  if 0< N then conditionalSample P N (z,regimeSample P (split u).1) (split u).2
  else fallback N

lemma measurable_sample (P : Data) (N : ℕ) :
    Measurable (Function.uncurry (sample P N)) := by
  unfold sample
  split_ifs
  · exact (measurable_conditionalSample P N).comp
      ((measurable_fst.prodMk ((measurable_regimeSample P).comp
        (measurable_split.fst.comp measurable_snd))).prodMk
        (measurable_split.snd.comp measurable_snd))
  · exact measurable_const

lemma sample_support (P : Data) (N : ℕ) (z : (Fin N → ℝ)×(ℕ×ℕ))
    (u : unitInterval) : 0<(scenarioLaw P N z.2 z.1).mass (sample P N z u) := by
  by_cases hn : 0< N
  · rw [scenarioLaw_conditional P N hn,sample,if_pos hn]
    exact (mul_pos (regimeSample_support P (split u).1)
      (conditionalSample_support P N (z,regimeSample P (split u).1) (split u).2)).trans_le
        (HierarchicalFiniteSampler.mass_mul_le_finiteMix _ _ _ _)
  · simp [scenarioLaw,sample,hn,fallback,FiniteLaw.dirac]

lemma sample_law (P : Data) (N : ℕ) (z : (Fin N → ℝ)×(ℕ×ℕ)) :
    volume.map (sample P N z)=FiniteLaw.probabilityMeasure (scenarioLaw P N z.2 z.1) := by
  by_cases hn : 0< N
  · have hm : Measurable (fun q : Bool×unitInterval => conditionalSample P N (z,q.1) q.2) :=
      (measurable_conditionalSample P N).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hf : Measurable (fun q : unitInterval×unitInterval =>
        conditionalSample P N (z,regimeSample P q.1) q.2) :=
      hm.comp (((measurable_regimeSample P).comp measurable_fst).prodMk measurable_snd)
    have he : sample P N z=(fun q : unitInterval×unitInterval =>
        conditionalSample P N (z,regimeSample P q.1) q.2) ∘ split := by
      funext u
      simp only [sample,if_pos hn,Function.comp_apply]
    rw [he,←Measure.map_map hf measurable_split,split_law,
      scenarioLaw_conditional P N hn]
    exact HierarchicalFiniteSampler.product_law _ _ (regimeSample P)
      (measurable_regimeSample P) (regimeSample_law P)
      (fun reg => conditionalSample P N (z,reg)) hm
      (fun reg => conditionalSample_law P N (z,reg))
  · have he : sample P N z = (fun _ : unitInterval => fallback N) := by
      funext u
      exact if_neg hn
    rw [he,Measure.map_const]
    simp only [scenarioLaw,dif_neg hn,FiniteLaw.probabilityMeasure,FiniteLaw.dirac]
    simp_rw [apply_ite ENNReal.ofReal]
    simp

lemma sample_regime (P : Data) (N : ℕ) (z : (Fin N → ℝ)×(ℕ×ℕ)) (u : unitInterval) :
    (sample P N z u).1=if 0< N then regimeSample P (split u).1 else false := by
  by_cases hn : 0< N
  · simp only [sample,if_pos hn,conditionalSample_regime P N hn]
  · simp only [sample,if_neg hn,fallback]

def draw (P : Data) (N : ℕ) (z : (Fin N → ℝ) × (ℕ × ℕ))
    (u : unitInterval) : Scenario N × unitInterval :=
  (sample P N z (split u).1,(split u).2)

lemma measurable_draw (P : Data) (N : ℕ) :
    Measurable (Function.uncurry (draw P N)) :=
  ((measurable_sample P N).comp (measurable_fst.prodMk
    (measurable_split.fst.comp measurable_snd))).prodMk
      (measurable_split.snd.comp measurable_snd)

lemma draw_law (P : Data) (N : ℕ) (z : (Fin N → ℝ) × (ℕ × ℕ)) :
    volume.map (draw P N z)=
      (FiniteLaw.probabilityMeasure (scenarioLaw P N z.2 z.1)).prod volume := by
  have hs : Measurable (sample P N z) :=
    (measurable_sample P N).comp (measurable_const.prodMk measurable_id)
  change volume.map ((Prod.map (sample P N z) id) ∘ split)=_
  rw [← Measure.map_map (hs.prodMap measurable_id) measurable_split,split_law,
    ← Measure.map_prod_map _ _ hs measurable_id,sample_law,Measure.map_id]

theorem draw_regime_independent_counts (P : Data) (N : ℕ)
    (b b' : Fin N → ℝ) (H H' : ℕ×ℕ) (u : unitInterval) :
    (draw P N (b,H) u).1.1=(draw P N (b',H') u).1.1 := by
  simp only [draw,sample_regime]

theorem draw_branch_independent_counts (P : Data) (N : ℕ)
    (b b' : Fin N → ℝ) (H H' : ℕ×ℕ) (u : unitInterval) :
    (draw P N (b,H) u).2=(draw P N (b',H') u).2 := rfl

def localChoice (E : Observable.Regions) (P : Data) (μL : Measure ℝ) (N : ℕ)
    {m : ℕ} (z : LocalList m × (TypicalGuard.BidBox N E.U × (ℕ × ℕ))) :
    Scenario N × unitInterval :=
  match Hybrid.seedOnList μL z.1 with
  | none => (fallback N,1)
  | some u => draw P N (TypicalGuard.bids z.2.1,z.2.2) u

lemma measurable_localChoice (E : Observable.Regions) (P : Data) (μL : Measure ℝ)
    (N m : ℕ) : Measurable (localChoice E P μL N (m:=m)) := by
  have hsome : Measurable (fun u : Option unitInterval => u.isSome) := by
    intro S hS
    change MeasurableSet ((fun _ : unitInterval => true) ⁻¹' S)
    exact measurable_const hS
  have hget : Measurable (fun u : Option unitInterval => u.getD 1) := by
    intro S hS
    change MeasurableSet S
    exact hS
  have ho : Measurable (fun z :
      ((Fin N → ℝ) × (ℕ × ℕ)) × Option unitInterval =>
      match z.2 with
      | none => (fallback N,(1:unitInterval))
      | some u => draw P N z.1 u) := by
    have he : (fun z : ((Fin N → ℝ) × (ℕ × ℕ)) × Option unitInterval =>
        match z.2 with
        | none => (fallback N,(1:unitInterval))
        | some u => draw P N z.1 u) =
        (fun z => if z.2.isSome=true then draw P N z.1 (z.2.getD 1)
          else (fallback N,1)) := by
      funext z
      cases z.2 <;> rfl
    rw [he]
    exact Measurable.ite
      (measurableSet_eq_fun (hsome.comp measurable_snd) measurable_const)
      ((measurable_draw P N).comp (measurable_fst.prodMk (hget.comp measurable_snd)))
      measurable_const
  exact ho.comp
    (((TypicalGuard.continuous_bids.measurable.comp measurable_snd.fst).prodMk
      measurable_snd.snd).prodMk ((Hybrid.measurable_seedOnList μL).comp measurable_fst))

lemma localChoice_of_seed (E : Observable.Regions) (P : Data) (μL : Measure ℝ)
    (N : ℕ) {m : ℕ} (L : LocalList m) (b : TypicalGuard.BidBox N E.U)
    (H : ℕ × ℕ) (u : unitInterval) (hu : Hybrid.seedOnList μL L=some u) :
    localChoice E P μL N (L,(b,H))=draw P N (TypicalGuard.bids b,H) u := by
  simp only [localChoice,hu]

lemma localChoice_empty (E : Observable.Regions) (P : Data) (μL : Measure ℝ)
    (N : ℕ) {m : ℕ} (b : TypicalGuard.BidBox N E.U) (H : ℕ × ℕ) :
    localChoice E P μL N ((fun _ : Fin m => none),(b,H))=(fallback N,1) := by
  have hs : Hybrid.seedOnList μL (fun _ : Fin m => none)=none := by
    simp only [Hybrid.seedOnList,Hybrid.localMinimum]
    have hn := (Hybrid.scanMinimum_none (List.finRange m) (fun _ : Fin m => none)).2
      (fun _ _ => rfl)
    rw [hn,Option.map_none]
  simp [localChoice,hs]

lemma flags_are_source (E : Observable.Regions) (P : Data) (N : ℕ)
    (hUB : E.U≤ P.B0) (hB : 1< P.B0)
    (hA0 : 0≤ P.eA) (hA1 : P.eA≤1) (hR0 : 0≤ P.eR) (hR1 : P.eR≤1)
    (reg : Bool) (b : TypicalGuard.BidBox N E.U) (i : Fin N) :
    sourceFlagProb (e0 P reg) P.B0 (TypicalGuard.bids b) i=
      e0 P reg*((P.B0-(b i).1)/(P.B0-1))^2 := by
  have he0 : 0≤ e0 P reg := by cases reg <;> simp [e0,hA0,hR0]
  have he1 : e0 P reg≤1 := by cases reg <;> simp [e0,hA1,hR1]
  exact sourceFlagProb_eq he0 he1 hB _ i ⟨(b i).2.1,(b i).2.2.trans hUB⟩

end FCAppendix.Affine.Tail04.PublicScenario
