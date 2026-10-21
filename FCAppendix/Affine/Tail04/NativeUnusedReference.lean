import FCAppendix.Affine.Tail04.UnusedFiniteCountError

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeUnusedReference
open MeasureTheory ProbabilityTheory Set Classical
open NativeLocalPolicy NativeHighExperiment NativeUnusedExperiment
open PublicScenario EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy
open MenuError UnusedPublicLaw UnusedPublicPrices UnusedFiniteCountError
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c A : ℕ} (K : NativeLocalPolicy.Data m c) (H0 H1 : Fin (m+1))
  (Q : PublicScenario.Data) (hc : Q.c=c) (hξ : Q.ξ=K.ξ)
  (hν0 : Q.marksLaw H0.val=K.marksLaw H0) (hν1 : Q.marksLaw H1.val=K.marksLaw H1)
  (ρ : ProbabilityMeasure (Ici K.E.H⊕Icc K.E.R K.E.Rp))
  (hrows : ∀H : Fin (m+1),K.originalPrivateRow H=PrivateRowSorting.sortedOriginalIid K.E H.val ρ)

def rowCount (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1))
    (outcome K H0 H1 Q b y) (measurable_outcome K H0 H1 Q b y)

local notation "br" => (fun b : Fin A→Icc (1:ℝ) K.E.U => TypicalGuard.bids (SortedAllNoise.sortedBox b))
local notation "scenarioAt" => (fun (b : Fin A→Icc (1:ℝ) K.E.U) (u : unitInterval) => Prod.fst (draw Q A (br b,(H0.val,H1.val)) u))

include hc hξ hν0 hν1 hrows in
lemma private_count_on_safe (B0 γ : ℝ) (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) (u : unitInterval)
    (hg : Safe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ (br b) (scenarioAt b u)) :
    FiniteLaw.ofMeasure (rawPayloadLaw K ρ H0 H1)
      (fun z=> outcome K H0 H1 Q b y (u,z))
      ((measurable_outcome K H0 H1 Q b y).comp (measurable_const.prodMk measurable_id))=
        scenarioCount Q A (H0.val,H1.val) (br b) y (scenarioAt b u) := by
  have hp : FocalInsertion.PublicGuard A H0.val H1.val c K.ξ K.E.U K.E.R K.E.Rp
      (K.marksLaw H0) (K.marksLaw H1) (parameter K H0 H1 Q b u) := by
    simpa only [FocalInsertion.PublicGuard,parameter,PartialNativePublicWeight.drawnParameter,
      publicBids,hc,hξ,hν0,hν1] using hg.1
  rw [private_count_on_guard K H0 H1 Q ρ hrows b y u hp]
  have hs:=hg.1.1
  have he0:=actual_price A H0.val Q.c Q.ξ (regime (scenarioAt b u))
    (owner0 (scenarioAt b u)) (mixed (scenarioAt b u)) (br b) (Q.marksLaw H0.val) hs.2.2.2.1
  have he1:=actual_price A H1.val Q.c Q.ξ (regime (scenarioAt b u))
    (owner1 (scenarioAt b u)) (mixed (scenarioAt b u)) (br b) (Q.marksLaw H1.val) hs.2.2.2.2.1
  unfold scenarioCount price0 price1
  simpa only [parameter,PartialNativePublicWeight.drawnParameter,publicBids,hc,hξ,hν0,hν1] using
    congrArg₂ (fun L0 L1=> UnusedFocalCountError.actualCount Q.ξ y
      (mixedReciprocalSum (mixed (scenarioAt b u)) (br b)) L0 L1) he0 he1

include hc hξ hν0 hν1 hrows in
theorem row_count_error (B0 γ a : ℝ) (b : Fin A→ Icc (1:ℝ) K.E.U) (y : ℝ) (f : Fin 3→ℝ) :
    |(rowCount K H0 H1 Q ρ b y).expect f-
      (publicCount Q A (H0.val,H1.val) (br b) y).expect f|≤
        2*MenuError.oscillation f*(scenarioLaw Q A (H0.val,H1.val) (br b)).prob
          (fun s=>¬StrongSafe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a (br b) s) := by
  let B : Set unitInterval:={u | ¬StrongSafe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a (br b) (scenarioAt b u)}
  let F : unitInterval→ℝ:=fun u=>∫z,f (outcome K H0 H1 Q b y (u,z)) ∂rawPayloadLaw K ρ H0 H1
  let G : unitInterval→ℝ:=fun u=>(scenarioCount Q A (H0.val,H1.val) (br b) y (scenarioAt b u)).expect f
  have hB : MeasurableSet B :=
    (Set.to_countable {s : Scenario A | ¬StrongSafe Q A (H0.val,H1.val)
      K.E.U B0 K.E.R K.E.Rp K.width γ a (br b) s}).measurableSet.preimage
        (PublicWeightLaw.measurable_drawScenario Q A (H0.val,H1.val) (br b))
  have hprod : Integrable (fun z=> f (outcome K H0 H1 Q b y z))
      ((volume:Measure unitInterval).prod (rawPayloadLaw K ρ H0 H1)) :=
    CountLaw.integrable_comp _ _ (measurable_outcome K H0 H1 Q b y) f
  have hFi : Integrable F (volume:Measure unitInterval) := hprod.integral_prod_left
  have hGm : Measurable G := (measurable_of_countable
    (fun s : Scenario A=>(scenarioCount Q A (H0.val,H1.val) (br b) y s).expect f)).comp
      (PublicWeightLaw.measurable_drawScenario Q A (H0.val,H1.val) (br b))
  have hGi : Integrable G (volume:Measure unitInterval) := Integrable.of_bound hGm.aestronglyMeasurable
    (∑k,‖f k‖) (ae_of_all _ fun u=> FiniteLaw.norm_expect_le_sum_norm _ f)
  have hBi : Integrable (fun u=> if u∈B then (1:ℝ) else 0) (volume:Measure unitInterval) :=
    Integrable.of_bound (Measurable.ite hB measurable_const measurable_const).aestronglyMeasurable 1
      (ae_of_all _ fun u=> by split_ifs <;> norm_num)
  have hpoint (u : unitInterval) : |F u-G u|≤2*MenuError.oscillation f*(if u∈B then 1 else 0) := by
    have hf:=FiniteLaw.expect_ofMeasure (rawPayloadLaw K ρ H0 H1)
      (fun z=> outcome K H0 H1 Q b y (u,z))
      ((measurable_outcome K H0 H1 Q b y).comp (measurable_const.prodMk measurable_id)) f
    by_cases hu : u∈B
    · rw [if_pos hu,mul_one]
      dsimp only [F,G]
      rw [←hf]
      exact count_expect_difference_bound _ _ f
    · have hs : Safe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ (br b) (scenarioAt b u) :=
        (not_not.mp hu).1
      have he:=private_count_on_safe K H0 H1 Q hc hξ hν0 hν1 ρ hrows B0 γ b y u hs
      have heF : F u=G u := by
        dsimp only [F,G]
        rw [←hf,he]
      rw [heF,sub_self,abs_zero,if_neg hu,mul_zero]
  have hsam:=FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (volume:Measure unitInterval)
    (fun u=>(draw Q A (br b,(H0.val,H1.val)) u).1)
    (PublicWeightLaw.measurable_drawScenario Q A (H0.val,H1.val) (br b))
    (scenarioLaw Q A (H0.val,H1.val) (br b))
    (PublicWeightLaw.drawScenario_law Q A (H0.val,H1.val) (br b))
  have hGe : ∫u,G u=(publicCount Q A (H0.val,H1.val) (br b) y).expect f := by
    rw [publicCount,FiniteLaw.expect_finiteMix,←hsam,FiniteLaw.expect_ofMeasure]
  have hBe : (volume:Measure unitInterval).real B=
      (scenarioLaw Q A (H0.val,H1.val) (br b)).prob
        (fun s=>¬StrongSafe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a (br b) s) := by
    rw [←hsam,NativeCountGuards.prob_ofMeasure]
  rw [rowCount,FiniteLaw.expect_ofMeasure,integral_prod _ hprod,←hGe,←integral_sub hFi hGi]
  calc
    |∫u,F u-G u|≤∫u,|F u-G u| := abs_integral_le_integral_abs
    _≤∫u,2*MenuError.oscillation f*(if u∈B then (1:ℝ) else 0) :=
      integral_mono_ae (hFi.sub hGi).abs (hBi.const_mul _) (ae_of_all _ hpoint)
    _=2*MenuError.oscillation f*(volume:Measure unitInterval).real B := by
      rw [integral_const_mul]
      congr 1
      simpa only [Set.indicator,Pi.one_apply] using integral_indicator_one (μ:=(volume:Measure unitInterval)) hB
    _=_ := by rw [hBe]

include hc hξ hν0 hν1 in
theorem native_failure (B0 γ a : ℝ) (b : Fin A→ Icc (1:ℝ) K.E.U) :
    (volume:Measure unitInterval).real {u|¬Good K H0 H1 Q b u}≤
      (scenarioLaw Q A (H0.val,H1.val) (br b)).prob
        (fun s=>¬StrongSafe Q A (H0.val,H1.val) K.E.U B0 K.E.R K.E.Rp K.width γ a (br b) s) := by
  apply (UnusedPublicLaw.native_use_failure K H0 H1 Q hc hξ hν0 hν1 B0 γ b).trans
  apply FiniteLaw.prob_mono
  intro s hs ht
  exact hs ht.1

end FCAppendix.Affine.Tail04.NativeUnusedReference
