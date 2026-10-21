import FCAppendix.Affine.Tail04.NativeCountCoordinates
import FCAppendix.Affine.Tail04.EqualPrivateCountPayoff
import FCAppendix.Affine.Tail04.UnequalOriginalCountPayoff
import FCAppendix.Affine.Tail04.PublicScenario
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSamplerCountLaw
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy
open NativeLocalPolicy NativeTypicalCount NativeCountCoordinates
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def pairLaw (H0 H1 : Fin (m+1)) :
    Measure ((Row H0.val D.E.R D.E.Rp D.E.H×unitInterval)×
      (Row H1.val D.E.R D.E.Rp D.E.H×unitInterval)) :=
  (((D.originalPrivateRow H0 : Measure _).prod volume).prod
    ((D.originalPrivateRow H1 : Measure _).prod volume))

instance pairLaw_probability (H0 H1 : Fin (m+1)) :
    IsProbabilityMeasure (pairLaw D H0 H1) := by unfold pairLaw;infer_instance

def samplerLaw (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) : CountLaw 2 :=
  originalIndependentCountLaw (D.zeroSampler N H0 H1) (D.oneSampler N H0 H1)
    (D.zeroSampler_measurable N H0 H1) (D.oneSampler_measurable N H0 H1)
    p (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) (Sum.inl i) (Sum.inl i)

theorem samplerLaw_equal (N : ℕ) (H : Fin (m+1))
    (p : Parameters N H.val D.E.R D.E.Rp D.E.U) (hp : p.2.1=D.signalLaw H) (i : Fin N) :
    samplerLaw D N H H p i=
      EqualPrivateCountPayoff.countLaw N H.val c D.E.R D.E.Rp D.ξ 1 D.E.U (equalParameter p) i := by
  have hθ : (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H)).map signal=WeakProbability.toMeasure p.2.1 := by
    rw [hp]
    exact D.signalLaw_exact H
  unfold samplerLaw
  simp only [D.zeroSampler_equal,D.oneSampler_equal]
  exact EqualPrivateCountPayoff.original_countLaw N H.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ (D.E.d_nonneg.trans D.E.d_lt_R.le)
    (D.E.Rp_lt_one.le.trans D.E.one_le_U) D.E.U_lt_H
    (((by norm_num : (0:ℝ)<1).trans_le D.E.one_le_U).trans D.E.U_lt_H)
    p (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H)) hθ hθ i

def sharedOutcome (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N)
    (z : unitInterval×((Row H0.val D.E.R D.E.Rp D.E.H×unitInterval)×
      (Row H1.val D.E.R D.E.Rp D.E.H×unitInterval))) : Fin 3 :=
  originalPairCount (D.zeroSampler N H0 H1) (D.oneSampler N H0 H1)
    (setCommonSeed p z.1) (Sum.inl i) (Sum.inl i) z.2

lemma sharedOutcome_equal (N : ℕ) (H : Fin (m+1))
    (p : Parameters N H.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    sharedOutcome D N H H p i=
      (originalPairCount (D.equalSampler N H) (D.equalSampler N H)
        p (Sum.inl i) (Sum.inl i)) ∘ Prod.snd := by
  funext z
  simp only [sharedOutcome,D.zeroSampler_equal,D.oneSampler_equal,
    originalPairCount,localAccept,Data.equalSampler,AllCountHighPolicy.equalSample,
    equalParameter,setCommonSeed,Function.comp_apply]
  rfl

lemma sharedOutcome_unequal (N : ℕ) (H0 H1 : Fin (m+1)) (hH : H0≠H1)
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    sharedOutcome D N H0 H1 p i=
      joinedCountOutcome N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width
        (D.marksLaw H0) (D.marksLaw H1) p i := by
  funext z
  simp only [sharedOutcome,D.zeroSampler_unequal N H0 H1 hH,
    D.oneSampler_unequal N H0 H1 hH,joinedCountOutcome]

lemma measurable_sharedOutcome (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    Measurable (sharedOutcome D N H0 H1 p i) := by
  by_cases hH : H0=H1
  · subst H1
    rw [sharedOutcome_equal]
    exact (measurable_originalPairCount _ _ (D.equalSampler_measurable N H0)
      (D.equalSampler_measurable N H0) p (Sum.inl i) (Sum.inl i)).comp measurable_snd
  · rw [sharedOutcome_unequal D N H0 H1 hH]
    exact measurable_joinedCountOutcome _ _ _ _ _ _ _ _ _ _ _ _ p i

def sharedLaw (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod (pairLaw D H0 H1))
    (sharedOutcome D N H0 H1 p i) (measurable_sharedOutcome D N H0 H1 p i)

theorem sharedLaw_equal (N : ℕ) (H : Fin (m+1))
    (p : Parameters N H.val D.E.R D.E.Rp D.E.U) (hp : p.2.1=D.signalLaw H) (i : Fin N) :
    sharedLaw D N H H p i=
      EqualPrivateCountPayoff.countLaw N H.val c D.E.R D.E.Rp D.ξ 1 D.E.U (equalParameter p) i := by
  rw [←samplerLaw_equal D N H p hp i]
  apply FiniteLaw.ext_expect
  intro f
  rw [sharedLaw,FiniteLaw.expect_ofMeasure,
    integral_prod _ (HierarchicalFiniteSampler.integrable_finite_comp _ _
      (measurable_sharedOutcome D N H H p i) f)]
  simp only [sharedOutcome_equal D N H p i,Function.comp_apply]
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul]
  unfold samplerLaw originalIndependentCountLaw
  rw [FiniteLaw.expect_ofMeasure,D.zeroSampler_equal,D.oneSampler_equal]
  rfl

theorem sharedLaw_unequal (N : ℕ) (H0 H1 : Fin (m+1)) (hH : H0≠H1)
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (i : Fin N) :
    sharedLaw D N H0 H1 p i=
      originalJoinedCountLaw N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width
        (D.marksLaw H0) (D.marksLaw H1) p
        (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) i := by
  unfold sharedLaw originalJoinedCountLaw
  apply FiniteLaw.ofMeasure_congr_ae
  exact ae_of_all _ fun z => congrFun (sharedOutcome_unequal D N H0 H1 hH p i) z

def atScenario (N : ℕ) (H0 : Fin (m+1)) (b : TypicalGuard.BidBox N D.E.U)
    (sc : Scenario N) : Parameters N H0.val D.E.R D.E.Rp D.E.U :=
  ((sc,b),(D.signalLaw H0,1))

def scenarioOutcome (N : ℕ) (H0 H1 : Fin (m+1)) (b : TypicalGuard.BidBox N D.E.U)
    (i : Fin N)
    (z : Scenario N×(unitInterval×((Row H0.val D.E.R D.E.Rp D.E.H×unitInterval)×
      (Row H1.val D.E.R D.E.Rp D.E.H×unitInterval)))) : Fin 3 :=
  sharedOutcome D N H0 H1 (atScenario D N H0 b z.1) i z.2

lemma measurable_scenarioOutcome (N : ℕ) (H0 H1 : Fin (m+1))
    (b : TypicalGuard.BidBox N D.E.U) (i : Fin N) :
    Measurable (scenarioOutcome D N H0 H1 b i) :=
  measurable_from_prod_countable_right (fun sc =>
    measurable_sharedOutcome D N H0 H1 (atScenario D N H0 b sc) i)

def scenarioExperimentLaw (N : ℕ) (H0 H1 : Fin (m+1))
    (b : TypicalGuard.BidBox N D.E.U) (C : FiniteLaw (Scenario N)) (i : Fin N) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((FiniteLaw.probabilityMeasure C).prod
    ((volume : Measure unitInterval).prod (pairLaw D H0 H1)))
    (scenarioOutcome D N H0 H1 b i) (measurable_scenarioOutcome D N H0 H1 b i)

theorem scenarioExperimentLaw_eq (N : ℕ) (H0 H1 : Fin (m+1))
    (b : TypicalGuard.BidBox N D.E.U) (C : FiniteLaw (Scenario N)) (i : Fin N) :
    scenarioExperimentLaw D N H0 H1 b C i=
      FiniteLaw.finiteMix C (fun sc => sharedLaw D N H0 H1 (atScenario D N H0 b sc) i) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [scenarioExperimentLaw,FiniteLaw.expect_ofMeasure,
    integral_prod _ (HierarchicalFiniteSampler.integrable_finite_comp _ _
      (measurable_scenarioOutcome D N H0 H1 b i) f),FiniteLaw.expect_finiteMix]
  rw [←LowBody.integral_probabilityMeasure C]
  apply integral_congr_ae
  exact ae_of_all _ fun sc => by
    exact (FiniteLaw.expect_ofMeasure
      ((volume : Measure unitInterval).prod (pairLaw D H0 H1))
      (sharedOutcome D N H0 H1 (atScenario D N H0 b sc) i)
      (measurable_sharedOutcome D N H0 H1 (atScenario D N H0 b sc) i) f).symm

theorem scenarioExperimentLaw_equal (N : ℕ) (H : Fin (m+1))
    (b : TypicalGuard.BidBox N D.E.U) (C : FiniteLaw (Scenario N)) (i : Fin N) :
    scenarioExperimentLaw D N H H b C i=
      EqualPrivateCountPayoff.countLaw N H.val c D.E.R D.E.Rp D.ξ 1 D.E.U
        (b,D.signalLaw H) i := by
  rw [scenarioExperimentLaw_eq]
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_finiteMix]
  have he (sc : Scenario N) : sharedLaw D N H H (atScenario D N H b sc) i =
      EqualPrivateCountPayoff.countLaw N H.val c D.E.R D.E.Rp D.ξ 1 D.E.U
        (b,D.signalLaw H) i := sharedLaw_equal D N H _ rfl i
  simp_rw [he]
  exact FiniteLaw.expect_const C _

def ownerScenarioLaw (Q : PublicScenario.Data) (N : ℕ) [Nonempty (Fin N)]
    (H0 H1 : Fin (m+1)) (b : TypicalGuard.BidBox N D.E.U) (i : Fin N) (reg : Bool) : CountLaw 2 :=
  OriginalOwnerCount.countLaw N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp
          D.E.H D.width (D.marksLaw H0) (D.marksLaw H1)
          (atScenario D N H0 b (reg,(∅,(Finset.univ,∅))))
          (sourceFlagProb (PublicScenario.e0 Q reg) Q.B0 (fun j => (b j:ℝ)))
          (sourceFlagProb_nonneg (PublicScenario.e0 Q reg) Q.B0 (fun j => (b j:ℝ)))
          (sourceFlagProb_le_one (PublicScenario.e0 Q reg) Q.B0 (fun j => (b j:ℝ)))
          (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) i

set_option maxHeartbeats 800000 in

theorem scenarioExperimentLaw_unequal (Q : PublicScenario.Data)
    (hc : Q.c=c) (hξ : Q.ξ=D.ξ) (N : ℕ) [Nonempty (Fin N)] (H0 H1 : Fin (m+1))
    (hH : H0≠H1) (hν0 : Q.marksLaw H0.val=D.marksLaw H0)
    (hν1 : Q.marksLaw H1.val=D.marksLaw H1)
    (b : TypicalGuard.BidBox N D.E.U) (i : Fin N) :
    scenarioExperimentLaw D N H0 H1 b
      (PublicScenario.scenarioLaw Q N (H0.val,H1.val) (fun j => (b j:ℝ))) i=
      FiniteLaw.finiteMix (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one)
        (ownerScenarioLaw D Q N H0 H1 b i) := by
  have hN : 0< N := Nat.zero_lt_of_lt i.isLt
  rw [scenarioExperimentLaw_eq,PublicScenario.scenarioLaw_conditional Q N hN]
  apply FiniteLaw.ext_expect
  intro f
  simp only [FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro reg
  simp only [PublicScenario.conditionalScenarioLaw,dif_pos hN,FiniteLaw.expect_map]
  unfold ownerScenarioLaw OriginalOwnerCount.countLaw
  rw [FiniteLaw.expect_finiteMix]
  have hquota : PublicScenario.ownerQuota Q N (H0.val,H1.val) reg =
      OriginalOwnerCount.quota N H0.val H1.val c D.ξ reg (D.marksLaw H0) (D.marksLaw H1) := by
    funext z
    simp only [PublicScenario.ownerQuota,OriginalOwnerCount.quota,hc,hξ,hν0,hν1]
  simp only [atScenario,publicBids,regime]
  rw [←hquota]
  apply FiniteLaw.expect_congr
  intro out
  rw [sharedLaw_unequal D N H0 H1 hH]
  rfl

theorem samplerLaw_noLow_unequal (N : ℕ) (H0 H1 : Fin (m+1)) (hH : H0≠H1)
    (b : TypicalGuard.BidBox N D.E.U) (i : Fin N) :
    samplerLaw D N H0 H1 (atScenario D N H0 b (PublicScenario.fallback N)) i=
      fallbackCount N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
        (atScenario D N H0 b (PublicScenario.fallback N))
        (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) (D.originalPrivateRow H1 : Measure (Row H1.val D.E.R D.E.Rp D.E.H)) i := by
  have hw := (TypicalGuard.weight_bounds N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp
    D.width false ∅ Finset.univ ∅ (fun j => (b j:ℝ)) (D.marksLaw H0) (D.marksLaw H1)).2
  have hn : ¬UseTypical N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.width
      (D.marksLaw H0) (D.marksLaw H1) (atScenario D N H0 b (PublicScenario.fallback N)) :=
    not_lt.mpr hw
  unfold samplerLaw fallbackCount originalIndependentCountLaw
  simp only [D.zeroSampler_unequal N H0 H1 hH,D.oneSampler_unequal N H0 H1 hH]
  apply FiniteLaw.ofMeasure_congr_ae
  exact ae_of_all _ fun z => by
    simp only [originalPairCount,localAccept,unequal0,unequal1,if_neg hn,
      fallback0,fallback1]
    rfl

end FCAppendix.Affine.Tail04.NativeSamplerCountLaw
