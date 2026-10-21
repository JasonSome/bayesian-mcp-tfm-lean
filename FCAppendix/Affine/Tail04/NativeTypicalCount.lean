import FCAppendix.Affine.Tail04.OriginalCountSampling
import FCAppendix.Affine.Tail04.TypicalMeanCount
import FCAppendix.Affine.Tail04.JoinedHighPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeTypicalCount
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

def privateMean (H : ℕ) (reg : Bool) (ν : FiniteLaw (Marks H)) : ℝ :=
  ν.expect (fun z => (((if reg then upperCount z else H):ℕ):ℝ))

theorem privateMean_regime_of_countMean (H : ℕ) (reg : Bool) (ν : FiniteLaw (Marks H))
    (π : ℝ) (hcount : ν.expect (fun z => (upperCount z:ℝ))=(H:ℝ)*π) :
    privateMean H reg ν=if reg then (H:ℝ)*π else (H:ℝ) := by
  cases reg
  · simp [privateMean]
  · exact hcount

theorem privateMean_regime (H : ℕ) (reg : Bool) (ν : FiniteLaw (Marks H))
    (π : ℝ) (hπ : ∀ k, ν.prob (fun z => z k=true)=π) :
    privateMean H reg ν=if reg then (H:ℝ)*π else (H:ℝ) := by
  exact privateMean_regime_of_countMean H reg ν π
    (TypicalHighPolicy.expected_upperCount H ν π hπ)

def countParameters (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : TypicalCountParameters :=
  ⟨ξ,c,N,privateMean H0 reg ν0,privateMean H1 reg ν1⟩

theorem activeMean_eq_meanMarginal (N H c : ℕ) {ξ B : ℝ} (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (ν : FiniteLaw (Marks H))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hb : ∀ i, b i ∈ Icc (1:ℝ) B)
    (hOI : Disjoint O I) (hcap : O.card+H ≤ c) (hI : I.Nonempty)
    (hg : TypicalHighPolicy.LocalGuard N H c ξ B reg O I b)
    (i : Fin N) (hi : i ∈ I) :
    TypicalHighPolicy.activeMean N H c ξ reg O I b ν i =
      meanMarginal ξ c O.card (privateMean H reg ν) I.card
        (mixedReciprocalSum I b) (b i) := by
  have hr := TypicalHighPolicy.mixed_receipt N H c reg O I b ν
    hξ hξ1 hb hOI hcap hI hg i hi
  have hbi : b i ≠ 0 := ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  have he : TypicalHighPolicy.activeMean N H c ξ reg O I b ν i =
      rawMeanMarginal ξ c O.card (privateMean H reg ν) I.card
        (mixedReciprocalSum I b) (b i) := by
    calc
      _ = (1-TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν / b i)/ξ := by
        field_simp [hξ.ne',hbi]
        nlinarith only [hr]
      _ = _ := by
        rw [TypicalHighPolicy.meanMultiplier_formula N H c ξ reg O I b ν hcap]
        unfold rawMeanMarginal privateMean
        congr 2
        ring
  unfold meanMarginal
  rw [← he,probabilityClip_eq (TypicalHighPolicy.activeMean_bounds N H c ξ reg O I b ν i)]

def typical0 (N H0 c : ℕ) (ξ B R Rp Rm : ℝ) :
    (Parameters N H0 R Rp B × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0) :=
  fun z u => typicalSampler N H0 c ξ R Rp Rm (regime z.1.1.1)
    (owner0 z.1.1.1) (mixed z.1.1.1) (publicBids z.1,z.2) u

def typical1 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    (Parameters N H0 R Rp B × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1) :=
  fun z u => typicalSampler N H1 c ξ R Rp Rm (regime z.1.1.1)
    (owner1 z.1.1.1) (mixed z.1.1.1) (publicBids z.1,z.2) u

def fallback0 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    (Parameters N H0 R Rp B × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0) :=
  fun z _ => AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) false z.2

def fallback1 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    (Parameters N H0 R Rp B × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1) :=
  fun z _ => AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) true z.2

theorem measurable_typical0 (N H0 c : ℕ) (ξ B R Rp Rm : ℝ) :
    Measurable (Function.uncurry (typical0 N H0 c ξ B R Rp Rm)) :=
  measurable_scenario_sampler N H0 H0 c ξ B R Rp Rm owner0

theorem measurable_typical1 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    Measurable (Function.uncurry (typical1 N H0 H1 c ξ B R Rp Rm)) :=
  measurable_scenario_sampler N H1 H0 c ξ B R Rp Rm owner1

theorem measurable_fallback0 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    Measurable (Function.uncurry (fallback0 N H0 H1 c ξ B R Rp Rm)) := by
  convert! (AllCountAtypical.measurable_select N H0 H1 c ξ false).comp
    ((measurable_publicBids.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)) using 1

theorem measurable_fallback1 (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ) :
    Measurable (Function.uncurry (fallback1 N H0 H1 c ξ B R Rp Rm)) := by
  convert! (AllCountAtypical.measurable_select N H0 H1 c ξ true).comp
    ((measurable_publicBids.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)) using 1

theorem typical0_mean (N H0 c : ℕ) (ξ B R Rp Rm : ℝ)
    (p : Parameters N H0 R Rp B) (θ : Measure (Row H0 R Rp Rm)) [IsProbabilityMeasure θ]
    (ν : FiniteLaw (Marks H0))
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν) (i : Fin N) :
    LocalSamplerMean.mean (typical0 N H0 c ξ B R Rp Rm) p θ (Sum.inl i) =
      TypicalHighPolicy.activeMean N H0 c ξ (regime p.1.1) (owner0 p.1.1)
        (mixed p.1.1) (publicBids p) ν i := by
  rw [LocalSamplerMean.of_finiteLaw _ (measurable_typical0 N H0 c ξ B R Rp Rm) p θ
    (TypicalHighPolicy.rowLaw N H0 c ξ (regime p.1.1) (owner0 p.1.1)
      (mixed p.1.1) (publicBids p))
    (fun row => typicalSampler_law N H0 c ξ R Rp Rm (regime p.1.1)
      (owner0 p.1.1) (mixed p.1.1) (publicBids p) row)]
  exact TypicalHighPolicy.original_active_mean N H0 c ξ (regime p.1.1)
    (owner0 p.1.1) (mixed p.1.1) (publicBids p) θ ν hν i

theorem typical1_mean (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ)
    (p : Parameters N H0 R Rp B) (θ : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ]
    (ν : FiniteLaw (Marks H1))
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν) (i : Fin N) :
    LocalSamplerMean.mean (typical1 N H0 H1 c ξ B R Rp Rm) p θ (Sum.inl i) =
      TypicalHighPolicy.activeMean N H1 c ξ (regime p.1.1) (owner1 p.1.1)
        (mixed p.1.1) (publicBids p) ν i := by
  rw [LocalSamplerMean.of_finiteLaw _ (measurable_typical1 N H0 H1 c ξ B R Rp Rm) p θ
    (TypicalHighPolicy.rowLaw N H1 c ξ (regime p.1.1) (owner1 p.1.1)
      (mixed p.1.1) (publicBids p))
    (fun row => typicalSampler_law N H1 c ξ R Rp Rm (regime p.1.1)
      (owner1 p.1.1) (mixed p.1.1) (publicBids p) row)]
  exact TypicalHighPolicy.original_active_mean N H1 c ξ (regime p.1.1)
    (owner1 p.1.1) (mixed p.1.1) (publicBids p) θ ν hν i

def typicalCount (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ)
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (i : Fin N) : CountLaw 2 :=
  originalIndependentCountLaw (typical0 N H0 c ξ B R Rp Rm)
    (typical1 N H0 H1 c ξ B R Rp Rm)
    (measurable_typical0 N H0 c ξ B R Rp Rm) (measurable_typical1 N H0 H1 c ξ B R Rp Rm)
    p θ0 θ1 (Sum.inl i) (Sum.inl i)

def fallbackCount (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ)
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (i : Fin N) : CountLaw 2 :=
  originalIndependentCountLaw (fallback0 N H0 H1 c ξ B R Rp Rm)
    (fallback1 N H0 H1 c ξ B R Rp Rm)
    (measurable_fallback0 N H0 H1 c ξ B R Rp Rm) (measurable_fallback1 N H0 H1 c ξ B R Rp Rm)
    p θ0 θ1 (Sum.inl i) (Sum.inl i)

theorem typicalCount_eq (N H0 H1 c : ℕ) {ξ B : ℝ} (R Rp Rm : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (p : Parameters N H0 R Rp B)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hg : TypicalHighPolicy.Guard N H0 H1 c ξ B R Rp (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1)
    (i : Fin N) :
    typicalCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i =
      if i ∈ mixed p.1.1 then
        meanCountLaw ξ c (owner0 p.1.1).card (owner1 p.1.1).card
          (privateMean H0 (regime p.1.1) ν0) (privateMean H1 (regime p.1.1) ν1)
          (mixed p.1.1).card (mixedReciprocalSum (mixed p.1.1) (publicBids p)) (publicBids p i)
      else FiniteLaw.dirac 1 := by
  have hs := hg.1
  have hO0I := hs.2.1.symm.mono_left
    (Finset.subset_union_left : owner0 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
  have hO1I := hs.2.1.symm.mono_left
    (Finset.subset_union_right : owner1 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
  have hb : ∀ j, publicBids p j ∈ Icc (1:ℝ) B := fun j => (p.1.2 j).2
  unfold typicalCount
  rw [originalIndependentCountLaw_eq]
  simp only [typical0_mean N H0 c ξ B R Rp Rm p θ0 ν0 hν0,
    typical1_mean N H0 H1 c ξ B R Rp Rm p θ1 ν1 hν1]
  by_cases hi : i ∈ mixed p.1.1
  · rw [if_pos hi]
    have h0 := activeMean_eq_meanMarginal N H0 c (regime p.1.1) (owner0 p.1.1)
      (mixed p.1.1) (publicBids p) ν0 hξ hξ1 hb hO0I hs.2.2.2.1 hs.2.2.2.2.2 hg.2.1 i hi
    have h1 := activeMean_eq_meanMarginal N H1 c (regime p.1.1) (owner1 p.1.1)
      (mixed p.1.1) (publicBids p) ν1 hξ hξ1 hb hO1I hs.2.2.2.2.1 hs.2.2.2.2.2 hg.2.2.1 i hi
    simp only [h0,h1,meanCountLaw]
  · rw [if_neg hi]
    have hiO : i ∈ owner0 p.1.1 ∪ owner1 p.1.1 := by
      have hh : i ∈ mixed p.1.1 ∪ (owner0 p.1.1 ∪ owner1 p.1.1) := by
        rw [hs.2.2.1]
        exact Finset.mem_univ i
      exact (Finset.mem_union.mp hh).resolve_left hi
    have h0 := TypicalHighPolicy.activeMean_formula N H0 c (regime p.1.1) (owner0 p.1.1)
      (mixed p.1.1) (publicBids p) ν0 hξ hξ1 hb hO0I hs.2.2.2.1 hs.2.2.2.2.2 hg.2.1 i
    have h1 := TypicalHighPolicy.activeMean_formula N H1 c (regime p.1.1) (owner1 p.1.1)
      (mixed p.1.1) (publicBids p) ν1 hξ hξ1 hb hO1I hs.2.2.2.2.1 hs.2.2.2.2.2 hg.2.2.1 i
    apply FiniteLaw.ext_expect
    intro f
    rw [twoCoinCountLaw_expect,FiniteLaw.expect_dirac,h0,h1]
    rcases Finset.mem_union.mp hiO with hi0 | hi1
    · have hn1 : i ∉ owner1 p.1.1 := fun hh => (Finset.disjoint_left.mp hs.1) hi0 hh
      simp [hi0,hn1,hi]
    · have hn0 : i ∉ owner0 p.1.1 := fun hh => (Finset.disjoint_left.mp hs.1) hh hi1
      simp [hn0,hi1,hi]

theorem typicalCount_eq_balanced (N H0 H1 c : ℕ) {ξ B : ℝ} (R Rp Rm : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (p : Parameters N H0 R Rp B)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hg : TypicalHighPolicy.Guard N H0 H1 c ξ B R Rp (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1)
    (hell0 : (owner0 p.1.1).card =
      (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).owner0 (mixed p.1.1).card)
    (hell1 : (owner1 p.1.1).card =
      (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).owner1 (mixed p.1.1).card)
    (i : Fin N) :
    typicalCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i =
      if i ∈ mixed p.1.1 then
        (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
          (mixed p.1.1).card (mixedReciprocalSum (mixed p.1.1) (publicBids p)) (publicBids p i)
      else FiniteLaw.dirac 1 := by
  rw [typicalCount_eq N H0 H1 c R Rp Rm ν0 ν1 hξ hξ1 p θ0 θ1 hν0 hν1 hg i,
    hell0,hell1]
  rfl

def setCommonSeed {N H : ℕ} {R Rp B : ℝ}
    (p : Parameters N H R Rp B) (u : unitInterval) : Parameters N H R Rp B :=
  (p.1,(p.2.1,u))

def weightParameter (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) : unitInterval :=
  ⟨publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p,
    TypicalGuard.weight_bounds N H0 H1 c ξ B R Rp width (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1⟩

def joinedCountOutcome (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (i : Fin N)
    (z : unitInterval × ((Row H0 R Rp Rm × unitInterval) × (Row H1 R Rp Rm × unitInterval))) : Fin 3 :=
  originalPairCount (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
    (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
    (setCommonSeed p z.1) (Sum.inl i) (Sum.inl i) z.2

theorem joinedCountOutcome_eq (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (i : Fin N) :
    joinedCountOutcome N H0 H1 c ξ B R Rp Rm width ν0 ν1 p i =
      seededBranchOutcome (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p)
        (originalPairCount (typical0 N H0 c ξ B R Rp Rm)
          (typical1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i))
        (originalPairCount (fallback0 N H0 H1 c ξ B R Rp Rm)
          (fallback1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i)) := by
  funext z
  by_cases hu : z.1 < weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p
  · have hu' : (z.1:ℝ) < publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p := hu
    dsimp only [publicWeight,publicBids] at hu'
    simp only [joinedCountOutcome,seededBranchOutcome,if_pos hu]
    simp [originalPairCount,localAccept,unequal0,unequal1,UseTypical,setCommonSeed,
      publicWeight,publicBids,typical0,typical1,hu']
    rfl
  · have hu' : ¬(z.1:ℝ) < publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p := hu
    dsimp only [publicWeight,publicBids] at hu'
    simp only [joinedCountOutcome,seededBranchOutcome,if_neg hu]
    simp [originalPairCount,localAccept,unequal0,unequal1,UseTypical,setCommonSeed,
      publicWeight,publicBids,fallback0,fallback1,hu']
    rfl

theorem measurable_joinedCountOutcome (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (i : Fin N) :
    Measurable (joinedCountOutcome N H0 H1 c ξ B R Rp Rm width ν0 ν1 p i) := by
  rw [joinedCountOutcome_eq]
  exact measurable_seededBranchOutcome _ _ _
    (measurable_originalPairCount _ _ (measurable_typical0 N H0 c ξ B R Rp Rm)
      (measurable_typical1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i))
    (measurable_originalPairCount _ _ (measurable_fallback0 N H0 H1 c ξ B R Rp Rm)
      (measurable_fallback1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i))

def originalJoinedCountLaw (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (i : Fin N) : CountLaw 2 :=
  FiniteLaw.ofMeasure ((volume : Measure unitInterval).prod
      ((θ0.prod volume).prod (θ1.prod volume)))
    (joinedCountOutcome N H0 H1 c ξ B R Rp Rm width ν0 ν1 p i)
    (measurable_joinedCountOutcome N H0 H1 c ξ B R Rp Rm width ν0 ν1 p i)

theorem originalJoinedCountLaw_eq (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (i : Fin N) :
    originalJoinedCountLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ0 θ1 i =
      FiniteLaw.mixture (typicalCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i)
        (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i)
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p : ℝ)
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p).property.1
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p).property.2 := by
  unfold originalJoinedCountLaw
  simp_rw [joinedCountOutcome_eq]
  have ht := measurable_originalPairCount _ _ (measurable_typical0 N H0 c ξ B R Rp Rm)
    (measurable_typical1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i)
  have ha := measurable_originalPairCount _ _ (measurable_fallback0 N H0 H1 c ξ B R Rp Rm)
    (measurable_fallback1 N H0 H1 c ξ B R Rp Rm) p (Sum.inl i) (Sum.inl i)
  convert! original_sharedBranch_law ((θ0.prod volume).prod (θ1.prod volume))
    (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p) _ _ ht ha using 1

theorem originalJoinedCountLaw_balanced (N H0 H1 c : ℕ) {ξ B : ℝ} (R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (hell0 : (owner0 p.1.1).card =
      (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).owner0 (mixed p.1.1).card)
    (hell1 : (owner1 p.1.1).card =
      (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).owner1 (mixed p.1.1).card)
    (i : Fin N) :
    originalJoinedCountLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ0 θ1 i =
      FiniteLaw.mixture
        (if i ∈ mixed p.1.1 then
          (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
            (mixed p.1.1).card (mixedReciprocalSum (mixed p.1.1) (publicBids p)) (publicBids p i)
        else FiniteLaw.dirac 1)
        (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i)
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p : ℝ)
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p).property.1
        (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p).property.2 := by
  rw [originalJoinedCountLaw_eq]
  by_cases hpos : 0 < (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p : ℝ)
  · have hg := TypicalGuard.guard_of_weight_pos N H0 H1 c ξ B R Rp width
      (regime p.1.1) (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p)
      ν0 ν1 hw hpos
    rw [typicalCount_eq_balanced N H0 H1 c R Rp Rm ν0 ν1 hξ hξ1 p θ0 θ1
      hν0 hν1 hg hell0 hell1 i]
  · have hz : (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p : ℝ)=0 :=
      le_antisymm (le_of_not_gt hpos) (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 p).property.1
    apply FiniteLaw.ext_expect
    intro f
    rw [FiniteLaw.expect_mixture,FiniteLaw.expect_mixture,hz]
    ring

end FCAppendix.Affine.Tail04.NativeTypicalCount
