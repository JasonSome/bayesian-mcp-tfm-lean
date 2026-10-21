import FCAppendix.Affine.Tail04.AtypicalOriginalPosterior
import FCAppendix.Affine.Tail04.TypicalGuard
import FCAppendix.Affine.Tail04.LocalSamplerMean

noncomputable section
namespace FCAppendix.Affine.Tail04.JoinedHighPolicy
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon

local instance (ι : Type*) : TopologicalSpace (Finset ι) := ⊥
local instance (ι : Type*) : DiscreteTopology (Finset ι) := ⟨rfl⟩
local instance (ι : Type*) : MeasurableSpace (Finset ι) := ⊤
local instance (ι : Type*) : BorelSpace (Finset ι) := ⟨borel_eq_top_of_discrete.symm⟩

abbrev Scenario (N : ℕ) := Bool × (Finset (Fin N) × (Finset (Fin N) × Finset (Fin N)))
def regime {N : ℕ} (s : Scenario N) : Bool := s.1
def mixed {N : ℕ} (s : Scenario N) : Finset (Fin N) := s.2.1
def owner0 {N : ℕ} (s : Scenario N) : Finset (Fin N) := s.2.2.1
def owner1 {N : ℕ} (s : Scenario N) : Finset (Fin N) := s.2.2.2

abbrev Parameters (N H : ℕ) (R Rp B : ℝ) :=
  (Scenario N × TypicalGuard.BidBox N B) ×
    (WeakProbability.Law (Signal H R Rp) × unitInterval)

def publicBids {N H : ℕ} {R Rp B : ℝ} (p : Parameters N H R Rp B) : Fin N → ℝ :=
  TypicalGuard.bids p.1.2

def equalParameter {N H : ℕ} {R Rp B : ℝ} (p : Parameters N H R Rp B) :
    PolicyParameters N H R Rp 1 B := (p.1.2,p.2.1)

def typicalSampler (N H c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool) (O I : Finset (Fin N)) :
    ((Fin N → ℝ) × Row H R Rp Rm) → unitInterval → Finset (Target N H) :=
  Classical.choose (TypicalHighPolicy.exists_sampler N H c ξ reg O I R Rp Rm)

lemma typicalSampler_measurable (N H c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) : Measurable (Function.uncurry (typicalSampler N H c ξ R Rp Rm reg O I)) :=
  (Classical.choose_spec (TypicalHighPolicy.exists_sampler N H c ξ reg O I R Rp Rm)).1

lemma typicalSampler_support (N H c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (row : Row H R Rp Rm) (u : unitInterval) :
    0 < (TypicalHighPolicy.law N H c ξ reg O I b (marks (signal row))).mass
      (typicalSampler N H c ξ R Rp Rm reg O I (b,row) u) :=
  (Classical.choose_spec (TypicalHighPolicy.exists_sampler N H c ξ reg O I R Rp Rm)).2.1 b row u

lemma typicalSampler_law (N H c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) (row : Row H R Rp Rm) :
    volume.map (typicalSampler N H c ξ R Rp Rm reg O I (b,row)) =
      FiniteLaw.probabilityMeasure (TypicalHighPolicy.law N H c ξ reg O I b (marks (signal row))) :=
  (Classical.choose_spec (TypicalHighPolicy.exists_sampler N H c ξ reg O I R Rp Rm)).2.2 b row

def publicWeight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) : ℝ :=
  TypicalGuard.weight N H0 H1 c ξ B R Rp width (regime p.1.1)
    (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1

def UseTypical (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) : Prop :=
  p.2.2.1 < publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 p

lemma measurable_publicBids {N H : ℕ} {R Rp B : ℝ} :
    Measurable (publicBids : Parameters N H R Rp B → Fin N → ℝ) :=
  TypicalGuard.continuous_bids.measurable.comp (measurable_snd.comp measurable_fst)

lemma measurable_publicWeight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (publicWeight N H0 H1 c ξ B R Rp width ν0 ν1) := by
  have h : Measurable (fun z : Scenario N × TypicalGuard.BidBox N B =>
      TypicalGuard.weight N H0 H1 c ξ B R Rp width (regime z.1)
        (mixed z.1) (owner0 z.1) (owner1 z.1) (TypicalGuard.bids z.2) ν0 ν1) :=
    measurable_from_prod_countable_right fun s =>
      (TypicalGuard.continuous_weight N H0 H1 c ξ B R Rp width
        (regime s) (mixed s) (owner0 s) (owner1 s) ν0 ν1).measurable
  exact h.comp measurable_fst

lemma measurableSet_useTypical (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    MeasurableSet {p | UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p} :=
  measurableSet_lt
    (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))
    (measurable_publicWeight N H0 H1 c ξ B R Rp width ν0 ν1)

lemma useTypical_guard (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p) :
    TypicalHighPolicy.Guard N H0 H1 c ξ B R Rp (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1 :=
  TypicalGuard.guard_of_weight_pos N H0 H1 c ξ B R Rp width (regime p.1.1)
    (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν0 ν1 hw
    (p.2.2.2.1.trans_lt hu)

def unequal0 (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    (Parameters N H0 R Rp B × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0) :=
  fun z u => if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 z.1 then
    typicalSampler N H0 c ξ R Rp Rm (regime z.1.1.1) (owner0 z.1.1.1) (mixed z.1.1.1)
      (publicBids z.1,z.2) u
  else AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) false z.2

def unequal1 (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    (Parameters N H0 R Rp B × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1) :=
  fun z u => if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 z.1 then
    typicalSampler N H1 c ξ R Rp Rm (regime z.1.1.1) (owner1 z.1.1.1) (mixed z.1.1.1)
      (publicBids z.1,z.2) u
  else AllCountAtypical.select N H0 H1 c ξ (publicBids z.1) true z.2

lemma measurable_scenario_sampler (N H Hpub c : ℕ) (ξ B R Rp Rm : ℝ)
    (O : Scenario N → Finset (Fin N)) :
    Measurable (fun z : (Parameters N Hpub R Rp B × Row H R Rp Rm) × unitInterval =>
      typicalSampler N H c ξ R Rp Rm (regime z.1.1.1.1) (O z.1.1.1.1) (mixed z.1.1.1.1)
        (publicBids z.1.1,z.1.2) z.2) := by
  have hs : Measurable (fun z : Scenario N × (((Fin N → ℝ) × Row H R Rp Rm) × unitInterval) =>
      typicalSampler N H c ξ R Rp Rm (regime z.1) (O z.1) (mixed z.1) z.2.1 z.2.2) :=
    measurable_from_prod_countable_right fun s => typicalSampler_measurable N H c ξ R Rp Rm
      (regime s) (O s) (mixed s)
  convert! hs.comp
    ((measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_publicBids.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)) using 1

theorem measurable_unequal0 (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (Function.uncurry (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1)) := by
  unfold Function.uncurry unequal0
  apply Measurable.ite
    ((measurableSet_useTypical N H0 H1 c ξ B R Rp width ν0 ν1).preimage
      (measurable_fst.comp measurable_fst))
    (measurable_scenario_sampler N H0 H0 c ξ B R Rp Rm owner0)
  convert! (AllCountAtypical.measurable_select N H0 H1 c ξ false).comp
    ((measurable_publicBids.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)) using 1

theorem measurable_unequal1 (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (Function.uncurry (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1)) := by
  unfold Function.uncurry unequal1
  apply Measurable.ite
    ((measurableSet_useTypical N H0 H1 c ξ B R Rp width ν0 ν1).preimage
      (measurable_fst.comp measurable_fst))
    (measurable_scenario_sampler N H1 H0 c ξ B R Rp Rm owner1)
  convert! (AllCountAtypical.measurable_select N H0 H1 c ξ true).comp
    ((measurable_publicBids.comp (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)) using 1

theorem unequal0_capacity (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (row : Row H0 R Rp Rm) (u : unitInterval) :
    (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row) u).card ≤ c := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · have hg := useTypical_guard N H0 H1 c ξ B R Rp width ν0 ν1 hw p hu
    have hs := hg.1
    have hOI := hs.2.1.symm.mono_left (Finset.subset_union_left : owner0 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hi := TypicalHighPolicy.implements N H0 c (regime p.1.1) (owner0 p.1.1) (mixed p.1.1)
      (publicBids p) hξ hξ1 (fun i => (p.1.2 i).2) hOI hs.2.2.2.1 hs.2.2.2.2.2 hg.2.1
      (marks (signal row))
    have hc := hi.1 _ (typicalSampler_support N H0 c ξ R Rp Rm (regime p.1.1)
      (owner0 p.1.1) (mixed p.1.1) (publicBids p) row u).ne'
    dsimp only [unequal0]
    rw [if_pos hu]
    exact hc.le
  · dsimp only [unequal0]
    rw [if_neg hu]
    convert! AllCountAtypical.capacity N H0 H1 c ξ (publicBids p) false row using 1

theorem unequal1_capacity (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (row : Row H1 R Rp Rm) (u : unitInterval) :
    (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row) u).card ≤ c := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · have hg := useTypical_guard N H0 H1 c ξ B R Rp width ν0 ν1 hw p hu
    have hs := hg.1
    have hOI := hs.2.1.symm.mono_left (Finset.subset_union_right : owner1 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hi := TypicalHighPolicy.implements N H1 c (regime p.1.1) (owner1 p.1.1) (mixed p.1.1)
      (publicBids p) hξ hξ1 (fun i => (p.1.2 i).2) hOI hs.2.2.2.2.1 hs.2.2.2.2.2 hg.2.2.1
      (marks (signal row))
    have hc := hi.1 _ (typicalSampler_support N H1 c ξ R Rp Rm (regime p.1.1)
      (owner1 p.1.1) (mixed p.1.1) (publicBids p) row u).ne'
    dsimp only [unequal1]
    rw [if_pos hu]
    exact hc.le
  · dsimp only [unequal1]
    rw [if_neg hu]
    convert! AllCountAtypical.capacity N H0 H1 c ξ (publicBids p) true row using 1

theorem unequal0_law (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (row : Row H0 R Rp Rm) :
    volume.map (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row)) =
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then
        FiniteLaw.probabilityMeasure (TypicalHighPolicy.rowLaw N H0 c ξ
          (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) row)
      else Measure.dirac (AllCountAtypical.select N H0 H1 c ξ (publicBids p) false row) := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · unfold unequal0
    simp only [if_pos hu]
    simpa only [TypicalHighPolicy.rowLaw] using typicalSampler_law N H0 c ξ R Rp Rm
      (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) row
  · unfold unequal0
    simp only [if_neg hu,Measure.map_const,measure_univ,one_smul]

theorem unequal1_law (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (row : Row H1 R Rp Rm) :
    volume.map (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row)) =
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then
        FiniteLaw.probabilityMeasure (TypicalHighPolicy.rowLaw N H1 c ξ
          (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) row)
      else Measure.dirac (AllCountAtypical.select N H0 H1 c ξ (publicBids p) true row) := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · unfold unequal1
    simp only [if_pos hu]
    simpa only [TypicalHighPolicy.rowLaw] using typicalSampler_law N H1 c ξ R Rp Rm
      (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) row
  · unfold unequal1
    simp only [if_neg hu,Measure.map_const,measure_univ,one_smul]

theorem unequal0_mean (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (θ : Measure (Row H0 R Rp Rm)) [IsProbabilityMeasure θ]
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0) (i : Fin N) :
    LocalSamplerMean.mean (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1) p θ (Sum.inl i) =
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then
        TypicalHighPolicy.activeMean N H0 c ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) ν0 i
      else AtypicalOriginalPosterior.mean N H0 H1 c ξ (publicBids p) false θ i := by
  have hf := measurable_unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · rw [if_pos hu]
    rw [LocalSamplerMean.of_finiteLaw _ hf p θ
      (TypicalHighPolicy.rowLaw N H0 c ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p))
      (fun row => by simpa [hu] using unequal0_law N H0 H1 c ξ B R Rp Rm width ν0 ν1 p row)]
    exact TypicalHighPolicy.original_active_mean N H0 c ξ (regime p.1.1) (owner0 p.1.1)
      (mixed p.1.1) (publicBids p) θ ν0 hν i
  · rw [if_neg hu]
    rw [LocalSamplerMean.of_law _ hf p θ
      (fun row => Measure.dirac (AllCountAtypical.select N H0 H1 c ξ (publicBids p) false row))
      (fun row => by simpa [hu] using unequal0_law N H0 H1 c ξ B R Rp Rm width ν0 ν1 p row)]
    simp [AtypicalOriginalPosterior.mean,AllCountAtypical.ownCount]
    rfl

theorem unequal1_mean (N H0 H1 c : ℕ) (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (θ : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ]
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1) (i : Fin N) :
    LocalSamplerMean.mean (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1) p θ (Sum.inl i) =
      if UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p then
        TypicalHighPolicy.activeMean N H1 c ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) ν1 i
      else AtypicalOriginalPosterior.mean N H0 H1 c ξ (publicBids p) true θ i := by
  have hf := measurable_unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · rw [if_pos hu]
    rw [LocalSamplerMean.of_finiteLaw _ hf p θ
      (TypicalHighPolicy.rowLaw N H1 c ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p))
      (fun row => by simpa [hu] using unequal1_law N H0 H1 c ξ B R Rp Rm width ν0 ν1 p row)]
    exact TypicalHighPolicy.original_active_mean N H1 c ξ (regime p.1.1) (owner1 p.1.1)
      (mixed p.1.1) (publicBids p) θ ν1 hν i
  · rw [if_neg hu]
    rw [LocalSamplerMean.of_law _ hf p θ
      (fun row => Measure.dirac (AllCountAtypical.select N H0 H1 c ξ (publicBids p) true row))
      (fun row => by simpa [hu] using unequal1_law N H0 H1 c ξ B R Rp Rm width ν0 ν1 p row)]
    simp [AtypicalOriginalPosterior.mean,AllCountAtypical.ownCount]
    rfl

theorem unequal0_optimal (N H0 H1 c : ℕ) (ξ B R Rp Rm width π : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hB : 1 ≤ B) (hw : 0 < width) (hπ : 0 ≤ π)
    (hR : 0 < R) (hRRp : R ≤ Rp) (hRp : Rp < 1) (hBRm : B < Rm)
    (hrare : (1-ξ)*B+ξ*B*((H1:ℝ)*π) ≤ R) (hfirst : (1-ξ)*B < 1)
    (hany : ν1.prob AtypicalOriginalPosterior.anyUpper ≤ (H1:ℝ)*π)
    (p : Parameters N H0 R Rp B) (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ1]
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (row : Row H0 R Rp Rm) (u : unitInterval) :
    Finite.Optimal c
      (receipt (publicBids p)
        (fun i => LocalSamplerMean.mean (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1) p θ1 (Sum.inl i)) ξ row)
      (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row) u) := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · have hq : (fun i => LocalSamplerMean.mean (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
        p θ1 (Sum.inl i)) =
        TypicalHighPolicy.activeMean N H1 c ξ (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) ν1 := by
      funext i
      rw [unequal1_mean N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ1 hν1 i,if_pos hu]
    rw [hq,unequal0,if_pos hu]
    have hg := useTypical_guard N H0 H1 c ξ B R Rp width ν0 ν1 hw p hu
    have hs := hg.1
    have hOI := hs.2.1.symm.mono_left (Finset.subset_union_left : owner0 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hPI := hs.2.1.symm.mono_left (Finset.subset_union_right : owner1 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hpart : if regime p.1.1 then Rp ≤ TypicalHighPolicy.meanMultiplier N H1 c ξ
        (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) ν1
      else TypicalHighPolicy.meanMultiplier N H1 c ξ
        (regime p.1.1) (owner1 p.1.1) (mixed p.1.1) (publicBids p) ν1 ≤ R := by
      have hh := hg.2.2.2
      cases he : regime p.1.1 <;> simp only [TypicalHighPolicy.PartialGuard,he,ite_true] at * <;>
        exact hh.2
    exact TypicalHighPolicy.physical_support_optimal N H0 H1 c (regime p.1.1)
      (mixed p.1.1) (owner0 p.1.1) (owner1 p.1.1) (publicBids p) ν1 row
      hξ hξ1 hB (fun i => (p.1.2 i).2) hR.le hRp hBRm hs.1 hOI hPI hs.2.2.1
      hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 hg.2.1 hg.2.2.1 hpart _
      (typicalSampler_support N H0 c ξ R Rp Rm (regime p.1.1) (owner0 p.1.1)
        (mixed p.1.1) (publicBids p) row u).ne'
  · have hq : (fun i => LocalSamplerMean.mean (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
        p θ1 (Sum.inl i)) = AtypicalOriginalPosterior.mean N H0 H1 c ξ (publicBids p) true θ1 := by
      funext i
      rw [unequal1_mean N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ1 hν1 i,if_neg hu]
    rw [hq,unequal0,if_neg hu]
    have hm : (AtypicalOriginalPosterior.markLaw θ1).prob
        AtypicalOriginalPosterior.anyUpper ≤ (H1:ℝ)*π := by
      rw [AtypicalOriginalPosterior.markLaw_eq_of_pushforward θ1 ν1 hν1]
      exact hany
    exact @AtypicalOriginalPosterior.actual_optimal N H0 H1 c R Rp Rm B ξ (publicBids p) false θ1
      ‹IsProbabilityMeasure θ1›
      π hπ ⟨hξ.le,hξ1⟩ (fun i => (p.1.2 i).2) hB hR hRRp hRp hBRm hrare hfirst hm row

theorem unequal1_optimal (N H0 H1 c : ℕ) (ξ B R Rp Rm width π : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hB : 1 ≤ B) (hw : 0 < width) (hπ : 0 ≤ π)
    (hR : 0 < R) (hRRp : R ≤ Rp) (hRp : Rp < 1) (hBRm : B < Rm)
    (hrare : (1-ξ)*B+ξ*B*((H0:ℝ)*π) ≤ R) (hfirst : (1-ξ)*B < 1)
    (hany : ν0.prob AtypicalOriginalPosterior.anyUpper ≤ (H0:ℝ)*π)
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm)) [IsProbabilityMeasure θ0]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (row : Row H1 R Rp Rm) (u : unitInterval) :
    Finite.Optimal c
      (receipt (publicBids p)
        (fun i => LocalSamplerMean.mean (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1) p θ0 (Sum.inl i)) ξ row)
      (unequal1 N H0 H1 c ξ B R Rp Rm width ν0 ν1 (p,row) u) := by
  by_cases hu : UseTypical N H0 H1 c ξ B R Rp width ν0 ν1 p
  · have hq : (fun i => LocalSamplerMean.mean (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
        p θ0 (Sum.inl i)) =
        TypicalHighPolicy.activeMean N H0 c ξ (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) ν0 := by
      funext i
      rw [unequal0_mean N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ0 hν0 i,if_pos hu]
    rw [hq,unequal1,if_pos hu]
    have hg := useTypical_guard N H0 H1 c ξ B R Rp width ν0 ν1 hw p hu
    have hs := hg.1
    have hOI := hs.2.1.symm.mono_left (Finset.subset_union_right : owner1 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hPI := hs.2.1.symm.mono_left (Finset.subset_union_left : owner0 p.1.1 ⊆ owner0 p.1.1 ∪ owner1 p.1.1)
    have hcover : mixed p.1.1 ∪ (owner1 p.1.1 ∪ owner0 p.1.1)=Finset.univ := by
      simpa [Finset.union_comm] using hs.2.2.1
    have hpart : if regime p.1.1 then Rp ≤ TypicalHighPolicy.meanMultiplier N H0 c ξ
        (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) ν0
      else TypicalHighPolicy.meanMultiplier N H0 c ξ
        (regime p.1.1) (owner0 p.1.1) (mixed p.1.1) (publicBids p) ν0 ≤ R := by
      have hh := hg.2.2.2
      cases he : regime p.1.1 <;> simp only [TypicalHighPolicy.PartialGuard,he,ite_true] at * <;>
        exact hh.1
    exact TypicalHighPolicy.physical_support_optimal N H1 H0 c (regime p.1.1)
      (mixed p.1.1) (owner1 p.1.1) (owner0 p.1.1) (publicBids p) ν0 row
      hξ hξ1 hB (fun i => (p.1.2 i).2) hR.le hRp hBRm hs.1.symm hOI hPI hcover
      hs.2.2.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2 hg.2.2.1 hg.2.1 hpart _
      (typicalSampler_support N H1 c ξ R Rp Rm (regime p.1.1) (owner1 p.1.1)
        (mixed p.1.1) (publicBids p) row u).ne'
  · have hq : (fun i => LocalSamplerMean.mean (unequal0 N H0 H1 c ξ B R Rp Rm width ν0 ν1)
        p θ0 (Sum.inl i)) = AtypicalOriginalPosterior.mean N H0 H1 c ξ (publicBids p) false θ0 := by
      funext i
      rw [unequal0_mean N H0 H1 c ξ B R Rp Rm width ν0 ν1 p θ0 hν0 i,if_neg hu]
    rw [hq,unequal1,if_neg hu]
    have hm : (AtypicalOriginalPosterior.markLaw θ0).prob
        AtypicalOriginalPosterior.anyUpper ≤ (H0:ℝ)*π := by
      rw [AtypicalOriginalPosterior.markLaw_eq_of_pushforward θ0 ν0 hν0]
      exact hany
    exact @AtypicalOriginalPosterior.actual_optimal N H0 H1 c R Rp Rm B ξ (publicBids p) true θ0
      ‹IsProbabilityMeasure θ0›
      π hπ ⟨hξ.le,hξ1⟩ (fun i => (p.1.2 i).2) hB hR hRRp hRp hBRm hrare hfirst hm row

end FCAppendix.Affine.Tail04.JoinedHighPolicy
