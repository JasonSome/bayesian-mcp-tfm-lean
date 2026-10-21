import FCAppendix.Affine.Tail04.FocalInsertionOptimal
import FCAppendix.Affine.Tail04.AtypicalOriginalPosterior
import FCAppendix.Affine.Tail04.OriginalCountSampling

set_option maxHeartbeats 600000

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalInsertion
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

abbrev Base (N : ℕ) := (Fin N → ℝ) × ℝ × ℝ
abbrev Public (N : ℕ) := (Fin N → ℝ) × ℝ

lemma measurable_reciprocal (N : ℕ) (I : Finset (Fin N)) :
    Measurable (mixedReciprocalSum I : (Fin N → ℝ) → ℝ) := by
  unfold mixedReciprocalSum
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.div (measurable_pi_apply i)

lemma measurable_baseline (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (ν : FiniteLaw (Marks H)) :
    Measurable (fun b : Fin N → ℝ =>
      TypicalHighPolicy.meanMultiplier N H c ξ reg O I b ν) := by
  unfold TypicalHighPolicy.meanMultiplier FiniteLaw.expect
  apply Finset.measurable_sum
  intro z _
  simp_rw [TypicalHighPolicy.multiplier_formula]
  exact measurable_const.mul (measurable_const.div (measurable_reciprocal N I))

lemma measurable_pair_left (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (fun p : Public N => (pair N H0 H1 c ξ reg O0 O1 I p.1 p.2 ν0 ν1).left) := by

  have hW : Measurable (fun p : Public N => mixedReciprocalSum I p.1) :=
    (measurable_reciprocal N I).comp measurable_fst
  have hL0 : Measurable (fun p : Public N => TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I p.1 ν0) :=
    (measurable_baseline N H0 c ξ reg O0 I ν0).comp measurable_fst
  have hL1 : Measurable (fun p : Public N => TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I p.1 ν1) :=
    (measurable_baseline N H1 c ξ reg O1 I ν1).comp measurable_fst
  have hD : Measurable (fun p : Public N => FocalResponse.denominator ξ p.2 (mixedReciprocalSum I p.1)) := by
    unfold FocalResponse.denominator
    exact measurable_const.mul (measurable_snd.add (measurable_const.div hW))
  have hh := FocalResponse.measurable_solution_left.comp
    (((measurable_snd.sub hL0).div hD).prodMk ((measurable_snd.sub hL1).div hD))
  simpa only [Function.comp_def,Pi.div_apply,Pi.sub_apply,pair,FocalResponse.focalPair] using hh

lemma measurable_pair_right (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (fun p : Public N => (pair N H0 H1 c ξ reg O0 O1 I p.1 p.2 ν0 ν1).right) := by

  have hW : Measurable (fun p : Public N => mixedReciprocalSum I p.1) :=
    (measurable_reciprocal N I).comp measurable_fst
  have hL0 : Measurable (fun p : Public N => TypicalHighPolicy.meanMultiplier N H0 c ξ reg O0 I p.1 ν0) :=
    (measurable_baseline N H0 c ξ reg O0 I ν0).comp measurable_fst
  have hL1 : Measurable (fun p : Public N => TypicalHighPolicy.meanMultiplier N H1 c ξ reg O1 I p.1 ν1) :=
    (measurable_baseline N H1 c ξ reg O1 I ν1).comp measurable_fst
  have hD : Measurable (fun p : Public N => FocalResponse.denominator ξ p.2 (mixedReciprocalSum I p.1)) := by
    unfold FocalResponse.denominator
    exact measurable_const.mul (measurable_snd.add (measurable_const.div hW))
  have hh := FocalResponse.measurable_solution_right.comp
    (((measurable_snd.sub hL0).div hD).prodMk ((measurable_snd.sub hL1).div hD))
  simpa only [Function.comp_def,Pi.div_apply,Pi.sub_apply,pair,FocalResponse.focalPair] using hh

lemma measurable_law_mass (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (S : Finset (Target N H)) :
    Measurable (fun z : Marks H × Base N =>
      (law N H c ξ reg O I z.2.1 z.2.2.1 z.2.2.2 z.1).mass S) := by
  apply measurable_from_prod_countable_right
  intro z
  have hb : Measurable (fun p : Base N => numericalBid H p.1 p.2.1) := by
    apply measurable_pi_lambda
    intro i
    cases i with
    | none => exact measurable_fst.comp measurable_snd
    | some i =>
      cases i with
      | inl i => exact (measurable_pi_apply i).comp measurable_fst
      | inr i => exact measurable_const
  have h := (FocalCapacity.measurable_lottery_mass ξ c (fixed N H reg O z)
    (mixed H I) none S).comp (hb.prodMk (measurable_snd.comp measurable_snd))
  simpa only [Function.comp_def,law] using h

theorem exists_sampler (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) :
    ∃ f : (Base N × Row H R Rp Rm) → unitInterval → Finset (Target N H),
      Measurable (Function.uncurry f) ∧
      (∀ p row u, 0 < (law N H c ξ reg O I p.1 p.2.1 p.2.2
        (marks (signal row))).mass (f (p,row) u)) ∧
      ∀ p row, volume.map (f (p,row))=FiniteLaw.probabilityMeasure
        (law N H c ξ reg O I p.1 p.2.1 p.2.2 (marks (signal row))) := by
  let μ : (Base N × Row H R Rp Rm) → FiniteLaw (Finset (Target N H)) :=
    fun z => law N H c ξ reg O I z.1.1 z.1.2.1 z.1.2.2 (marks (signal z.2))
  have hr : Measurable (fun z : Base N × Row H R Rp Rm => (marks (signal z.2),z.1)) :=
    ((show Measurable (fun row : Row H R Rp Rm => marks (signal row)) from
      continuous_marks.measurable.comp continuous_signal.measurable).comp measurable_snd).prodMk measurable_fst
  have hm (S : Finset (Target N H)) : Measurable (fun z => (μ z).mass S) := by
    simpa only [μ,Function.comp_def] using (measurable_law_mass N H c ξ reg O I S).comp hr
  obtain ⟨f,hf,hs,hl⟩ := Hybrid.exists_support_sampler μ hm
  exact ⟨f,hf,fun p row u => hs (p,row) u,fun p row => hl (p,row)⟩

def sampler (N H c : ℕ) (ξ : ℝ) (reg : Bool) (O I : Finset (Fin N)) (R Rp Rm : ℝ) :
    (Base N × Row H R Rp Rm) → unitInterval → Finset (Target N H) :=
  (exists_sampler N H c ξ reg O I R Rp Rm).choose

lemma measurable_sampler (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) :
    Measurable (Function.uncurry (sampler N H c ξ reg O I R Rp Rm)) :=
  (exists_sampler N H c ξ reg O I R Rp Rm).choose_spec.1

lemma sampler_support (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) (p : Base N) (row : Row H R Rp Rm) (u : unitInterval) :
    0 < (law N H c ξ reg O I p.1 p.2.1 p.2.2 (marks (signal row))).mass
      (sampler N H c ξ reg O I R Rp Rm (p,row) u) :=
  (exists_sampler N H c ξ reg O I R Rp Rm).choose_spec.2.1 p row u

lemma sampler_law (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) (p : Base N) (row : Row H R Rp Rm) :
    volume.map (sampler N H c ξ reg O I R Rp Rm (p,row))=
      FiniteLaw.probabilityMeasure (law N H c ξ reg O I p.1 p.2.1 p.2.2 (marks (signal row))) :=
  (exists_sampler N H c ξ reg O I R Rp Rm).choose_spec.2.2 p row

theorem original_selection_law (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) (p : Base N)
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ] :
    FiniteLaw.ofMeasure (θ.prod volume)
      (fun z : Row H R Rp Rm × unitInterval => sampler N H c ξ reg O I R Rp Rm (p,z.1) z.2)
      ((measurable_sampler N H c ξ reg O I R Rp Rm).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))=
      mixture N H c ξ reg O I p.1 p.2.1 p.2.2 (AtypicalOriginalPosterior.markLaw θ) := by
  apply FiniteLaw.ext_expect
  intro g
  rw [FiniteLaw.expect_ofMeasure]
  have hg : Integrable (fun z : Row H R Rp Rm × unitInterval =>
      g (sampler N H c ξ reg O I R Rp Rm (p,z.1) z.2)) (θ.prod volume) := by
    apply Integrable.of_bound
      ((measurable_of_countable g).comp
        ((measurable_sampler N H c ξ reg O I R Rp Rm).comp
          ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))).aestronglyMeasurable
      (∑ S : Finset (Target N H), |g S|)
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun S _ => abs_nonneg (g S)) (Finset.mem_univ _)
  rw [integral_prod _ hg]
  simp only [mixture,FiniteLaw.expect_finiteMix,AtypicalOriginalPosterior.markLaw_expect]
  apply integral_congr_ae
  exact ae_of_all _ fun row => by
    have hf : Measurable (sampler N H c ξ reg O I R Rp Rm (p,row)) :=
      (measurable_sampler N H c ξ reg O I R Rp Rm).comp (measurable_const.prodMk measurable_id)
    dsimp only
    unfold AtypicalOriginalPosterior.rowMarks
    rw [←LocalSamplerMean.integral_finiteLaw,←sampler_law N H c ξ reg O I R Rp Rm p row,
      integral_map hf.aemeasurable (measurable_of_countable g).aestronglyMeasurable]

lemma original_mean (N H c : ℕ) (ξ : ℝ) (reg : Bool)
    (O I : Finset (Fin N)) (R Rp Rm : ℝ) (p : Base N)
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ] (i : Target N H) :
    LocalSamplerMean.mean (sampler N H c ξ reg O I R Rp Rm) p θ i=
      (mixture N H c ξ reg O I p.1 p.2.1 p.2.2 (AtypicalOriginalPosterior.markLaw θ)).prob
        (fun S => i∈S) := by
  rw [LocalSamplerMean.of_finiteLaw _ (measurable_sampler N H c ξ reg O I R Rp Rm) p θ
    (fun row => law N H c ξ reg O I p.1 p.2.1 p.2.2 (marks (signal row)))
    (fun row => sampler_law N H c ξ reg O I R Rp Rm p row)]
  simp only [mixture,FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix,
    AtypicalOriginalPosterior.markLaw_expect,AtypicalOriginalPosterior.rowMarks]

def zeroSampler (N H0 H1 c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    (Public N × Row H0 R Rp Rm) → unitInterval → Finset (Target N H0) :=
  fun z u => sampler N H0 c ξ reg O0 I R Rp Rm
    ((z.1.1,z.1.2,(pair N H0 H1 c ξ reg O0 O1 I z.1.1 z.1.2 ν0 ν1).left),z.2) u

def oneSampler (N H0 H1 c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    (Public N × Row H1 R Rp Rm) → unitInterval → Finset (Target N H1) :=
  fun z u => sampler N H1 c ξ reg O1 I R Rp Rm
    ((z.1.1,z.1.2,(pair N H0 H1 c ξ reg O0 O1 I z.1.1 z.1.2 ν0 ν1).right),z.2) u

lemma measurable_zeroSampler (N H0 H1 c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (Function.uncurry (zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)) := by
  have hp : Measurable (fun z : (Public N × Row H0 R Rp Rm) × unitInterval => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hm := ((hp.fst.prodMk (hp.snd.prodMk
      ((measurable_pair_left N H0 H1 c ξ reg O0 O1 I ν0 ν1).comp hp))).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hh := (measurable_sampler N H0 c ξ reg O0 I R Rp Rm).comp hm
  change Measurable (fun z : (Public N × Row H0 R Rp Rm) × unitInterval =>
    sampler N H0 c ξ reg O0 I R Rp Rm
      ((z.1.1.1,z.1.1.2,(pair N H0 H1 c ξ reg O0 O1 I z.1.1.1 z.1.1.2 ν0 ν1).left),z.1.2) z.2)
  simpa only [Function.comp_def,Function.uncurry] using hh

lemma measurable_oneSampler (N H0 H1 c : ℕ) (ξ R Rp Rm : ℝ) (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (Function.uncurry (oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)) := by
  have hp : Measurable (fun z : (Public N × Row H1 R Rp Rm) × unitInterval => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hm := ((hp.fst.prodMk (hp.snd.prodMk
      ((measurable_pair_right N H0 H1 c ξ reg O0 O1 I ν0 ν1).comp hp))).prodMk
    (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hh := (measurable_sampler N H1 c ξ reg O1 I R Rp Rm).comp hm
  change Measurable (fun z : (Public N × Row H1 R Rp Rm) × unitInterval =>
    sampler N H1 c ξ reg O1 I R Rp Rm
      ((z.1.1.1,z.1.1.2,(pair N H0 H1 c ξ reg O0 O1 I z.1.1.1 z.1.1.2 ν0 ν1).right),z.1.2) z.2)
  simpa only [Function.comp_def,Function.uncurry] using hh

theorem pair_sampler_card (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ} (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b) (hg1 : LocalGuard N H1 c ξ B reg O1 I b) :
    (∀ row u,(zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u).card=c) ∧
    (∀ row u,(oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u).card=c) := by
  obtain ⟨hOO,hIO,hcover,hc0,hc1,hI⟩ := hs
  let pp := pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
  constructor
  · intro row u
    change (sampler N H0 c ξ reg O0 I R Rp Rm ((b,y,pp.left),row) u).card = c
    exact (implements N H0 c reg O0 I b y pp.left hξ hξ1 hb pp.left_mem
      (hIO.mono_right Finset.subset_union_left).symm hc0 hI hg0 (marks (signal row))).1
      (sampler N H0 c ξ reg O0 I R Rp Rm ((b,y,pp.left),row) u)
      (sampler_support N H0 c ξ reg O0 I R Rp Rm (b,y,pp.left) row u).ne'
  · intro row u
    change (sampler N H1 c ξ reg O1 I R Rp Rm ((b,y,pp.right),row) u).card = c
    exact (implements N H1 c reg O1 I b y pp.right hξ hξ1 hb pp.right_mem
      (hIO.mono_right Finset.subset_union_right).symm hc1 hI hg1 (marks (signal row))).1
      (sampler N H1 c ξ reg O1 I R Rp Rm ((b,y,pp.right),row) u)
      (sampler_support N H1 c ξ reg O1 I R Rp Rm (b,y,pp.right) row u).ne'

theorem original_focal_means (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ} (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b) (hg1 : LocalGuard N H1 c ξ B reg O1 I b) :
    let ν0:=AtypicalOriginalPosterior.markLaw θ0
    let ν1:=AtypicalOriginalPosterior.markLaw θ1
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    LocalSamplerMean.mean (zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1) (b,y) θ0 none=p.left ∧
    LocalSamplerMean.mean (oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1) (b,y) θ1 none=p.right := by
  obtain ⟨hOO,hIO,hcover,hc0,hc1,hI⟩ := hs
  dsimp only
  constructor
  · change LocalSamplerMean.mean (sampler N H0 c ξ reg O0 I R Rp Rm)
      (b,y,(pair _ _ _ _ _ _ _ _ _ _ _ _ _).left) θ0 none=_
    rw [original_mean]
    exact focal_marginal N H0 c reg O0 I b y _ _ hξ hξ1 hb
      (pair _ _ _ _ _ _ _ _ _ _ _ _ _).left_mem
      (hIO.mono_right Finset.subset_union_left).symm hc0 hI hg0
  · change LocalSamplerMean.mean (sampler N H1 c ξ reg O1 I R Rp Rm)
      (b,y,(pair _ _ _ _ _ _ _ _ _ _ _ _ _).right) θ1 none=_
    rw [original_mean]
    exact focal_marginal N H1 c reg O1 I b y _ _ hξ hξ1 hb
      (pair _ _ _ _ _ _ _ _ _ _ _ _ _).right_mem
      (hIO.mono_right Finset.subset_union_right).symm hc1 hI hg1

theorem original_focal_count (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ} (reg : Bool)
    (O0 O1 I : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b) (hg1 : LocalGuard N H1 c ξ B reg O1 I b) :
    let ν0:=AtypicalOriginalPosterior.markLaw θ0
    let ν1:=AtypicalOriginalPosterior.markLaw θ1
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    originalIndependentCountLaw
      (zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (measurable_zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (measurable_oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1)
      (b,y) θ0 θ1 none none=
      twoCoinCountLaw p.left p.right p.left_mem.1 p.left_mem.2 p.right_mem.1 p.right_mem.2 := by
  dsimp only
  rw [originalIndependentCountLaw_eq]
  have hh := original_focal_means N H0 H1 c reg O0 O1 I b y θ0 θ1 hξ hξ1 hb hs hg0 hg1
  simp only [hh.1,hh.2]

theorem pair_sampler_optimal (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hB : 1≤ B) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hy : 0≤ y)
    (hRp : Rp<1) (hBRm : B< Rm)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b) (hg1 : LocalGuard N H1 c ξ B reg O1 I b)
    (hp0 : PartialGuard N H0 c ξ R Rp reg O0 I b ν0)
    (hp1 : PartialGuard N H1 c ξ R Rp reg O1 I b ν1) :
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    (∀ row u,Finite.Optimal c
      (receipt b y (activeMean N H1 c ξ reg O1 I b y p.right ν1) p.right ξ row)
      (zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u)) ∧
    (∀ row u,Finite.Optimal c
      (receipt b y (activeMean N H0 c ξ reg O0 I b y p.left ν0) p.left ξ row)
      (oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u)) := by
  have h := pair_physical_support_optimal N H0 H1 c reg I O0 O1 b y ν0 ν1
    hξ hξ1 hB hb hy hRp hBRm hs hg0 hg1 hp0 hp1
  dsimp only
  exact ⟨fun row u => h.1 row
    (sampler N H0 c ξ reg O0 I R Rp Rm
      ((b,y,(pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1).left),row) u)
    (sampler_support N H0 c ξ reg O0 I R Rp Rm
      (b,y,(pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1).left) row u).ne',
    fun row u => h.2 row
      (sampler N H1 c ξ reg O1 I R Rp Rm
        ((b,y,(pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1).right),row) u)
      (sampler_support N H1 c ξ reg O1 I R Rp Rm
        (b,y,(pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1).right) row u).ne'⟩

theorem pair_sampler_threshold (N H0 H1 c : ℕ) {ξ B R Rp Rm : ℝ}
    (reg : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ) (y : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hB : 1≤ B) (hb : ∀ i,b i∈Icc (1:ℝ) B) (hy : 0≤ y)
    (hRp : Rp<1) (hBRm : B< Rm)
    (hs : TypicalHighPolicy.Structural N H0 H1 c I O0 O1)
    (hg0 : LocalGuard N H0 c ξ B reg O0 I b) (hg1 : LocalGuard N H1 c ξ B reg O1 I b)
    (hp0 : PartialGuard N H0 c ξ R Rp reg O0 I b ν0)
    (hp1 : PartialGuard N H1 c ξ R Rp reg O1 I b ν1) :
    let p:=pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
    (∀ row u,Threshold c
      (receipt b y (activeMean N H1 c ξ reg O1 I b y p.right ν1) p.right ξ row)
      (zeroSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u)
      (meanPrice N H1 c ξ reg O1 I b p.right ν1)) ∧
    (∀ row u,Threshold c
      (receipt b y (activeMean N H0 c ξ reg O0 I b y p.left ν0) p.left ξ row)
      (oneSampler N H0 H1 c ξ R Rp Rm reg O0 O1 I ν0 ν1 ((b,y),row) u)
      (meanPrice N H0 c ξ reg O0 I b p.left ν0)) := by
  obtain ⟨hOO,hIO,hcover,hc0,hc1,hI⟩ := hs
  have hO0I : Disjoint O0 I := (hIO.mono_right Finset.subset_union_left).symm
  have hO1I : Disjoint O1 I := (hIO.mono_right Finset.subset_union_right).symm
  have hW := mixedReciprocalSum_pos I b hI
    (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (hb i).1)
  have hsc := pair_scalar_optimal N H0 H1 c ξ reg O0 O1 I b y ν0 ν1 hξ hy hW
  let pp := pair N H0 H1 c ξ reg O0 O1 I b y ν0 ν1
  dsimp only
  constructor
  · intro row u
    exact physical_support_threshold N H0 H1 c reg I O0 O1 b y pp.left pp.right ν1 row hξ hξ1 hB hb
      pp.left_mem pp.right_mem hRp hBRm hOO hO0I hO1I hcover hc0 hc1 hI hg0 hg1 hp1 hsc.1
      (sampler N H0 c ξ reg O0 I R Rp Rm ((b,y,pp.left),row) u)
      (sampler_support N H0 c ξ reg O0 I R Rp Rm (b,y,pp.left) row u).ne'
  · intro row u
    have hc : I∪(O1∪O0)=Finset.univ := by simpa only [Finset.union_comm O1 O0] using hcover
    exact physical_support_threshold N H1 H0 c reg I O1 O0 b y pp.right pp.left ν0 row hξ hξ1 hB hb
      pp.right_mem pp.left_mem hRp hBRm hOO.symm hO1I hO0I hc hc1 hc0 hI hg1 hg0 hp0 hsc.2
      (sampler N H1 c ξ reg O1 I R Rp Rm ((b,y,pp.right),row) u)
      (sampler_support N H1 c ξ reg O1 I R Rp Rm (b,y,pp.right) row u).ne'

end FCAppendix.Affine.Tail04.FocalInsertion
