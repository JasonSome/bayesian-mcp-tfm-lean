import FCAppendix.Affine.Uniform06.CanonicalRareDerivative
import FCAppendix.Affine.Uniform06.CrossoverRankDensity
import FCAppendix.Affine.Uniform06.CompactStieltjes
import FCAppendix.Affine.Uniform06.WeightedBorelContraction
import FCAppendix.Finite.PPITailArea

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PrimitiveStieltjesMeasures

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open PureRankCounts PureRankProbability PurePivotalSource PureDuplicateIntervals PureDuplicateRare
open LiteralExperiment LiteralPrefixStieltjes LiteralRankIC LiteralKernelDecomposition
open LiteralLowDuplicate LiteralPureComponents LowRankMeasures CrossoverRankPreparation EqualCanonicalRegularity
open CompactStieltjes SupportIntervalDomination ScaledMeasure ICAbsorption
open scoped BigOperators

section MeasureTools

theorem continuousOn_of_monotone_increment (f : ℝ → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ b,ν {b}=0)
    {lo hi : ℝ} (hf : MonotoneOn f (Icc lo hi))
    (hinc : ∀ a ∈ Icc lo hi,∀ b ∈ Icc lo hi,a ≤ b →
      f b-f a ≤ ν.real (Ioc a b)) : ContinuousOn f (Icc lo hi) := by
  let V := cumulative ν
  have hcV : Continuous V := continuous_cumulative ν hν
  have hmV : Monotone V := by
    intro a b hab
    have hh := cumulative_increment ν hab
    have hn : 0 ≤ ν.real (Ioc a b) := measureReal_nonneg
    dsimp [V]
    linarith
  have hd {a b : ℝ} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
      dist (f a) (f b) ≤ dist (V a) (V b) := by
    rcases le_total a b with hab | hba
    · rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hf ha hb hab)),neg_sub,
        Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hmV hab)),neg_sub]
      have hh := hinc a ha b hb hab
      have he := cumulative_increment ν hab
      dsimp [V]
      linarith
    · rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hf hb ha hba)),
        Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmV hba))]
      have hh := hinc b hb a ha hba
      have he := cumulative_increment ν hba
      dsimp [V]
      linarith
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hnear := (hcV.continuousAt.tendsto.mono_left
    (show 𝓝[Icc lo hi] x ≤ 𝓝 x from nhdsWithin_le_nhds))
      (Metric.ball_mem_nhds (V x) hε)
  filter_upwards [self_mem_nhdsWithin,hnear] with y hy hVy
  exact (hd hy hx).trans_lt hVy

theorem restricted_domination_of_short_intervals
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ b,μ {b}=0) (hν : ∀ b,ν {b}=0)
    {lo hi δ : ℝ} (hδ : 0 < δ)
    (hI : ∀ a ∈ Icc lo hi,∀ b ∈ Icc lo hi,a ≤ b → b-a ≤ δ →
      μ.real (Ioc a b) ≤ ν.real (Ioc a b)) :
    μ.restrict (Ioc lo hi) ≤ ν.restrict (Ioc lo hi) := by
  apply measure_restrict_le_of_Ioc_real_le μ ν hμ hν
  let F := fun b => cumulative ν b-cumulative μ b
  have hm : MonotoneOn F (Icc lo hi) := by
    apply monotoneOn_of_uniform_short_steps hδ
    intro a ha b hb hab hsmall
    have hh := hI a ha b hb hab hsmall
    have hνi := cumulative_increment ν hab
    have hμi := cumulative_increment μ hab
    dsimp [F]
    linarith
  intro a ha b hb hab
  have hh := hm ha hb hab
  have hνi := cumulative_increment ν hab
  have hμi := cumulative_increment μ hab
  dsimp [F] at hh
  linarith

def weightedMeasure (μ : Measure ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun b => ENNReal.ofReal (f b))

theorem integrable_bounded_weight (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) {C : ℝ}
    (hbound : ∀ b,f b ∈ Icc (0:ℝ) C) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun b => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hbound b).1]
    exact (hbound b).2

theorem weightedMeasure_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) {C : ℝ}
    (hbound : ∀ b,f b ∈ Icc (0:ℝ) C) : IsFiniteMeasure (weightedMeasure μ f) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_bounded_weight μ f hf hbound)
    (Filter.Eventually.of_forall fun b => (hbound b).1)]
  exact ENNReal.ofReal_ne_top

theorem weightedMeasure_atomless (μ : Measure ℝ) (hμ : ∀ b,μ {b}=0)
    (f : ℝ → ℝ) (b : ℝ) : weightedMeasure μ f {b}=0 :=
  withDensity_absolutelyContinuous μ _ (hμ b)

theorem weightedMeasure_real_apply (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) {C : ℝ}
    (hbound : ∀ b,f b ∈ Icc (0:ℝ) C) {A : Set ℝ} (hA : MeasurableSet A) :
    (weightedMeasure μ f).real A=∫ b in A,f b ∂μ := by
  have hi : Integrable f (μ.restrict A) :=
    (integrable_bounded_weight μ f hf hbound).mono_measure Measure.restrict_le_self
  have hn : ∀ᵐ b ∂μ.restrict A,0 ≤ f b := Filter.Eventually.of_forall fun b => (hbound b).1
  rw [Measure.real,weightedMeasure,withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hi hn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)]

theorem weightedMeasure_Ioc_right (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Measurable f) (hm : Monotone f) {C : ℝ}
    (hbound : ∀ b,f b ∈ Icc (0:ℝ) C) (a b : ℝ) :
    (weightedMeasure μ f).real (Ioc a b) ≤ f b*μ.real (Ioc a b) := by
  rw [weightedMeasure_real_apply μ f hf hbound measurableSet_Ioc]
  have hi : Integrable f (μ.restrict (Ioc a b)) :=
    (integrable_bounded_weight μ f hf hbound).mono_measure Measure.restrict_le_self
  have hh := integral_mono_ae hi (integrable_const (f b)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hm hx.2)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

end MeasureTools

section SourceWeight

def rankKernel (i : Row) (m : ℕ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b)

theorem rankKernel_eq_probability (i : Row) (m : ℕ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    rankKernel i m G b=
      (Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) G).real
        {ω | PiBinomial.count (higherAtSet b) Finset.univ ω < capacity m} := by
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  rw [iid_count_lt_eq_binomBelow _ _ (measurableSet_higherAtSet b),
    source_higher_probability (cutoff_pos i).le (cutoff_lt_one i).le G b]
  simp only [Finset.card_univ,Fintype.card_fin,rankKernel,Rank.pureRank]

theorem rankKernel_bounds (i : Row) (m : ℕ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    rankKernel i m G b ∈ Icc (0:ℝ) 1 := by
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  rw [rankKernel_eq_probability]
  exact ⟨measureReal_nonneg,measureReal_le_one⟩

theorem rankKernel_monotone (i : Row) (m : ℕ)
    (G : Measure ℝ) [IsProbabilityMeasure G] : Monotone (rankKernel i m G) := by
  classical
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  intro a b hab
  rw [rankKernel_eq_probability,rankKernel_eq_probability]
  refine measureReal_mono (μ := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) G) ?_ (measure_ne_top _ _)
  intro ω hω
  have hc : PiBinomial.count (higherAtSet b) Finset.univ ω ≤
      PiBinomial.count (higherAtSet a) Finset.univ ω := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
      higherAt_antitone hab (Finset.mem_filter.mp hj).2⟩
  exact hc.trans_lt hω

theorem rankKernel_continuous (i : Row) (m : ℕ)
    (G : Measure ℝ) [IsFiniteMeasure G] (hatom : ∀ b,G {b}=0) :
    Continuous (rankKernel i m G) := by
  exact (Bayes.continuous_binomBelow (m-1) (capacity m)).comp
    (continuous_const.sub (continuous_sourceRank (cutoff i) G hatom))

def firstWeight (i : Row) (m : ℕ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  ((m:ℝ)/80000)*rankKernel i m G b

def weightedRank (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  weightedMeasure (bidMeasure i G) (firstWeight i m (G.map Prod.snd))

theorem firstWeight_bounds (i : Row) (m : ℕ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    firstWeight i m G b ∈ Icc (0:ℝ) ((m:ℝ)/80000) := by
  have hq := rankKernel_bounds i m G b
  have hm : 0 ≤ (m:ℝ)/80000 := by positivity
  exact ⟨mul_nonneg hm hq.1,by simpa only [firstWeight,mul_one] using! mul_le_mul_of_nonneg_left hq.2 hm⟩

theorem source_success_stieltjes (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hmenu : ∀ᵐ p ∂G,p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)))
    (hatom : ∀ b,(G.map Prod.snd) {b}=0)
    (g : GuardData) {lo H : ℝ} (hlo : 0 < lo) (hlH : lo ≤ H)
    (hg : PrefixConditions (xi i) g H) (margin : (Fin (m-1) → Fin 4) → ℝ) :
    ∃ F : StieltjesFunction ℝ,Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
      (∀ b ∈ Icc lo H,F b=sourceSuccess i m G g margin b) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hH : 0 < H := hlo.trans_le hlH
  have hco := (source_extensions_continuous i m G hmenu hatom g hH hg margin).1
  have hc : ContinuousOn (sourceSuccess i m G g margin) (Icc lo H) := by
    apply (hco.mono (fun _ hb => hlo.trans_le hb.1)).congr
    intro b hb
    exact (source_extensions_agree i m G g hg margin (hlo.trans_le hb.1) hb.2).1
  have hm := (actual_prefix_monotone (κ := kappa i) (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ])
    (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) Gb
    (source_floor_bid_nonnegative i G (hmenu.mono fun _ h => h.1))
    (capacity m) g hg margin).1
  have hmono : MonotoneOn (sourceSuccess i m G g margin) (Icc lo H) :=
    hm.mono (fun _ hb => ⟨(hlo.trans_le hb.1).le,hb.2⟩)
  let F := ofMonotoneOn (sourceSuccess i m G g margin) hlH hmono hc
  exact ⟨F,ofMonotoneOn_continuous _ hlH hmono hc,
    fun b => (source_first_duplicate_bounds i m G g margin (clip lo H b)).1,
    fun b hb => ofMonotoneOn_eq _ hlH hmono hc hb⟩

theorem eventually_source_first_stieltjes_lower (i : Row) :
    ∀ᶠ m : ℕ in atTop,∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      (∀ᵐ p ∂G,p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i))) →
      (∀ b,(G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (H lo : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      0 < lo → lo ≤ H → PrefixConditions (xi i) g H →
      (∀ b,b ∈ Ioc (0:ℝ) H → sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i) →
      ∃ F : StieltjesFunction ℝ,Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
        (∀ b ∈ Icc lo H,F b=sourceSuccess i m G g margin b) ∧
        (weightedRank i m G).restrict (Ioc lo H) ≤ F.measure.restrict (Ioc lo H) := by
  filter_upwards [source_actual_first_pivotal_interval i] with m hpiv
  intro G hG hmenu hatom g H lo margin hlo hloH hg hM
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hnon : ∀ᵐ p ∂G,0 ≤ p.2 := by
    filter_upwards [hmenu] with p hp
    have hf : 0 ≤ LowChernoff.physicalFloor i p.1 := by unfold LowChernoff.physicalFloor; positivity
    exact hf.trans hp.1
  obtain ⟨δ,hδ,hinterval⟩ := hpiv G hG hnon hatom g H margin hg hM
  obtain ⟨F,hFc,hFb,hFe⟩ := source_success_stieltjes i m G hmenu hatom g hlo hloH hg margin
  letI := finite_of_bounds F hFb
  have hwc : Continuous (firstWeight i m Gb) :=
    continuous_const.mul (rankKernel_continuous i m Gb hatom)
  have hwb := firstWeight_bounds i m Gb
  have hwm : Monotone (firstWeight i m Gb) :=
    (rankKernel_monotone i m Gb).const_mul (by positivity)
  letI : IsFiniteMeasure (weightedRank i m G) := weightedMeasure_finite
    (bidMeasure i G) _ hwc.measurable hwb
  have hμatom (b : ℝ) : bidMeasure i G {b}=0 := by simp [bidMeasure,hatom b]
  refine ⟨F,hFc,hFb,hFe,?_⟩
  apply restricted_domination_of_short_intervals (weightedRank i m G) F.measure
    (weightedMeasure_atomless _ hμatom _) (continuous_measure_atomless F hFc) hδ
  intro a ha b hb hab hstep
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hu := weightedMeasure_Ioc_right (bidMeasure i G) _ hwc.measurable hwm hwb a b
  have hl := hinterval a b (hlo.trans_le ha.1) hab hb.2 hstep
  rw [measure_real_Ioc F hab.le,hFe b hb,hFe a ha]
  apply hu.trans
  simpa only [firstWeight,rankKernel,bidMeasure_real] using hl

end SourceWeight

section PureUpper

def pureComparison (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) : Measure ℝ :=
  ENNReal.ofReal ((m-1:ℕ)*Real.exp (-(9/1000000:ℝ)*m)) •
    (bidMeasure i G+scaledRankMeasure (kappa i) (bidMeasure i G))

private instance scaledRankMeasure_finite (κ : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (scaledRankMeasure κ μ) := by
  unfold scaledRankMeasure
  infer_instance

instance pureComparison_finite (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsFiniteMeasure G] : IsFiniteMeasure (pureComparison i m G) := by
  exact (bidMeasure i G+scaledRankMeasure (kappa i) (bidMeasure i G)).smul_finite ENNReal.ofReal_ne_top

theorem pureComparison_atomless (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (hatom : ∀ b,(G.map Prod.snd) {b}=0) (b : ℝ) : pureComparison i m G {b}=0 := by
  have hμ : ∀ b,bidMeasure i G {b}=0 := fun b => by simp [bidMeasure,hatom b]
  have hκ : kappa i ≠ 0 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  rw [pureComparison,Measure.smul_apply,Measure.add_apply,hμ,
    scaledRankMeasure_atomless _ hμ hκ]
  simp

theorem pureComparison_interval (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsFiniteMeasure G] (a b : ℝ) :
    (pureComparison i m G).real (Ioc a b)=
      ((m-1:ℕ)*Real.exp (-(9/1000000:ℝ)*m))*
        (cutoff i*(G.map Prod.snd).real (Ioc a b)+
          cutoff i*(G.map Prod.snd).real (Ioc (kappa i*a) (kappa i*b))) := by
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  rw [pureComparison,measureReal_ennreal_smul_apply,
    ENNReal.toReal_ofReal (by positivity),
    measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _),
    scaledRankMeasure_real_apply hκ.ne' _ measurableSet_Ioc,scaledSet_Ioc hκ,
    bidMeasure_real,bidMeasure_real]

theorem source_pure_duplicate_stieltjes_upper (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b,(G.map Prod.snd) {b}=0)
    {m : ℕ} (hm : 4 ≤ m) {lo H : ℝ}
    (hlo : 0 < lo) (hloH : lo ≤ H) (hHM : H ≤ RankCutoff.Mstar i) :
    ∃ D : StieltjesFunction ℝ,Continuous D ∧ (∀ b,D b ∈ Icc (0:ℝ) 1) ∧
      (∀ b ∈ Icc lo H,D b=expectedPureDuplicate (N := m-1)
        (cutoff i) 0 (1-cutoff i) (kappa i) (G.map Prod.snd) (capacity m) b) ∧
      D.measure.restrict (Ioc lo H) ≤ (pureComparison i m G).restrict (Ioc lo H) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI := sourceRivalLaw_probability (cutoff_mem i) Gb
  let P := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) Gb
  let d := expectedPureDuplicate (N := m-1) (cutoff i) 0 (1-cutoff i) (kappa i) Gb (capacity m)
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hmono : Monotone d := by
    intro a b hab
    exact integral_mono (integrable_rowPureDuplicate _ _ _ P)
      (integrable_rowPureDuplicate _ _ _ P)
      (fun ω => raw_duplicate_monotone hκ (capacity m) ω hab)
  have hbound (b : ℝ) : d b ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact integral_nonneg fun ω => (rowPureDuplicate_bounds _ _ _ ω).1
    · simpa using! integral_mono (integrable_rowPureDuplicate _ _ _ P)
        (integrable_const (1:ℝ)) (fun ω => (rowPureDuplicate_bounds _ _ _ ω).2)
  have hinc : ∀ a ∈ Icc lo H,∀ b ∈ Icc lo H,a ≤ b →
      d b-d a ≤ (pureComparison i m G).real (Ioc a b) := by
    intro a ha b hb hab
    rcases hab.eq_or_lt with rfl | hab
    · simp
    rw [pureComparison_interval]
    have hh := source_pure_duplicate_stieltjes_interval i G hvalue hfloor hatom hm
      a b (hlo.trans_le ha.1) hab (hb.2.trans hHM)
    convert! hh using 1
    ring
  have hco := continuousOn_of_monotone_increment d (pureComparison i m G)
    (pureComparison_atomless i m G hatom) (hmono.monotoneOn (Icc lo H)) hinc
  let D := ofMonotoneOn d hloH (hmono.monotoneOn (Icc lo H)) hco
  have hDc : Continuous D := ofMonotoneOn_continuous d hloH (hmono.monotoneOn (Icc lo H)) hco
  have hDb : ∀ b,D b ∈ Icc (0:ℝ) 1 := fun b => hbound (clip lo H b)
  have hDe : ∀ b ∈ Icc lo H,D b=d b := fun b hb => ofMonotoneOn_eq d hloH (hmono.monotoneOn (Icc lo H)) hco hb
  letI := finite_of_bounds D hDb
  refine ⟨D,hDc,hDb,hDe,?_⟩
  apply measure_restrict_le_of_Ioc_real_le D.measure (pureComparison i m G)
    (continuous_measure_atomless D hDc) (pureComparison_atomless i m G hatom)
  intro a ha b hb hab
  rw [measure_real_Ioc D hab,hDe a ha,hDe b hb]
  exact hinc a ha b hb hab

theorem source_actual_pure_duplicate_stieltjes_upper (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b,(G.map Prod.snd) {b}=0)
    {m : ℕ} (hm : 4 ≤ m) {lo H : ℝ}
    (hlo : 0 < lo) (hloH : lo ≤ H) (hHM : H ≤ RankCutoff.Mstar i) :
    ∃ D : StieltjesFunction ℝ,Continuous D ∧ (∀ b,D b ∈ Icc (0:ℝ) 1) ∧
      (∀ b ∈ Icc lo H,D b=sourcePureDuplicate i m G b) ∧
      D.measure.restrict (Ioc lo H) ≤ (pureComparison i m G).restrict (Ioc lo H) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI := sourceRivalLaw_probability (cutoff_mem i) Gb
  let P := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) Gb
  let d := sourcePureDuplicate i m G
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hmono : Monotone d := by
    intro a b hab
    apply integral_mono (integrable_rowUnequalPureDuplicate _ _ _ P)
      (integrable_rowUnequalPureDuplicate _ _ _ P)
    intro ω
    unfold rowUnequalPureDuplicate
    split_ifs
    · exact le_rfl
    · exact raw_duplicate_monotone hκ (capacity m) ω hab
  have hbound (b : ℝ) : d b ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact integral_nonneg fun ω => (row_unequal_duplicate_bounds _ _ _ ω).1
    · simpa using! integral_mono (integrable_rowUnequalPureDuplicate _ _ _ P)
        (integrable_const (1:ℝ)) (fun ω => (row_unequal_duplicate_bounds _ _ _ ω).2.trans (rowPureDuplicate_bounds _ _ _ ω).2)
  have hinc : ∀ a ∈ Icc lo H,∀ b ∈ Icc lo H,a ≤ b →
      d b-d a ≤ (pureComparison i m G).real (Ioc a b) := by
    intro a ha b hb hab
    rcases hab.eq_or_lt with rfl | hab
    · simp
    rw [pureComparison_interval]
    have hraw := source_pure_duplicate_stieltjes_interval i G hvalue hfloor hatom hm
      a b (hlo.trans_le ha.1) hab (hb.2.trans hHM)
    have hmask := CrossoverRankDensity.unequal_duplicate_increment_le_pure
      (cutoff_mem i) hκ hab.le Gb (m-1) (capacity m)
    convert! hmask.trans hraw using 1
    ring
  have hco := continuousOn_of_monotone_increment d (pureComparison i m G)
    (pureComparison_atomless i m G hatom) (hmono.monotoneOn (Icc lo H)) hinc
  let D := ofMonotoneOn d hloH (hmono.monotoneOn (Icc lo H)) hco
  have hDc : Continuous D := ofMonotoneOn_continuous d hloH (hmono.monotoneOn (Icc lo H)) hco
  have hDb : ∀ b,D b ∈ Icc (0:ℝ) 1 := fun b => hbound (clip lo H b)
  have hDe : ∀ b ∈ Icc lo H,D b=d b := fun b hb => ofMonotoneOn_eq d hloH (hmono.monotoneOn (Icc lo H)) hco hb
  letI := finite_of_bounds D hDb
  refine ⟨D,hDc,hDb,hDe,?_⟩
  apply measure_restrict_le_of_Ioc_real_le D.measure (pureComparison i m G)
    (continuous_measure_atomless D hDc) (pureComparison_atomless i m G hatom)
  intro a ha b hb hab
  rw [measure_real_Ioc D hab,hDe a ha,hDe b hb]
  exact hinc a ha b hb hab

end PureUpper

section ActualCanonical
variable {N : ℕ}

theorem row_low_canonical_duplicate_eq_equal {ξ B : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (g : GuardData)
    (hg : PrefixConditions ξ g B) (margin : (Fin N → Fin 4) → ℝ)
    {b : ℝ} (hb : b ≤ g.multiplier-g.radius) (ω : Fin N → RowRival) :
    rowCanonicalDuplicate ξ c g margin b ω=equalDuplicate ξ c b ω := by
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    simp only [rowCanonicalDuplicate,equalDuplicate,if_pos heT,if_pos he,
      row_complement_eq_equal ξ c b ω he]
  · have heT : ¬(patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have hz := (SourceGuardGeometry.canonical_low_focal_zero hξ hξ1
      {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.lower_pos (rowBids_outside c b ω) 0
      (by simpa only [rowBids,Fin.cons_zero] using hb)).2
    simpa only [rowCanonicalDuplicate,equalDuplicate,if_neg heT,if_neg he,
      canonicalLaw_update_countMargin] using hz

theorem source_low_canonical_duplicate_eq_equal (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) (g : GuardData) {B : ℝ}
    (hg : PrefixConditions (xi i) g B) (margin : (Fin (m-1) → Fin 4) → ℝ)
    {b : ℝ} (hb : b ≤ g.multiplier-g.radius) :
    sourceCanonicalDuplicate i m G g margin b=
      expectedEqualDuplicate (Measure.pi fun _ : Fin (m-1) =>
        sourceRivalLaw (cutoff i) (G.map Prod.snd)) (xi i) (capacity m) b := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω => row_low_canonical_duplicate_eq_equal
    (xi_pos i) (by cases i <;> norm_num [xi,xiQ,etaQ]) (capacity m) g hg margin hb ω

def canonicalRare (i : Row) (m : ℕ) : ℝ :=
  Real.exp ((LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
    (m-1:ℕ)*((LowChernoff.thetaQ i:ℝ)*rho+LowChernoff.rankI0 i+LowChernoff.sourceGap i))

attribute [local irreducible] sourceCanonicalDuplicate expectedEqualDuplicate

theorem source_canonical_duplicate_derivative_ae (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 2 ≤ m) (g : GuardData) {B : ℝ}
    (hg : PrefixConditions (xi i) g B)
    (hsmall : (501/1000:ℝ)*cutoff i ≤ g.multiplier-g.radius)
    (margin : (Fin (m-1) → Fin 4) → ℝ) :
    ∀ᵐ b ∂volume,b ∈ Ioo (0:ℝ) ((501/1000:ℝ)*cutoff i) →
      DifferentiableAt ℝ (sourceCanonicalDuplicate i m G g margin) b ∧
      0 ≤ deriv (sourceCanonicalDuplicate i m G g margin) b ∧
      deriv (sourceCanonicalDuplicate i m G g margin) b ≤ 2*canonicalRare i m/(xi i*b) := by
  filter_upwards [CanonicalRareDerivative.source_equal_duplicate_derivative_ae i G hvalue hfloor hm]
    with b hder hb
  have hd := hder hb
  have heq : sourceCanonicalDuplicate i m G g margin =ᶠ[𝓝 b]
      expectedEqualDuplicate (Measure.pi fun _ : Fin (m-1) =>
        sourceRivalLaw (cutoff i) (G.map Prod.snd)) (xi i) (capacity m) := by
    filter_upwards [Iio_mem_nhds hb.2] with z hz
    exact source_low_canonical_duplicate_eq_equal i m G g hg margin (hz.le.trans hsmall)
  have ha := hd.1.hasDerivAt.congr_of_eventuallyEq heq
  refine ⟨ha.differentiableAt,?_,?_⟩
  · rw [ha.deriv]
    exact hd.2.1
  · rw [ha.deriv]
    exact hd.2.2

end ActualCanonical

structure PrimitiveStieltjesBounds (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ) (lo H : ℝ) where
  success : StieltjesFunction ℝ
  pureDuplicate : StieltjesFunction ℝ
  success_continuous : Continuous success
  duplicate_continuous : Continuous pureDuplicate
  success_bounds : ∀ b,success b ∈ Icc (0:ℝ) 1
  duplicate_bounds : ∀ b,pureDuplicate b ∈ Icc (0:ℝ) 1
  success_agrees : ∀ b ∈ Icc lo H,success b=sourceSuccess i m G g margin b
  duplicate_agrees : ∀ b ∈ Icc lo H,pureDuplicate b=sourcePureDuplicate i m G b
  first_lower : (weightedRank i m G).restrict (Ioc lo H) ≤ success.measure.restrict (Ioc lo H)
  pure_upper : pureDuplicate.measure.restrict (Ioc lo H) ≤ (pureComparison i m G).restrict (Ioc lo H)
  canonical_derivative : ∀ᵐ b ∂volume,b ∈ Ioo (0:ℝ) ((501/1000:ℝ)*cutoff i) →
    DifferentiableAt ℝ (sourceCanonicalDuplicate i m G g margin) b ∧
    0 ≤ deriv (sourceCanonicalDuplicate i m G g margin) b ∧
    deriv (sourceCanonicalDuplicate i m G g margin) b ≤ 2*canonicalRare i m/(xi i*b)

theorem eventually_primitive_stieltjes_bounds (i : Row) :
    ∀ᶠ m : ℕ in atTop,∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G,p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i))) →
      (∀ b,(G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (H lo : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      0 < lo → lo ≤ H → H ≤ RankCutoff.Mstar i → PrefixConditions (xi i) g H →
      (501/1000:ℝ)*cutoff i ≤ g.multiplier-g.radius →
      (∀ b,b ∈ Ioc (0:ℝ) H → sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i) →
      Nonempty (PrimitiveStieltjesBounds i m G g margin lo H) := by
  filter_upwards [eventually_source_first_stieltjes_lower i,eventually_ge_atTop (4:ℕ)] with m hf hm
  intro G hG hvalue hmenu hatom g H lo margin hlo hloH hHM hg hsmall hM
  letI := hG
  have hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
  obtain ⟨S,hSc,hSb,hSe,hSl⟩ := hf G hG hmenu hatom g H lo margin hlo hloH hg hM
  obtain ⟨D,hDc,hDb,hDe,hDu⟩ := source_actual_pure_duplicate_stieltjes_upper i G hvalue hfloor
    hatom hm hlo hloH hHM
  exact ⟨⟨S,D,hSc,hDc,hSb,hDb,hSe,hDe,hSl,hDu,
    source_canonical_duplicate_derivative_ae i G hvalue hfloor (by omega) g hg hsmall margin⟩⟩

end FCAppendix.Affine.Uniform06.PrimitiveStieltjesMeasures
