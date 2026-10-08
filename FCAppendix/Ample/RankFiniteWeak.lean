import FCAppendix.Ample.RankMeasureTools
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
namespace FCAppendix.Ample.RankMeasureTools
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators

theorem volume_rank_interval_finite (h : ℝ) :
    IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) h)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

theorem finite_of_rank_domination {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) : IsFiniteMeasure μ := by
  letI := volume_rank_interval_finite h
  exact ⟨lt_of_le_of_lt ((Measure.le_iff'.mp hd) univ) (measure_lt_top _ _)⟩

theorem atomless_of_rank_domination {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (u : ℝ) : μ {u} = 0 := by
  apply le_antisymm _ (zero_le : (0 : ℝ≥0∞) ≤ _)
  calc
    μ {u} ≤ (volume.restrict (Ioc 0 h)) {u} := (Measure.le_iff'.mp hd) _
    _ ≤ volume {u} := (Measure.le_iff'.mp Measure.restrict_le_self) _
    _ = 0 := by simp

theorem support_of_rank_domination {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) : ∀ᵐ u ∂μ, u ∈ Ioc 0 h :=
  (ae_restrict_mem measurableSet_Ioc).filter_mono (ae_mono hd)

theorem interval_mass_le_length {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) {u v : ℝ} (huv : u ≤ v) :
    μ.real (Ioc u v) ≤ v - u := by
  have hm : μ (Ioc u v) ≤ volume (Ioc u v) :=
    ((Measure.le_iff'.mp hd) _).trans
      ((Measure.le_iff'.mp Measure.restrict_le_self) _)
  rw [Measure.real]
  have he := ENNReal.toReal_mono (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hm
  simpa only [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr huv)] using he

theorem strict_tail_one_lipschitz {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (u v : ℝ) :
    |μ.real (Ioi u) - μ.real (Ioi v)| ≤ |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [strict_tail_sub huv, abs_of_nonneg measureReal_nonneg,
      abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using interval_mass_le_length hd huv
  · rw [abs_sub_comm (μ.real (Ioi u)), abs_sub_comm u,
      strict_tail_sub hvu, abs_of_nonneg measureReal_nonneg,
      abs_of_nonpos (sub_nonpos.mpr hvu)]
    simpa only [neg_sub] using interval_mass_le_length hd hvu

def rankCemetery : FiniteMeasure ℝ := ⟨Measure.dirac (-1), inferInstance⟩

@[simp] theorem rankCemetery_mass : rankCemetery.mass = 1 := by
  change (Measure.dirac (-1 : ℝ) univ).toNNReal = 1
  rw [Measure.dirac_apply_of_mem (mem_univ _)]
  rfl

def completeRankFinite (μ : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  μ + (1 - μ.mass) • rankCemetery

theorem completeRankFinite_mass (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    (completeRankFinite μ).mass = 1 := by
  change ((μ : Measure ℝ) univ + (1 - μ.mass) •
    Measure.dirac (-1 : ℝ) univ).toNNReal = 1
  rw [Measure.dirac_apply_of_mem (mem_univ _), ENNReal.smul_one,
    ENNReal.toNNReal_add (measure_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  exact add_tsub_cancel_of_le hμ

def completeRankProbability (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1) :
    ProbabilityMeasure ℝ :=
  ⟨(completeRankFinite μ : Measure ℝ), ⟨by
    rw [← FiniteMeasure.ennreal_mass, completeRankFinite_mass μ hμ]
    rfl⟩⟩

theorem continuous_completeRankFinite : Continuous completeRankFinite := by
  exact continuous_id.add
    ((continuous_const.sub FiniteMeasure.continuous_mass).smul continuous_const)

theorem completeRankProbability_tendsto {ι : Type*} {l : Filter ι}
    {μt : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (ht : ∀ t, (μt t).mass ≤ 1) (hμ : μ.mass ≤ 1)
    (hw : Tendsto μt l (𝓝 μ)) :
    Tendsto (fun t => completeRankProbability (μt t) (ht t)) l
      (𝓝 (completeRankProbability μ hμ)) := by
  apply (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).mpr
  exact continuous_completeRankFinite.continuousAt.tendsto.comp hw

theorem completeRankProbability_tail (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (completeRankProbability μ hμ : Measure ℝ) (Ioi u) = (μ : Measure ℝ) (Ioi u) := by
  change ((μ : Measure ℝ) + (1 - μ.mass) • Measure.dirac (-1) : Measure ℝ) (Ioi u) = _
  have hnot : (-1 : ℝ) ∉ Ioi u := by simp only [mem_Ioi]; linarith
  simp [Measure.add_apply, Measure.smul_apply,
    hnot]

theorem completeRankProbability_atom (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1)
    {u : ℝ} (hu : 0 ≤ u) :
    (completeRankProbability μ hμ : Measure ℝ) {u} = (μ : Measure ℝ) {u} := by
  change ((μ : Measure ℝ) + (1 - μ.mass) • Measure.dirac (-1) : Measure ℝ) {u} = _
  have hnot : (-1 : ℝ) ∉ ({u} : Set ℝ) := by simp only [mem_singleton_iff]; linarith
  simp [Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' (-1) (measurableSet_singleton u), hnot]

theorem completeRankProbability_restrict (μ : FiniteMeasure ℝ) (hμ : μ.mass ≤ 1)
    (hs : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
    (completeRankProbability μ hμ : Measure ℝ).restrict (Icc (0 : ℝ) 1) = μ := by
  classical
  change (((μ : Measure ℝ) + (1-μ.mass) • Measure.dirac (-1)).restrict
    (Icc (0 : ℝ) 1)) = (μ : Measure ℝ)
  have hc : (Measure.dirac (-1 : ℝ)).restrict (Icc (0 : ℝ) 1) = 0 := by
    ext s hs
    rw [Measure.restrict_apply hs,
      Measure.dirac_apply' (-1) (hs.inter measurableSet_Icc)]
    have hnot : (-1 : ℝ) ∉ s ∩ Icc (0 : ℝ) 1 := by
      intro hx
      norm_num at hx
    rw [Set.indicator_of_notMem hnot]
    rfl
  rw [Measure.restrict_add, Measure.restrict_smul,
    Measure.restrict_eq_self_of_ae_mem hs, hc, smul_zero, add_zero]

theorem finite_tail_tendsto {ι : Type*} {l : Filter ι}
    {μt : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (ht : ∀ t, (μt t).mass ≤ 1) (hμ : μ.mass ≤ 1)
    (hw : Tendsto μt l (𝓝 μ)) {u : ℝ} (hu : 0 ≤ u)
    (hatom : (μ : Measure ℝ) {u} = 0) :
    Tendsto (fun t => (μt t : Measure ℝ).real (Ioi u)) l
      (𝓝 ((μ : Measure ℝ).real (Ioi u))) := by
  have hc := completeRankProbability_tendsto ht hμ hw
  have hb : (completeRankProbability μ hμ : Measure ℝ) (frontier (Ioi u)) = 0 := by
    rw [frontier_Ioi, completeRankProbability_atom μ hμ hu, hatom]
  have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hc hb
  simp only [completeRankProbability_tail _ _ hu] at he
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp he

theorem rank_eventually_finset {ι α : Type*} {l : Filter α} (s : Finset ι)
    (P : α → ι → Prop) (h : ∀ i ∈ s, ∀ᶠ t in l, P t i) :
    ∀ᶠ t in l, ∀ i ∈ s, P t i := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => intro _; exact Eventually.of_forall (by simp)
  | @insert i s hi ih =>
    intro h
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    filter_upwards [h i (Finset.mem_insert_self _ _), hs] with t ht hs
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact ht
    · exact hs j hj

theorem uniform_of_one_lipschitz {ι : Type*} {l : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ} {h : ℝ}
    (hf : ∀ᶠ t in l, ∀ u ∈ Icc 0 h, ∀ v ∈ Icc 0 h, |f t u - f t v| ≤ |u-v|)
    (hg : ∀ u ∈ Icc 0 h, ∀ v ∈ Icc 0 h, |g u - g v| ≤ |u-v|)
    (hpoint : ∀ u ∈ Icc 0 h, Tendsto (fun t => f t u) l (𝓝 (g u))) :
    ∀ ε > 0, ∀ᶠ t in l, ∀ u ∈ Icc 0 h, |f t u - g u| < ε := by
  classical
  intro ε hε
  let U : (u : ℝ) → u ∈ Icc 0 h → Set ℝ := fun u _ => Metric.ball u (ε/4)
  have hU : ∀ u (hu : u ∈ Icc 0 h), U u hu ∈ 𝓝 u := by
    intro u _
    exact Metric.ball_mem_nhds u (by linarith)
  obtain ⟨mesh, hmesh⟩ := isCompact_Icc.elim_nhds_subcover' U hU
  have hm : ∀ᶠ t in l, ∀ a ∈ mesh, |f t a - g a| < ε/4 := by
    apply rank_eventually_finset mesh
    intro a _
    have he : Tendsto (fun t => |f t a - g a|) l (𝓝 0) := by
      simpa only [sub_self, abs_zero] using ((hpoint a a.2).sub_const (g a)).abs
    exact he.eventually_lt_const (show (0 : ℝ) < ε/4 by linarith)
  filter_upwards [hf, hm] with t ht hm
  intro u hu
  obtain ⟨a, ham, hua⟩ := Set.mem_iUnion₂.mp (hmesh hu)
  have hdist : |u - (a : ℝ)| < ε/4 := by
    simpa only [U, Metric.mem_ball, Real.dist_eq] using hua
  have h1 := ht u hu a a.2
  have h2 := hg a a.2 u hu
  have h3 := hm a ham
  calc
    |f t u - g u| ≤ |f t u - f t a| + |f t a - g a| + |g a - g u| := by
      have ha := abs_sub_le (f t u) (f t a) (g u)
      have hb := abs_sub_le (f t a) (g a) (g u)
      linarith
    _ < ε := by rw [abs_sub_comm (a : ℝ) u] at h2; linarith

theorem finite_marked_compactness {ι : Type*} [Fintype ι]
    (μ : ℕ → ι → FiniteMeasure ℝ)
    (hm : ∀ t i, (μ t i).mass ≤ 1)
    (hs : ∀ t i, ∀ᵐ x ∂(μ t i : Measure ℝ), x ∈ Icc (0 : ℝ) 1) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ ν : ι → FiniteMeasure ℝ,
      (∀ i, Tendsto (fun t => μ (psi t) i) atTop (𝓝 (ν i))) ∧
      (∀ i, (ν i).mass ≤ 1) ∧
      (∀ i, ∀ᵐ x ∂(ν i : Measure ℝ), x ∈ Icc (0 : ℝ) 1) := by
  classical
  let K : Set (FiniteMeasure ℝ) :=
    {ν | ν.mass ≤ 1 ∧ ν (Icc (0 : ℝ) 1)ᶜ = 0}
  have hK : IsCompact K :=
    isCompact_setOf_finiteMeasure_le_of_isCompact 1 isCompact_Icc
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hKs (ν : K) : ∀ᵐ x ∂(ν.1 : Measure ℝ), x ∈ Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp ν.2.2
  let embed : K → ProbabilityMeasure ℝ := fun ν => completeRankProbability ν.1 ν.2.1
  have hcont : Continuous embed := by
    apply continuous_iff_continuousAt.mpr
    intro ν
    exact completeRankProbability_tendsto (fun κ : K => κ.2.1) ν.2.1
      continuous_subtype_val.continuousAt.tendsto
  have hinj : Function.Injective embed := by
    intro ν κ he
    have hr := congrArg (fun p : ProbabilityMeasure ℝ =>
      (p : Measure ℝ).restrict (Icc (0 : ℝ) 1)) he
    change (completeRankProbability ν.1 ν.2.1 : Measure ℝ).restrict _ =
      (completeRankProbability κ.1 κ.2.1 : Measure ℝ).restrict _ at hr
    rw [completeRankProbability_restrict ν.1 ν.2.1 (hKs ν),
      completeRankProbability_restrict κ.1 κ.2.1 (hKs κ)] at hr
    exact Subtype.ext (Subtype.ext hr)

  letI : TopologicalSpace.MetrizableSpace K := (hcont.isClosedEmbedding hinj).isEmbedding.metrizableSpace
  let seq : ℕ → ι → K := fun t i => ⟨μ t i, hm t i,
    (FiniteMeasure.null_iff_toMeasure_null _ _).mpr (by
      exact (ae_iff.mp (hs t i)))⟩
  obtain ⟨ν, psi, hpsi, hw⟩ := CompactSpace.tendsto_subseq seq
  refine ⟨psi, hpsi, fun i => (ν i).1, ?_, ?_, ?_⟩
  · intro i
    exact continuous_subtype_val.continuousAt.tendsto.comp
      (((continuous_apply i).tendsto ν).comp hw)
  · intro i
    exact (ν i).2.1
  · intro i
    rw [ae_iff]
    exact (FiniteMeasure.null_iff_toMeasure_null _ _).mp (ν i).2.2

end FCAppendix.Ample.RankMeasureTools
