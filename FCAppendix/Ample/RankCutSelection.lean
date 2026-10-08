import FCAppendix.Ample.RankSupportSelection

noncomputable section
namespace FCAppendix.Ample.RankMeasureTools
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem lower_tail_eq_total_sub (μ : Measure ℝ) [IsFiniteMeasure μ] (u : ℝ) :
    μ.real (Iic u) = μ.real univ-μ.real (Ioi u) := by
  rw [← measureReal_sdiff (subset_univ (Ioi u)) measurableSet_Ioi]
  congr 1
  ext x
  simp only [Set.mem_sdiff, mem_univ, mem_Ioi, mem_Iic, true_and, not_lt]

theorem exists_good_lower_cut (μ : Measure ℝ) [IsFiniteMeasure μ]
    {h : ℝ} (hatom : ∀ u, μ {u} = 0) (hs : ∀ᵐ u ∂μ, u ∈ Ioc 0 h)
    (hm : 0 < μ.real univ) {P : ℝ → Prop} (hP : ∀ᵐ u ∂μ, P u)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : ℝ, 0 < u ∧ u ≤ h ∧ P u ∧ μ.real (Iic u) < δ := by
  classical
  let E : BidStratum μ (fun u : ℝ => u) :=
    { carrier := Ioc 0 h
      measurable_carrier := measurableSet_Ioc
      positive := fun _ hu => hu.1
      atomless := by
        intro b
        exact measure_mono_null (fun _ hx => hx.2) (hatom b) }
  have hmass : E.mass = μ.real univ := by
    apply measureReal_congr
    filter_upwards [hs] with u hu
    exact propext ⟨fun _ => trivial, fun _ => hu⟩
  have he0 : 0 < E.mass := by rwa [hmass]
  let e : ℝ := min δ E.mass
  have he : 0 < e := lt_min hδ he0
  have heδ : e ≤ δ := min_le_left _ _
  have hem : e ≤ E.mass := min_le_right _ _
  obtain ⟨u, huE, hutail, _hupper, _, huP⟩ :=
    E.exists_good_in_band measurable_id
      (lo := E.mass-e/2) (hi := E.mass-e/4)
      (by linarith) (by linarith) (by linarith)
      ∅ (by simp only [measureReal_empty]; linarith) P hP
  have htail : E.tail u = μ.real (Ioi u) := by
    apply measureReal_congr
    filter_upwards [hs] with v hv
    change (v ∈ Ioc 0 h ∧ u < v) = (u < v)
    exact propext ⟨fun ht => ht.2, fun ht => ⟨hv, ht⟩⟩
  refine ⟨u, huE.1, huE.2, huP, ?_⟩
  rw [lower_tail_eq_total_sub]
  rw [htail, hmass] at hutail
  linarith

end FCAppendix.Ample.RankMeasureTools

namespace FCAppendix.Bayes.RankLimit
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem mass_tendsto {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    Tendsto (fun t => (rankClassLaw (Γ t) j).real univ) atTop (𝓝 (pi j)) := by
  letI := hr.finite hj
  have he := hr.weak j hj (fun _ : ℝ => (1:ℝ)) continuous_const
  simpa only [integral_const, smul_eq_mul, mul_one, hr.mass j hj] using he

theorem lower_tail_tendsto {j : ℕ} (hj : j ∈ Finset.Icc 1 n)
    {u : ℝ} (hu : u ∈ Icc 0 h) :
    Tendsto (fun t => (rankClassLaw (Γ t) j).real (Iic u)) atTop
      (𝓝 ((nu j).real (Iic u))) := by
  letI := hr.finite hj
  have he := (hr.mass_tendsto hj).sub
    (hr.moving_tail (Eventually.of_forall (fun _ => hu)) tendsto_const_nhds hj)
  rw [hr.tail_eq_strict hj, ← hr.mass j hj, ← lower_tail_eq_total_sub] at he
  simpa only [lower_tail_eq_total_sub] using he

end FCAppendix.Bayes.RankLimit
