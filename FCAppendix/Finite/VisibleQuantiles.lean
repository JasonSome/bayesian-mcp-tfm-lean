import FCAppendix.Finite.SingletonDeviation
import Mathlib.Probability.CDF

namespace FCAppendix

open MeasureTheory ProbabilityTheory Filter Set Topology

namespace TailQuantile

noncomputable def quantile (α : ℝ → ℝ) (q : ℝ) : ℝ := sInf {b | 0 ≤ b ∧ α b ≤ q}

theorem tail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Tendsto (fun b => μ.real (Ioi b)) atTop (𝓝 0) := by
  have h := (tendsto_cdf_atTop μ).const_sub 1
  simp only [sub_self] at h
  apply h.congr
  intro b
  rw [cdf_eq_real]
  have hc : μ.real (Ioi b) = 1 - μ.real (Iic b) := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  exact hc.symm

theorem eligible_nonempty {α : ℝ → ℝ} {q : ℝ} (hq : 0 < q)
    (htail : Tendsto α atTop (𝓝 0)) : {b | 0 ≤ b ∧ α b ≤ q}.Nonempty := by
  obtain ⟨b, hb, hα⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (htail.eventually (gt_mem_nhds hq))).exists
  exact ⟨b, hb, hα.le⟩

theorem nonneg {α : ℝ → ℝ} {q : ℝ} (hne : {b | 0 ≤ b ∧ α b ≤ q}.Nonempty) :
    0 ≤ quantile α q := le_csInf hne (fun _ h => h.1)

theorem le_of_tail_le {α : ℝ → ℝ} {q b : ℝ} (hb : 0 ≤ b) (hα : α b ≤ q) :
    quantile α q ≤ b := csInf_le ⟨0, fun _ h => h.1⟩ ⟨hb, hα⟩

theorem tail_le_above {α : ℝ → ℝ} (hα : Antitone α) {q : ℝ}
    (hne : {b | 0 ≤ b ∧ α b ≤ q}.Nonempty) {d : ℝ} (hd : 0 < d) :
    α (quantile α q + d) ≤ q := by
  obtain ⟨b, hb, hlt⟩ := exists_lt_of_csInf_lt hne
    (show quantile α q < quantile α q + d by linarith)
  exact (hα hlt.le).trans hb.2

theorem lt_tail_below {α : ℝ → ℝ} {q b : ℝ} (hb : 0 ≤ b)
    (hlt : b < quantile α q) : q < α b := by
  by_contra h
  exact (not_le_of_gt hlt) (le_of_tail_le hb (le_of_not_gt h))

theorem uniformly_bounded {ι : Type*} (α : ι → ℝ → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (g q : ℝ) (hq : 0 < q)
    (hbound : ∀ i b, 0 ≤ b → α i b ≤ μ.real (Ioi (g + b))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i, quantile (α i) q ≤ M := by
  have hg : Tendsto (fun b : ℝ => g + b) atTop atTop := tendsto_atTop_add_const_left atTop g tendsto_id
  have ht := (tail_tendsto_zero μ).comp hg
  obtain ⟨M, hM, htail⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (ht.eventually (gt_mem_nhds hq))).exists
  exact ⟨M, hM, fun i => le_of_tail_le hM ((hbound i M hM).trans htail.le)⟩

end TailQuantile
namespace Bayes

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem alphaGt_antitone (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Antitone (alphaGt Γ j) := by
  intro b d hbd
  exact measureReal_mono (fun _ h => ⟨h.1, hbd.trans_lt h.2⟩)

theorem alphaGt_tendsto_zero_onPath (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ) (j : Fin n) :
    Tendsto (alphaGt Γ j) atTop (𝓝 0) := by
  have htail := (TailQuantile.tail_tendsto_zero Γ.F).comp
    (tendsto_atTop_add_const_left atTop Γ.g tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail ?_ ?_
  · exact Filter.Eventually.of_forall fun _ => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with b hb
    exact alphaGt_le_value_tail_onPath Γ hm hc hΓ j b hb

theorem visible_quantile_nonneg (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ) (j : Fin n)
    (q : ℝ) (hq : 0 < q) : 0 ≤ TailQuantile.quantile (alphaGt Γ j) q :=
  TailQuantile.nonneg (TailQuantile.eligible_nonempty hq (alphaGt_tendsto_zero_onPath Γ hm hc hΓ j))

theorem alphaGt_above_quantile (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsAEEquilibrium Γ) (j : Fin n)
    (q d : ℝ) (hq : 0 < q) (hd : 0 < d) :
    alphaGt Γ j (TailQuantile.quantile (alphaGt Γ j) q + d) ≤ q :=
  TailQuantile.tail_le_above (alphaGt_antitone Γ j)
    (TailQuantile.eligible_nonempty hq (alphaGt_tendsto_zero_onPath Γ hm hc hΓ j)) hd

end Bayes
end FCAppendix
