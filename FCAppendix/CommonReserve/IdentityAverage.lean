import FCAppendix.Probability.CountLaw
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
namespace FCAppendix.CommonReserve
open Filter Topology
open scoped BigOperators

theorem finite_average_tendsto_of_all_selections
    (M : ℕ → ℕ) (hM : ∀ k, 0 < M k) (x : ∀ k, Fin (M k) → ℝ) (q : ℝ)
    (hx : ∀ i : ∀ k, Fin (M k), Tendsto (fun k => x k (i k)) atTop (𝓝 q)) :
    Tendsto (fun k => (∑ i, x k i) / M k) atTop (𝓝 q) := by
  classical
  have hmax (k : ℕ) : ∃ i : Fin (M k), ∀ j, |x k j - q| ≤ |x k i - q| := by
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (M k)))
      (fun i => |x k i - q|) ⟨⟨0, hM k⟩, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
  choose i hi using hmax
  have he : Tendsto (fun k => |x k (i k) - q|) atTop (𝓝 0) := by
    simpa using ((hx i).sub_const q).abs
  have hb : ∀ k, |(∑ j, x k j) / M k - q| ≤ |x k (i k) - q| := by
    intro k
    have hm : (0 : ℝ) < M k := Nat.cast_pos.mpr (hM k)
    have hid : (∑ j : Fin (M k), x k j) / M k - q =
        (∑ j : Fin (M k), (x k j - q)) / M k := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hm.ne']
    rw [hid, abs_div, abs_of_pos hm]
    apply (div_le_iff₀ hm).mpr
    calc
      _ ≤ ∑ j : Fin (M k), |x k j - q| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (M k), |x k (i k) - q| := Finset.sum_le_sum fun j _ => hi k j
      _ = _ := by simp [mul_comm]
  have habs := squeeze_zero (fun k => abs_nonneg ((∑ j, x k j) / M k - q)) hb he
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [Real.dist_eq] using habs)

end FCAppendix.CommonReserve
