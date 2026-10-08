import FCAppendix.Exclusive.OnceFinite

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped ProbabilityTheory BigOperators

variable {n : ℕ} {population capacity : ℕ → ℕ}
variable {Seeds : ℕ → Type*} [∀ t, MeasurableSpace (Seeds t)]

theorem exclusive_once_coverage_limit
    (Γ : ∀ t, FiniteGame (population t) n (capacity t) (Seeds t))
    (B : ∀ t, PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hvalid : ∀ᶠ t in atTop, 0 < capacity t ∧ capacity t < population t ∧
      ExclusiveOnceEquilibrium (Γ t) (B t))
    {h ρ Q : ℝ} (hh : 0 < h) (hρ : 0 < ρ) (hρh : ρ < h)
    (hactive : ∀ᶠ t in atTop, exclusiveActiveMass (Γ t) = h)
    (hcap : Tendsto (fun t => (capacity t : ℝ) / population t) atTop (𝓝 ρ))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) :
    Q ≤ h * (1 - (1 - ρ / h) ^ n) ∧
      h * (1 - (1 - ρ / h) ^ n) < min ((n : ℝ) * ρ) h := by
  let j : Fin n := ⟨0, by omega⟩
  let f : ℝ → ℝ := fun x => h * (1 - (1 - min (x / h) 1) ^ n)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hlim : Tendsto (fun t => f ((capacity t : ℝ) / population t))
      atTop (𝓝 (h * (1 - (1 - ρ / h) ^ n))) := by
    have he := (hf.tendsto ρ).comp hcap
    simpa only [Function.comp_def, f, min_eq_left ((div_lt_one hh).mpr hρh).le] using he
  have hbound : ∀ᶠ t in atTop, finiteCoverage (Γ t) ≤
      f ((capacity t : ℝ) / population t) := by
    filter_upwards [hvalid, hactive] with t hv ha
    have he := (exclusive_once_contribution_bounds (Γ t) hv.1 hv.2.1 (B t)
      hv.2.2 j (ha.symm ▸ hh)).coverage
    simp only [ha] at he
    simpa only [f, div_div] using he
  exact ⟨le_of_tendsto_of_tendsto hQ hlim hbound,
    Exclusive.once_coverage_cap_strict n hn h ρ hh hρ hρh⟩

theorem exclusive_once_duplicates_limit
    (Γ : ∀ t, FiniteGame (population t) n (capacity t) (Seeds t))
    (B : ∀ t, PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hvalid : ∀ᶠ t in atTop, 0 < capacity t ∧ capacity t < population t ∧
      ExclusiveOnceEquilibrium (Γ t) (B t))
    {h Q D : ℝ} (hh : 0 < h)
    (hactive : ∀ᶠ t in atTop, exclusiveActiveMass (Γ t) = h)
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hD : Tendsto (fun t => finiteExclusiveDuplicates (Γ t)) atTop (𝓝 D)) :
    ((n : ℝ) - 1) * Q ^ 2 / ((n : ℝ) ^ 2 * h) ≤ D ∧ (0 < Q → 0 < D) := by
  let j : Fin n := ⟨0, by omega⟩
  have hlim := ((hQ.pow 2).const_mul ((n : ℝ) - 1)).div_const ((n : ℝ) ^ 2 * h)
  have hbound : ∀ᶠ t in atTop,
      ((n : ℝ) - 1) * finiteCoverage (Γ t) ^ 2 / ((n : ℝ) ^ 2 * h) ≤
        finiteExclusiveDuplicates (Γ t) := by
    filter_upwards [hvalid, hactive] with t hv ha
    have he := (exclusive_once_contribution_bounds (Γ t) hv.1 hv.2.1 (B t)
      hv.2.2 j (ha.symm ▸ hh)).duplicates_coverage
    rwa [ha, ← finiteExclusiveDuplicates_eq_load_sub_coverage (Γ t)] at he
  have hle := le_of_tendsto_of_tendsto hlim hD hbound
  refine ⟨hle, ?_⟩
  intro hpos
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hstrict : 0 < ((n : ℝ) - 1) * Q ^ 2 / ((n : ℝ) ^ 2 * h) := by
    exact div_pos (mul_pos (by linarith) (sq_pos_of_pos hpos))
      (mul_pos (sq_pos_of_pos (by linarith)) hh)
  exact hstrict.trans_le hle

theorem exclusive_once_existing_equilibrium_limit
    (Γ : ∀ t, FiniteGame (population t) n (capacity t) (Seeds t))
    (B : ∀ t, PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hvalid : ∀ᶠ t in atTop, 0 < capacity t ∧ capacity t < population t ∧
      ExclusiveOnceEquilibrium (Γ t) (B t))
    (F : Measure ℝ) (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    {ρ Q L : ℝ} (hρ : 0 < ρ) (hρh : ρ < F.real (Set.Ioi g))
    (hcap : Tendsto (fun t => (capacity t : ℝ) / population t) atTop (𝓝 ρ))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hL : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 L)) :
    Q ≤ F.real (Set.Ioi g) * (1 - (1 - ρ / F.real (Set.Ioi g)) ^ n) ∧
      F.real (Set.Ioi g) * (1 - (1 - ρ / F.real (Set.Ioi g)) ^ n) <
        min ((n : ℝ) * ρ) (F.real (Set.Ioi g)) ∧
      ((n : ℝ) - 1) * Q ^ 2 / ((n : ℝ) ^ 2 * F.real (Set.Ioi g)) ≤ L - Q ∧
      (0 < Q → 0 < L - Q) := by
  have hh : 0 < F.real (Set.Ioi g) := hρ.trans hρh
  have ha : ∀ᶠ t in atTop, exclusiveActiveMass (Γ t) = F.real (Set.Ioi g) :=
    Eventually.of_forall fun t => by simp only [exclusiveActiveMass, hF t, hg t]
  have hcov := exclusive_once_coverage_limit Γ B hn hvalid hh hρ hρh ha hcap hQ
  have hdup : Tendsto (fun t => finiteExclusiveDuplicates (Γ t)) atTop (𝓝 (L - Q)) := by
    simpa only [finiteExclusiveDuplicates_eq_load_sub_coverage] using hL.sub hQ
  have hd := exclusive_once_duplicates_limit Γ B hn hvalid hh ha hQ hdup
  exact ⟨hcov.1, hcov.2, hd.1, hd.2⟩

theorem exclusive_once_existing_sequence
    (Γ : ∀ t, FiniteGame (population t) n (capacity t) (Seeds t))
    (B : ∀ t, PosteriorSystem (Γ t)) (hn : 2 ≤ n)
    (hM : Tendsto population atTop atTop)
    (heq : ∀ᶠ t in atTop, ExclusiveOnceEquilibrium (Γ t) (B t))
    (F : Measure ℝ) (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    {ρ Q L : ℝ} (hρ : 0 < ρ) (hρh : ρ < F.real (Set.Ioi g))
    (hcap : Tendsto (fun t => (capacity t : ℝ) / population t) atTop (𝓝 ρ))
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hL : Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 L)) :
    Q ≤ F.real (Set.Ioi g) * (1 - (1 - ρ / F.real (Set.Ioi g)) ^ n) ∧
      F.real (Set.Ioi g) * (1 - (1 - ρ / F.real (Set.Ioi g)) ^ n) <
        min ((n : ℝ) * ρ) (F.real (Set.Ioi g)) ∧
      ((n : ℝ) - 1) * Q ^ 2 / ((n : ℝ) ^ 2 * F.real (Set.Ioi g)) ≤ L - Q ∧
      (0 < Q → 0 < L - Q) := by
  have hmass1 : F.real (Set.Ioi g) ≤ 1 := by
    rw [← hF 0]
    exact measureReal_le_one
  have hρ1 : ρ < 1 := hρh.trans_le hmass1
  have hvalid : ∀ᶠ t in atTop, 0 < capacity t ∧ capacity t < population t ∧
      ExclusiveOnceEquilibrium (Γ t) (B t) := by
    filter_upwards [heq,hM.eventually_gt_atTop 0,
      hcap.eventually (eventually_gt_nhds hρ),
      hcap.eventually (eventually_lt_nhds hρ1)] with t ht hm hp hq
    have hmR : (0 : ℝ) < population t := Nat.cast_pos.mpr hm
    have hcR : (0 : ℝ) < capacity t := by
      simpa only [zero_mul] using (lt_div_iff₀ hmR).mp hp
    exact ⟨Nat.cast_pos.mp hcR,by exact_mod_cast (div_lt_one hmR).mp hq,ht⟩
  exact exclusive_once_existing_equilibrium_limit Γ B hn hvalid F g hF hg hρ hρh hcap hQ hL

end FCAppendix.Bayes
