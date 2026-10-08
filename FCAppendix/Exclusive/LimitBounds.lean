import FCAppendix.Exclusive.BroadcastCapacity

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped BigOperators ProbabilityTheory

variable {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {M C : ℕ → ℕ}

theorem exclusive_eventual_capacity_guards (hM : Tendsto M atTop atTop)
    {rho : ℝ} (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    ∀ᶠ t in atTop, 0 < C t ∧ C t < M t := by
  filter_upwards [hM.eventually_gt_atTop 0,
    hrho.eventually (eventually_gt_nhds hrho0),
    hrho.eventually (eventually_lt_nhds hrho1)] with t hm hp hq
  have hmR : (0 : ℝ) < M t := Nat.cast_pos.mpr hm
  have hcR : (0 : ℝ) < C t := by
    simpa only [zero_mul] using (lt_div_iff₀ hmR).mp hp
  exact ⟨Nat.cast_pos.mp hcR, by exact_mod_cast (div_lt_one hmR).mp hq⟩

theorem exclusive_capacity_bound_tendsto (n : ℕ) {rho h : ℝ}
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hh : 0 < h) (hrhoh : rho < h) :
    Tendsto (fun t => h * PayOnce.success n (min ((C t : ℝ) / ((M t : ℝ) * h)) 1))
      atTop (𝓝 (h * PayOnce.success n (rho / h))) := by
  have hd : Tendsto (fun t => (C t : ℝ) / ((M t : ℝ) * h)) atTop (𝓝 (rho / h)) := by
    simpa only [div_div] using hrho.div_const h
  have hp : rho / h < 1 := (div_lt_one hh).mpr hrhoh
  have hm := hd.min (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  rw [min_eq_left hp.le] at hm
  exact ((PayOnce.continuous_success n).tendsto _ |>.comp hm).const_mul h

theorem exclusive_existing_limit_bounds
    (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
    (hk : 1 ≤ k) (hM : Tendsto M atTop atTop)
    (B : ∀ t, PosteriorSystem (Γ t)) (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (hr : ∀ᶠ t in atTop, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ),
      x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k + 1))
    (E : Set ℝ) (hE : MeasurableSet E)
    (hout : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.1 ∉ E → x.2.routeCount = 0)
    {h rho Q D : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrhoh : rho < h)
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q))
    (hD : Tendsto (fun t => finiteLoad (Γ t) - finiteCoverage (Γ t)) atTop (𝓝 D)) :
    Q ≤ h * PayOnce.success (k + 1) (rho / h) ∧
      h * PayOnce.success (k + 1) (rho / h) < min (((k + 1 : ℕ) : ℝ) * rho) h ∧
      (((k + 1 : ℕ) : ℝ) - 1) * Q ^ 2 / ((((k + 1 : ℕ) : ℝ) ^ 2) * h) ≤ D ∧
      (0 < Q → 0 < D) := by
  have hh : 0 < h := hrho0.trans hrhoh
  have hb : ∀ᶠ t in atTop,
      finiteCoverage (Γ t) ≤ h * PayOnce.success (k + 1)
        (min ((C t : ℝ) / ((M t : ℝ) * h)) 1) ∧
      (((k + 1 : ℕ) : ℝ) - 1) * finiteCoverage (Γ t) ^ 2 /
        ((((k + 1 : ℕ) : ℝ) ^ 2) * h) ≤ finiteLoad (Γ t) - finiteCoverage (Γ t) := by
    filter_upwards [hM.eventually_gt_atTop 0, hr] with t hm hrt
    have he := finite_exclusive_bounds (Γ t) hk hm (B t) (hB t) (hsym t) hrt E hE
      (by rwa [hmass t]) (hout t)
    simpa only [hmass t] using he
  have hupper := le_of_tendsto_of_tendsto hQ
    (exclusive_capacity_bound_tendsto (k + 1) hrho hh hrhoh) (hb.mono fun _ => And.left)
  have hquad : (((k + 1 : ℕ) : ℝ) - 1) * Q ^ 2 /
      ((((k + 1 : ℕ) : ℝ) ^ 2) * h) ≤ D := by
    apply le_of_tendsto_of_tendsto
      (((hQ.pow 2).const_mul (((k + 1 : ℕ) : ℝ) - 1)).div_const
        ((((k + 1 : ℕ) : ℝ) ^ 2) * h)) hD
    exact hb.mono fun _ => And.right
  refine ⟨hupper, Exclusive.coverage_bound_strict (k + 1) (by omega) hrho0 hrhoh, hquad, ?_⟩
  intro hQ0
  have hn : (1 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast (show 1 < k + 1 by omega)
  exact lt_of_lt_of_le (by positivity) hquad

theorem exclusive_scarce_eventual_multiplicity
    (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
    (hk : 1 ≤ k) (hM : Tendsto M atTop atTop)
    (B : ∀ t, PosteriorSystem (Γ t)) (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho target : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrhoh : rho < h)
    (htarget : target < (((k + 1 : ℕ) : ℝ) * rho) /
      (h * PayOnce.success (k + 1) (rho / h))) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k + 1 : ℕ) : ℝ) * rho)) ∧
      ∀ᶠ t in atTop, 0 < finiteCoverage (Γ t) ∧
        target < finiteMultiplicity (Γ t) ∧ finiteMultiplicity (Γ t) ≤ (k + 1 : ℕ) := by
  have hh : 0 < h := hrho0.trans hrhoh
  have hn : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hL := exclusive_broadcast_load_limit Γ hk hM B hB hsym E hE hclass hmass hrho hrhoh.le
  let u : ℕ → ℝ := fun t => h * PayOnce.success (k + 1)
    (min ((C t : ℝ) / ((M t : ℝ) * h)) 1)
  have hu := exclusive_capacity_bound_tendsto (k + 1) hrho hh hrhoh
  have hu0 : 0 < h * PayOnce.success (k + 1) (rho / h) :=
    mul_pos hh (PayOnce.success_pos (k + 1) (by omega) _ (div_pos hrho0 hh)
      ((div_lt_one hh).mpr hrhoh).le)
  have hquot := hL.div hu hu0.ne'
  refine ⟨hL, ?_⟩
  filter_upwards [hM.eventually_gt_atTop 0, hL.eventually (eventually_gt_nhds (mul_pos hn hrho0)),
    hu.eventually (eventually_gt_nhds hu0),
    hquot.eventually (eventually_gt_nhds htarget)] with t hm hLt _hut hqt
  have hLQ := finiteLoad_le_mul_coverage (Γ t) hm
  have hQ0 : 0 < finiteCoverage (Γ t) := by nlinarith
  have hb := (finite_exclusive_bounds (Γ t) hk hm (B t) (hB t) (hsym t)
    (hclass t).routes E hE (by rwa [hmass t]) ((hclass t).mono fun _ => And.right)).1
  rw [hmass t] at hb
  have hratio : finiteLoad (Γ t) / u t ≤ finiteMultiplicity (Γ t) := by
    unfold finiteMultiplicity
    exact div_le_div_of_nonneg_left hLt.le hQ0 hb
  refine ⟨hQ0, hqt.trans_le hratio, ?_⟩
  unfold finiteMultiplicity
  exact (div_le_iff₀ hQ0).mpr hLQ

theorem exclusive_scarce_limit_multiplicity
    (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
    (hk : 1 ≤ k) (hM : Tendsto M atTop atTop)
    (B : ∀ t, PosteriorSystem (Γ t)) (hB : ∀ t, ExclusiveOptimalOnPath (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t))
    (E : Set ℝ) (hE : MeasurableSet E) (hclass : ∀ t, ExclusiveBroadcastOn (Γ t) E)
    {h rho Q : ℝ} (hmass : ∀ t, (Γ t).F.real E = h)
    (hrho : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho))
    (hrho0 : 0 < rho) (hrhoh : rho < h)
    (hQ : Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q)) :
    rho ≤ Q ∧ Q ≤ h * PayOnce.success (k + 1) (rho / h) ∧
      Tendsto (fun t => finiteMultiplicity (Γ t)) atTop
        (𝓝 ((((k + 1 : ℕ) : ℝ) * rho) / Q)) ∧
      (((k + 1 : ℕ) : ℝ) * rho) / (h * PayOnce.success (k + 1) (rho / h)) ≤
        (((k + 1 : ℕ) : ℝ) * rho) / Q ∧
      (((k + 1 : ℕ) : ℝ) * rho) / Q ≤ (k + 1 : ℕ) := by
  have hn : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hL := exclusive_broadcast_load_limit Γ hk hM B hB hsym E hE hclass hmass hrho hrhoh.le
  have hLQ : (((k + 1 : ℕ) : ℝ) * rho) ≤ (k + 1 : ℕ) * Q := by
    apply le_of_tendsto_of_tendsto hL (hQ.const_mul ((k + 1 : ℕ) : ℝ))
    filter_upwards [hM.eventually_gt_atTop 0] with t hm
    exact finiteLoad_le_mul_coverage (Γ t) hm
  have hlow : rho ≤ Q := by nlinarith
  have hQ0 : 0 < Q := hrho0.trans_le hlow
  have hb := exclusive_existing_limit_bounds Γ hk hM B hB hsym
    (Eventually.of_forall fun t => (hclass t).routes) E hE
    (fun t => (hclass t).mono fun _ => And.right) hmass hrho hrho0 hrhoh hQ (hL.sub hQ)
  refine ⟨hlow, hb.1, hL.div hQ hQ0.ne', ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (mul_nonneg hn.le hrho0.le) hQ0 hb.1
  · exact (div_le_iff₀ hQ0).mpr hLQ

end FCAppendix.Bayes
