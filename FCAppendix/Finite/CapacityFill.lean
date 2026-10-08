import FCAppendix.Finite.LowBidInclusions
import FCAppendix.PayOnce.FiniteJensen

namespace FCAppendix.Finite

theorem optimal_unused_le_shortfall {ι : Type*} [DecidableEq ι]
    (c : ℕ) (r : ι → ℝ) (S H : Finset ι) (hS : Optimal c r S)
    (hpos : ∀ h ∈ H, 0 < r h) : c - S.card ≤ c - H.card := by
  classical
  by_cases hH : H ⊆ S
  · exact Nat.sub_le_sub_left (Finset.card_le_card hH) c
  · obtain ⟨h, hh, hnot⟩ := Finset.not_subset.mp hH
    rw [optimal_fills c r S hS h hnot (hpos h hh), Nat.sub_self]
    exact Nat.zero_le _

theorem optimal_unused_real_le_shortfall {ι : Type*} [DecidableEq ι]
    (c : ℕ) (r : ι → ℝ) (S H : Finset ι) (hS : Optimal c r S)
    (hpos : ∀ h ∈ H, 0 < r h) :
    (c : ℝ) - S.card ≤ max ((c : ℝ) - H.card) 0 := by
  have hh := optimal_unused_le_shortfall c r S H hS hpos
  have he : ((c - S.card : ℕ) : ℝ) = (c : ℝ) - S.card := Nat.cast_sub hS.1
  by_cases hH : H.card ≤ c
  · have hR : ((c - S.card : ℕ) : ℝ) ≤ (c - H.card : ℕ) := Nat.cast_le.mpr hh
    rw [he, Nat.cast_sub hH] at hR
    exact hR.trans (le_max_left _ _)
  · have hz : c - S.card = 0 := by omega
    have hzero : (c : ℝ) - S.card = 0 := by rw [← he, hz, Nat.cast_zero]
    rw [hzero]
    exact le_max_right _ _

end FCAppendix.Finite

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped BigOperators ProbabilityTheory Topology

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def unusedCapacity (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ω : Background m n Seed) : ℝ :=
  (c : ℝ) - (allocation (drawsRealization ω.1) Γ.policy ω.2 j).card

theorem unusedCapacity_nonneg (Γ : FiniteGame m n c Seed) (j : Fin n)
    (ω : Background m n Seed) : 0 ≤ unusedCapacity Γ j ω := by
  apply sub_nonneg.mpr
  exact_mod_cast (Γ.policy j (observe (drawsRealization ω.1) j) (ω.2 j)).property.1

theorem measurable_unusedCapacity (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measurable (unusedCapacity Γ j) :=
  measurable_const.sub ((measurable_of_countable (fun S : Finset (Fin m) => (S.card : ℝ))).comp
    (measurable_allocation_draws Γ j))

theorem integrable_unusedCapacity (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Integrable (unusedCapacity Γ j) (backgroundLaw Γ) := by
  apply Integrable.of_bound (measurable_unusedCapacity Γ j).aestronglyMeasurable (c : ℝ)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (unusedCapacity_nonneg Γ j ω)]
  exact sub_le_self _ (Nat.cast_nonneg _)

theorem unusedCapacity_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (t : ℝ) (ht : 0 < t) (ω : Background m n Seed)
    (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c
      (beliefReceipts Γ.A belief (observe (drawsRealization ω.1) j))
      (allocation (drawsRealization ω.1) Γ.policy ω.2 j)) :
    unusedCapacity Γ j ω ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0 := by
  classical
  apply Finite.optimal_unused_real_le_shortfall c _ _
    (Finset.univ.filter fun i => ω.1 i ∈ aboveAt j t) hopt
  intro h hh
  have hh' : j ∈ firstK (ω.1 h).2 (ω.1 h).1.2.routeCount ∧ t < (ω.1 h).1.2.bid :=
    (Finset.mem_filter.mp hh).2
  have hsome : observe (drawsRealization ω.1) j h = some (ω.1 h).1.2.bid := by
    simp [observe, drawsRealization, hh'.1]
  have hrh := (beliefReceipts_bounds Γ.A belief _ a hA h _
    (ω.1 h).1.2.bid_nonneg hsome).1
  exact (mul_pos ha (ht.trans hh'.2)).trans_le hrh

theorem ae_unusedCapacity_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (t : ℝ) (ht : 0 < t) : ∀ᵐ ω ∂backgroundLaw Γ,
    unusedCapacity Γ j ω ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0 := by
  have hm := (PiBinomial.measurable_count (aboveAt j t) (measurableSet_aboveAt j t)
    (Finset.univ : Finset (Fin m))).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst)
  have hset : MeasurableSet {ω : Background m n Seed | unusedCapacity Γ j ω ≤
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0} :=
    measurableSet_le (measurable_unusedCapacity Γ j)
      ((measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm)).max measurable_const)
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  obtain ⟨belief, hopt⟩ := hj
  have hd := ae_of_ae_map (measurable_observe_draws j).aemeasurable hopt
  filter_upwards [hd] with d hd
  have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hd
  filter_upwards [hs] with s hs
  exact unusedCapacity_le_shortfall Γ j a ha hA t ht (d, s) _ hs

theorem integral_unusedCapacity_le_shortfall (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (t : ℝ) (ht : 0 < t) :
    (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) ≤
      ∫ d, max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0
        ∂(userProfileLaw Γ) := by
  have hm := (PiBinomial.measurable_count (aboveAt j t) (measurableSet_aboveAt j t)
    (Finset.univ : Finset (Fin m))).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst)
  have hi : Integrable (fun ω : Background m n Seed =>
      max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ ω.1) 0) (backgroundLaw Γ) := by
    apply Integrable.of_bound ((measurable_const.sub ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm)).max measurable_const).aestronglyMeasurable c
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hle := integral_mono_ae (integrable_unusedCapacity Γ j) hi
    (ae_unusedCapacity_le_shortfall Γ j hj a ha hA t ht)
  simpa only [backgroundLaw, integral_fun_fst (fun d : UserProfile m n =>
    max ((c : ℝ) - PiBinomial.count (aboveAt j t) Finset.univ d) 0),
    probReal_univ, one_smul, userProfileLaw] using hle

theorem integral_unusedCapacity_normalized_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (j : Fin n) (hj : ProposerRationalOnPath Γ j) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (t ρ ε : ℝ) (ht0 : 0 < t) (hε : 0 ≤ ε) (ht : ρ - ε ≤ alphaGt Γ j t) :
    (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) / m ≤
      ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  apply (div_le_div_of_nonneg_right
    (integral_unusedCapacity_le_shortfall Γ j hj a ha hA t ht0) hmR.le).trans
  have hh := PiBinomial.integral_normalized_shortfall_le (userLaw Γ) (aboveAt j t)
    (measurableSet_aboveAt j t) (Finset.univ : Finset (Fin m)) (by simpa using hm)
    ((c : ℝ) / m) ρ ε hε ht
  simpa only [Finset.card_univ, Fintype.card_fin, mul_div_cancel₀ _ hmR.ne',
    userProfileLaw] using hh

theorem sum_unusedCapacity_eq_load_gap (Γ : FiniteGame m n c Seed) :
    (∑ j, (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ)) / m =
      (n : ℝ) * ((c : ℝ) / m) - finiteLoad Γ := by
  have hi (i : Fin m) := CountLaw.integrable_comp (backgroundLaw Γ) _
    (measurable_playedCount Γ i) (fun r => (r.val : ℝ))
  have hpoint (ω : Background m n Seed) :
      (∑ j, unusedCapacity Γ j ω) = (n : ℝ) * c - ∑ i, ((playedCount Γ i ω).val : ℝ) := by
    simp only [unusedCapacity, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    congr 1
    have hh := double_count (drawsRealization ω.1) Γ.policy ω.2
    exact_mod_cast hh.symm
  have he : (∑ j, ∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) =
      (n : ℝ) * c - ∑ i, ∫ ω, ((playedCount Γ i ω).val : ℝ) ∂backgroundLaw Γ := by
    rw [← integral_finsetSum _ (fun j _ => integrable_unusedCapacity Γ j)]
    simp_rw [hpoint]
    rw [integral_sub (integrable_const _) (integrable_finsetSum _ (fun i _ => hi i)),
      integral_finsetSum _ (fun i _ => hi i), integral_const, probReal_univ, one_smul]
  rw [he, finiteLoad_eq_actual, sub_div, mul_div_assoc]

theorem finiteLoad_le_capacity (Γ : FiniteGame m n c Seed) :
    finiteLoad Γ ≤ (n : ℝ) * ((c : ℝ) / m) := by
  have hh : 0 ≤ (∑ j, ∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) / m :=
    div_nonneg (Finset.sum_nonneg fun j _ => integral_nonneg (unusedCapacity_nonneg Γ j))
      (Nat.cast_nonneg _)
  rw [sum_unusedCapacity_eq_load_gap] at hh
  linarith

theorem capacity_gap_le_visible_shortfall (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hΓ : ∀ j, ProposerRationalOnPath Γ j) (j₀ : Fin n) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (t ρ ε : ℝ) (ht0 : 0 < t) (hε : 0 ≤ ε) (ht : ρ - ε ≤ alphaGt Γ j₀ t) :
    (n : ℝ) * ((c : ℝ) / m) - finiteLoad Γ ≤
      n * (ε + |(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m)) := by
  rw [← sum_unusedCapacity_eq_load_gap, Finset.sum_div]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun j _ =>
    integral_unusedCapacity_normalized_le Γ hm j (hΓ j) a ha hA t ρ ε ht0 hε
      (by rwa [alphaGt_eq Γ j j₀]))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh

theorem tendsto_finiteLoad_of_visible_tail
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j₀ : Fin n)
    (a : ℕ → ℝ) (t ρ : ℝ) (ht : 0 < t)
    (hM : Tendsto M atTop atTop)
    (ha : ∀ᶠ k in atTop, 0 < a k)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (hΓ : ∀ k j, ProposerRationalOnPath (Γ k) j)
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (htail : ∀ ε > 0, ∀ᶠ k in atTop, ρ - ε ≤ alphaGt (Γ k) j₀ t) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) := by
  have hmc : Tendsto (fun k => (M k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hM
  have hs : Tendsto (fun k => 1 / (2 * Real.sqrt (M k))) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmc)).div_const 2
    simpa only [zero_div, one_div, mul_inv_rev, div_eq_mul_inv, Function.comp_def, one_mul, zero_mul] using hh
  have hg : Tendsto (fun k => |(C k : ℝ) / M k - ρ|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hcap.sub_const ρ).abs
  have hgap : Tendsto (fun k => (n : ℝ) * ((C k : ℝ) / M k) - finiteLoad (Γ k))
      atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro z hz
      exact Eventually.of_forall fun k => hz.trans_le (sub_nonneg.mpr (finiteLoad_le_capacity (Γ k)))
    · intro z hz
      let ε := z / (2 * ((n : ℝ) + 1))
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hsmall : (n : ℝ) * ε < z := by
        have hh : ε * (2 * ((n : ℝ) + 1)) = z := div_mul_cancel₀ _ (by positivity)
        nlinarith
      have hright : Tendsto (fun k => (n : ℝ) *
          (ε + |(C k : ℝ) / M k - ρ| + 1 / (2 * Real.sqrt (M k))))
          atTop (𝓝 ((n : ℝ) * ε)) := by
        simpa using ((hg.const_add ε).add hs).const_mul (n : ℝ)
      filter_upwards [ha, hM.eventually_gt_atTop 0, htail ε hε,
        (tendsto_order.mp hright).2 z hsmall] with k ha hm htail hright
      exact (capacity_gap_le_visible_shortfall (Γ k) hm (hΓ k) j₀ (a k) ha (hA k)
        t ρ ε ht hε.le htail).trans_lt hright
  have hh := (hcap.const_mul (n : ℝ)).sub hgap
  simpa only [sub_sub_cancel, sub_zero] using hh

end FCAppendix.Bayes
