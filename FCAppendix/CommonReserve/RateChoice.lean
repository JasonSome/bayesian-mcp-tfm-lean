import FCAppendix.CommonReserve.Quantiles

noncomputable section
namespace FCAppendix.CommonReserve
open MeasureTheory Filter Set Topology

def marketSlack (m c : ℕ) : ℝ :=
  min ((c : ℝ) / m / 2) (1 / Real.sqrt (Real.sqrt (m : ℝ)))

def singletonFailure (m c : ℕ) : ℝ :=
  1 / ((m : ℝ) * marketSlack m c ^ 2)

def slotError (m c : ℕ) : ℝ := marketSlack m c + 1 / (2 * Real.sqrt (m : ℝ))

theorem marketSlack_pos (m c : ℕ) (hm : 0 < m) (hc : 0 < c) :
    0 < marketSlack m c := by
  unfold marketSlack
  apply lt_min
  · positivity
  · positivity

theorem marketSlack_le_half (m c : ℕ) : marketSlack m c ≤ (c : ℝ) / m / 2 :=
  min_le_left _ _

theorem marketSlack_lt_capacity (m c : ℕ) (hm : 0 < m) (hc : 0 < c) :
    marketSlack m c < (c : ℝ) / m := by
  have hκ : (0 : ℝ) < (c : ℝ) / m := by positivity
  exact (marketSlack_le_half m c).trans_lt (by linarith)

theorem singletonFailure_nonneg (m c : ℕ) : 0 ≤ singletonFailure m c := by
  unfold singletonFailure
  positivity

theorem binomialFailure_le (m c : ℕ) (hm : 0 < m) (hc : 0 < c) :
    ((m - 1 : ℕ) : ℝ) / (4 * ((m : ℝ) * marketSlack m c) ^ 2) ≤ singletonFailure m c := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hd := marketSlack_pos m c hm hc
  have hmr : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
  unfold singletonFailure
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hmr
    (show (0 : ℝ) ≤ (m : ℝ) * marketSlack m c ^ 2 by positivity),
    sq_nonneg ((m : ℝ) * marketSlack m c)]

theorem slotError_nonneg (m c : ℕ) (hm : 0 < m) (hc : 0 < c) :
    0 ≤ slotError m c := by
  exact add_nonneg (marketSlack_pos m c hm hc).le (by positivity)

theorem marketSlack_tendsto (M C : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hM : Tendsto M atTop atTop)
    (hκ : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)) :
    Tendsto (fun k => marketSlack (M k) (C k)) atTop (𝓝 0) := by
  have hroot := Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM))
  have hsmall := tendsto_inv_atTop_zero.comp hroot
  have h := (hκ.div_const 2).min hsmall
  simpa only [marketSlack, one_div, Function.comp_def,
    min_eq_right (by positivity : 0 ≤ ρ / 2)] using h

theorem eventually_marketSlack_eq (M C : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hM : Tendsto M atTop atTop)
    (hκ : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)) :
    ∀ᶠ k in atTop, marketSlack (M k) (C k) =
      1 / Real.sqrt (Real.sqrt (M k : ℝ)) := by
  have hroot := Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM))
  have hsmall : Tendsto (fun k => 1 / Real.sqrt (Real.sqrt (M k : ℝ)))
      atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hroot
  filter_upwards [hκ.eventually (lt_mem_nhds (show ρ / 2 < ρ by linarith)),
    hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < ρ / 4 by linarith))] with k hk hs
  exact min_eq_right (by linarith)

theorem singletonFailure_tendsto (M C : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hM : Tendsto M atTop atTop)
    (hκ : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)) :
    Tendsto (fun k => singletonFailure (M k) (C k)) atTop (𝓝 0) := by
  have hroot := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hsmall : Tendsto (fun k => 1 / Real.sqrt (M k : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hroot
  apply hsmall.congr'
  filter_upwards [eventually_marketSlack_eq M C ρ hρ hM hκ,
    hM.eventually_gt_atTop 0] with k hk hm
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hm
  have hs : 0 < Real.sqrt (M k : ℝ) := Real.sqrt_pos.mpr hmR
  have he : (Real.sqrt (M k : ℝ)) ^ 2 = M k := Real.sq_sqrt hmR.le
  have he' : (Real.sqrt (Real.sqrt (M k : ℝ))) ^ 2 = Real.sqrt (M k : ℝ) :=
    Real.sq_sqrt hs.le
  unfold singletonFailure
  rw [hk, div_pow, one_pow, he']
  field_simp [hs.ne', hmR.ne']
  nlinarith [he]

theorem slotError_tendsto (M C : ℕ → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (hM : Tendsto M atTop atTop)
    (hκ : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ)) :
    Tendsto (fun k => slotError (M k) (C k)) atTop (𝓝 0) := by
  have hroot := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hsmall := (tendsto_inv_atTop_zero.comp hroot).div_const 2
  have h := (marketSlack_tendsto M C ρ hρ hM hκ).add hsmall
  simpa [slotError, one_div, mul_inv_rev, div_eq_mul_inv, mul_comm] using h

theorem exists_positive_lower_bound {κ : ℕ → ℝ} {ρ : ℝ}
    (hκ : ∀ k, 0 < κ k) (hρ : 0 < ρ) (ht : Tendsto κ atTop (𝓝 ρ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ k, a ≤ κ k := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually
    (lt_mem_nhds (show ρ / 2 < ρ by linarith)))
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (N + 1)))
    (fun j => κ j.val) ⟨0, Finset.mem_univ 0⟩
  refine ⟨min (ρ / 2) (κ j.val), lt_min (by linarith) (hκ _), ?_⟩
  intro k
  by_cases hk : k < N
  · exact (min_le_right _ _).trans (hj ⟨k, by omega⟩ (Finset.mem_univ _))
  · exact (min_le_left _ _).trans (hN k (by omega)).le

theorem bounded_reserve_prices {n : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) r Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (hn : 0 < n) (hm : ∀ k, 0 < M k) (hc : ∀ k, 0 < C k) (hρ : 0 < ρ)
    (hκ : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (htail : ∀ k j b, (n : ℝ) * g ≤ b →
      bidTail (Γ k) j b ≤ F.real (Ioi (g + b - (n : ℝ) * g))) :
    ∃ B : ℝ, ∀ k, price (Γ k) (marketSlack (M k) (C k)) ≤ B := by
  obtain ⟨a, ha, haκ⟩ := exists_positive_lower_bound
    (κ := fun k => (C k : ℝ) / M k)
    (fun k => div_pos (Nat.cast_pos.mpr (hc k)) (Nat.cast_pos.mpr (hm k))) hρ hκ
  have htailF : Tendsto (fun b : ℝ => F.real (Ioi (g + b - (n : ℝ) * g)))
      atTop (𝓝 0) := by
    apply (TailQuantile.tail_tendsto_zero F).comp
    exact (tendsto_atTop_add_const_left atTop (g - (n : ℝ) * g) tendsto_id).congr
      (fun _ => by dsimp; ring)
  obtain ⟨B, hB, hmassF⟩ := ((eventually_ge_atTop (max r ((n : ℝ) * g))).and
    (htailF.eventually (gt_mem_nhds (show (0 : ℝ) < a / 2 by linarith)))).exists
  have hBr := (le_max_left r ((n : ℝ) * g)).trans hB
  have hBn := (le_max_right r ((n : ℝ) * g)).trans hB
  refine ⟨B, fun k => ?_⟩
  let j : Fin n := ⟨0, hn⟩
  apply (price_le_quantile (Γ k) (marketSlack (M k) (C k)) j).trans
  change ReserveQuantile.quantile (bidTail (Γ k) j) r
    ((C k : ℝ) / M k - marketSlack (M k) (C k)) ≤ B
  have hmass : bidTail (Γ k) j B ≤ a / 2 := (htail k j B hBn).trans hmassF.le
  exact ReserveQuantile.le_of_tail_le hBr (hmass.trans (by
    have hδ := marketSlack_le_half (M k) (C k)
    have hk := haκ k
    linarith))

end FCAppendix.CommonReserve
