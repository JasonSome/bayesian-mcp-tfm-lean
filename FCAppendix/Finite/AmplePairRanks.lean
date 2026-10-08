import FCAppendix.Finite.PairDuplicates

noncomputable section

namespace FCAppendix.BernoulliPairs
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

variable {Ω' : ℕ → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (μ' : (n : ℕ) → Measure (Ω' n)) [∀ n, IsProbabilityMeasure (μ' n)]
    (N' : ℕ → ℕ) (X' : (n : ℕ) → Fin (N' n) → Fin 2 → Ω' n → ℝ)
    (p' σ' : ℕ → ℝ)

theorem eventually_joint_pos_of_correlation_floor
    (hXm : ∀ n i j, Measurable (X' n i j))
    (hX : ∀ n i j, ∀ᵐ ω ∂μ' n, X' n i j ω = 0 ∨ X' n i j ω = 1)
    (hm : ∀ n i j, ∫ ω, X' n i j ω ∂μ' n = p' n)
    (hXi : ∀ n, iIndepFun (pair (X' n)) (μ' n))
    (hσ : ∀ n, 0 < σ' n)
    (hvar : ∀ n, (N' n : ℝ) * p' n * (1 - p' n) = σ' n ^ 2)
    (hσlim : Tendsto σ' atTop atTop) {p₀ κ : ℝ}
    (hp : Tendsto p' atTop (𝓝 p₀)) (hp₀ : 0 < p₀) (hp₁ : p₀ < 1)
    (hκ : -1 < κ)
    (hfloor : ∀ᶠ n in atTop,
      κ ≤ (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2)
    (a : ℝ) (t : ℕ → ℝ) (ht : ∀ᶠ n in atTop, a ≤ t n) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, q ≤
      (μ' n).real {ω | load (X' n) (p' n) (σ' n) 0 ω ≤ t n ∧
        load (X' n) (p' n) (σ' n) 1 ω ≤ t n} := by
  let r : ℕ → ℝ := fun n =>
    (∑ i, covariance (X' n i 0) (X' n i 1) (μ' n)) / σ' n ^ 2
  have hr : ∀ᶠ n in atTop, r n ∈ Set.Icc κ 1 := by
    filter_upwards [hfloor, hp.eventually (eventually_gt_nhds hp₀),
      hp.eventually (eventually_lt_nhds hp₁)] with n hn hn0 hn1
    exact ⟨hn, (correlation_bounds _ _ _ (hXm n) (hX n) (hm n)
      hn0 hn1 (hσ n) (hvar n)).2⟩
  apply eventually_pos_of_compact_subsequences r _ κ 1 hr
    (fun _ => measureReal_nonneg)
  intro f hf r₀ hrf
  have hlo : κ ≤ r₀ := ge_of_tendsto hrf (hf.eventually (hr.mono fun _ h => h.1))
  have hhi : r₀ ≤ 1 := le_of_tendsto hrf (hf.eventually (hr.mono fun _ h => h.2))
  by_cases he : r₀ = 1
  · subst r₀
    exact ⟨cdf (gaussianReal 0 1) (a - 1) / 2,
      div_pos (CorrelatedLoads.gaussian_cdf_pos _) (by norm_num),
      eventually_joint_pos_of_correlation_one (fun n => μ' (f n))
        (fun n => N' (f n)) (fun n => X' (f n)) (fun n => p' (f n))
        (fun n => σ' (f n)) (fun n => hXm (f n)) (fun n => hX (f n))
        (fun n => hm (f n)) (fun n => hXi (f n)) (fun n => hσ (f n))
        (fun n => hvar (f n)) (hσlim.comp hf) hrf a (t ∘ f) (hf.eventually ht)⟩
  · exact eventually_joint_pos_of_nondegenerate_correlation (fun n => μ' (f n))
      (fun n => N' (f n)) (fun n => X' (f n)) (fun n => p' (f n))
      (fun n => σ' (f n)) (fun n => hXm (f n)) (fun n => hX (f n))
      (fun n => hm (f n)) (fun n => hXi (f n)) (fun n => hσ (f n))
      (fun n => hvar (f n)) (hσlim.comp hf) (hp.comp hf) hp₀ hp₁ hrf
      (abs_lt.mpr ⟨hκ.trans_le hlo, lt_of_le_of_ne hhi he⟩) a (t ∘ f) (hf.eventually ht)

end FCAppendix.BernoulliPairs

namespace FCAppendix.Game
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma permLaw_mul_right {n : ℕ} (P : Equiv.Perm (Fin n) → Prop)
    (π : Equiv.Perm (Fin n)) :
    permLaw n {τ | P (τ * π)} = permLaw n {τ | P τ} := by
  classical
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (permLaw n).real _ = (permLaw n).real _
  rw [permLaw_real_filter, permLaw_real_filter]
  congr 2
  apply Finset.card_nbij' (fun τ => τ * π) (fun τ => τ * π⁻¹)
  · intro τ hτ
    simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] using hτ
  · intro τ hτ
    simpa only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
      mul_assoc, inv_mul_cancel, mul_one] using hτ
  · intro τ _
    simp [mul_assoc]
  · intro τ _
    simp [mul_assoc]

end FCAppendix.Game

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma measure_aboveAt_pair_perm (Γ : FiniteGame m n c Seed) (j l : Fin n)
    (b : ℝ) (π : Equiv.Perm (Fin n)) :
    userLaw Γ (aboveAt (π j) b ∩ aboveAt (π l) b) =
      userLaw Γ (aboveAt j b ∩ aboveAt l b) := by
  rw [userLaw, Measure.prod_apply ((measurableSet_aboveAt _ _).inter
    (measurableSet_aboveAt _ _)), Measure.prod_apply ((measurableSet_aboveAt _ _).inter
    (measurableSet_aboveAt _ _))]
  apply lintegral_congr
  intro x
  convert permLaw_mul_right
    (fun τ : Equiv.Perm (Fin n) =>
      (j ∈ firstK τ x.2.routeCount ∧ b < x.2.bid) ∧
      (l ∈ firstK τ x.2.routeCount ∧ b < x.2.bid)) π using 1 <;>
    congr 1; ext τ; simp [aboveAt, mem_firstK, Equiv.Perm.mul_apply]

def higherBidContact (j : Fin n) (b : ℝ) (d : UserDraw n) : ℝ :=
  by classical exact if d ∈ aboveAt j b then 1 else 0

lemma higherBidContact_measurable (j : Fin n) (b : ℝ) :
    Measurable (higherBidContact j b) := by
  classical
  exact Measurable.ite (measurableSet_aboveAt _ _) measurable_const measurable_const

lemma higherBidContact_bernoulli (j : Fin n) (b : ℝ) (d : UserDraw n) :
    higherBidContact j b d = 0 ∨ higherBidContact j b d = 1 := by
  unfold higherBidContact
  split_ifs <;> simp

lemma higherBidContact_memLp (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ) :
    MemLp (higherBidContact j b) 2 (userLaw Γ) :=
  BernoulliApproximation.memLp_bernoulli (higherBidContact_measurable j b)
    (Filter.Eventually.of_forall (higherBidContact_bernoulli j b)) 2

lemma integral_higherBidContact (Γ : FiniteGame m n c Seed) (j : Fin n) (b : ℝ) :
    (∫ d, higherBidContact j b d ∂userLaw Γ) = alphaGt Γ j b :=
  integral_indicator_one (measurableSet_aboveAt j b)

lemma covariance_higherBidContact (Γ : FiniteGame m n c Seed) (j l : Fin n) (b : ℝ) :
    covariance (higherBidContact j b) (higherBidContact l b) (userLaw Γ) =
      (userLaw Γ).real (aboveAt j b ∩ aboveAt l b) - (alphaGt Γ j b) ^ 2 := by
  classical
  rw [covariance_eq_sub (higherBidContact_memLp Γ j b) (higherBidContact_memLp Γ l b),
    integral_higherBidContact, integral_higherBidContact, alphaGt_eq Γ l j]
  have he : higherBidContact j b * higherBidContact l b =
      (aboveAt j b ∩ aboveAt l b).indicator (fun _ => (1 : ℝ)) := by
    ext d
    simp only [Pi.mul_apply, higherBidContact, Set.indicator_apply, Set.mem_inter_iff]
    split_ifs <;> simp_all
  rw [he]
  have hi := integral_indicator_one (μ := userLaw Γ)
    ((measurableSet_aboveAt j b).inter (measurableSet_aboveAt l b))
  change (∫ d, (aboveAt j b ∩ aboveAt l b).indicator (fun _ => (1 : ℝ)) d
    ∂userLaw Γ) = _ at hi
  rw [hi]
  ring

lemma covariance_higherBidContact_perm (Γ : FiniteGame m n c Seed) (j l : Fin n)
    (b : ℝ) (π : Equiv.Perm (Fin n)) :
    covariance (higherBidContact (π j) b) (higherBidContact (π l) b) (userLaw Γ) =
      covariance (higherBidContact j b) (higherBidContact l b) (userLaw Γ) := by
  rw [covariance_higherBidContact, covariance_higherBidContact,
    alphaGt_eq Γ (π j) j]
  exact congrArg (fun s => s.toReal - (alphaGt Γ j b) ^ 2)
    (measure_aboveAt_pair_perm Γ j l b π)

lemma higherBidContact_covariance_lower_three (Γ : FiniteGame m n c Seed)
    (j l k : Fin n) (hjl : j ≠ l) (hjk : j ≠ k) (hlk : l ≠ k) (b : ℝ) :
    -(1 / 2 : ℝ) * (alphaGt Γ j b * (1 - alphaGt Γ j b)) ≤
      covariance (higherBidContact j b) (higherBidContact l b) (userLaw Γ) := by
  let X := higherBidContact j b
  let Y := higherBidContact l b
  let Z := higherBidContact k b
  have hX := higherBidContact_memLp Γ j b
  have hY := higherBidContact_memLp Γ l b
  have hZ := higherBidContact_memLp Γ k b
  have hXZ : covariance X Z (userLaw Γ) = covariance X Y (userLaw Γ) := by
    simpa only [Equiv.swap_apply_of_ne_of_ne hjl hjk, Equiv.swap_apply_left] using
      covariance_higherBidContact_perm Γ j l b (Equiv.swap l k)
  have hYZ : covariance Y Z (userLaw Γ) = covariance X Y (userLaw Γ) := by
    have hh := covariance_higherBidContact_perm Γ j l b (Equiv.swap j k)
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hjl.symm hlk,
      covariance_comm] using hh
  have hv (q : Fin n) : variance (higherBidContact q b) (userLaw Γ) =
      alphaGt Γ j b * (1 - alphaGt Γ j b) := by
    rw [BernoulliApproximation.bernoulli_variance (higherBidContact_measurable q b)
      (Filter.Eventually.of_forall (higherBidContact_bernoulli q b)),
      integral_higherBidContact, alphaGt_eq Γ q j]
  have hh := variance_nonneg (X + Y + Z) (userLaw Γ)
  rw [variance_add (hX.add hY) hZ, variance_add hX hY,
    covariance_add_left hX hY hZ, hXZ, hYZ, hv, hv, hv] at hh
  linarith

lemma aboveAt_union_le_active (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ) (j l : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    (userLaw Γ).real (aboveAt j b ∪ aboveAt l b) ≤ Γ.F.real (Set.Ioi Γ.g) := by
  have hsub : (aboveAt j b ∪ aboveAt l b : Set (UserDraw n)) ≤ᵐ[userLaw Γ]
      {d : UserDraw n | Γ.g < d.1.1} := by
    filter_upwards [ae_no_overbid_userLaw_onPath Γ hm hc hΓ] with d hd hreach
    have hreach' : ∃ q : Fin n, q ∈ firstK d.2 d.1.2.routeCount ∧ b < d.1.2.bid := by
      rcases hreach with h | h
      · exact ⟨j, h⟩
      · exact ⟨l, h⟩
    obtain ⟨q, hq, hbid⟩ := hreach'
    have hk : 0 < d.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨q, hq⟩
      rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
    have hmax := lt_of_lt_of_le hbid (hd hk)
    rcases lt_max_iff.mp hmax with hv | hz
    · change Γ.g < d.1.1
      linarith
    · exact (not_lt_of_ge hb hz).elim
  have hbound := measure_mono_ae hsub
  have he : userLaw Γ {d : UserDraw n | Γ.g < d.1.1} = Γ.F (Set.Ioi Γ.g) := by
    rw [← userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  change (userLaw Γ (aboveAt j b ∪ aboveAt l b)).toReal ≤ (Γ.F (Set.Ioi Γ.g)).toReal
  rw [← he]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hbound

lemma higherBidContact_covariance_lower_union (Γ : FiniteGame m n c Seed)
    (j l : Fin n) (b H : ℝ)
    (hunion : (userLaw Γ).real (aboveAt j b ∪ aboveAt l b) ≤ H) :
    2 * alphaGt Γ j b - H - (alphaGt Γ j b) ^ 2 ≤
      covariance (higherBidContact j b) (higherBidContact l b) (userLaw Γ) := by
  have hh := measureReal_union_add_inter (μ := userLaw Γ) (s := aboveAt j b)
    (measurableSet_aboveAt l b)
  change _ + _ = alphaGt Γ j b + alphaGt Γ l b at hh
  rw [alphaGt_eq Γ l j] at hh
  rw [covariance_higherBidContact]
  linarith

lemma covariance_pairRankIndicators (Γ : FiniteGame (m + 1) n c Seed)
    (i : Fin (m + 1)) (j : Fin 2 → Fin n) (b : ℝ) (l : Fin m) :
    covariance (pairRankIndicators i j b l 0) (pairRankIndicators i j b l 1)
      (Measure.pi fun _ : Fin (m + 1) => userLaw Γ) =
    covariance (higherBidContact (j 0) b) (higherBidContact (j 1) b) (userLaw Γ) := by
  have he := measurePreserving_eval (fun _ : Fin (m + 1) => userLaw Γ) (i.succAbove l)
  have hh := covariance_map (μ := Measure.pi fun _ : Fin (m + 1) => userLaw Γ)
    (higherBidContact_measurable (j 0) b).aestronglyMeasurable
    (higherBidContact_measurable (j 1) b).aestronglyMeasurable he.measurable.aemeasurable
  rw [he.map_eq] at hh
  exact hh.symm

lemma ample_two_correlation_floor {ρ H : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hH : H ≤ 1) (hample : H < 2 * ρ) :
    -1 < (2 * ρ - H - ρ ^ 2) / (ρ * (1 - ρ)) := by
  rw [lt_div_iff₀ (mul_pos hρ0 (sub_pos.mpr hρ1))]
  by_cases h : ρ ≤ 1 / 2
  · have hnon : 0 ≤ ρ * (1 - 2 * ρ) := mul_nonneg hρ0.le (by linarith)
    nlinarith
  · have hpos : 0 < (1 - ρ) * (2 * ρ - 1) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem eventually_pairRank_correlation_floor
    (M : ℕ → ℕ) (C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (j : Fin 2 → Fin n) (hj : j 0 ≠ j 1)
    (b σ : ℕ → ℝ) (hσ : ∀ r, 0 < σ r)
    (hvar : ∀ r, (M r : ℝ) * alphaGt (Γ r) (j 0) (b r) *
      (1 - alphaGt (Γ r) (j 0) (b r)) = σ r ^ 2)
    {ρ H : ℝ} (hp : Tendsto (fun r => alphaGt (Γ r) (j 0) (b r)) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r, (userLaw (Γ r)).real (aboveAt (j 0) (b r) ∪ aboveAt (j 1) (b r)) ≤ H) :
    ∃ κ : ℝ, -1 < κ ∧ ∀ᶠ r in atTop, κ ≤
      (∑ l, covariance (pairRankIndicators (i r) j (b r) l 0)
        (pairRankIndicators (i r) j (b r) l 1)
        (Measure.pi fun _ : Fin (M r + 1) => userLaw (Γ r))) / σ r ^ 2 := by
  classical
  have hn : 2 ≤ n := by
    by_contra hh
    have hjval := (j 0).isLt
    have hlval := (j 1).isLt
    have he : j 0 = j 1 := Fin.ext (by omega)
    exact hj he
  by_cases hn3 : 2 < n
  · obtain ⟨k, hkj, hkl⟩ := Fin.exists_ne_and_ne_of_two_lt (j 0) (j 1) hn3
    refine ⟨-1 / 2, by norm_num, Filter.Eventually.of_forall fun r => ?_⟩
    simp_rw [covariance_pairRankIndicators]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply (le_div_iff₀ (sq_pos_of_pos (hσ r))).mpr
    rw [← hvar r]
    have hc := higherBidContact_covariance_lower_three (Γ r) (j 0) (j 1) k
      hj hkj.symm hkl.symm (b r)
    have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (M r) : (0 : ℝ) ≤ M r)
    nlinarith
  · have hn2 : n = 2 := by omega
    let p := fun r => alphaGt (Γ r) (j 0) (b r)
    let κ₀ := (2 * ρ - H - ρ ^ 2) / (ρ * (1 - ρ))
    have hk0 : -1 < κ₀ := ample_two_correlation_floor hρ0 hρ1 hH (by simpa [hn2] using hample)
    let κ := (-1 + κ₀) / 2
    have hk : -1 < κ := by dsimp only [κ]; linarith
    have hklt : κ < κ₀ := by dsimp only [κ]; linarith
    have hlim : Tendsto (fun r => (2 * p r - H - p r ^ 2) / (p r * (1 - p r)))
        atTop (𝓝 κ₀) :=
      (((hp.const_mul 2).sub_const H).sub (hp.pow 2)).div
        (hp.mul (tendsto_const_nhds.sub hp)) (ne_of_gt (mul_pos hρ0 (sub_pos.mpr hρ1)))
    refine ⟨κ, hk, ?_⟩
    filter_upwards [hlim.eventually (eventually_gt_nhds hklt),
      hp.eventually (eventually_gt_nhds hρ0), hp.eventually (eventually_lt_nhds hρ1)]
      with r hr hp0 hp1
    have hlo := higherBidContact_covariance_lower_union (Γ r) (j 0) (j 1) (b r) H (hunion r)
    have hc : (2 * p r - H - p r ^ 2) / (p r * (1 - p r)) ≤
        (∑ l, covariance (pairRankIndicators (i r) j (b r) l 0)
          (pairRankIndicators (i r) j (b r) l 1)
          (Measure.pi fun _ : Fin (M r + 1) => userLaw (Γ r))) / σ r ^ 2 := by
      simp_rw [covariance_pairRankIndicators]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      apply (le_div_iff₀ (sq_pos_of_pos (hσ r))).mpr
      rw [← hvar r]
      have hh := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (M r) : (0 : ℝ) ≤ M r)
      have he : (2 * p r - H - p r ^ 2) / (p r * (1 - p r)) *
          ((M r : ℝ) * p r * (1 - p r)) = (M r : ℝ) * (2 * p r - H - p r ^ 2) := by
        field_simp [show p r ≠ 0 from ne_of_gt hp0,
          show 1 - p r ≠ 0 from ne_of_gt (sub_pos.mpr hp1)]
      rw [he]
      exact hh
    exact hr.le.trans hc

theorem eventually_ample_ppi_pair_acceptance_pos
    (M C : ℕ → ℕ) (Γ : (m : ℕ) → FiniteGame (M m + 1) n (C m) Seed)
    (i : (m : ℕ) → Fin (M m + 1)) (j : Fin 2 → Fin n) (b σ : ℕ → ℝ)
    (hA : ∀ m, (Γ m).A = Schedule.ppi n)
    (hatom : ∀ m, PositiveVisibleAtomless (Γ m))
    (hj : ∀ m k, ProposerRationalAtFeasibleLists (Γ m) (j k))
    (hb : ∀ m, 0 < b m) (hσ : ∀ m, 0 < σ m)
    (hvar : ∀ m, (M m : ℝ) * alphaGt (Γ m) (j 0) (b m) *
      (1 - alphaGt (Γ m) (j 0) (b m)) = σ m ^ 2)
    (hσlim : Tendsto σ atTop atTop) {ρ : ℝ}
    (hp : Tendsto (fun m => alphaGt (Γ m) (j 0) (b m)) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdist : j 0 ≠ j 1) (H : ℝ) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r, (userLaw (Γ r)).real (aboveAt (j 0) (b r) ∪ aboveAt (j 1) (b r)) ≤ H) (a : ℝ)
    (ht : ∀ᶠ m in atTop, a ≤ pairRankThreshold (M m) (C m) (alphaGt (Γ m) (j 0) (b m)) (σ m)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ m in atTop, d ≤ (backgroundLaw (Γ m)).real
      {ω | Accepts (Γ m) (i m) (b m) (j 0) ω ∧ Accepts (Γ m) (i m) (b m) (j 1) ω} := by
  let μ := fun m => Measure.pi (fun _ : Fin (M m + 1) => userLaw (Γ m))
  obtain ⟨κ, hκ, hfloor⟩ := eventually_pairRank_correlation_floor M C Γ i j hdist b σ
    hσ hvar hp hρ0 hρ1 hH hample hunion
  have hpair := BernoulliPairs.eventually_joint_pos_of_correlation_floor μ M
    (fun m => pairRankIndicators (i m) j (b m))
    (fun m => alphaGt (Γ m) (j 0) (b m)) σ
    (fun m => pairRankIndicators_measurable (i m) j (b m))
    (fun m l k => Filter.Eventually.of_forall (pairRankIndicators_bernoulli (i m) j (b m) l k))
    (fun m => pairRankIndicators_integral (Γ m) (i m) j (b m))
    (fun m => pairRankIndicators_indep (Γ m) (i m) j (b m))
    hσ hvar hσlim hp hρ0 hρ1 hκ hfloor a
    (fun m => pairRankThreshold (M m) (C m) (alphaGt (Γ m) (j 0) (b m)) (σ m)) ht
  obtain ⟨d, hd, hde⟩ := hpair
  refine ⟨d, hd, ?_⟩
  filter_upwards [hde] with m hm
  rw [ppi_pair_acceptance_eq_normalized (Γ m) (hA m) (hatom m) j (hj m) (i m) (b m) (hb m) (σ m) (hσ m)]
  exact hm

theorem eventually_nonrare_ample_ppi_pair_acceptance_pos
    (M C : ℕ → ℕ) (Γ : (m : ℕ) → FiniteGame (M m + 1) n (C m) Seed)
    (i : (m : ℕ) → Fin (M m + 1)) (j : Fin 2 → Fin n) (b σ : ℕ → ℝ)
    (hA : ∀ m, (Γ m).A = Schedule.ppi n)
    (hatom : ∀ m, PositiveVisibleAtomless (Γ m))
    (hj : ∀ m k, ProposerRationalAtFeasibleLists (Γ m) (j k))
    (hb : ∀ m, 0 < b m) (hσ : ∀ m, 0 < σ m)
    (hvar : ∀ m, (M m : ℝ) * alphaGt (Γ m) (j 0) (b m) *
      (1 - alphaGt (Γ m) (j 0) (b m)) = σ m ^ 2)
    (hσlim : Tendsto σ atTop atTop) {ρ : ℝ}
    (hp : Tendsto (fun m => alphaGt (Γ m) (j 0) (b m)) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdist : j 0 ≠ j 1) (H : ℝ) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r, (userLaw (Γ r)).real (aboveAt (j 0) (b r) ∪ aboveAt (j 1) (b r)) ≤ H) (ε : ℝ) (hε : 0 < ε)
    (hq : ∀ᶠ m in atTop, ε ≤ binomBelow (M m) (alphaGt (Γ m) (j 0) (b m)) (C m)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ m in atTop, d ≤ (backgroundLaw (Γ m)).real
      {ω | Accepts (Γ m) (i m) (b m) (j 0) ω ∧ Accepts (Γ m) (i m) (b m) (j 1) ω} := by
  apply eventually_ample_ppi_pair_acceptance_pos M C Γ i j b σ hA hatom hj hb hσ hvar hσlim hp
    hρ0 hρ1 hdist H hH hample hunion (-Real.sqrt (2 / ε))
  filter_upwards [hq] with m hm
  exact nonrare_pairRankThreshold_ge (Γ m) (i m) j (b m) (σ m) (hσ m) (hvar m) ε hε hm

theorem eventually_nonrare_ample_ppi_pair_pos
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (j : Fin 2 → Fin n) (b : ℕ → ℝ)
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r k, ProposerRationalAtFeasibleLists (Γ r) (j k))
    (hb : ∀ r, 0 < b r) (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdist : j 0 ≠ j 1) (H : ℝ) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r, (userLaw (Γ r)).real (aboveAt (j 0) (b r) ∪ aboveAt (j 1) (b r)) ≤ H)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε)
    (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r) (alphaGt (Γ r) (j 0) (b r)) (C r)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, d ≤ (backgroundLaw (Γ r)).real
      {ω | Accepts (Γ r) (i r) (b r) (j 0) ω ∧ Accepts (Γ r) (i r) (b r) (j 1) ω} := by
  let p : ℕ → ℝ := fun r => alphaGt (Γ r) (j 0) (b r)
  have hp0 : ∀ r, 0 ≤ p r := fun _ => measureReal_nonneg
  have hp1 : ∀ r, p r ≤ 1 := fun _ => measureReal_le_one
  apply BernoulliPairs.eventually_pos_of_compact_subsequences p _ 0 1
    (Filter.Eventually.of_forall fun r => ⟨hp0 r, hp1 r⟩) (fun _ => measureReal_nonneg)
  intro f hf p₀ hpf
  have hpρ := nonrare_rank_limit_le_capacity (M ∘ f) (C ∘ f) (p ∘ f) (hM.comp hf)
    (fun r => hC (f r)) (fun r => hp0 (f r)) (fun r => hp1 (f r)) hpf (hc.comp hf) ε hε (hf.eventually hq)
  by_cases hlt : p₀ < ρ
  · have hq1 := binomBelow_tendsto_one_of_subcritical (M ∘ f) (C ∘ f) (p ∘ f)
      (hM.comp hf) (fun r => hC (f r)) (fun r => hp0 (f r)) (fun r => hp1 (f r)) hpf (hc.comp hf) hlt
    refine ⟨1 / 2, by norm_num, ?_⟩
    filter_upwards [hq1.eventually (eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1))] with r hr
    have hh := ppi_pair_acceptance_ge_two_rank_sub_one (Γ (f r)) (hA (f r)) (hatom (f r))
      (i (f r)) j (hj (f r)) (b (f r)) (hb (f r))
    dsimp only [Function.comp_def, p] at hr
    linarith
  · have heq : p₀ = ρ := le_antisymm hpρ (le_of_not_gt hlt)
    subst p₀
    let σ : ℕ → ℝ := fun r => Real.sqrt ((M (f r) : ℝ) * p (f r) * (1 - p (f r)))
    have hv : ∀ r, (M (f r) : ℝ) * p (f r) * (1 - p (f r)) = σ r ^ 2 := by
      intro r
      exact (Real.sq_sqrt (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp0 _))
        (sub_nonneg.mpr (hp1 _)))).symm
    have hs : Tendsto σ atTop atTop := by
      have hpv : Tendsto (fun r => p (f r) * (1 - p (f r))) atTop (𝓝 (ρ * (1 - ρ))) :=
        hpf.mul (tendsto_const_nhds.sub hpf)
      have hN : Tendsto (fun r => (M (f r) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (hM.comp hf)
      have hvarlim := hN.atTop_mul_pos (mul_pos hρ0 (by linarith : 0 < 1 - ρ)) hpv
      simpa only [σ, Function.comp_def, mul_assoc] using Real.tendsto_sqrt_atTop.comp hvarlim
    obtain ⟨L, hL⟩ := eventually_atTop.mp (hs.eventually_gt_atTop 0)
    let g : ℕ → ℕ := fun r => f (r + L)
    have hg : Tendsto g atTop atTop := hf.comp (tendsto_add_atTop_nat L)
    obtain ⟨d, hd, hde⟩ := eventually_nonrare_ample_ppi_pair_acceptance_pos (M ∘ g) (C ∘ g)
      (fun r => Γ (g r)) (fun r => i (g r)) j (b ∘ g) (fun r => σ (r + L))
      (fun r => hA (g r)) (fun r => hatom (g r)) (fun r => hj (g r)) (fun r => hb (g r))
      (fun r => hL (r + L) (by omega)) (fun r => hv (r + L)) (hs.comp (tendsto_add_atTop_nat L))
      (hpf.comp (tendsto_add_atTop_nat L)) hρ0 hρ1 hdist H hH hample
      (fun r => hunion (g r)) ε hε (hg.eventually hq)
    refine ⟨d, hd, ?_⟩
    let P : ℕ → ℝ := fun r => (backgroundLaw (Γ (f r))).real
      {ω | Accepts (Γ (f r)) (i (f r)) (b (f r)) (j 0) ω ∧
        Accepts (Γ (f r)) (i (f r)) (b (f r)) (j 1) ω}
    have hshift : ∀ᶠ r in Filter.map (fun r : ℕ => r + L) atTop, d ≤ P r := hde
    simpa only [map_add_atTop_eq_nat] using hshift

theorem eventually_nonrare_ample_ppi_duplicates_pos
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (a : ℕ → JointAction n)
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hb : ∀ r, 0 < (a r).bid) (hk : ∀ r, 2 ≤ (a r).routeCount)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : ℝ) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r b, 0 < b → ∀ j l : Fin n,
      (userLaw (Γ r)).real (aboveAt j b ∪ aboveAt l b) ≤ H)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r)
      (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) (a r).bid) (C r)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, d ≤ ((problem (Γ r) (i r)).outcome (a r)).duplicates := by
  let j : Fin 2 → Fin n := fun k => ⟨k.val, lt_of_lt_of_le k.isLt hn⟩
  obtain ⟨d, hd, hde⟩ := eventually_nonrare_ample_ppi_pair_pos M C Γ i j (fun r => (a r).bid)
    hA hatom (fun r k => hj r (j k)) hb hM hC hρ0 hρ1
    (by intro he; have hh := congrArg Fin.val he; norm_num [j] at hh)
    H hH hample (fun r => hunion r (a r).bid (hb r) (j 0) (j 1)) hc ε hε hq
  refine ⟨d / (Fintype.card (Equiv.Perm (Fin n)) : ℝ), by positivity, ?_⟩
  filter_upwards [hde] with r hr
  have hdiv := div_le_div_of_nonneg_right hr (show (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin n)) by positivity)
  exact hdiv.trans (first_pair_acceptance_div_card_le_duplicates (Γ r) (i r) (a r) (hk r))

theorem uniform_nonrare_ample_ppi_duplicates_pos
    (hn : 2 ≤ n) (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1))
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r j, ProposerRationalAtFeasibleLists (Γ r) j)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (H : ℝ) (hH : H ≤ 1) (hample : H < n * ρ)
    (hunion : ∀ r b, 0 < b → ∀ j l : Fin n,
      (userLaw (Γ r)).real (aboveAt j b ∪ aboveAt l b) ≤ H)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, ∀ a : JointAction n,
      0 < a.bid → 2 ≤ a.routeCount →
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) →
      d ≤ ((problem (Γ r) (i r)).outcome a).duplicates := by
  classical
  by_contra hnot
  have hex : ∀ k : ℕ, ∃ r : ℕ, k ≤ r ∧ ∃ a : JointAction n,
      0 < a.bid ∧ 2 ≤ a.routeCount ∧
      ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) ∧
      ((problem (Γ r) (i r)).outcome a).duplicates < 1 / ((k : ℝ) + 1) := by
    intro k
    have hbad : ¬ ∀ᶠ r in atTop, ∀ a : JointAction n,
        0 < a.bid → 2 ≤ a.routeCount →
        ε ≤ binomBelow (M r) (alphaGt (Γ r) (⟨0, by omega⟩ : Fin n) a.bid) (C r) →
        1 / ((k : ℝ) + 1) ≤ ((problem (Γ r) (i r)).outcome a).duplicates := by
      intro hh
      exact hnot ⟨1 / ((k : ℝ) + 1), by positivity, hh⟩
    simp only [eventually_atTop] at hbad
    push Not at hbad
    exact hbad k
  choose f hf a hab hak haq had using hex
  have hft : Tendsto f atTop atTop := tendsto_atTop_mono hf tendsto_id
  obtain ⟨d, hd, hde⟩ := eventually_nonrare_ample_ppi_duplicates_pos hn (M ∘ f) (C ∘ f)
    (fun r => Γ (f r)) (fun r => i (f r)) a (fun r => hA (f r)) (fun r => hatom (f r))
    (fun r => hj (f r)) hab hak (hM.comp hft) (fun r => hC (f r)) hρ0 hρ1 H hH hample
    (fun r => hunion (f r)) (hc.comp hft)
    ε hε (Filter.Eventually.of_forall haq)
  have hzero : Tendsto (fun r => ((problem (Γ (f r)) (i (f r))).outcome (a r)).duplicates)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun r => CountLaw.duplicates_nonneg _) (fun r => (had r).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hh : d ≤ 0 := ge_of_tendsto hzero hde
  linarith

end FCAppendix.Bayes
