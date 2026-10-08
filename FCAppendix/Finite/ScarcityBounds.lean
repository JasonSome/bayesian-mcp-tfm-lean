import FCAppendix.Game.RealizedIntegrals
import FCAppendix.PayOnce.FiniteJensen
import FCAppendix.Finite.QuantileAsymptotics

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem finiteCoverage_le_capacity (Γ : FiniteGame m n c Seed) :
    finiteCoverage Γ ≤ (n : ℝ) * ((c : ℝ) / m) := by
  have hi (i : Fin m) := CountLaw.integrable_comp (backgroundLaw Γ) _
    (measurable_playedCount Γ i) (fun r => successIndicator r.val)
  rw [finiteCoverage_eq_actual, ← integral_finsetSum _ (fun i _ => hi i)]
  have hbound : ∀ ω : Background m n Seed,
      (∑ i, successIndicator (playedCount Γ i ω).val) ≤ (n : ℝ) * c := by
    intro ω
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => successIndicator_le_count (playedCount Γ i ω).val)
    have hc := total_capacity (drawsRealization ω.1) Γ.policy ω.2
    have hcR : (∑ i, ((playedCount Γ i ω).val : ℝ)) ≤ (n : ℝ) * c := by
      exact_mod_cast hc
    exact hs.trans hcR
  have hh := integral_mono (integrable_finsetSum _ (fun i _ => hi i))
    (integrable_const ((n : ℝ) * c)) hbound
  simp only [integral_const, probReal_univ, one_smul] at hh
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg m)

theorem bestResponse_success_lower_singleton (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (i : Fin m) (act : JointAction n) (hk : act.routeCount = 1)
    (r η : ℝ) (hr : 0 ≤ r) (hη : 0 < η)
    (hq : 1 - r ≤ meanAcceptProb Γ i act.bid)
    (v : ℝ) (hv : η ≤ v - Γ.g) (b : JointAction n)
    (hbr : (problem Γ i).BestResponse v b) :
    1 - r - act.bid / η ≤ ((problem Γ i).outcome b).success := by
  have hw : 0 ≤ v - Γ.g := hη.le.trans hv
  have hlo := envelope_lower_singleton Γ hn i act hk r hr hq v
  rw [← (problem Γ i).bestResponse_iff_attains v b |>.mp hbr,
    max_eq_left hw] at hlo
  have hu := ((problem Γ i).outcome b).utility_le_bid_net_success
    v b.bid Γ.g Γ.A Γ.G b.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff v b ≤ _ at hu
  have hbs := mul_nonneg b.bid_nonneg ((problem Γ i).outcome b).success_nonneg
  have hmax := le_max_left (v - Γ.g - act.bid) 0
  have hdiv : act.bid / η * η = act.bid := div_mul_cancel₀ _ hη.ne'
  have hbn := div_nonneg act.bid_nonneg hη.le
  by_cases hs : 1 - r ≤ ((problem Γ i).outcome b).success
  · linarith
  · have hm := mul_le_mul_of_nonneg_right hv
      (show 0 ≤ 1 - r - ((problem Γ i).outcome b).success by linarith)
    nlinarith

theorem finiteCoverage_lower_singleton (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hΓ : UsersOptimal Γ)
    (act : JointAction n) (hk : act.routeCount = 1)
    (r η : ℝ) (hr : 0 ≤ r) (hη : 0 < η)
    (hq : ∀ i, 1 - r ≤ meanAcceptProb Γ i act.bid) :
    Γ.F.real (Ioi (Γ.g + η)) * (1 - r - act.bid / η) ≤ finiteCoverage Γ := by
  classical
  let s : Set (ℝ × JointAction n) := (Ioi (Γ.g + η)) ×ˢ univ
  have hs : MeasurableSet s := measurableSet_Ioi.prod MeasurableSet.univ
  have hmeasure : (Γ.F ⊗ₘ Γ.σ) s = Γ.F (Ioi (Γ.g + η)) := by
    simp [s, Measure.compProd_apply_prod measurableSet_Ioi MeasurableSet.univ]
  have hi (i : Fin m) :
      Γ.F.real (Ioi (Γ.g + η)) * (1 - r - act.bid / η) ≤
        ∫ x, ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ) := by
    have hms := (measurable_outcome_expect Γ i (fun r => successIndicator r.val)).comp
      (show Measurable (fun x : ℝ × JointAction n => x.2) from measurable_snd)
    have his := UnitInterval.integrable (Γ.F ⊗ₘ Γ.σ) _ hms
      (fun x => CountLaw.success_nonneg _) (fun x => CountLaw.success_le_one _)
    have hh := integral_mono_ae
      ((integrable_const (1 - r - act.bid / η)).indicator hs) his (show
        s.indicator (fun _ => 1 - r - act.bid / η) ≤ᵐ[Γ.F ⊗ₘ Γ.σ]
          (fun x => ((problem Γ i).outcome x.2).success) from by
        filter_upwards [ae_bestResponse_compProd Γ hΓ i] with x hx
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs]
          exact bestResponse_success_lower_singleton Γ hn i act hk r η hr hη
            (hq i) x.1 (by have hh := hxs.1; simp only [mem_Ioi] at hh; linarith) x.2 hx
        · rw [indicator_of_notMem hxs]
          exact CountLaw.success_nonneg _)
    rw [integral_indicator_const _ hs] at hh
    simpa only [smul_eq_mul, measureReal_def, hmeasure, Function.comp_apply, CountLaw.success] using hh
  rw [finiteCoverage_eq_actual]
  simp_rw [integral_realized_success_eq_interim]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m)).mpr
  simpa [mul_comm] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i _ => hi i)

theorem singleton_success_of_quantile_gap (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc0 : 0 < c) (hc : c ≤ m) (hΓ : IsAEEquilibrium Γ)
    (hp : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hatom : PositiveVisibleAtomless Γ)
    (j : Fin n) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (q d δ : ℝ) (hq : 0 < q) (hd : 0 < d) (hδ : 0 < δ)
    (hgap : δ ≤ (c : ℝ) - (m - 1 : ℕ) * q) :
    0 < TailQuantile.quantile (alphaGt Γ j) q / a + d ∧
      ∀ i, 1 - (m - 1 : ℕ) / (4 * δ ^ 2) ≤
        meanAcceptProb Γ i (TailQuantile.quantile (alphaGt Γ j) q / a + d) := by
  let u := TailQuantile.quantile (alphaGt Γ j) q
  have hu : 0 ≤ u := visible_quantile_nonneg Γ hm hc0 hΓ j q hq
  let t := u / a + d
  have ht : 0 < t := add_pos_of_nonneg_of_pos (div_nonneg hu ha.le) hd
  refine ⟨ht, fun i => ?_⟩
  have hα : alphaGt Γ j (a * t) ≤ q := by
    have hh := alphaGt_above_quantile Γ hm hc0 hΓ j q (a * d) hq (mul_pos ha hd)
    have he : a * t = u + a * d := by dsimp [t]; field_simp
    rw [he]
    exact hh
  have hslot : δ ≤ (c : ℝ) - (m - 1 : ℕ) * alphaGt Γ j (a * t) := by
    have hh := mul_le_mul_of_nonneg_left hα (Nat.cast_nonneg (m - 1) : (0 : ℝ) ≤ (m - 1 : ℕ))
    linarith
  exact meanAcceptProb_lower_of_gap Γ hm hc hp hatom i j a ha hA t δ ht hδ hslot

theorem singleton_failure_tendsto_zero (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun k => (M k - 1 : ℕ) / (4 * ((M k : ℝ) * e / 2) ^ 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun k => 1 / ((M k : ℝ) * e ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop.comp hM).atTop_mul_const (sq_pos_of_pos he))
  apply squeeze_zero' (Eventually.of_forall fun k => by positivity) _ ht
  filter_upwards [hM.eventually_gt_atTop 0] with k hk
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hk
  have hh : ((M k - 1 : ℕ) : ℝ) ≤ M k := Nat.cast_le.mpr (Nat.sub_le (M k) 1)
  have hid : 4 * ((M k : ℝ) * e / 2) ^ 2 = (M k : ℝ) ^ 2 * e ^ 2 := by ring
  rw [hid]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hh (show 0 ≤ (M k : ℝ) * e ^ 2 by positivity)]

theorem eventually_singleton_success_of_quantile
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (a : ℕ → ℝ) (ρ q d : ℝ) (hρ : ρ < 1) (hq : 0 < q) (hqr : q < ρ) (hd : 0 < d)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r) :
    ∀ᶠ k in atTop, 0 < TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d ∧
      ∀ i, 1 - (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2) ≤
        meanAcceptProb (Γ k) i (TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d) := by
  filter_upwards [(tendsto_order.mp ha).1 0 zero_lt_one,
    (tendsto_order.mp hcap).2 1 hρ,
    (tendsto_order.mp hcap).1 ((ρ + q) / 2) (by linarith),
    hM.eventually_gt_atTop 0] with k ha hc hc' hm
  have hmR : (0 : ℝ) < M k := Nat.cast_pos.mpr hm
  have hcR : (0 : ℝ) < C k := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hmid : 0 < (ρ + q) / 2 := by linarith
    exact lt_of_lt_of_le (mul_pos hmid hmR) hh.le
  have hc0 : 0 < C k := Nat.cast_pos.mp hcR
  have hcM : C k ≤ M k := by
    have hh := (div_lt_iff₀ hmR).mp hc
    exact Nat.cast_le.mp (by linarith : (C k : ℝ) ≤ M k)
  have hδ : 0 < (M k : ℝ) * (ρ - q) / 2 := by positivity
  have hgap : (M k : ℝ) * (ρ - q) / 2 ≤ (C k : ℝ) - (M k - 1 : ℕ) * q := by
    have hh := (lt_div_iff₀ hmR).mp hc'
    have hn : ((M k - 1 : ℕ) : ℝ) ≤ M k := Nat.cast_le.mpr (Nat.sub_le _ _)
    nlinarith [mul_le_mul_of_nonneg_right hn hq.le]
  exact singleton_success_of_quantile_gap (Γ k) hm hc0 hcM (hΓ k) (hp k) (hatom k)
    j (a k) ha (hA k) q d ((M k : ℝ) * (ρ - q) / 2) hq hd hδ hgap

theorem capacity_lower_of_quantile_limit
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ q p : ℝ) (hρ : ρ < 1) (hq : 0 < q) (hqr : q < ρ)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (η d : ℝ) (hη : 0 < η) (hd : 0 < d) :
    F.real (Ioi (g + η)) * (1 - (p + d) / η) ≤ (n : ℝ) * ρ := by
  let r := fun k => (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2)
  let t := fun k => TailQuantile.quantile (alphaGt (Γ k) j) q / a k + d
  have hr := singleton_failure_tendsto_zero M hM (ρ - q) (sub_pos.mpr hqr)
  have ht : Tendsto t atTop (𝓝 (p + d)) := by
    simpa [t] using (hu.div ha one_ne_zero).add_const d
  have hlo : Tendsto (fun k => F.real (Ioi (g + η)) * (1 - r k - t k / η))
      atTop (𝓝 (F.real (Ioi (g + η)) * (1 - (p + d) / η))) := by
    simpa only [sub_zero] using ((hr.const_sub 1).sub (ht.div_const η)).const_mul (F.real (Ioi (g + η)))
  apply le_of_tendsto_of_tendsto hlo (hcap.const_mul (n : ℝ))
  filter_upwards [eventually_singleton_success_of_quantile M C Γ j a ρ q d hρ hq hqr hd
    hM hcap ha hΓ hp hatom hA, hM.eventually_gt_atTop 0] with k hk hm
  let act : JointAction n := ⟨t k, hk.1.le, 1, Nat.zero_lt_of_lt j.isLt⟩
  have hh := finiteCoverage_lower_singleton (Γ k) hm (Nat.zero_lt_of_lt j.isLt)
    (hΓ k).users act rfl (r k) η (by dsimp [r]; positivity) hη hk.2
  rw [hF k, hg k] at hh
  exact hh.trans (finiteCoverage_le_capacity (Γ k))

theorem exists_positive_tail_margin (F : Measure ℝ) [IsProbabilityMeasure F]
    (g L : ℝ) (hL : L < F.real (Ioi g)) :
    ∃ η > 0, L < F.real (Ioi (g + η)) := by
  let η : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hη : ∀ k, 0 < η k := fun k => by dsimp [η]; positivity
  have ht : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun k => g + η k) atTop (𝓝[Ici g] g) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun k => g + η k)
      (by simpa using ht.const_add g)
    exact Eventually.of_forall fun k => by simp only [mem_Ici]; linarith [hη k]
  have hc := (cdf F).right_continuous g |>.tendsto.comp hg
  have htail : Tendsto (fun k => F.real (Ioi (g + η k))) atTop (𝓝 (F.real (Ioi g))) := by
    have he (b : ℝ) : F.real (Ioi b) = 1 - cdf F b := by
      rw [cdf_eq_real, ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    simpa only [he, Function.comp_apply] using hc.const_sub 1
  obtain ⟨k, hk⟩ := ((tendsto_order.mp htail).1 L hL).exists
  exact ⟨η k, hη k, hk⟩

theorem quantile_limit_pos_of_scarcity
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ k, (Γ k).F = F)
    (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ q p : ℝ) (hρ : ρ < 1) (hq : 0 < q) (hqr : q < ρ)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 p))
    (hp0 : 0 ≤ p) (hscarce : (n : ℝ) * ρ < F.real (Ioi g)) : 0 < p := by
  by_contra hnot
  have hpz : p = 0 := le_antisymm (le_of_not_gt hnot) hp0
  obtain ⟨η, hη, htail⟩ := exists_positive_tail_margin F g ((n : ℝ) * ρ) hscarce
  have hh (d : ℝ) (hd : 0 < d) := capacity_lower_of_quantile_limit M C Γ j F hF g hg
    a ρ q p hρ hq hqr hM hcap ha hΓ hp hatom hA hu η d hη hd
  have hzero : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k : ℕ => F.real (Ioi (g + η)) *
      (1 - (p + 1 / ((k : ℝ) + 1)) / η)) atTop (𝓝 (F.real (Ioi (g + η)))) := by
    simpa [hpz] using (((hzero.const_add p).div_const η).const_sub 1).const_mul (F.real (Ioi (g + η)))
  have hle := le_of_tendsto hlim (Eventually.of_forall fun k => hh _ (by positivity))
  exact (not_le_of_gt htail) hle

end FCAppendix.Bayes
