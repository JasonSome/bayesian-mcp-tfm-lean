import FCAppendix.Exclusive.NarrowKernel
import FCAppendix.Exclusive.BroadcastCapacity
import FCAppendix.Probability.EmpiricalMean

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def clippedInverseDraw (n : ℕ) (a B : ℝ) (u : UserDraw n) : ℝ :=
  if u.1.2.routeCount = 0 then 0 else inverseBid n (max a (min B u.1.2.bid))

theorem measurable_clippedInverseDraw (n : ℕ) (a B : ℝ) :
    Measurable (clippedInverseDraw n a B) := by
  have hb : Measurable (fun u : UserDraw n => u.1.2.bid) := (measurable_bid n).comp (measurable_snd.comp measurable_fst)
  have hk : Measurable (fun u : UserDraw n => u.1.2.routeCount) := (measurable_routeCount n).comp (measurable_snd.comp measurable_fst)
  exact Measurable.ite (measurableSet_eq_fun hk measurable_const) measurable_const
    ((measurable_const.max (measurable_const.min hb)).pow_const (-Exclusive.rate n))

theorem clippedInverseDraw_bounds (n : ℕ) (hn : 2 ≤ n) {a B : ℝ}
    (ha : 0 < a) (u : UserDraw n) :
    0 ≤ clippedInverseDraw n a B u ∧ clippedInverseDraw n a B u ≤ inverseBid n a := by
  unfold clippedInverseDraw
  split_ifs
  · exact ⟨le_rfl, (inverseBid_pos n ha).le⟩
  · exact ⟨(inverseBid_pos n (ha.trans_le (le_max_left _ _))).le,
      inverseBid_antitone n hn ha (le_max_left _ _)⟩

theorem clippedInverseDraw_eq (n : ℕ) {a B : ℝ} (u : UserDraw n)
    (hk : u.1.2.routeCount ≠ 0) (hb : u.1.2.bid ∈ Icc a B) :
    clippedInverseDraw n a B u = inverseBid n u.1.2.bid := by
  rw [clippedInverseDraw, if_neg hk, min_eq_right hb.2, max_eq_right hb.1]

@[simp] theorem clippedInverseDraw_abstain (n : ℕ) (a B : ℝ) (u : UserDraw n)
    (hk : u.1.2.routeCount = 0) : clippedInverseDraw n a B u = 0 := by
  simp [clippedInverseDraw, hk]

theorem exclusive_inverseBid_L1_le (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hn : 2 ≤ n) {a B : ℝ} (ha : 0 < a) :
    (∫ d, |populationMean (fun i => clippedInverseDraw n a B (d i)) -
      ∫ u, clippedInverseDraw n a B u ∂userLaw Γ| ∂userProfileLaw Γ) ≤
        inverseBid n a / Real.sqrt m := by
  have h := Probability.iid_empiricalMean_L1_le (userLaw Γ)
    (measurable_clippedInverseDraw n a B).aestronglyMeasurable
    (inverseBid n a) (inverseBid_pos n ha).le
    (Eventually.of_forall fun u => by
      rw [abs_of_nonneg (clippedInverseDraw_bounds n hn ha u).1]
      exact (clippedInverseDraw_bounds n hn ha u).2) m hm
  simpa only [populationMean, Fintype.card_fin, userProfileLaw] using h

theorem exclusive_inverseBid_L1_tendsto_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop) {a B : ℝ} (ha : 0 < a) :
    Tendsto (fun t => ∫ d,
      |populationMean (fun i => clippedInverseDraw n a B (d i)) -
        ∫ u, clippedInverseDraw n a B u ∂userLaw (Γ t)| ∂userProfileLaw (Γ t))
      atTop (𝓝 0) := by
  have h := Probability.iid_empiricalMean_L1_tendsto_zero
    (fun t => userLaw (Γ t)) (fun _ => clippedInverseDraw n a B)
    (fun _ => (measurable_clippedInverseDraw n a B).aestronglyMeasurable)
    (inverseBid n a) (inverseBid_pos n ha).le
    (fun _ => Eventually.of_forall fun u => by
      rw [abs_of_nonneg (clippedInverseDraw_bounds n hn ha u).1]
      exact (clippedInverseDraw_bounds n hn ha u).2) M hM
  simpa only [populationMean, Fintype.card_fin, userProfileLaw] using h

noncomputable def inverseDrawShare (n : ℕ) (a B : ℝ) (d : UserProfile m n) (i : Fin m) : ℝ :=
  clippedInverseDraw n a B (d i) / ∑ j, clippedInverseDraw n a B (d j)

theorem measurable_inverseDrawShare (n : ℕ) (a B : ℝ) (i : Fin m) :
    Measurable (fun d : UserProfile m n => inverseDrawShare n a B d i) := by
  exact ((measurable_clippedInverseDraw n a B).comp (measurable_pi_apply i)).div
    (Finset.measurable_sum _ fun j _ =>
      (measurable_clippedInverseDraw n a B).comp (measurable_pi_apply j))

theorem inverseDrawShare_bounds (n : ℕ) (hn : 2 ≤ n) {a B : ℝ} (ha : 0 < a)
    (d : UserProfile m n) (i : Fin m) :
    0 ≤ inverseDrawShare n a B d i ∧ inverseDrawShare n a B d i ≤ 1 := by
  have hw j := (clippedInverseDraw_bounds n hn (B := B) ha (d j)).1
  have hsum : 0 ≤ ∑ j, clippedInverseDraw n a B (d j) := Finset.sum_nonneg fun j _ => hw j
  have hle : clippedInverseDraw n a B (d i) ≤ ∑ j, clippedInverseDraw n a B (d j) :=
    Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  refine ⟨div_nonneg (hw i) hsum, ?_⟩
  rcases hsum.eq_or_lt with hz | hp
  · simp [inverseDrawShare, ← hz]
  · exact (div_le_one hp).mpr hle

theorem populationMean_inverseDrawShare_le (n : ℕ) (a B : ℝ) (d : UserProfile m n) :
    populationMean (inverseDrawShare n a B d) ≤ 1 / (m : ℝ) := by
  unfold populationMean inverseDrawShare
  rw [← Finset.sum_div, Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  by_cases hz : (∑ j, clippedInverseDraw n a B (d j)) = 0
  · simp [hz]
  · rw [div_self hz]

theorem exclusive_own_share_tendsto_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 2 ≤ n) (hM : Tendsto M atTop atTop) {a B : ℝ} (ha : 0 < a) :
    Tendsto (fun t => ∫ d, populationMean (inverseDrawShare n a B d)
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  have hR : Tendsto (fun t => 1 / (M t : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hM)
  apply squeeze_zero (fun t => integral_nonneg fun d =>
    div_nonneg (Finset.sum_nonneg fun i _ => (inverseDrawShare_bounds n hn ha d i).1)
      (Nat.cast_nonneg _)) _ hR
  intro t
  have hi := integrable_populationMean (userProfileLaw (Γ t)) (inverseDrawShare n a B)
    (fun i => UnitInterval.integrable _ _ (measurable_inverseDrawShare n a B i)
      (fun d => (inverseDrawShare_bounds n hn ha d i).1)
      (fun d => (inverseDrawShare_bounds n hn ha d i).2))
  calc
    _ ≤ ∫ _d, 1 / (M t : ℝ) ∂userProfileLaw (Γ t) :=
      integral_mono hi (integrable_const _) (populationMean_inverseDrawShare_le n a B)
    _ = 1 / (M t : ℝ) := by simp

end FCAppendix.Bayes
