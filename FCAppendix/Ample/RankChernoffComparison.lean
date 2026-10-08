import FCAppendix.Ample.RankRateAlgebra

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

theorem rank_exp_div_scale_tendsto_zero {M : ℕ → ℕ} {D : ℕ → ℝ}
    {J d : ℝ} (hM : Tendsto M atTop atTop) (hD : HasPopulationRate M D J)
    (hgap : J < d) :
    Tendsto (fun t => exp (-d*(M t:ℝ))/D t) atTop (𝓝 0) := by
  let b : ℝ := (J+d)/2
  have hJb : J < b := by dsimp [b]; linarith
  have hbd : b < d := by dsimp [b]; linarith
  have hbound : ∀ᶠ t in atTop,
      0 ≤ exp (-d*(M t:ℝ))/D t ∧
      exp (-d*(M t:ℝ))/D t ≤ exp (-(d-b)*(M t:ℝ)) := by
    filter_upwards [hD.1, hD.2.eventually_lt_const hJb,
      hM.eventually_gt_atTop 0] with t hDt hrate hm
    have hmR : (0:ℝ) < M t := by exact_mod_cast hm
    have hlog : -b*(M t:ℝ) < log (D t) := by
      unfold populationLogRate at hrate
      have he := (div_lt_iff₀ hmR).mp hrate
      linarith
    have hlow : exp (-b*(M t:ℝ)) ≤ D t := by
      rw [← exp_log hDt]
      exact exp_le_exp.mpr hlog.le
    refine ⟨div_nonneg (exp_pos _).le hDt.le, ?_⟩
    calc
      exp (-d*(M t:ℝ))/D t ≤ exp (-d*(M t:ℝ))/exp (-b*(M t:ℝ)) :=
        div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _) hlow
      _ = exp (-(d-b)*(M t:ℝ)) := by
        rw [← exp_sub]
        congr 1
        ring
  have he : Tendsto (fun t => exp (-(d-b)*(M t:ℝ))) atTop (𝓝 0) := by
    have ht := tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp hM).const_mul_atTop (sub_pos.mpr hbd))
    convert ht using 1
    funext t
    dsimp only [Function.comp_apply]
    congr 1
    ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
    (hbound.mono fun _ ht => ht.1) (hbound.mono fun _ ht => ht.2)

theorem rank_exp_pow_eventually_le {M N : ℕ → ℕ} {a q : ℕ → ℝ} {L d : ℝ}
    (hM : Tendsto M atTop atTop) (hq : ∀ᶠ t in atTop, 0 < q t)
    (hL : Tendsto (fun t => a t/(M t:ℝ) + ((N t:ℝ)/(M t:ℝ))*log (q t))
      atTop (𝓝 L)) (hd : L < -d) :
    ∀ᶠ t in atTop, exp (a t)*(q t)^N t ≤ exp (-d*(M t:ℝ)) := by
  filter_upwards [hq, hL.eventually_lt_const hd,
    hM.eventually_gt_atTop 0] with t hqt hlt hmt
  have hmR : (0:ℝ) < M t := by exact_mod_cast hmt
  have he : exp (a t)*(q t)^N t =
      exp ((M t:ℝ)*(a t/(M t:ℝ) + ((N t:ℝ)/(M t:ℝ))*log (q t))) := by
    rw [show (q t)^N t = exp ((N t:ℝ)*log (q t)) by
      rw [exp_nat_mul, exp_log hqt], ← exp_add]
    congr 1
    field_simp [hmR.ne']
  rw [he]
  apply exp_le_exp.mpr
  nlinarith

namespace RankLimit
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem fixed_cut_failure_small
    (hM : Tendsto M atTop atTop) {ρ : ℝ}
    (hC : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 ρ))
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    {D : ℕ → ℝ} {J : ℝ} (hD : HasPopulationRate M D J)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {u θ : ℝ}
    (hu : u ∈ Icc 0 h) (hθ : 0 ≤ θ)
    (hgap : J < rivalObjective n ρ k (rankTail nu h u) θ) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ a : JointAction n,
      0 < a.bid → a.routeCount = k → u ≤ ascendingBidRank (Γ t) a.bid →
      actualFailure (Γ t) a / D t ≤ ε := by
  let q : ℕ → ℝ := fun t => rivalMGF n k
    (fun j => (rankClassLaw (Γ t) j).real (Ioi u)) θ
  let q₀ : ℝ := rivalMGF n k (rankTail nu h u) θ
  have hq (t : ℕ) : 0 < q t := zero_lt_one.trans_le
    (one_le_rivalMGF (Finset.mem_Icc.mp hk).2 (fun _ _ => measureReal_nonneg) hθ)
  have hq₀ : 0 < q₀ := zero_lt_one.trans_le
    (one_le_rivalMGF (Finset.mem_Icc.mp hk).2 (fun _ _ => measureReal_nonneg) hθ)
  have hqt : Tendsto q atTop (𝓝 q₀) := rivalMGF_tendsto_weights
    (fun j hj => hr.moving_tail (Eventually.of_forall (fun _ => hu))
      tendsto_const_nhds hj) θ
  have hlog : Tendsto (fun t => log (q t)) atTop (𝓝 (log q₀)) :=
    (continuousAt_log hq₀.ne').tendsto.comp hqt
  let I : ℝ := rivalObjective n ρ k (rankTail nu h u) θ
  let d : ℝ := (J+I)/2
  have hJd : J < d := by dsimp [d, I]; linarith
  have hdI : d < I := by dsimp [d, I]; linarith
  have hlim : Tendsto
      (fun t => (-θ*(k:ℝ)*(C t:ℝ))/(M t:ℝ) +
        (((M t-1:ℕ):ℝ)/(M t:ℝ))*log (q t)) atTop (𝓝 (-I)) := by
    have he := (hC.const_mul (-θ*(k:ℝ))).add
      ((SimultaneousCongestion.rival_population_scaling hM).2.mul hlog)
    convert he using 1
    · funext t
      ring
    · dsimp [I, rivalObjective, q₀]
      ring
  have hub := rank_exp_pow_eventually_le hM (Eventually.of_forall hq) hlim
    (neg_lt_neg hdI)
  have hratio := rank_exp_div_scale_tendsto_zero hM hD hJd
  intro ε hε
  filter_upwards [hub, hD.1, hratio.eventually_lt_const hε,
    hM.eventually_gt_atTop 0] with t ht hDt hεt hmt
  intro a hbid hroute hrank
  have hch := actual_failure_rank_chernoff (Γ t) hmt (hA t) (hatom t)
    (hpolicy t) a hbid hrank hθ
  rw [hroute] at hch
  have hf : actualFailure (Γ t) a ≤ exp (-d*(M t:ℝ)) := hch.trans ht
  exact (div_le_div_of_nonneg_right hf hDt.le).trans hεt.le

end RankLimit
end FCAppendix.Bayes
