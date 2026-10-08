import FCAppendix.Ample.BoundaryRankProperties
import FCAppendix.Ample.RankSupportSelection
import FCAppendix.Ample.RankChernoffComparison

noncomputable section
namespace FCAppendix.Bayes.RankLimit
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem used_allContact_le_actual
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hu : ∀ t, UsersOptimal (Γ t)) (hact : ∀ t, NonpositiveAbstention (Γ t))
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hfree : ∀ t, FreeDuplicateBase (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hM : Tendsto M atTop atTop) (hscarce : ∀ᶠ t in atTop, C t < M t)
    (hpart : ∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = h)
    {a : ℝ} (ha : 0 < a)
    (hfull : HasPopulationRate M (fun t => actualAllFailure (Γ t)) (-log a))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, allContactTail n k nu h u ≤ a := by
  letI := hr.finite hk
  have hn : 0 < n := by have := Finset.mem_Icc.mp hk; omega
  filter_upwards [hr.used_allContact_positive hk, (nu k).support_mem_ae]
    with u huRank huSupport
  have hQ : ∀ᶠ t in atTop, 0 < M t ∧ C t ≤ M t-1 := by
    filter_upwards [hscarce] with t ht
    omega
  obtain ⟨phi, hphi, x, hx, hxr⟩ := hr.supported_approximation F g hF hg hu hact
    (fun t => 0 < M t ∧ C t ≤ M t-1) hQ hk
    huRank.1 huRank.2.1 huSupport
  let p : ℕ → ℕ → ℝ := fun q => visibleClassMass (Γ (phi q)) (x q).2.bid
  let A : ℕ → ℝ := fun q => boundaryClassContact n k (p q)
  have hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun q => p q j) atTop (𝓝 (rankTail nu h u j)) :=
    (hr.along phi hphi.tendsto_atTop).visible_weights_tendsto
      (fun q => hatom (phi q)) (fun q => (x q).2.bid)
      (Eventually.of_forall (fun q => (hx q).2.2.2.1.le))
      (hphi.tendsto_atTop.eventually hpart) hxr
  have hAlim : Tendsto A atTop (𝓝 (allContactTail n k nu h u)) :=
    boundaryClassContact_tendsto hconv
  have hApos : ∀ᶠ q in atTop, 0 < A q := hAlim.eventually_const_lt huRank.2.2
  have hlog : Tendsto (fun q => log (A q)) atTop
      (𝓝 (log (allContactTail n k nu h u))) :=
    (continuousAt_log huRank.2.2.ne').tendsto.comp hAlim
  have hpowrate : Tendsto (fun q =>
      populationLogRate (M (phi q)) ((A q)^(M (phi q)-1))) atTop
      (𝓝 (-log (allContactTail n k nu h u))) := by
    have hl := (rival_fraction_tendsto_one (M ∘ phi)
      (hM.comp hphi.tendsto_atTop)).neg.mul hlog
    simp only [neg_one_mul] at hl
    convert hl using 1
    funext q
    unfold populationLogRate
    rw [log_pow]
    dsimp only [Function.comp_def]
    ring
  have hcommon := hfull.2.comp hphi.tendsto_atTop
  have hrate : -log a ≤ -log (allContactTail n k nu h u) := by
    apply le_of_tendsto_of_tendsto hcommon hpowrate
    filter_upwards [hApos] with q hAq
    have hfinite := (actual_failure_coefficient_AM9 (Γ (phi q)) (hx q).1.1
      (hx q).1.2 (hA _) (hatom _) (hpolicy _) (x q).2 (hx q).2.2.2.1
      (by rw [(hx q).2.2.2.2]; exact (Finset.mem_Icc.mp hk).1)).1
    rw [(hx q).2.2.2.2] at hfinite
    have hBR := (hx q).2.1 (hx q).1.1
    have hw : 0 < (x q).1-g := sub_pos.mpr (hx q).2.2.1
    have hAM := actual_AM1 (Γ (phi q)) (hx q).1.1 (hA _) (hfree _)
      (hatom _) (hpolicy _) hn hw (x q).2 hBR
    exact populationLogRate_anti (hx q).1.1 (pow_pos hAq _)
      (hfinite.trans hAM.2.1)
  by_contra hnot
  have hloglt := log_lt_log ha (lt_of_not_ge hnot)
  linarith

theorem boundary_fixed_cut_failure_small
    (hM : Tendsto M atTop atTop)
    (hC : Tendsto (fun t => (C t:ℝ)/M t) atTop (𝓝 1))
    (hscarce : ∀ᶠ t in atTop, C t < M t)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    {D : ℕ → ℝ} {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hD : HasPopulationRate M D (-log a))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) {u : ℝ}
    (hu : u ∈ Icc 0 h) (hgap : allContactTail n k nu h u < a) :
    ∀ ε > 0, ∀ᶠ t in atTop, ∀ x : JointAction n,
      0 < x.bid → x.routeCount = k → u ≤ ascendingBidRank (Γ t) x.bid →
      actualFailure (Γ t) x / D t ≤ ε := by
  let A₀ := allContactTail n k nu h u
  let A : ℕ → ℝ := fun t => boundaryClassContact n k
    (fun j => (rankClassLaw (Γ t) j).real (Ioi u))
  have hAt : Tendsto A atTop (𝓝 A₀) := boundaryClassContact_tendsto
    (fun j hj => hr.moving_tail (Eventually.of_forall (fun _ => hu)) tendsto_const_nhds hj)
  obtain ⟨θ, hθ, hq₀, hqa⟩ := boundary_finite_tilt_gap
    (allContactTail_nonneg n k nu h u) ha1 hgap
  let q : ℕ → ℝ := fun t => A t + (1-A t)*exp (-θ)
  let q₀ : ℝ := A₀ + (1-A₀)*exp (-θ)
  have hqt : Tendsto q atTop (𝓝 q₀) := hAt.add ((hAt.const_sub 1).mul_const _)
  have hqpos : ∀ᶠ t in atTop, 0 < q t := hqt.eventually_const_lt hq₀
  have hlog : Tendsto (fun t => log (q t)) atTop (𝓝 (log q₀)) :=
    (continuousAt_log hq₀.ne').tendsto.comp hqt
  let J : ℝ := -log a
  let d : ℝ := (J-log q₀)/2
  have hJq : J < -log q₀ := neg_lt_neg ((log_lt_log_iff hq₀ ha).2 hqa)
  have hJd : J < d := by dsimp [d]; linarith
  have hdq : d < -log q₀ := by dsimp [d]; linarith
  have hlim : Tendsto
      (fun t => (θ*(k:ℝ)*((M t-1-C t:ℕ):ℝ))/(M t:ℝ) +
        (((M t-1:ℕ):ℝ)/M t)*log (q t)) atTop (𝓝 (log q₀)) := by
    have hl := ((boundary_shortage_fraction_tendsto_zero M C hM hC hscarce).const_mul (θ*(k:ℝ))).add ((rival_fraction_tendsto_one M hM).mul hlog)
    convert hl using 1
    · funext t
      ring
    · simp only [mul_zero, one_mul, zero_add]
  have hub := rank_exp_pow_eventually_le hM hqpos hlim (by linarith [hdq])
  have hratio := rank_exp_div_scale_tendsto_zero hM hD hJd
  intro ε hε
  filter_upwards [hub, hD.1, hratio.eventually_lt_const hε, hscarce]
    with t ht hDt hεt hct
  intro x hbid hroute hrank
  have hch := actual_failure_rank_AM9 (Γ t) (by omega) (by omega)
    (hA t) (hatom t) (hpolicy t) x hbid
    (by rw [hroute]; exact (Finset.mem_Icc.mp hk).1) hrank hθ
  rw [hroute] at hch
  exact (div_le_div_of_nonneg_right (hch.trans ht) hDt.le).trans hεt.le

end FCAppendix.Bayes.RankLimit
