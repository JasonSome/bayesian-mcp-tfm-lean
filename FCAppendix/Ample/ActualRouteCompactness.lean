import FCAppendix.Ample.CommonRateActualAdapters
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Topology Set
open scoped BigOperators ENNReal

theorem eventually_of_subsequence_eventually (P : ℕ → Prop)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᶠ t in atTop, P (phi (psi t))) :
    ∀ᶠ t in atTop, P t := by
  classical
  by_contra hn
  have hfreq : ∃ᶠ t in atTop, ¬ P t := by
    simpa only [not_eventually] using hn
  obtain ⟨phi, hphi, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨psi, _, hgood⟩ := h phi hphi
  obtain ⟨t, ht⟩ := hgood.exists
  exact hbad (psi t) ht

theorem coordinate_subsequence_principle (x : ℕ → ℝ) (a : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        Tendsto (fun t => x (phi (psi t))) atTop (𝓝 a)) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  apply eventually_of_subsequence_eventually (fun t => dist (x t) a < eps)
  intro phi hphi
  obtain ⟨psi, hpsi, hlim⟩ := h phi hphi
  exact ⟨psi, hpsi, Metric.tendsto_nhds.mp hlim eps heps⟩

theorem finite_route_compactness_with_composite
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ StrictMono (phi ∘ psi) ∧ ∃ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi (psi t))) pi := by
  classical
  let x : ℕ → Fin (n + 1) → Icc (0 : ℝ) 1 := fun t j =>
    ⟨actualRouteMass (Γ (phi t)) j.val, measureReal_nonneg, measureReal_le_one⟩
  obtain ⟨p, psi, hpsi, hp⟩ := CompactSpace.tendsto_subseq x
  let pi : ℕ → ℝ := fun j =>
    if hj : j ≤ n then (p ⟨j, Nat.lt_succ_of_le hj⟩).val else 0
  refine ⟨psi, hpsi, hphi.comp hpsi, pi, ?_⟩
  intro j hj
  have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
  have hcont : Continuous (fun y : Fin (n + 1) → Icc (0 : ℝ) 1 =>
      (y ⟨j, Nat.lt_succ_of_le hjn⟩).val) :=
    continuous_subtype_val.comp (continuous_apply _)
  have hc := (hcont.tendsto p).comp hp
  simpa only [Function.comp_def, x, pi, dif_pos hjn] using hc

theorem finite_route_compactness
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi (psi t))) pi := by
  obtain ⟨psi, hpsi, _, pi, hp⟩ := finite_route_compactness_with_composite Γ phi hphi
  exact ⟨psi, hpsi, pi, hp⟩

theorem squeeze_count_error {x y e : ℕ → ℝ} {a : ℝ}
    (hy : Tendsto y atTop (𝓝 a)) (he : Tendsto e atTop (𝓝 0))
    (hxy : ∀ᶠ t in atTop, |x t - y t| ≤ e t) :
    Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [hxy, Metric.tendsto_nhds.mp hy (eps / 2) (half_pos heps),
    he.eventually_lt_const (half_pos heps)] with t ht hyt het
  rw [Real.dist_eq] at hyt ⊢
  have htriangle : |x t - a| ≤ |x t - y t| + |y t - a| := by
    rw [show x t - a = (x t - y t) + (y t - a) by ring]
    exact abs_add_le _ _
  linarith

theorem hasPopulationRate_subsequence_principle
    (M : ℕ → ℕ) (p : ℕ → ℝ) (J : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        HasPopulationRate (fun t => M (phi (psi t)))
          (fun t => p (phi (psi t))) J) :
    HasPopulationRate M p J := by
  constructor
  · apply eventually_of_subsequence_eventually (fun t => 0 < p t)
    intro phi hphi
    obtain ⟨psi, hpsi, hp⟩ := h phi hphi
    exact ⟨psi, hpsi, hp.1⟩
  · apply coordinate_subsequence_principle _ J
    intro phi hphi
    obtain ⟨psi, hpsi, hp⟩ := h phi hphi
    exact ⟨psi, hpsi, hp.2⟩

theorem uniform_subsequence_principle {α : Type*}
    (f : ℕ → α → ℝ) (target : α → ℝ) (S : Set α)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ∀ eps > 0, ∀ᶠ t in atTop, ∀ w ∈ S,
          |f (phi (psi t)) w - target w| < eps) :
    ∀ eps > 0, ∀ᶠ t in atTop, ∀ w ∈ S, |f t w - target w| < eps := by
  intro eps heps
  apply eventually_of_subsequence_eventually
    (fun t => ∀ w ∈ S, |f t w - target w| < eps)
  intro phi hphi
  obtain ⟨psi, hpsi, hp⟩ := h phi hphi
  exact ⟨psi, hpsi, hp eps heps⟩

theorem eventually_of_route_limits
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (P : ℕ → Prop)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi → ∀ᶠ t in atTop, P (phi t)) :
    ∀ᶠ t in atTop, P t := by
  apply eventually_of_subsequence_eventually P
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  exact ⟨psi, hpsi, h (phi ∘ psi) (hphi.comp hpsi) pi hp⟩

theorem coordinate_tendsto_of_route_limits
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (x : ℕ → ℝ) (a : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi →
        Tendsto (fun t => x (phi t)) atTop (𝓝 a)) :
    Tendsto x atTop (𝓝 a) := by
  apply coordinate_subsequence_principle x a
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  exact ⟨psi, hpsi, h (phi ∘ psi) (hphi.comp hpsi) pi hp⟩

theorem routeLimit_of_identified_clusters
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (q : ℕ → ℝ)
    (identify : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi →
        ∀ j ∈ Finset.Icc 0 n, pi j = q j) :
    RouteLimit Γ q := by
  intro j hj
  apply coordinate_tendsto_of_route_limits Γ _ (q j)
  intro phi hphi pi hp
  simpa only [identify phi hphi pi hp j hj] using hp j hj

theorem hasPopulationRate_of_route_limits
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (p : ℕ → ℝ) (J : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi →
        HasPopulationRate (M ∘ phi) (p ∘ phi) J) :
    HasPopulationRate M p J := by
  apply hasPopulationRate_subsequence_principle M p J
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  exact ⟨psi, hpsi, h (phi ∘ psi) (hphi.comp hpsi) pi hp⟩

theorem eventually_shift_iff (T : ℕ) (P : ℕ → Prop) :
    (∀ᶠ t in atTop, P (T + t)) ↔ ∀ᶠ t in atTop, P t := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    apply eventually_atTop.mpr
    refine ⟨T + N, fun t ht => ?_⟩
    have hh := hN (t - T) (by omega)
    have hident : T + (t - T) = t := by omega
    simpa only [hident] using hh
  · intro h
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    exact eventually_atTop.mpr ⟨N, fun t ht => hN (T + t) (by omega)⟩

theorem shift_tendsto_atTop (T : ℕ) :
    Tendsto (fun t : ℕ => T + t) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_ge_atTop N] with t ht
  omega

theorem tendsto_shift_iff {α : Type*} (x : ℕ → α) (T : ℕ) (l : Filter α) :
    Tendsto (fun t => x (T + t)) atTop l ↔ Tendsto x atTop l := by
  constructor
  · intro h
    apply Filter.tendsto_def.mpr
    intro s hs
    exact (eventually_shift_iff T (fun t => x t ∈ s)).mp (h.eventually hs)
  · intro h
    exact h.comp (shift_tendsto_atTop T)

end FCAppendix.Bayes

namespace FCAppendix.Ample.DownstreamNormalizationCore
open MeasureTheory Filter
open scoped ENNReal

theorem probZero_along {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    {μ : (t : ℕ) → Measure (Ω t)} {X : (t : ℕ) → Ω t → ℝ}
    (h : ProbZero μ X) (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    ProbZero (fun t => μ (phi t)) (fun t => X (phi t)) := by
  intro eps heps eta heta
  exact hphi.eventually (h eps heps eta heta)

theorem probZero_shift_iff {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (μ : (t : ℕ) → Measure (Ω t)) (X : (t : ℕ) → Ω t → ℝ) (T : ℕ) :
    ProbZero (fun t => μ (T + t)) (fun t => X (T + t)) ↔ ProbZero μ X := by
  constructor
  · intro h eps heps eta heta
    exact (FCAppendix.Bayes.eventually_shift_iff T _).mp (h eps heps eta heta)
  · intro h
    exact probZero_along h _ (FCAppendix.Bayes.shift_tendsto_atTop T)

end FCAppendix.Ample.DownstreamNormalizationCore
