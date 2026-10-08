import FCAppendix.Ample.SlackAccounting
import FCAppendix.Ample.FreeBaseIncentives

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure FreeBaseBoundarySequence
    (M C : ℕ → ℕ) (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) (g : ℝ) : Prop where
  proposers_two : 2 ≤ n
  common_values : ∀ t, (Γ t).F = F
  common_fee : ∀ t, (Γ t).g = g
  atomless_values : ∀ v : ℝ, F {v} = 0
  active_pos : 0 < F.real (Ioi g)
  population_grows : Tendsto M atTop atTop
  capacity_ratio : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 1)
  strict_shortage : ∀ᶠ t in atTop, C t < M t
  users : ∀ t, UsersOptimal (Γ t)
  bayes_receipts : ∀ t, BayesReceiptOptimalOnPath (Γ t) (B t)
  feasible_continuations : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j
  visible_atomless : ∀ t, PositiveVisibleAtomless (Γ t)
  ppi : ∀ t, (Γ t).A = Schedule.ppi n
  free : ∀ t, FreeDuplicateBase (Γ t)
  abstention : ∀ t, NonpositiveAbstention (Γ t)
  reject_zero : ∀ t, RejectsZeroBids (Γ t)

namespace FreeBaseBoundarySequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g : ℝ}
  (h : FreeBaseBoundarySequence M C Γ B F g)
include h

lemma probability : IsProbabilityMeasure F := by
  rw [← h.common_values 0]
  infer_instance

lemma active_le_one : F.real (Ioi g) ≤ 1 := by
  letI := h.probability
  exact measureReal_le_one

lemma ample_at_boundary : F.real (Ioi g) < (n : ℝ) := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h.proposers_two
  linarith [h.active_le_one]

lemma eventually_finite_guards :
    ∀ᶠ t in atTop, 1 < M t ∧ 0 < C t ∧ C t ≤ M t - 1 := by
  have hratio : ∀ᶠ t in atTop, (1 / 2 : ℝ) < (C t : ℝ) / M t :=
    (tendsto_order.mp h.capacity_ratio).1 (1 / 2) (by norm_num)
  filter_upwards [h.population_grows.eventually_ge_atTop 2,
    h.strict_shortage, hratio] with t hm hc hr
  have hmR : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
  have hcR : (0 : ℝ) < C t := by
    have hh := (lt_div_iff₀ hmR).mp hr
    nlinarith
  exact ⟨by omega, Nat.cast_pos.mp hcR, by omega⟩

lemma along (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    FreeBaseBoundarySequence (M ∘ φ) (C ∘ φ) (fun t => Γ (φ t))
      (fun t => B (φ t)) F g where
  proposers_two := h.proposers_two
  common_values := fun t => h.common_values (φ t)
  common_fee := fun t => h.common_fee (φ t)
  atomless_values := h.atomless_values
  active_pos := h.active_pos
  population_grows := h.population_grows.comp hφ
  capacity_ratio := h.capacity_ratio.comp hφ
  strict_shortage := hφ.eventually h.strict_shortage
  users := fun t => h.users (φ t)
  bayes_receipts := fun t => h.bayes_receipts (φ t)
  feasible_continuations := fun t => h.feasible_continuations (φ t)
  visible_atomless := fun t => h.visible_atomless (φ t)
  ppi := fun t => h.ppi (φ t)
  free := fun t => h.free (φ t)
  abstention := fun t => h.abstention (φ t)
  reject_zero := fun t => h.reject_zero (φ t)

end FreeBaseBoundarySequence
end FCAppendix.Bayes.CompletionDraft

namespace FCAppendix.Ample.CompletionDraft
open Filter Set Topology Finset
open scoped BigOperators

theorem mean_gap_of_singleton_mass {n : ℕ} (hn : 1 ≤ n)
    (π : ℕ → ℝ) (hπ : ∀ j ∈ Finset.Icc 1 n, 0 ≤ π j) :
    (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * π j) / n ≤
      (∑ j ∈ Finset.Icc 1 n, π j) - ((n : ℝ) - 1) / n * π 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsum : ((n : ℝ) - 1) * π 1 ≤
      ∑ j ∈ Finset.Icc 1 n, ((n : ℝ) - j) * π j := by
    have hh := Finset.single_le_sum
      (s := Finset.Icc 1 n) (f := fun j : ℕ => ((n : ℝ) - j) * π j)
      (fun j hj => mul_nonneg
        (sub_nonneg.mpr (show (j : ℝ) ≤ n by exact_mod_cast (mem_Icc.mp hj).2))
        (hπ j hj)) (mem_Icc.mpr ⟨le_rfl, hn⟩ : 1 ∈ Finset.Icc 1 n)
    simpa only [Nat.cast_one] using hh
  have he : (∑ j ∈ Finset.Icc 1 n, ((n : ℝ) - j) * π j) =
      (n : ℝ) * (∑ j ∈ Finset.Icc 1 n, π j) -
        ∑ j ∈ Finset.Icc 1 n, (j : ℝ) * π j := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he] at hsum
  apply (div_le_iff₀ hnR).mpr
  have hcancel :
      ((∑ j ∈ Finset.Icc 1 n, π j) - ((n : ℝ) - 1) / n * π 1) * n =
      (n : ℝ) * (∑ j ∈ Finset.Icc 1 n, π j) - ((n : ℝ) - 1) * π 1 := by
    field_simp [hnR.ne']
  rw [hcancel]
  linarith

theorem eventually_mean_gap_of_singleton_floor
    {n : ℕ} (hn : 2 ≤ n) (π : ℕ → ℕ → ℝ)
    (hπ : ∀ t j, j ∈ Finset.Icc 1 n → 0 ≤ π t j)
    {h a : ℝ} (hh : h ≤ 1) (ha : 0 < a)
    (htotal : Tendsto (fun t => ∑ j ∈ Finset.Icc 1 n, π t j) atTop (𝓝 h))
    (hfloor : ∀ᶠ t in atTop, a ≤ π t 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t in atTop,
      (∑ j ∈ Finset.Icc 1 n, (j : ℝ) * π t j) / n ≤ 1 - δ := by
  let δ : ℝ := ((n : ℝ) - 1) * a / (2 * n)
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  have hsmall : ∀ᶠ t in atTop, (∑ j ∈ Finset.Icc 1 n, π t j) < h + δ :=
    (tendsto_order.mp htotal).2 _ (by linarith)
  filter_upwards [hfloor, hsmall] with t hft hst
  have hbound := mean_gap_of_singleton_mass (by omega : 1 ≤ n) (π t) (hπ t)
  have hcoef : 0 ≤ ((n : ℝ) - 1) / n := by positivity
  have hmul := mul_le_mul_of_nonneg_left hft hcoef
  have he : ((n : ℝ) - 1) / n * a = 2 * δ := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hnR)
    dsimp [δ]
    field_simp [hn0]
  rw [he] at hmul
  linarith

end FCAppendix.Ample.CompletionDraft
