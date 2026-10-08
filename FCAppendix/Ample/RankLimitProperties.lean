import FCAppendix.Ample.RankMeasureBasics
import FCAppendix.Ample.RankFiniteWeak
import FCAppendix.Ample.CongestionRate

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

theorem rank_finite_sum_finite_on {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    (hμ : ∀ i ∈ s, IsFiniteMeasure (μ i)) : IsFiniteMeasure (∑ i ∈ s, μ i) := by
  classical
  revert hμ
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    infer_instance
  | @insert i s hi ih =>
    intro hμ
    letI := hμ i (Finset.mem_insert_self _ _)
    letI := ih (fun j hj => hμ j (Finset.mem_insert_of_mem hj))
    rw [Finset.sum_insert hi]
    infer_instance

theorem rank_finite_sum_real_on {ι : Type*} (s : Finset ι) (μ : ι → Measure ℝ)
    (hμ : ∀ i ∈ s, IsFiniteMeasure (μ i)) (A : Set ℝ) :
    (∑ i ∈ s, μ i).real A = ∑ i ∈ s, (μ i).real A := by
  classical
  revert hμ
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert i s hi ih =>
    intro hμ
    letI := hμ i (Finset.mem_insert_self _ _)
    have hs := fun j hj => hμ j (Finset.mem_insert_of_mem hj)
    letI := rank_finite_sum_finite_on s μ hs
    rw [Finset.sum_insert hi, measureReal_add_apply, ih hs, Finset.sum_insert hi]

namespace RankLimit
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem finite {j : ℕ} (hj : j ∈ Finset.Icc 1 n) : IsFiniteMeasure (nu j) :=
  finite_of_rank_domination (hr.dominated j hj)

theorem atomless {j : ℕ} (hj : j ∈ Finset.Icc 1 n) (u : ℝ) : nu j {u} = 0 :=
  atomless_of_rank_domination (hr.dominated j hj) u

theorem supported {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu j, u ∈ Ioc 0 h := support_of_rank_domination (hr.dominated j hj)

theorem tail_eq_strict {j : ℕ} (hj : j ∈ Finset.Icc 1 n) (u : ℝ) :
    rankTail nu h u j = (nu j).real (Ioi u) := by
  letI := hr.finite hj
  exact (strict_tail_eq_bounded_tail ((hr.supported hj).mono fun _ hx => hx.2) u).symm

theorem continuous_tail {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    Continuous (fun u => rankTail nu h u j) := by
  letI := hr.finite hj
  exact continuous_bounded_tail (nu j) (hr.atomless hj) h

theorem tail_one_lipschitz {j : ℕ} (hj : j ∈ Finset.Icc 1 n) (u v : ℝ) :
    |rankTail nu h u j - rankTail nu h v j| ≤ |u-v| := by
  letI := hr.finite hj
  simp only [hr.tail_eq_strict hj]
  exact strict_tail_one_lipschitz (hr.dominated j hj) u v

theorem tail_le_mass {j : ℕ} (hj : j ∈ Finset.Icc 1 n) (u : ℝ) :
    rankTail nu h u j ≤ pi j := by
  letI := hr.finite hj
  rw [← hr.mass j hj]
  exact measureReal_mono (subset_univ _)

theorem tail_zero {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    rankTail nu h 0 j = pi j := by
  letI := hr.finite hj
  rw [← hr.mass j hj]
  apply measureReal_congr
  filter_upwards [hr.supported hj] with u hu
  exact propext ⟨fun _ => trivial, fun _ => hu⟩

theorem sum_tail {u : ℝ} (hu : u ∈ Icc 0 h) :
    (∑ j ∈ Finset.Icc 1 n, rankTail nu h u j) = h-u := by
  change (∑ j ∈ Finset.Icc 1 n, (nu j).real (Ioc u h)) = _
  rw [← rank_finite_sum_real_on (Finset.Icc 1 n) nu
    (fun j hj => hr.finite hj) (Ioc u h), hr.sum_law,
    measureReal_restrict_apply measurableSet_Ioc]
  have hsub : Ioc u h ⊆ Ioc 0 h := fun x hx => ⟨hu.1.trans_lt hx.1, hx.2⟩
  rw [inter_eq_left.mpr hsub, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hu.2)]

theorem interval_mass {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ h) :
    (∀ j ∈ Finset.Icc 1 n, 0 ≤ rankTail nu h u j - rankTail nu h v j) ∧
    (∑ j ∈ Finset.Icc 1 n, (rankTail nu h u j - rankTail nu h v j)) = v-u := by
  refine ⟨?_, ?_⟩
  · intro j hj
    letI := hr.finite hj
    exact sub_nonneg.mpr (measureReal_mono (fun x hx => ⟨huv.trans_lt hx.1, hx.2⟩))
  · rw [Finset.sum_sub_distrib, hr.sum_tail ⟨hu, huv.trans hv⟩,
      hr.sum_tail ⟨hu.trans huv, hv⟩]
    ring

theorem valid_tail (hh : h ≤ 1) (u : ℝ) : ValidLaw n (rankTail nu h u) := by
  refine ⟨fun _ _ => measureReal_nonneg, ?_⟩
  calc
    (∑ j ∈ Finset.Icc 1 n, rankTail nu h u j)
        = (volume.restrict (Ioc 0 h)).real (Ioc u h) := by
          change (∑ j ∈ Finset.Icc 1 n, (nu j).real (Ioc u h)) = _
          rw [← rank_finite_sum_real_on (Finset.Icc 1 n) nu
            (fun j hj => hr.finite hj) (Ioc u h), hr.sum_law]
    _ ≤ (volume.restrict (Ioc 0 h)).real univ := by
      letI := volume_rank_interval_finite h
      exact measureReal_mono (subset_univ _)
    _ ≤ 1 := by
      rw [measureReal_restrict_apply_univ, Measure.real, Real.volume_Ioc, sub_zero]
      by_cases hh0 : 0 ≤ h
      · rwa [ENNReal.toReal_ofReal hh0]
      · rw [ENNReal.ofReal_of_nonpos (lt_of_not_ge hh0).le, ENNReal.toReal_zero]
        norm_num

theorem used_tail_positive {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, 0 < u ∧ u < h ∧ 0 < rankTail nu h u k := by
  letI := hr.finite hk
  exact bounded_tail_pos_ae (nu k) (hr.atomless hk) (hr.supported hk)

theorem along (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    RankLimit (fun t => Γ (phi t)) pi h nu where
  dominated := hr.dominated
  sum_law := hr.sum_law
  mass := hr.mass
  weak := fun j hj f hf => (hr.weak j hj f hf).comp hphi
  tails := fun ε hε => hphi.eventually (hr.tails ε hε)

end RankLimit
end FCAppendix.Bayes
