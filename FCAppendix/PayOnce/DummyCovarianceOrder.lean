import FCAppendix.PayOnce.InactiveProfileWeights
import FCAppendix.PayOnce.ProfileCovarianceOrder

namespace FCAppendix.PayOnce.KernelTailEvent
open CommonList

theorem kernel_monotone_bid (n : ℕ) (hn : 2 ≤ n) {L : ℝ} (hL : 0 < L) :
    Monotone (fun b : ℝ => kernel n b L) := by
  intro a b hab
  dsimp only
  by_cases ha : 0 < a
  · exact kernel_monotone_positive_bid hn ha hab hL
  · rw [kernel_of_le n ((le_of_not_gt ha).trans hL.le)]
    by_cases hb : 0 < b
    · exact kernel_nonneg n hn hb hL
    · rw [kernel_of_le n ((le_of_not_gt hb).trans hL.le)]

end FCAppendix.PayOnce.KernelTailEvent

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.DummyKernel PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_all_profile_effectiveBids_eq_type (Γ : FiniteGame m n c Seed) (bid : ℝ → ℝ)
    (hpure : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i, effectiveBid (d i).1.2 = bid (d i).1.1 := by
  have hu := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae hpure
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

theorem ae_dummy_profile_marginal_coordered (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (bid : ℝ → ℝ) (hmono : Monotone bid)
    (hpure : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1)
    (h : ℝ → ℝ) (hh : Monotone h) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i j,
      0 ≤ (h (d i).1.1-h (d j).1.1)*(dummyProfileMarginal Γ hn d i-dummyProfileMarginal Γ hn d j) := by
  filter_upwards [ae_all_profile_effectiveBids_eq_type Γ bid hpure] with d htype
  obtain ⟨L,hL,hp,_⟩ := profileMarginal_root (c := c) hn (fun j => effectiveBid (d j).1.2)
  intro i j
  change 0 ≤ (h (d i).1.1-h (d j).1.1)*
    (profileMarginal n c hn (fun j => effectiveBid (d j).1.2) i-
      profileMarginal n c hn (fun j => effectiveBid (d j).1.2) j)
  rw [hp i,hp j,htype i,htype j]
  rcases le_total (d j).1.1 (d i).1.1 with hij | hij
  · exact mul_nonneg (sub_nonneg.mpr (hh hij))
      (sub_nonneg.mpr (KernelTailEvent.kernel_monotone_bid n hn hL (hmono hij)))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hh hij))
      (sub_nonpos.mpr (KernelTailEvent.kernel_monotone_bid n hn hL (hmono hij)))

theorem ae_dummy_profile_success_coordered (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n)
    (bid : ℝ → ℝ) (hmono : Monotone bid)
    (hpure : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), effectiveBid x.2 = bid x.1)
    (h : ℝ → ℝ) (hh : Monotone h) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i j,
      0 ≤ (h (d i).1.1-h (d j).1.1)*(success n (dummyProfileMarginal Γ hn d i)-
        success n (dummyProfileMarginal Γ hn d j)) := by
  filter_upwards [ae_dummy_profile_marginal_coordered Γ hn bid hmono hpure h hh] with d hd
  intro i j
  have hp := dummyProfileMarginal_bounds Γ hn d i
  have hq := dummyProfileMarginal_bounds Γ hn d j
  have hs {p q : ℝ} (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hpq : p ≤ q) : success n p ≤ success n q := by
    unfold success
    exact sub_le_sub_left (pow_le_pow_left₀ (sub_nonneg.mpr hq1) (by linarith) n) 1
  rcases le_total (dummyProfileMarginal Γ hn d j) (dummyProfileMarginal Γ hn d i) with hij | hij
  · by_cases he : dummyProfileMarginal Γ hn d j = dummyProfileMarginal Γ hn d i
    · simp only [he,sub_self,mul_zero,le_refl]
    · have hval : 0 ≤ h (d i).1.1-h (d j).1.1 :=
        nonneg_of_mul_nonneg_left (hd i j) (sub_pos.mpr (lt_of_le_of_ne hij he))
      exact mul_nonneg hval (sub_nonneg.mpr (hs hq.2 hp.2 hij))
  · by_cases he : dummyProfileMarginal Γ hn d i = dummyProfileMarginal Γ hn d j
    · simp only [he,sub_self,mul_zero,le_refl]
    · have hval : h (d i).1.1-h (d j).1.1 ≤ 0 :=
        nonpos_of_mul_nonneg_left (hd i j) (sub_neg.mpr (lt_of_le_of_ne hij he))
      exact mul_nonneg_of_nonpos_of_nonpos hval (sub_nonpos.mpr (hs hp.2 hq.2 hij))

end FCAppendix.Bayes
