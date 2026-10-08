import FCAppendix.PayOnce.DummyJointKernel
import FCAppendix.PayOnce.VisibleDummyKernel
import FCAppendix.PayOnce.KernelAgreement

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList Bayes
open scoped BigOperators
variable {m n c : ℕ}

noncomputable def profileMarginal (n c : ℕ) (hn : 2 ≤ n) (b : Fin m → ℝ) (i : Fin m) : ℝ :=
  allocation n c hn (fun j : Rival i => b j.val) (b i)

theorem active_card_focal (b : Fin m → ℝ) (i : Fin m) (hb : 0 < b i) :
    Fintype.card (Active b) = Fintype.card (Active (fun j : Rival i => b j.val))+1 := by
  classical
  have ha : (∑ j, if 0 < b j then (1:ℝ) else 0) = (Fintype.card (Active b):ℝ) := by
    simp [Active,Fintype.card_subtype]
  have hr : (∑ j : Rival i, if 0 < b j.val then (1:ℝ) else 0) =
      (Fintype.card (Active (fun j : Rival i => b j.val)):ℝ) := by
    simp [Active,Fintype.card_subtype]
  have hs := sum_focal_rivals i (fun j => if 0 < b j then (1:ℝ) else 0)
  rw [if_pos hb,ha,hr] at hs
  exact_mod_cast (show (Fintype.card (Active b):ℝ) =
    (Fintype.card (Active (fun j : Rival i => b j.val)):ℝ)+1 by linarith)

theorem profileMarginal_bounds (hn : 2 ≤ n) (b : Fin m → ℝ) (i : Fin m) :
    profileMarginal n c hn b i ∈ Icc (0:ℝ) 1 := allocation_bounds hn _ _

theorem measurable_profileMarginal (hn : 2 ≤ n) (i : Fin m) :
    Measurable (fun b : Fin m → ℝ => profileMarginal n c hn b i) := by
  have hr : Measurable (fun b : Fin m → ℝ => fun j : Rival i => b j.val) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply j.val
  have hm : Measurable (fun b : Fin m → ℝ => (b i,fun j : Rival i => b j.val)) :=
    (measurable_pi_apply i).prodMk hr
  exact (measurable_allocation_joint hn).comp hm

theorem profileMarginal_eq_kernel (hn : 2 ≤ n) (b : Fin m → ℝ) {L : ℝ} (hL : 0 < L)
    (hcap : (∑ j, kernel n (b j) L) = min c (Fintype.card (Active b))) (i : Fin m) :
    profileMarginal n c hn b i = kernel n (b i) L := by
  unfold profileMarginal
  by_cases hb : 0 < b i
  · apply allocation_eq_kernel hn _ hb hL
    rw [← active_card_focal b i hb]
    exact (sum_focal_rivals i (fun j => kernel n (b j) L)).trans hcap
  · rw [allocation_eq_zero_of_nonpos hn _ (le_of_not_gt hb),
      kernel_of_le n ((le_of_not_gt hb).trans hL.le)]

theorem profileMarginal_root (hn : 2 ≤ n) (b : Fin m → ℝ) :
    ∃ L : ℝ, 0 < L ∧ (∀ i, profileMarginal n c hn b i = kernel n (b i) L) ∧
      (∑ j, kernel n (b j) L) = min c (Fintype.card (Active b)) := by
  classical
  obtain ⟨μ,hμ,_⟩ := CommonList.exists_equilibrium n hn (fun j : Active b => b j.val)
    (fun j => j.property) (min c (Fintype.card (Active b))) (min_le_right _ _)
  obtain ⟨L,hL,_,hcap⟩ := CommonList.equilibrium_kernel n hn (fun j : Active b => b j.val)
    (fun j => j.property) (min c (Fintype.card (Active b))) (min_le_right _ _) μ hμ
  rw [sum_active b hL] at hcap
  exact ⟨L,hL,profileMarginal_eq_kernel hn b hL hcap,hcap⟩

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set CommonList
open PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_profileCountLaw_eq_dummy_binomial (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1)) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i,
      profileCountLaw Γ d i = IndependentCounts.binomial (k+1)
        (profileMarginal (k+1) c (by omega) (fun j => effectiveBid (d j).1.2) i)
        (profileMarginal_bounds (by omega) _ i).1 (profileMarginal_bounds (by omega) _ i).2 := by
  filter_upwards [ae_dummy_kernel_representation Γ hk hA B hB hsym hroute] with d hd
  obtain ⟨L,hL,hlaw,hcap⟩ := hd
  intro i
  have he := profileMarginal_eq_kernel (by omega : 2 ≤ k+1) (fun j => effectiveBid (d j).1.2) hL hcap i
  simpa only [he] using hlaw i

end FCAppendix.Bayes
