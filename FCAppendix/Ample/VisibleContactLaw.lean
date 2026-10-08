import FCAppendix.Ample.ContactLawIdentification
import FCAppendix.Finite.AmplePairRanks
import FCAppendix.Game.CommonListSeeds

namespace FCAppendix

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FiniteLaw

theorem prob_ofMeasure {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → α) (hf : Measurable f)
    (E : α → Prop) :
    (ofMeasure μ f hf).prob E = μ.real {ω | E (f ω)} := by
  classical
  rw [prob_eq_expect, expect_ofMeasure]
  have hE : MeasurableSet {a | E a} := (Set.toFinite _).measurableSet
  simpa only [Set.indicator, Set.mem_setOf_eq, Set.mem_preimage, Set.preimage_setOf_eq, Pi.one_apply] using
    integral_indicator_one (μ := μ) (hf hE)

theorem integrable_finite_comp {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → α) (hf : Measurable f)
    (g : α → ℝ) : Integrable (fun ω => g (f ω)) μ := by
  classical
  have h := integrable_finsetSum Finset.univ
    (fun a _ => (integrable_finite_fiber μ f hf a).mul_const (g a))
  simpa [ite_mul, eq_comm] using h

end FiniteLaw

namespace Bayes

open Game

variable {m n N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def visibleContact (b : ℝ) (d : UserDraw n) : Finset (Fin n) :=
  if b < d.1.2.bid then firstK d.2 d.1.2.routeCount else ∅

@[simp] theorem mem_visibleContact (b : ℝ) (d : UserDraw n) (s : Fin n) :
    s ∈ visibleContact b d ↔ d ∈ aboveAt s b := by
  classical
  by_cases hb : b < d.1.2.bid <;> simp [visibleContact, aboveAt, hb]

theorem visibleContact_inactive (b : ℝ) (d : UserDraw n)
    (hd : d.1.2.routeCount = 0) : visibleContact b d = ∅ := by
  classical
  ext s
  simp [visibleContact, hd, firstK]

theorem measurable_visibleContact (b : ℝ) : Measurable (visibleContact (n := n) b) := by
  classical
  have hb : Measurable (fun d : UserDraw n => d.1.2.bid) :=
    (measurable_bid n).comp (measurable_snd.comp measurable_fst)
  have hk : Measurable (fun d : UserDraw n => d.1.2.routeCount) :=
    (measurable_routeCount n).comp (measurable_snd.comp measurable_fst)
  have hr : Measurable (fun d : UserDraw n => firstK d.2 d.1.2.routeCount) :=
    (measurable_of_countable (fun p : Equiv.Perm (Fin n) × ℕ => firstK p.1 p.2)).comp
      (measurable_snd.prodMk hk)
  exact Measurable.ite (measurableSet_lt measurable_const hb) hr measurable_const

noncomputable def visibleLaw (Γ : FiniteGame m n c Seed) (b : ℝ) :
    FiniteLaw (Finset (Fin n)) :=
  FiniteLaw.ofMeasure (userLaw Γ) (visibleContact b) (measurable_visibleContact b)

theorem visibleContact_mul_right (b : ℝ) (x : ℝ × JointAction n)
    (τ e : Equiv.Perm (Fin n)) :
    visibleContact b (x, τ * e) = e.symm.finsetCongr (visibleContact b (x, τ)) := by
  classical
  ext s
  simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv, Equiv.symm_symm,
    mem_visibleContact, aboveAt, Set.mem_setOf_eq, mem_firstK, Equiv.Perm.mul_apply]

theorem visibleLaw_permInvariant (Γ : FiniteGame m n c Seed) (b : ℝ) :
    Ample.PermInvariant (visibleLaw Γ b) := by
  classical
  intro e T
  change (FiniteLaw.ofMeasure _ _ _).mass (e.finsetCongr T) =
    (FiniteLaw.ofMeasure _ _ _).mass T
  rw [FiniteLaw.ofMeasure_mass, FiniteLaw.ofMeasure_mass]
  apply congrArg ENNReal.toReal
  rw [userLaw, Measure.prod_apply (measurableSet_eq_fun (measurable_visibleContact b) measurable_const),
    Measure.prod_apply (measurableSet_eq_fun (measurable_visibleContact b) measurable_const)]
  apply lintegral_congr
  intro x
  have he : {τ : Equiv.Perm (Fin n) | visibleContact b (x, τ) = e.finsetCongr T} =
      {τ : Equiv.Perm (Fin n) | visibleContact b (x, τ * e) = T} := by
    ext τ
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, visibleContact_mul_right]
    constructor
    · intro h
      rw [h, ← Equiv.finsetCongr_symm]
      exact e.finsetCongr.symm_apply_apply T
    · intro h
      have hh := congrArg e.finsetCongr h
      rw [← Equiv.finsetCongr_symm, Equiv.apply_symm_apply] at hh
      exact hh
  change (permLaw n) {τ | visibleContact b (x, τ) = e.finsetCongr T} = _
  rw [he]
  exact permLaw_mul_right (fun τ => visibleContact b (x, τ) = T) e

noncomputable def visibleClassMass (Γ : FiniteGame m n c Seed) (b : ℝ) : ℕ → ℝ :=
  Ample.classMass (visibleLaw Γ b)

theorem visibleClassMass_valid (Γ : FiniteGame m n c Seed) (b : ℝ) :
    Ample.ValidLaw n (visibleClassMass Γ b) :=
  Ample.validLaw_classMass _

theorem visibleLaw_eq_contactLaw (Γ : FiniteGame m n c Seed) (b : ℝ) :
    visibleLaw Γ b = Ample.contactLaw n (visibleClassMass Γ b)
      (visibleClassMass_valid Γ b) :=
  Ample.eq_contactLaw_of_permInvariant (visibleLaw_permInvariant Γ b)

theorem visibleClassMass_eq_compProd (Γ : FiniteGame m n c Seed) (b : ℝ)
    {j : ℕ} (hj : 1 ≤ j) :
    visibleClassMass Γ b j =
      (Γ.F ⊗ₘ Γ.σ).real {x | b < x.2.bid ∧ x.2.routeCount = j} := by
  classical
  change (FiniteLaw.ofMeasure (userLaw Γ) (visibleContact b) (measurable_visibleContact b)).prob
    (fun T => T.card = j) = _
  rw [FiniteLaw.prob_ofMeasure]
  have he : {d : UserDraw n | (visibleContact b d).card = j} =
      {x : ℝ × JointAction n | b < x.2.bid ∧ x.2.routeCount = j} ×ˢ Set.univ := by
    ext d
    by_cases hb : b < d.1.2.bid
    · simp [visibleContact, hb, card_firstK _ _ d.1.2.routeCount_le]
    · have hj0 : j ≠ 0 := by omega
      simp [visibleContact, hb, Ne.symm hj0]
  rw [he, userLaw, measureReal_prod_prod, probReal_univ, mul_one]

theorem visibleLaw_marginal (Γ : FiniteGame m n c Seed) (b : ℝ) (s : Fin n) :
    Proposer.marginal (visibleLaw Γ b) s = alphaGt Γ s b := by
  change (FiniteLaw.ofMeasure _ _ _).prob _ = _
  rw [FiniteLaw.prob_ofMeasure]
  simp only [mem_visibleContact]
  rfl

theorem visibleClassMass_marginal (Γ : FiniteGame m n c Seed) (b : ℝ) (s : Fin n) :
    Ample.contactMarginal n (visibleClassMass Γ b) = alphaGt Γ s b := by
  rw [← Ample.contactLaw_marginal n _ (visibleClassMass_valid Γ b) s,
    ← visibleLaw_eq_contactLaw, visibleLaw_marginal]

noncomputable def submittedMarginal (Γ : FiniteGame m n c Seed) : ℝ :=
  (∫ x : ℝ × JointAction n, (x.2.routeCount : ℝ) ∂(Γ.F ⊗ₘ Γ.σ)) / n

theorem submittedMarginal_eq_contactMarginal (Γ : FiniteGame m n c Seed) :
    submittedMarginal Γ = Ample.contactMarginal n (visibleClassMass Γ (-1)) := by
  have hcard (d : UserDraw n) : (visibleContact (-1) d).card = d.1.2.routeCount := by
    rw [visibleContact, if_pos (show (-1 : ℝ) < d.1.2.bid by linarith [d.1.2.bid_nonneg]),
      card_firstK _ _ d.1.2.routeCount_le]
  have he : (visibleLaw Γ (-1)).expect (fun T => (T.card : ℝ)) =
      ∫ x : ℝ × JointAction n, (x.2.routeCount : ℝ) ∂(Γ.F ⊗ₘ Γ.σ) := by
    rw [visibleLaw, FiniteLaw.expect_ofMeasure]
    simp_rw [hcard]
    have hi : Integrable (fun d : UserDraw n => (d.1.2.routeCount : ℝ)) (userLaw Γ) := by
      simpa only [hcard] using FiniteLaw.integrable_finite_comp (userLaw Γ)
        (visibleContact (-1)) (measurable_visibleContact (-1)) (fun T => (T.card : ℝ))
    rw [userLaw, integral_prod _ hi]
    simp
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_expect_card] at he
  unfold submittedMarginal Ample.contactMarginal
  rw [he]

noncomputable def rivalContacts (i : Fin (N + 1)) (b : ℝ)
    (d : UserProfile (N + 1) n) : Fin N → Finset (Fin n) :=
  fun l => visibleContact b (d (i.succAbove l))

theorem measurable_rivalContacts (i : Fin (N + 1)) (b : ℝ) :
    Measurable (rivalContacts (n := n) i b) :=
  measurable_pi_lambda _ fun _ => (measurable_visibleContact b).comp (measurable_pi_apply _)

theorem rivalContacts_law (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (b : ℝ) :
    FiniteLaw.ofMeasure (Measure.pi fun _ : Fin (N + 1) => userLaw Γ)
      (rivalContacts i b) (measurable_rivalContacts i b) =
        CommonList.iid (visibleLaw Γ b) N := by
  let drop : UserProfile (N + 1) n → (Fin N → UserDraw n) :=
    fun d l => d (i.succAbove l)
  have hdrop : MeasurePreserving drop
      (Measure.pi fun _ : Fin (N + 1) => userLaw Γ)
      (Measure.pi fun _ : Fin N => userLaw Γ) :=
    (measurePreserving_snd (μ := userLaw Γ)
      (ν := Measure.pi fun _ : Fin N => userLaw Γ)).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => userLaw Γ) i)
  let f : (Fin N → UserDraw n) → (Fin N → Finset (Fin n)) :=
    fun d l => visibleContact b (d l)
  have hf : Measurable f := measurable_pi_lambda _ fun _ =>
    (measurable_visibleContact b).comp (measurable_pi_apply _)
  change FiniteLaw.ofMeasure _ (f ∘ drop) _ = _
  rw [FiniteLaw.ofMeasure_comp_measurePreserving _ _ drop hdrop f hf]
  exact FiniteLaw.ofMeasure_pi_eq_iid (userLaw Γ) N (fun _ => visibleContact b)
    (fun _ => measurable_visibleContact b) (visibleLaw Γ b) (fun _ => rfl)

theorem includers_rivalContacts (i : Fin (N + 1)) (b : ℝ)
    (d : UserProfile (N + 1) n) (s : Fin n) :
    CommonList.includers s (rivalContacts i b d) =
      PiBinomial.count (aboveAt s b) (Finset.univ.erase i) d := by
  classical
  rw [PiBinomial.count_eq_sum]
  unfold CommonList.includers rivalContacts
  simp only [mem_visibleContact]
  have hsum := Fin.sum_univ_succAbove
    (fun l => if d l ∈ aboveAt s b then (1 : ℕ) else 0) i
  have herase := Finset.sum_erase_add Finset.univ
    (fun l => if d l ∈ aboveAt s b then (1 : ℕ) else 0) (Finset.mem_univ i)
  omega

theorem joint_rank_congestion_eq (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (b : ℝ) (K : Finset (Fin n)) :
    (backgroundLaw Γ).real {ω | ∀ s ∈ K, c ≤ rivals i (aboveAt s b) ω} =
      Ample.congestProbAt n N c (visibleClassMass Γ b) K := by
  classical
  have he : {ω : Background (N + 1) n Seed |
      ∀ s ∈ K, c ≤ rivals i (aboveAt s b) ω} =
      {d : UserProfile (N + 1) n | SimultaneousCongestion.Congested K c
        (rivalContacts i b d)} ×ˢ Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true,
      SimultaneousCongestion.Congested, includers_rivalContacts, rivals]
  rw [he, backgroundLaw, measureReal_prod_prod, probReal_univ, mul_one]
  rw [← FiniteLaw.prob_ofMeasure _ _ (measurable_rivalContacts i b), rivalContacts_law]
  change SimultaneousCongestion.congestionProb (visibleLaw Γ b) K N c = _
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb]

theorem ppi_joint_rejection_eq_congestProbAt (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ s, ProposerRationalAtFeasibleLists Γ s)
    (i : Fin (N + 1)) (b : ℝ) (hb : 0 < b) (K : Finset (Fin n)) :
    (backgroundLaw Γ).real {ω | ∀ s ∈ K, ¬ Accepts Γ i b s ω} =
      Ample.congestProbAt n N c (visibleClassMass Γ b) K := by
  have ha : ∀ᵐ ω ∂backgroundLaw Γ, ∀ s,
      (Accepts Γ i b s ω ↔ rivals i (aboveAt s b) ω < c) :=
    ae_all_iff.mpr (fun s => ae_ppi_accepts_iff_rank Γ hA hatom s (hj s) i b hb)
  calc
    _ = (backgroundLaw Γ).real {ω | ∀ s ∈ K, c ≤ rivals i (aboveAt s b) ω} := by
      apply measureReal_congr
      filter_upwards [ha] with ω hω
      apply propext
      constructor
      · intro h s hs
        exact Nat.le_of_not_gt (fun hr => h s hs ((hω s).mpr hr))
      · intro h s hs haccept
        exact (Nat.not_lt_of_ge (h s hs)) ((hω s).mp haccept)
    _ = _ := joint_rank_congestion_eq Γ i b K

end Bayes
end FCAppendix
