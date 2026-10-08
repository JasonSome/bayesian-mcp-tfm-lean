import FCAppendix.PayOnce.FiniteJensen
import FCAppendix.Game.PosteriorReceipts

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def exclusiveReceipts (belief : Fin m → FiniteLaw (Fin n))
    (ℓ : LocalList m) : Fin m → ℝ :=
  fun l => match ℓ l with
    | some b => b * (belief l).prob (fun r => r.val = 0)
    | none => 0

def ExclusivePosteriorOptimalAE (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) :
    Prop :=
  ∀ j ℓ, FeasibleObservedList j ℓ → ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

def ExclusivePosteriorOptimalOnPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) : Prop :=
  ∀ j, ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

theorem ExclusivePosteriorOptimalAE.to_onPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (h : ExclusivePosteriorOptimalAE Γ B) :
    ExclusivePosteriorOptimalOnPath Γ B := by
  intro j
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  obtain ⟨d, hd⟩ := hℓ.exists
  exact h j ℓ ⟨d, hd⟩

theorem exclusiveReceipts_none (belief : Fin m → FiniteLaw (Fin n)) (ℓ : LocalList m)
    (l : Fin m) (hl : ℓ l = none) : exclusiveReceipts belief ℓ l = 0 := by
  simp [exclusiveReceipts, hl]

theorem exclusiveReceipts_some (belief : Fin m → FiniteLaw (Fin n)) (ℓ : LocalList m)
    (l : Fin m) (b : ℝ) (hl : ℓ l = some b) :
    exclusiveReceipts belief ℓ l = b * (belief l).prob (fun r => r.val = 0) := by
  simp [exclusiveReceipts, hl]

noncomputable def noOtherProb (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) : ℝ :=
  (posteriorCountBelief Γ B j ℓ i).prob (fun r => r.val = 0)

theorem noOtherProb_nonneg (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) : 0 ≤ noOtherProb Γ B j ℓ i :=
  FiniteLaw.prob_nonneg _ _

theorem noOtherProb_eq_integral (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    noOtherProb Γ B j ℓ i = ∫ ω, (if (otherInclusionCount Γ j i ω).val = 0 then (1 : ℝ) else 0)
      ∂posteriorBackground Γ B j ℓ := by
  rw [noOtherProb, FiniteLaw.prob_eq_expect, posteriorCountBelief, FiniteLaw.expect_ofMeasure]

theorem measurable_noOtherProb (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (i : Fin m) : Measurable (fun ℓ => noOtherProb Γ B j ℓ i) := by
  let f : Background m n Seed → ℝ := fun ω =>
    if (otherInclusionCount Γ j i ω).val = 0 then (1 : ℝ) else 0
  have hf : Measurable f :=
    (measurable_of_countable (fun r : Fin n => if r.val = 0 then (1 : ℝ) else 0)).comp
      (measurable_otherInclusionCount Γ j i)
  have hb : ∀ ω, ‖f ω‖ ≤ 1 := by
    intro ω
    dsimp only [f]
    split <;> simp
  have he (ℓ : LocalList m) : noOtherProb Γ B j ℓ i =
      ∫ d, ∫ s, f (d, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw) ∂B.posterior j ℓ := by
    rw [noOtherProb_eq_integral]
    exact integral_prod _
      (Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hb))
  have hm : Measurable (fun d : UserProfile m n =>
      ∫ s, f (d, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmk : Measurable (fun z : LocalList m × UserProfile m n =>
      ∫ s, f (z.2, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) :=
    hm.comp measurable_snd
  simp_rw [he]
  exact hmk.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem ae_noOtherProb_pos (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (i : Fin m) :
    ∀ᵐ ω ∂backgroundLaw Γ, (otherInclusionCount Γ j i ω).val = 0 →
      0 < noOtherProb Γ B j (observe (drawsRealization ω.1) j) i := by
  classical
  let N : Set (LocalList m) := {ℓ | noOtherProb Γ B j ℓ i = 0}
  have hN : MeasurableSet N :=
    measurableSet_eq_fun (measurable_noOtherProb Γ B j i) measurable_const
  let f : LocalList m × Seed → ℝ := fun z => if z.1 ∈ N then 1 else 0
  let g : (LocalList m × UserProfile m n) × (Fin n → Seed) → ℝ := fun z =>
    if (otherInclusionCount Γ j i (z.1.2, z.2)).val = 0 then 1 else 0
  have hf : Measurable f := Measurable.ite (measurable_fst hN) measurable_const measurable_const
  have hg : Measurable g :=
    (measurable_of_countable (fun r : Fin n => if r.val = 0 then (1 : ℝ) else 0)).comp
      ((measurable_otherInclusionCount Γ j i).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hBf : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    dsimp only [f]
    split <;> simp
  have hBg : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    dsimp only [g]
    split <;> simp
  have heq := ConditionalAveraging.integral_observation_private_seed
    (userProfileLaw Γ) (observedListLaw Γ j) Γ.seedLaw
    (fun d => observe (drawsRealization d) j) (measurable_observe_draws j)
    (B.posterior j) (B.on_path j) j f g hf hg 1 1 hBf hBg
    (fun _ d s u => by dsimp only [g]; rw [otherInclusionCount_update_seed])
  have hrhs : (∫ ℓ, (∫ u, f (ℓ, u) ∂Γ.seedLaw) *
      (∫ z : UserProfile m n × (Fin n → Seed), g ((ℓ, z.1), z.2)
        ∂(B.posterior j ℓ).prod (Measure.pi (fun _ : Fin n => Γ.seedLaw)))
        ∂observedListLaw Γ j) = 0 := by
    apply integral_eq_zero_of_ae
    apply Eventually.of_forall
    intro ℓ
    by_cases hℓ : ℓ ∈ N
    · have hgℓ : (∫ z : UserProfile m n × (Fin n → Seed), g ((ℓ, z.1), z.2)
          ∂(B.posterior j ℓ).prod (Measure.pi (fun _ : Fin n => Γ.seedLaw))) = 0 := by
        have h0 : noOtherProb Γ B j ℓ i = 0 := hℓ
        rw [noOtherProb_eq_integral] at h0
        exact h0
      simp only [hgℓ, mul_zero, Pi.zero_apply]
    · have hfℓ : (∫ u, f (ℓ, u) ∂Γ.seedLaw) = 0 := by
        simp only [f, hℓ, if_false, integral_zero]
      simp only [hfℓ, zero_mul, Pi.zero_apply]
  rw [hrhs] at heq
  let H : UserProfile m n × (Fin n → Seed) → ℝ := fun z =>
    f (observe (drawsRealization z.1) j, z.2 j) *
      g ((observe (drawsRealization z.1) j, z.1), z.2)
  have hH : Measurable H :=
    (hf.comp (((measurable_observe_draws j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd))).mul
      (hg.comp ((((measurable_observe_draws j).comp measurable_fst).prodMk
        measurable_fst).prodMk measurable_snd))
  have hH0 : ∀ z, 0 ≤ H z := by
    intro z
    dsimp only [H, f, g]
    split <;> split <;> norm_num
  have hHi : Integrable H ((userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)) := by
    apply Integrable.of_bound hH.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro z
    dsimp only [H, f, g]
    split <;> split <;> norm_num
  have hae := (integral_eq_zero_iff_of_nonneg hH0 hHi).mp heq
  change ∀ᵐ ω ∂(userProfileLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw), _
  filter_upwards [hae] with ω hω hcount
  have hnot : observe (drawsRealization ω.1) j ∉ N := by
    intro hmem
    simp only [H, f, g, hmem, if_true, hcount, one_mul, Pi.zero_apply] at hω
    exact one_ne_zero hω
  exact lt_of_le_of_ne (noOtherProb_nonneg Γ B j _ i) (Ne.symm hnot)

def rerouteDraw (π : Equiv.Perm (Fin n)) (x : UserDraw n) : UserDraw n := (x.1, x.2 * π)

theorem measurePreserving_mul_right_permLaw (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun τ : Equiv.Perm (Fin n) => τ * π) (permLaw n) (permLaw n) := by
  classical
  refine ⟨measurable_of_countable _, ?_⟩
  ext S hS
  rw [Measure.map_apply (measurable_of_countable _) hS]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (permLaw n).real {τ | τ * π ∈ S} = (permLaw n).real {τ | τ ∈ S}
  rw [permLaw_real_filter, permLaw_real_filter]
  have hcard : (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => τ * π ∈ S)).card =
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => τ ∈ S)).card := by
    apply Finset.card_bij (fun τ _ => τ * π)
    · intro τ hτ
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hτ
    · intro τ _ υ _ he
      exact mul_right_cancel he
    · intro υ hυ
      refine ⟨υ * π⁻¹, ?_, by simp⟩
      simpa using hυ
  rw [hcard]

theorem measurePreserving_rerouteDraw (Γ : FiniteGame m n c Seed) (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (rerouteDraw π) (userLaw Γ) (userLaw Γ) :=
  (MeasurePreserving.id (Γ.F ⊗ₘ Γ.σ)).prod (measurePreserving_mul_right_permLaw π)

def rerouteUser (i : Fin m) (π : Equiv.Perm (Fin n)) (d : UserProfile m n) :
    UserProfile m n :=
  fun l => (if l = i then rerouteDraw π else id) (d l)

theorem measurePreserving_rerouteUser (Γ : FiniteGame m n c Seed) (i : Fin m)
    (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (rerouteUser i π) (userProfileLaw Γ) (userProfileLaw Γ) := by
  unfold userProfileLaw rerouteUser
  refine measurePreserving_pi (fun _ => userLaw Γ) (fun _ => userLaw Γ)
    (f := fun l => if l = i then rerouteDraw π else id) (fun l => ?_)
  by_cases h : l = i
  · simp only [h, if_true]
    exact measurePreserving_rerouteDraw Γ π
  · simp only [h, if_false]
    exact MeasurePreserving.id _

omit [MeasurableSpace Seed] in
theorem observe_rerouteUser_fixed (d : UserProfile m n) (i : Fin m)
    (π : Equiv.Perm (Fin n)) (l : Fin n) (hl : π l = l) :
    observe (drawsRealization (rerouteUser i π d)) l = observe (drawsRealization d) l := by
  classical
  funext u
  by_cases hu : u = i
  · subst hu
    simp [observe, drawsRealization, rerouteUser, rerouteDraw, mem_firstK,
      Equiv.Perm.mul_apply, hl]
  · simp [observe, drawsRealization, rerouteUser, hu]

omit [MeasurableSpace Seed] in
theorem observe_rerouteUser_self_entry (d : UserProfile m n) (i : Fin m)
    (π : Equiv.Perm (Fin n)) (l : Fin n) :
    observe (drawsRealization (rerouteUser i π d)) l i =
      if π l ∈ firstK (d i).2 (d i).1.2.routeCount then some (d i).1.2.bid else none := by
  classical
  simp [observe, drawsRealization, rerouteUser, rerouteDraw, mem_firstK, Equiv.Perm.mul_apply]

omit [MeasurableSpace Seed] in
theorem observe_rerouteUser_other_entry (d : UserProfile m n) (i : Fin m)
    (π : Equiv.Perm (Fin n)) (l : Fin n) (u : Fin m) (hu : u ≠ i) :
    observe (drawsRealization (rerouteUser i π d)) l u = observe (drawsRealization d) l u := by
  classical
  simp [observe, drawsRealization, rerouteUser, hu]

def singletonList (i : Fin m) (b : ℝ) : LocalList m := fun l => if l = i then some b else none

omit [MeasurableSpace Seed] in

theorem observe_reroute_singleton (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ l, firstK (d l).2 (d l).1.2.routeCount = R) (r j : Fin n)
    (hr : r ∈ R) (hj : j ∉ R) (i : Fin m) :
    observe (drawsRealization (rerouteUser i (Equiv.swap r j) d)) j =
      singletonList i (d i).1.2.bid := by
  classical
  funext u
  by_cases hu : u = i
  · rw [hu, observe_rerouteUser_self_entry, Equiv.swap_apply_right, hd i]
    simp [singletonList, hr]
  · rw [observe_rerouteUser_other_entry _ _ _ _ _ hu]
    simp [singletonList, hu, observe, drawsRealization, hd u, hj]

theorem notMem_allocation_of_playedCount_zero (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ω : Background m n Seed) (h : playedCount Γ i ω = 0) (l : Fin n) :
    i ∉ allocation (drawsRealization ω.1) Γ.policy ω.2 l := by
  classical
  intro hin
  have hcard : 0 < (accepted (drawsRealization ω.1) Γ.policy ω.2 i).card :=
    Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩⟩
  have hz : (accepted (drawsRealization ω.1) Γ.policy ω.2 i).card = 0 := congrArg Fin.val h
  omega

theorem notMem_allocation_of_none (Γ : FiniteGame m n c Seed) (x : Realization m n)
    (s : Fin n → Seed) (l : Fin n) (i : Fin m) (h : observe x l i = none) :
    i ∉ allocation x Γ.policy s l :=
  fun hin => (Γ.policy l (observe x l) (s l)).property.2 i hin h

theorem otherInclusionCount_reroute_zero (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (R : Finset (Fin n))
    (hd : ∀ l, firstK (d l).2 (d l).1.2.routeCount = R) (r j : Fin n) (hj : j ∉ R)
    (i : Fin m) (s : Fin n → Seed) (hfail : playedCount Γ i (d, s) = 0) :
    (otherInclusionCount Γ j i (rerouteUser i (Equiv.swap r j) d, s)).val = 0 := by
  classical
  rw [otherInclusionCount_eq_sum]
  apply Finset.sum_eq_zero
  intro l hl
  have hlj : l ≠ j := Finset.ne_of_mem_erase hl
  have hnot : i ∉ allocation
      (drawsRealization (rerouteUser i (Equiv.swap r j) d)) Γ.policy s l := by
    by_cases hlr : l = r
    · subst hlr
      apply notMem_allocation_of_none
      rw [observe_rerouteUser_self_entry, Equiv.swap_apply_left, hd i]
      simp [hj]
    · have hfix : Equiv.swap r j l = l := Equiv.swap_apply_of_ne_of_ne hlr hlj
      change i ∉ (Γ.policy l
        (observe (drawsRealization (rerouteUser i (Equiv.swap r j) d)) l) (s l)).val
      rw [observe_rerouteUser_fixed d i _ l hfix]
      exact notMem_allocation_of_playedCount_zero Γ i (d, s) hfail l
  simp only [if_neg hnot]

theorem exclusive_singleton_accepts (c : ℕ) (hc : 0 < c) (belief : Fin m → FiniteLaw (Fin n))
    (i : Fin m) (b : ℝ) (hb : 0 < b) (hpos : 0 < (belief i).prob (fun r => r.val = 0))
    (S : Finset (Fin m)) (hS : Finite.Optimal c (exclusiveReceipts belief (singletonList i b)) S) :
    i ∈ S := by
  classical
  have hri : 0 < exclusiveReceipts belief (singletonList i b) i := by
    rw [exclusiveReceipts_some _ _ i b (by simp [singletonList])]
    exact mul_pos hb hpos
  apply Finite.included_of_few_competitors c _ _ hS i hri
  have hempty : (Finset.univ.filter fun l => l ≠ i ∧
      exclusiveReceipts belief (singletonList i b) i ≤
        exclusiveReceipts belief (singletonList i b) l) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro l _ h
    have hz := exclusiveReceipts_none belief (singletonList i b) l
      (by simp [singletonList, h.1])
    linarith [h.2]
  simpa only [hempty, Finset.card_empty] using hc

theorem ae_common_route_singleton_accepts (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (hcm : c < m) (B : PosteriorSystem Γ) (hB : ExclusivePosteriorOptimalOnPath Γ B)
    (hsym : SymmetricProposersOnPath Γ) (R : Finset (Fin n)) (r j : Fin n)
    (hr : r ∈ R) (hj : j ∉ R) :
    ∀ᵐ d ∂userProfileLaw Γ, (∀ l, firstK (d l).2 (d l).1.2.routeCount = R) →
      (∀ l, 0 < (d l).1.2.bid) →
      ∃ i : Fin m, (∃ E : Set (Fin n → Seed),
          (Measure.pi fun _ : Fin n => Γ.seedLaw) E ≠ 0 ∧
            ∀ s ∈ E, playedCount Γ i (d, s) = 0) ∧
        ∀ᵐ u ∂Γ.seedLaw, i ∈ (Γ.policy j (singletonList i (d i).1.2.bid) u).val := by
  classical
  have hdrawsym : ∀ᵐ d ∂userProfileLaw Γ, ∀ l : Fin n,
      SymmetricAtList Γ (observe (drawsRealization d) l)
        (seedLottery Γ l (observe (drawsRealization d) l)) :=
    ae_all_iff.mpr fun l => ae_of_ae_map (measurable_observe_draws l).aemeasurable (hsym l)
  have hbay : ∀ᵐ d ∂userProfileLaw Γ, ∀ i : Fin m,
      ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
        (otherInclusionCount Γ j i (rerouteUser i (Equiv.swap r j) d, s)).val = 0 →
          0 < noOtherProb Γ B j
            (observe (drawsRealization (rerouteUser i (Equiv.swap r j) d)) j) i := by
    apply ae_all_iff.mpr
    intro i
    have h := Measure.ae_ae_of_ae_prod (ae_noOtherProb_pos Γ B j i)
    exact (measurePreserving_rerouteUser Γ i (Equiv.swap r j)).quasiMeasurePreserving.ae h
  have hopt : ∀ᵐ d ∂userProfileLaw Γ, ∀ i : Fin m,
      ∀ᵐ u ∂Γ.seedLaw,
        Finite.Optimal c (exclusiveReceipts (posteriorCountBelief Γ B j
          (observe (drawsRealization (rerouteUser i (Equiv.swap r j) d)) j))
          (observe (drawsRealization (rerouteUser i (Equiv.swap r j) d)) j))
          (Γ.policy j (observe (drawsRealization
            (rerouteUser i (Equiv.swap r j) d)) j) u).val := by
    apply ae_all_iff.mpr
    intro i
    have h := ae_of_ae_map (measurable_observe_draws j).aemeasurable (hB j)
    exact (measurePreserving_rerouteUser Γ i (Equiv.swap r j)).quasiMeasurePreserving.ae h
  filter_upwards [hdrawsym, hbay, hopt] with d hds hbd hod hR hbpos
  obtain ⟨i, E, hE, hfail⟩ := exists_common_route_failure Γ hcm d R hR (fun l _ => hds l)
  refine ⟨i, ⟨E, hE, hfail⟩, ?_⟩
  obtain ⟨s, hsE, hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE
    (ae_restrict_of_ae (hbd i))
  have hpos := hs (otherInclusionCount_reroute_zero Γ d R hR r j hj i s (hfail s hsE))
  rw [observe_reroute_singleton d R hR r j hr hj i] at hpos
  have ho := hod i
  rw [observe_reroute_singleton d R hR r j hr hj i] at ho
  filter_upwards [ho] with u hu
  exact exclusive_singleton_accepts c hc _ i _ (hbpos i) hpos _ hu

end FCAppendix.Bayes
