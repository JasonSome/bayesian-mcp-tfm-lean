import FCAppendix.Game.Bayesian

noncomputable section
namespace FCAppendix.Affine.UniformFinite.LocalInformation
open Game Set MeasureTheory
open scoped BigOperators

def bidPayoff (η v b success duplicate : ℝ) : ℝ :=
  (v-b)*success-η*b*duplicate

section NativeBayesian
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
theorem observe_deviations_same_local (i : Fin m) (a a' : JointAction n)
    (ω : Bayes.Sample m n Seed) (j : Fin n) (hbid : a.bid = a'.bid)
    (hmem : j ∈ firstK ω.2 a.routeCount ↔ j ∈ firstK ω.2 a'.routeCount) :
    observe (Bayes.deviated i a ω) j = observe (Bayes.deviated i a' ω) j := by
  classical
  funext l
  unfold observe
  by_cases hl : l = i
  · subst l
    rw [Bayes.deviated_recipients_self, Bayes.deviated_recipients_self,
      Bayes.deviated_bid_self, Bayes.deviated_bid_self]
    simp only [hbid, hmem]
  · rw [Bayes.deviated_recipients_other i l hl,
      Bayes.deviated_recipients_other i l hl,
      Bayes.deviated_bid_other i l hl, Bayes.deviated_bid_other i l hl]

lemma allocation_deviations_same_local (Γ : Bayes.FiniteGame m n c Seed)
    (i : Fin m) (a a' : JointAction n) (ω : Bayes.Sample m n Seed)
    (j : Fin n) (hbid : a.bid = a'.bid)
    (hmem : j ∈ firstK ω.2 a.routeCount ↔ j ∈ firstK ω.2 a'.routeCount) :
    allocation (Bayes.deviated i a ω) Γ.policy ω.1.2 j =
      allocation (Bayes.deviated i a' ω) Γ.policy ω.1.2 j := by
  unfold allocation
  rw [observe_deviations_same_local i a a' ω j hbid hmem]

end NativeBayesian

section DeterministicRecipients
variable {m n c : ℕ} {Seed : Type*}

lemma observe_recipient_interventions (x : Realization m n) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (R T : Finset (Fin n)) (j : Fin n)
    (hmem : j ∈ R ↔ j ∈ T) :
    observe (deviate x i b hb R) j = observe (deviate x i b hb T) j := by
  classical
  funext l
  by_cases hl : l = i
  · subst l
    simp [observe, deviate, hmem]
  · simp [observe, deviate, hl]

lemma allocation_recipient_interventions (x : Realization m n) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (R T : Finset (Fin n)) (j : Fin n)
    (hmem : j ∈ R ↔ j ∈ T) :
    allocation (deviate x i b hb R) policy seed j =
      allocation (deviate x i b hb T) policy seed j := by
  unfold allocation
  rw [observe_recipient_interventions x i b hb R T j hmem]

lemma intervention_nonrecipient_rejects (x : Realization m n) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (R : Finset (Fin n)) (j : Fin n) (hj : j ∉ R) :
    i ∉ allocation (deviate x i b hb R) policy seed j := by
  classical
  intro hi
  have haccepted : j ∈ accepted (deviate x i b hb R) policy seed i := by
    simpa [accepted] using hi
  have hrec := accepted_subset_recipients (deviate x i b hb R) policy seed i haccepted
  have he : (deviate x i b hb R).recipients i = R := by simp [deviate]
  rw [he] at hrec
  exact hj hrec

lemma singleton_acceptance_at_recipient (x : Realization m n) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin n → LocalPolicy m c Seed)
    (seed : Fin n → Seed) (j : Fin n) :
    allocation (deviate x i b hb {j}) policy seed j =
      allocation (deviate x i b hb Finset.univ) policy seed j := by
  apply allocation_recipient_interventions
  simp

end DeterministicRecipients

section TwoProposers
variable {m c : ℕ} {Seed : Type*}

def nativeHit (x : Realization m 2) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) (i : Fin m) (j : Fin 2) : ℝ :=
  if i ∈ allocation x policy seed j then 1 else 0

def nativeSuccess (x : Realization m 2) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) (i : Fin m) : ℝ :=
  nativeHit x policy seed i 0 + nativeHit x policy seed i 1 -
    nativeHit x policy seed i 0 * nativeHit x policy seed i 1

def nativeDuplicate (x : Realization m 2) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) (i : Fin m) : ℝ :=
  nativeHit x policy seed i 0 * nativeHit x policy seed i 1

lemma nativeSuccess_is_actual_count (x : Realization m 2)
    (policy : Fin 2 → LocalPolicy m c Seed) (seed : Fin 2 → Seed) (i : Fin m) :
    nativeSuccess x policy seed i =
      if 0 < inclusionCount x policy seed i then 1 else 0 := by
  classical
  rw [inclusionCount_eq_sum]
  rw [Fin.sum_univ_two]
  by_cases h0 : i ∈ allocation x policy seed 0 <;>
    by_cases h1 : i ∈ allocation x policy seed 1 <;>
      simp [nativeSuccess, nativeHit, h0, h1]

lemma nativeDuplicate_is_actual_count (x : Realization m 2)
    (policy : Fin 2 → LocalPolicy m c Seed) (seed : Fin 2 → Seed) (i : Fin m) :
    nativeDuplicate x policy seed i =
      if inclusionCount x policy seed i = 2 then 1 else 0 := by
  classical
  rw [inclusionCount_eq_sum]
  rw [Fin.sum_univ_two]
  by_cases h0 : i ∈ allocation x policy seed 0 <;>
    by_cases h1 : i ∈ allocation x policy seed 1 <;>
      simp [nativeDuplicate, nativeHit, h0, h1]

lemma native_singleton_success (x : Realization m 2) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) (j : Fin 2) :
    nativeSuccess (deviate x i b hb {j}) policy seed i =
      nativeHit (deviate x i b hb Finset.univ) policy seed i j := by
  classical
  have hsame := singleton_acceptance_at_recipient x i b hb policy seed j
  fin_cases j
  · have hnone := intervention_nonrecipient_rejects x i b hb policy seed {0} 1 (by simp)
    change allocation (deviate x i b hb {0}) policy seed 0 =
      allocation (deviate x i b hb Finset.univ) policy seed 0 at hsame
    simp [nativeSuccess, nativeHit, hnone, hsame]
  · have hnone := intervention_nonrecipient_rejects x i b hb policy seed {1} 0 (by simp)
    change allocation (deviate x i b hb {1}) policy seed 1 =
      allocation (deviate x i b hb Finset.univ) policy seed 1 at hsame
    simp [nativeSuccess, nativeHit, hnone, hsame]

lemma native_singleton_duplicate_zero (x : Realization m 2) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) (j : Fin 2) :
    nativeDuplicate (deviate x i b hb {j}) policy seed i = 0 := by
  classical
  fin_cases j
  · have hnone := intervention_nonrecipient_rejects x i b hb policy seed {0} 1 (by simp)
    simp [nativeDuplicate, nativeHit, hnone]
  · have hnone := intervention_nonrecipient_rejects x i b hb policy seed {1} 0 (by simp)
    simp [nativeDuplicate, nativeHit, hnone]

theorem native_fair_singleton_success (x : Realization m 2) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) :
    (nativeSuccess (deviate x i b hb {0}) policy seed i +
      nativeSuccess (deviate x i b hb {1}) policy seed i)/2 =
    (nativeSuccess (deviate x i b hb Finset.univ) policy seed i +
      nativeDuplicate (deviate x i b hb Finset.univ) policy seed i)/2 := by
  rw [native_singleton_success, native_singleton_success]
  unfold nativeSuccess nativeDuplicate
  ring

theorem native_broadcast_payoff_identity (x : Realization m 2) (i : Fin m)
    (η v b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) :
    let xb := deviate x i b hb Finset.univ
    let q := (nativeSuccess (deviate x i b hb {0}) policy seed i +
      nativeSuccess (deviate x i b hb {1}) policy seed i)/2
    bidPayoff η v b (nativeSuccess xb policy seed i) (nativeDuplicate xb policy seed i)
      -(v-b)*q = (v-b)*q-((v-b)+η*b)*nativeDuplicate xb policy seed i := by
  dsimp only
  rw [native_fair_singleton_success]
  unfold bidPayoff
  ring

theorem native_permutation_singleton_success (x : Realization m 2) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) :
    (∫ τ, nativeSuccess (deviate x i b hb (firstK τ 1)) policy seed i ∂permLaw 2) =
      (nativeSuccess (deviate x i b hb Finset.univ) policy seed i +
        nativeDuplicate (deviate x i b hb Finset.univ) policy seed i) / 2 := by
  classical
  let E : Set (Equiv.Perm (Fin 2)) := {τ | (0 : Fin 2) ∈ firstK τ 1}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  let h₀ := nativeHit (deviate x i b hb Finset.univ) policy seed i 0
  let h₁ := nativeHit (deviate x i b hb Finset.univ) policy seed i 1
  have he (τ : Equiv.Perm (Fin 2)) :
      nativeSuccess (deviate x i b hb (firstK τ 1)) policy seed i =
        h₁ + (h₀ - h₁) * (if τ ∈ E then (1 : ℝ) else 0) := by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (card_firstK τ 1 (by norm_num))
    simp only [E, hj, native_singleton_success]
    fin_cases j <;> simp [hj, h₀, h₁]
  have hI : MeasureTheory.Integrable (fun τ : Equiv.Perm (Fin 2) =>
      if τ ∈ E then (1 : ℝ) else 0) (permLaw 2) := by
    convert! (MeasureTheory.integrable_const (1 : ℝ) (μ := permLaw 2)).indicator hE using 1
    funext τ
    simp only [Set.indicator_apply]
  have hhalf : (∫ τ : Equiv.Perm (Fin 2),
      (if τ ∈ E then (1 : ℝ) else 0) ∂permLaw 2) = (1 : ℝ) / 2 := by
    have hi : (∫ τ : Equiv.Perm (Fin 2),
        (if τ ∈ E then (1 : ℝ) else 0) ∂permLaw 2) = (permLaw 2).real E := by
      simpa only [Set.indicator, Pi.one_apply] using
        MeasureTheory.integral_indicator_one (μ := permLaw 2) hE
    rw [hi]
    simpa only [E, Nat.cast_one, Nat.cast_ofNat] using
      permLaw_mem_firstK 2 1 (by norm_num) (by norm_num) 0
  simp_rw [he]
  rw [MeasureTheory.integral_add (MeasureTheory.integrable_const h₁)
      (hI.const_mul (h₀ - h₁)), MeasureTheory.integral_const_mul, hhalf,
    MeasureTheory.integral_const, MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
  unfold h₀ h₁ nativeSuccess nativeDuplicate
  ring

theorem native_permutation_singleton_duplicate_zero (x : Realization m 2) (i : Fin m)
    (b : ℝ) (hb : 0 ≤ b) (policy : Fin 2 → LocalPolicy m c Seed)
    (seed : Fin 2 → Seed) :
    (∫ τ, nativeDuplicate (deviate x i b hb (firstK τ 1)) policy seed i ∂permLaw 2) = 0 := by
  have he (τ : Equiv.Perm (Fin 2)) :
      nativeDuplicate (deviate x i b hb (firstK τ 1)) policy seed i = 0 := by
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (card_firstK τ 1 (by norm_num))
    rw [hj]
    exact native_singleton_duplicate_zero x i b hb policy seed j
  simp_rw [he]
  simp

end TwoProposers
end FCAppendix.Affine.UniformFinite.LocalInformation
