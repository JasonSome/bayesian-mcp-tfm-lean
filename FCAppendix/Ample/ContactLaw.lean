import FCAppendix.Ample.CommonRateModel
import FCAppendix.Probability.SimultaneousCongestionUniform

namespace FCAppendix.Ample

open Finset Filter Topology Real
open scoped BigOperators

noncomputable def contactLaw (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights) :
    FiniteLaw (Finset (Fin n)) where
  mass := contactWeight n lawWeights
  nonneg := contactWeight_nonneg hlam
  total := sum_contactWeight n lawWeights

@[simp] theorem contactLaw_mass (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (T : Finset (Fin n)) : (contactLaw n lawWeights hlam).mass T = contactWeight n lawWeights T := rfl

theorem contactWeight_perm (n : ℕ) (lawWeights : ℕ → ℝ) (e : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) : contactWeight n lawWeights (e.finsetCongr T) = contactWeight n lawWeights T := by
  simp only [contactWeight, Equiv.finsetCongr_apply, Finset.card_map, Finset.map_eq_empty]

theorem contactLaw_swapInvariant (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) : SimultaneousCongestion.SwapInvariant (contactLaw n lawWeights hlam) K := by
  intro s _ t _ T
  exact contactWeight_perm n lawWeights (Equiv.swap s t) T

theorem contacts_eq_includers {n N : ℕ} (T : Fin N → Finset (Fin n)) (s : Fin n) :
    contacts T s = CommonList.includers s T := by
  simp only [contacts, CommonList.includers, Finset.card_filter]

@[simp] theorem contactLaw_congestionProb (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) (N c : ℕ) :
    SimultaneousCongestion.congestionProb (contactLaw n lawWeights hlam) K N c =
      congestProbAt n N c lawWeights K := by
  classical
  unfold SimultaneousCongestion.congestionProb FiniteLaw.prob FiniteLaw.expect
  simp only [CommonList.iid, contactLaw, SimultaneousCongestion.Congested,
    congestProbAt, contacts_eq_includers]
  apply Finset.sum_congr rfl
  intro T _
  by_cases h : ∀ j ∈ K, c ≤ CommonList.includers j T <;> simp [h]

theorem contactLaw_Z (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) (t : ℝ) :
    FiniteCramer.Z (contactLaw n lawWeights hlam) (SimultaneousCongestion.count K) t =
      rivalMGF n K.card lawWeights t := by
  unfold FiniteCramer.Z FiniteLaw.expect
  change (∑ T : Finset (Fin n), contactWeight n lawWeights T * exp (t * ((T ∩ K).card : ℝ))) = _
  calc
    _ = ∑ T : Finset (Fin n), contactWeight n lawWeights T * exp t ^ (T ∩ K).card := by
      apply Finset.sum_congr rfl
      intro T _
      rw [mul_comm t ((T ∩ K).card : ℝ), Real.exp_nat_mul]
    _ = _ := sum_contactWeight_exp n lawWeights K t

@[simp] theorem contactLaw_cgf (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) (t : ℝ) :
    FiniteCramer.cgf (contactLaw n lawWeights hlam) (SimultaneousCongestion.count K) t =
      log (rivalMGF n K.card lawWeights t) := by
  rw [FiniteCramer.cgf, contactLaw_Z]

theorem contactLaw_expect_card_fun (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (f : ℕ → ℝ) :
    (contactLaw n lawWeights hlam).expect (fun T => f T.card) =
      (1 - ∑ j ∈ Icc 1 n, lawWeights j) * f 0 + ∑ j ∈ Icc 1 n, lawWeights j * f j := by
  classical
  let g : ℕ → ℝ := fun j =>
    (if j = 0 then 1 - ∑ l ∈ Icc 1 n, lawWeights l else lawWeights j / (n.choose j : ℝ)) * f j
  have he : ∀ T : Finset (Fin n), contactWeight n lawWeights T * f T.card = g T.card := by
    intro T
    simp only [g, contactWeight, Finset.card_eq_zero]
  unfold FiniteLaw.expect
  change (∑ T : Finset (Fin n), contactWeight n lawWeights T * f T.card) = _
  rw [Finset.sum_congr rfl (fun T _ => he T), sum_finset_card_eq, Finset.sum_range_succ']
  have hs : ∑ j ∈ range n, (n.choose (j + 1) : ℝ) * g (j + 1) =
      ∑ j ∈ Icc 1 n, lawWeights j * f j := by
    rw [sum_Icc_one_eq_sum_range (fun j => lawWeights j * f j) n]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j + 1 ≤ n := by simpa using Finset.mem_range.mp hj
    have hC : (n.choose (j + 1) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
    simp only [g, Nat.succ_ne_zero, if_false]
    field_simp
  rw [hs]
  simp [g, add_comm]

theorem contactLaw_expect_card (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights) :
    (contactLaw n lawWeights hlam).expect (fun T => (T.card : ℝ)) =
      ∑ j ∈ Icc 1 n, lawWeights j * j := by
  rw [contactLaw_expect_card_fun]
  simp

noncomputable def contactMarginal (n : ℕ) (lawWeights : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Icc 1 n, lawWeights j * j) / n

theorem contactLaw_marginal (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights) (s : Fin n) :
    Proposer.marginal (contactLaw n lawWeights hlam) s = contactMarginal n lawWeights := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt s.isLt
  have hall (t : Fin n) : Proposer.marginal (contactLaw n lawWeights hlam) t =
      Proposer.marginal (contactLaw n lawWeights hlam) s :=
    SimultaneousCongestion.marginal_eq_of_swap (fun T => contactWeight_perm n lawWeights (Equiv.swap t s) T)
  have hh := SimultaneousCongestion.sum_marginal_eq (contactLaw n lawWeights hlam) (univ : Finset (Fin n))
  have hsum : (∑ t : Fin n, Proposer.marginal (contactLaw n lawWeights hlam) t) =
      ∑ _t : Fin n, Proposer.marginal (contactLaw n lawWeights hlam) s :=
    Finset.sum_congr rfl (fun t _ => hall t)
  rw [hsum] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    SimultaneousCongestion.selected, Finset.inter_univ] at hh
  rw [contactLaw_expect_card] at hh
  unfold contactMarginal
  rw [← hh]
  field_simp [hn.ne']

theorem contactLaw_expect_selected (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) :
    (contactLaw n lawWeights hlam).expect (SimultaneousCongestion.count K) =
      (K.card : ℝ) * contactMarginal n lawWeights := by
  have h := SimultaneousCongestion.sum_marginal_eq (contactLaw n lawWeights hlam) K
  simp only [contactLaw_marginal, Finset.sum_const, nsmul_eq_mul] at h
  exact h.symm

theorem contactLaw_tilted_marginal (n : ℕ) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (K : Finset (Fin n)) (t : ℝ) {s : Fin n} (hs : s ∈ K) :
    Proposer.marginal
      (SimultaneousCongestion.selTilt (contactLaw n lawWeights hlam) K t) s =
    FiniteCramer.mean (contactLaw n lawWeights hlam) (SimultaneousCongestion.count K) t / K.card :=
  SimultaneousCongestion.marginal_selTilt (contactLaw_swapInvariant n lawWeights hlam K) t hs

theorem selected_inter (n j k : ℕ) :
    selected n j ∩ selected n k = selected n (min j k) := by
  ext s
  simp only [selected, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    lt_min_iff]

theorem contactLaw_interior {n k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n)
    {lawWeights : ℕ → ℝ} (hlam : ValidLaw n lawWeights) {ρ : ℝ}
    (hslack : contactMarginal n lawWeights < ρ)
    (htop : ∃ j ∈ Icc 1 n, 0 < lawWeights j ∧ (k : ℝ) * ρ < (min k j : ℕ)) :
    FiniteCramer.Interior (contactLaw n lawWeights hlam)
      (SimultaneousCongestion.count (selected n k)) (k * ρ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  refine ⟨?_, ?_⟩
  · rw [contactLaw_expect_selected, card_selected hk]
    exact mul_lt_mul_of_pos_left hslack hkpos
  · obtain ⟨j, hj, hmass, hcount⟩ := htop
    have hj0 : 0 < j := (Finset.mem_Icc.mp hj).1
    have hjn : j ≤ n := (Finset.mem_Icc.mp hj).2
    have hT : selected n j ≠ ∅ := by
      intro hz
      have hc := card_selected hjn
      rw [hz, Finset.card_empty] at hc
      omega
    refine ⟨selected n j, ?_, ?_⟩
    · rw [contactLaw_mass, contactWeight_of_ne lawWeights hT, card_selected hjn]
      exact div_pos hmass (by exact_mod_cast Nat.choose_pos hjn)
    · change (k : ℝ) * ρ < ((selected n j ∩ selected n k).card : ℝ)
      rw [selected_inter, card_selected ((min_le_left j k).trans hjn), min_comm]
      exact hcount

theorem contactLaw_rate {n k : ℕ} (hk : k ≤ n) (lawWeights : ℕ → ℝ) (hlam : ValidLaw n lawWeights)
    (ρ : ℝ) :
    FiniteCramer.rate (contactLaw n lawWeights hlam)
      (SimultaneousCongestion.count (selected n k)) (k * ρ) = rivalRate n ρ k lawWeights := by
  unfold FiniteCramer.rate FiniteCramer.objective rivalRate rivalObjective
  simp only [contactLaw_cgf, card_selected hk]

theorem contactLaw_mass_tendsto {A : Type*} {l : Filter A} {n : ℕ}
    {lama : A → ℕ → ℝ} {lawWeights : ℕ → ℝ}
    (hlama : ∀ a, ValidLaw n (lama a)) (hlam : ValidLaw n lawWeights)
    (hconv : ∀ j ∈ Icc 1 n, Tendsto (fun a => lama a j) l (𝓝 (lawWeights j)))
    (T : Finset (Fin n)) :
    Tendsto (fun a => (contactLaw n (lama a) (hlama a)).mass T) l
      (𝓝 ((contactLaw n lawWeights hlam).mass T)) := by
  by_cases hT : T = ∅
  · simp only [contactLaw_mass, hT, contactWeight_empty]
    exact tendsto_const_nhds.sub (tendsto_finsetSum _ hconv)
  · simp only [contactLaw_mass, contactWeight_of_ne _ hT]
    exact (hconv T.card (card_mem_Icc_of_ne hT)).div_const _

end FCAppendix.Ample
