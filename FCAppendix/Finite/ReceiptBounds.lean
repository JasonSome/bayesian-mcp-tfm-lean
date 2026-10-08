import FCAppendix.Finite.NoOverbid

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measure_visible_eq (Γ : FiniteGame m n c Seed) (j l : Fin n)
    (B : Set ℝ) (hB : MeasurableSet B) :
    userLaw Γ {d | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ B} =
      userLaw Γ {d | l ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ B} := by
  rw [userLaw, Measure.prod_apply (measurableSet_reach j hB),
    Measure.prod_apply (measurableSet_reach l hB)]
  apply lintegral_congr
  intro x
  change permLaw n {τ | j ∈ firstK τ x.2.routeCount ∧ x.2.bid ∈ B} =
    permLaw n {τ | l ∈ firstK τ x.2.routeCount ∧ x.2.bid ∈ B}
  by_cases hx : x.2.bid ∈ B
  · simp only [hx, and_true]
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    exact (permLaw_mem_firstK n x.2.routeCount (Nat.zero_lt_of_lt j.isLt)
      x.2.routeCount_le j).trans
      (permLaw_mem_firstK n x.2.routeCount (Nat.zero_lt_of_lt j.isLt)
        x.2.routeCount_le l).symm
  · simp [hx]

theorem alphaGt_eq (Γ : FiniteGame m n c Seed) (j l : Fin n) (b : ℝ) :
    alphaGt Γ j b = alphaGt Γ l b :=
  congrArg ENNReal.toReal (measure_visible_eq Γ j l (Set.Ioi b) measurableSet_Ioi)

def VisibleAtomless (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ (j : Fin n) (b : ℝ), userLaw Γ {d |
    j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = b} = 0

theorem alphaGe_eq_alphaGt (Γ : FiniteGame m n c Seed) (hΓ : VisibleAtomless Γ)
    (j : Fin n) (b : ℝ) : alphaGe Γ j b = alphaGt Γ j b := by
  apply measureReal_congr
  have hnull := measure_eq_zero_iff_ae_notMem.mp (hΓ j b)
  filter_upwards [hnull] with d hd
  apply propext
  change (j ∈ firstK d.2 d.1.2.routeCount ∧ b ≤ d.1.2.bid) ↔
    (j ∈ firstK d.2 d.1.2.routeCount ∧ b < d.1.2.bid)
  constructor
  · rintro ⟨hj, hb⟩
    exact ⟨hj, lt_of_le_of_ne hb (fun he => hd ⟨hj, he.symm⟩)⟩
  · exact fun h => ⟨h.1, h.2.le⟩

theorem meanAcceptProb_bounds (Γ : FiniteGame m n c Seed) (hΓ : IsEquilibrium Γ)
    (hatom : VisibleAtomless Γ) (j : Fin n) (i : Fin m)
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b : ℝ) (hb : 0 < b) :
    binomBelow (m - 1) (alphaGt Γ j (a * b)) c ≤ meanAcceptProb Γ i b ∧
      meanAcceptProb Γ i b ≤ binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hbounds (l : Fin n) := acceptProb_bounds Γ l (hΓ.proposers l) i a ha hA b hb
  have hlo (l : Fin n) : binomBelow (m - 1) (alphaGt Γ j (a * b)) c ≤
      acceptProb Γ i b l := by
    have h := (hbounds l).1
    rwa [alphaGe_eq_alphaGt Γ hatom l, alphaGt_eq Γ l j] at h
  have hhi (l : Fin n) : acceptProb Γ i b l ≤
      binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
    have h := (hbounds l).2
    rwa [alphaGt_eq Γ l j] at h
  have hsumlo := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hlo l)
  have hsumhi := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hhi l)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumlo hsumhi
  unfold meanAcceptProb
  constructor
  · have h := mul_le_mul_of_nonneg_left hsumlo (one_div_pos.mpr hn).le
    simpa only [← mul_assoc, one_div_mul_cancel hn.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hsumhi (one_div_pos.mpr hn).le
    simpa only [← mul_assoc, one_div_mul_cancel hn.ne', one_mul] using h

theorem balanced_receipt_bounds (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : IsEquilibrium Γ) (hatom : VisibleAtomless Γ)
    (j : Fin n) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (act : JointAction n) (hb : 0 < act.bid) (hk : 1 ≤ act.routeCount) :
    (binomBelow (m - 1) (alphaGt Γ j (a * act.bid)) c ≤ meanAcceptProb Γ i act.bid ∧
      meanAcceptProb Γ i act.bid ≤ binomBelow (m - 1) (alphaGt Γ j (act.bid / a)) c) ∧
    ((problem Γ i).outcome act).load = act.routeCount * meanAcceptProb Γ i act.bid ∧
    (meanAcceptProb Γ i act.bid ≤ ((problem Γ i).outcome act).success ∧
      ((problem Γ i).outcome act).success ≤ n * meanAcceptProb Γ i act.bid) ∧
    (∀ᵐ v ∂Γ.F, ∀ᵐ b ∂(Γ.σ v), 0 < b.routeCount → b.bid ≤ max (v - Γ.g) 0) ∧
    (∀ b : ℝ, 0 ≤ b → alphaGt Γ j b ≤ Γ.F.real (Set.Ioi (Γ.g + b))) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  exact ⟨meanAcceptProb_bounds Γ hΓ hatom j i a ha hA act.bid hb,
    load_eq_mean Γ hn i act,
    ⟨meanAcceptProb_le_success Γ hn i act hk, success_le_n_meanAcceptProb Γ hn i act⟩,
    ae_no_overbid Γ hm hc hΓ, alphaGt_le_value_tail Γ hm hc hΓ j⟩

end FCAppendix.Bayes
