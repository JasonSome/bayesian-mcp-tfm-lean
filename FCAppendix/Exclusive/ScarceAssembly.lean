import FCAppendix.Exclusive.LimitBounds
import FCAppendix.Exclusive.TariffInterim

namespace FCAppendix.Exclusive
open Filter Topology

theorem exists_scarce_parameters (n : ℕ) (hn : 2 ≤ n) {rho zeta : ℝ}
    (hrho : 0 < rho) (hbeta : (n : ℝ) * rho < 1) (hzeta : 0 < zeta) :
    ∃ h : ℝ, rho < h ∧ h < (n : ℝ) * rho ∧ h < 1 ∧
      (n : ℝ) - zeta < (n : ℝ) * rho / (h * PayOnce.success n (rho / h)) := by
  obtain ⟨p, hp, hp1, hmu⟩ := exists_near_full_multiplicity n hn hzeta
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : 0 < p := (one_div_pos.mpr hn0).trans hp
  have hrhoh : rho < rho / p := by
    apply (lt_div_iff₀ hp0).mpr
    nlinarith
  have hnp : 1 < (n : ℝ) * p := by
    have h := (div_lt_iff₀ hn0).mp hp
    nlinarith
  have hhbeta : rho / p < (n : ℝ) * rho := by
    apply (div_lt_iff₀ hp0).mpr
    nlinarith [mul_pos hrho (sub_pos.mpr hnp)]
  refine ⟨rho / p, hrhoh, hhbeta, hhbeta.trans hbeta, ?_⟩
  have he : rho / (rho / p) = p := by field_simp [hrho.ne', hp0.ne']
  rw [he]
  have hS : PayOnce.success n p ≠ 0 :=
    (PayOnce.success_pos n (by omega) p hp0 hp1.le).ne'
  have hrat : (n : ℝ) * rho / ((rho / p) * PayOnce.success n p) =
      (n : ℝ) * p / PayOnce.success n p := by
    field_simp [hrho.ne', hp0.ne', hS]
  rw [hrat]
  exact hmu

end FCAppendix.Exclusive

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Exclusive Set Filter Topology
open scoped BigOperators ProbabilityTheory

theorem prop_exclusive_scarce_existing
    {k : ℕ} (hk : 1 ≤ k) {rho zeta : ℝ}
    (hrho0 : 0 < rho) (hbeta : ((k + 1 : ℕ) : ℝ) * rho < 1) (hzeta : 0 < zeta) :
    ∃ h : ℝ, rho < h ∧ h < ((k + 1 : ℕ) : ℝ) * rho ∧ h < 1 ∧
      ((k + 1 : ℕ) : ℝ) - zeta <
        (((k + 1 : ℕ) : ℝ) * rho) / (h * PayOnce.success (k + 1) (rho / h)) ∧
      ∀ {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
        (Γ : ∀ t, FiniteGame (M t) (k + 1) (C t) Seed)
        (tariff : UserTariff), tariff.Allowed →
        (∀ t, ExclusiveTariffUsersOptimal (Γ t) tariff) →
        ∀ (B : ∀ t, PosteriorSystem (Γ t)),
          (∀ t, ExclusivePosteriorOptimalAE (Γ t) (B t)) →
          (∀ t, SymmetricProposersOnPath (Γ t)) →
          ∀ (E : Set ℝ), MeasurableSet E →
          (∀ t, ExclusiveBroadcastOn (Γ t) E) →
          (∀ t, (Γ t).F.real E = h) →
          (∀ t, (Γ t).F.real (Ioi (Γ t).g) = 1) →
          Tendsto M atTop atTop →
          Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 rho) →
          Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k + 1 : ℕ) : ℝ) * rho)) ∧
            ∀ᶠ t in atTop, 0 < finiteCoverage (Γ t) ∧
              ((k + 1 : ℕ) : ℝ) - zeta < finiteMultiplicity (Γ t) ∧
              finiteMultiplicity (Γ t) ≤ (k + 1 : ℕ) := by
  obtain ⟨h, hrhoh, hhbeta, hh1, htarget⟩ :=
    exists_scarce_parameters (k + 1) (by omega) hrho0 hbeta hzeta
  refine ⟨h, hrhoh, hhbeta, hh1, htarget, ?_⟩
  intro Seed _inst M C Γ _tariff _ha _hu B hB hsym E hE hclass hmass _hpositive hM hrho
  exact exclusive_scarce_eventual_multiplicity Γ hk hM B
    (fun t => exclusiveOptimalOnPath_of_feasible (Γ t) (B t) (hB t)) hsym E hE
    hclass hmass hrho hrho0 hrhoh htarget

end FCAppendix.Bayes
