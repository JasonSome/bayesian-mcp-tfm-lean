import FCAppendix.Finite.NoOverbid
import FCAppendix.PayOnce.BayesianVisibleList

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ProposerRationalOnPath (Γ : FiniteGame m n c Seed) (j : Fin n) : Prop :=
  ∃ belief : LocalList m → Fin m → FiniteLaw (Fin n),
    ∀ᵐ ℓ ∂observedListLaw Γ j, ∀ᵐ s ∂Γ.seedLaw,
      Finite.Optimal c (beliefReceipts Γ.A (belief ℓ) ℓ) (Γ.policy j ℓ s).val

structure IsAEEquilibrium (Γ : FiniteGame m n c Seed) : Prop where
  users : UsersOptimal Γ
  proposers : ∀ j, ProposerRationalOnPath Γ j

theorem IsEquilibrium.isAEEquilibrium (Γ : FiniteGame m n c Seed)
    (hΓ : IsEquilibrium Γ) : IsAEEquilibrium Γ := by
  refine ⟨hΓ.users, ?_⟩
  intro j
  obtain ⟨belief, hb⟩ := hΓ.proposers j
  exact ⟨belief, Filter.Eventually.of_forall fun ℓ =>
    Filter.Eventually.of_forall (hb ℓ)⟩

theorem isAEEquilibrium_of_posterior {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalOnPath Γ B) : IsAEEquilibrium Γ :=
  ⟨hu, fun j => ⟨posteriorCountBelief Γ B j, hB j⟩⟩

theorem measure_overbidAt_zero_onPath (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : UsersOptimal Γ) (j : Fin n) (hj : ProposerRationalOnPath Γ j) :
    userLaw Γ (overbidAt Γ.g j) = 0 := by
  classical
  by_contra hmass
  have hall : ∀ᵐ ω ∂(backgroundLaw Γ), ∀ i,
      Overbid Γ.g (ω.1 i).1 → playedCount Γ i ω = 0 :=
    (ae_all_iff).mpr (ae_played_overbid_zero Γ hΓ)
  obtain ⟨belief, hopt⟩ := hj
  have hdrawopt : ∀ᵐ d ∂userProfileLaw Γ,
      ∀ᵐ s ∂Γ.seedLaw, Finite.Optimal c
        (beliefReceipts Γ.A (belief (observe (drawsRealization d) j))
          (observe (drawsRealization d) j))
        (Γ.policy j (observe (drawsRealization d) j) s).val :=
    (ae_of_ae_map (measurable_observe_draws j).aemeasurable hopt)
  have hdrawzero := Measure.ae_ae_of_ae_prod hall
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m => overbidAt Γ.g j
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdz, hdo⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae (hdrawzero.and hdrawopt))
  have hseedopt : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
      Finite.Optimal c (beliefReceipts Γ.A (belief (observe (drawsRealization d) j))
        (observe (drawsRealization d) j))
        (Γ.policy j (observe (drawsRealization d) j) (s j)).val :=
    (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hdo
  obtain ⟨s, hsz, hso⟩ := (hdz.and hseedopt).exists
  let ω : Background m n Seed := (d, s)
  have hbad (i : Fin m) : (ω.1 i) ∈ overbidAt Γ.g j := hdD i (Set.mem_univ i)
  have hzero (i : Fin m) : playedCount Γ i ω = 0 := hsz i (hbad i).2
  have hempty : allocation (drawsRealization ω.1) Γ.policy ω.2 j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hmem : j ∈ accepted (drawsRealization ω.1) Γ.policy ω.2 i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    have hz : inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i = 0 :=
      congrArg Fin.val (hzero i)
    exact (Nat.ne_of_gt hpos) hz
  let i : Fin m := ⟨0, hm⟩
  let ℓ := observe (drawsRealization ω.1) j
  have hi : ℓ i = some (ω.1 i).1.2.bid := by
    simp [ℓ, observe, drawsRealization, (hbad i).1]
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt j.isLt)
  have hA (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) : (1 / (n : ℝ)) * r ≤ Γ.A.charge r := by
    have hrR : (r : ℝ) ≤ n := by exact_mod_cast hrn
    have hratio : (r : ℝ) / n ≤ 1 := (div_le_one hn).mpr hrR
    have hlow := Γ.A.lower r hr hrn
    simpa [div_eq_mul_inv, mul_comm] using hratio.trans hlow
  have hb : 0 < (ω.1 i).1.2.bid := lt_of_le_of_lt (le_max_right _ _) (hbad i).2
  have hreceipt := (beliefReceipts_bounds Γ.A (belief ℓ) ℓ (1 / (n : ℝ)) hA
    i _ hb.le hi).1
  have hpos : 0 < beliefReceipts Γ.A (belief ℓ) ℓ i :=
    lt_of_lt_of_le (mul_pos (one_div_pos.mpr hn) hb) hreceipt
  have hfill := Finite.optimal_fills c _ _ hso i
    (by change i ∉ allocation (drawsRealization ω.1) Γ.policy ω.2 j; simp [hempty]) hpos
  change (allocation (drawsRealization ω.1) Γ.policy ω.2 j).card = c at hfill
  rw [hempty, Finset.card_empty] at hfill
  omega

theorem ae_no_overbid_userLaw_onPath (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ) :
    ∀ᵐ d ∂(userLaw Γ), 0 < d.1.2.routeCount → d.1.2.bid ≤ max (d.1.1 - Γ.g) 0 := by
  classical
  have hall : ∀ᵐ d ∂(userLaw Γ), ∀ j : Fin n, d ∉ overbidAt Γ.g j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp
      (measure_overbidAt_zero_onPath Γ hm hc hΓ.users j (hΓ.proposers j))
  filter_upwards [hall] with d hd hk
  by_contra hb
  have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
    rw [card_firstK _ _ d.1.2.routeCount_le]
    exact hk
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  exact hd j ⟨hj, lt_of_not_ge hb⟩

theorem ae_no_overbid_compProd_onPath (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → x.2.bid ≤ max (x.1 - Γ.g) 0 := by
  have h := Measure.ae_ae_of_ae_prod (ae_no_overbid_userLaw_onPath Γ hm hc hΓ)
  filter_upwards [h] with x hx
  obtain ⟨_, hτ⟩ := hx.exists
  exact hτ

theorem ae_no_overbid_onPath (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂(Γ.σ v), 0 < a.routeCount → a.bid ≤ max (v - Γ.g) 0 :=
  Measure.ae_ae_of_ae_compProd (ae_no_overbid_compProd_onPath Γ hm hc hΓ)

end FCAppendix.Bayes
