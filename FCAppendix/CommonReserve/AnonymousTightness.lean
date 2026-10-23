import FCAppendix.CommonReserve.AnonymousReserve
import FCAppendix.Finite.NoOverbidAE
import FCAppendix.Finite.ReceiptBounds

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def eligibleOverbidAt (g r : ℝ) (j : Fin n) : Set (Bayes.UserDraw n) :=
  {d | r ≤ d.1.2.bid ∧ d ∈ Bayes.overbidAt g j}

theorem anonymous_measure_eligibleOverbidAt_zero
    (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hu : Bayes.UsersOptimal Γ)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (j : Fin n) :
    Bayes.userLaw Γ (eligibleOverbidAt Γ.g r j) = 0 := by
  classical
  by_contra hmass
  have hall : ∀ᵐ ω ∂Bayes.backgroundLaw Γ, ∀ i,
      Bayes.Overbid Γ.g (ω.1 i).1 → Bayes.playedCount Γ i ω = 0 :=
    ae_all_iff.mpr (Bayes.ae_played_overbid_zero Γ hu)
  have hdrawzero := Measure.ae_ae_of_ae_prod hall
  let D : Set (Bayes.UserProfile m n) :=
    Set.univ.pi fun _ : Fin m => eligibleOverbidAt Γ.g r j
  have hD : Bayes.userProfileLaw Γ D ≠ 0 := by
    simp only [D, Bayes.userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨d, hdD, hdz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae hdrawzero)
  let L := Game.observe (Bayes.drawsRealization d) j
  have hseedopt : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
      TopChoice L r c (positiveSelection L (Γ.policy j L (s j)).val) :=
    (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
      ((hT j).ae_topChoice L)
  obtain ⟨s, hsz, hso⟩ := (hdz.and hseedopt).exists
  have hbad (i : Fin m) : d i ∈ eligibleOverbidAt Γ.g r j := hdD i (Set.mem_univ i)
  have hzero (i : Fin m) : Bayes.playedCount Γ i (d, s) = 0 := hsz i (hbad i).2.2
  have hempty : (Γ.policy j L (s j)).val = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hmem : j ∈ Game.accepted (Bayes.drawsRealization d) Γ.policy s i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    have hz : Game.inclusionCount (Bayes.drawsRealization d) Γ.policy s i = 0 :=
      congrArg Fin.val (hzero i)
    exact (Nat.ne_of_gt hpos) hz
  let i : Fin m := ⟨0, hm⟩
  have hi : L i = some (d i).1.2.bid := by
    simp [L, Game.observe, Bayes.drawsRealization, (hbad i).2.1]
  have hbi : 0 < (d i).1.2.bid :=
    lt_of_le_of_lt (le_max_right _ _) (hbad i).2.2
  have hiE : i ∈ positiveEligible L r := by
    rw [mem_positiveEligible_iff, hi]
    exact ⟨Option.some_ne_none _, (hbad i).1, hbi⟩
  have hpos : 0 < Bayes.entryBid (positiveList L r i) := by
    rw [positiveList_entry_of_mem L r i hiE, hi]
    exact hbi
  have hfill := Finite.optimal_fills c _ _ hso.2 i
    (by simp [hempty, positiveSelection]) hpos
  simp only [hempty, positiveSelection, Finset.filter_empty, Finset.card_empty] at hfill
  omega

theorem anonymous_ae_no_overbid_eligible
    (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hu : Bayes.UsersOptimal Γ)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    ∀ᵐ d ∂Bayes.userLaw Γ, r ≤ d.1.2.bid → 0 < d.1.2.routeCount →
      d.1.2.bid ≤ max (d.1.1 - Γ.g) 0 := by
  classical
  have hall : ∀ᵐ d ∂Bayes.userLaw Γ, ∀ j : Fin n,
      d ∉ eligibleOverbidAt Γ.g r j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp
      (anonymous_measure_eligibleOverbidAt_zero Γ r hm hc hu hT j)
  filter_upwards [hall] with d hd hr hk
  by_contra hb
  have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
    rw [card_firstK _ _ d.1.2.routeCount_le]
    exact hk
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  exact hd j ⟨hr, hj, lt_of_not_ge hb⟩

def anonymousEligibleTail (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ)
    (j : Fin n) (b : ℝ) : ℝ :=
  (Bayes.userLaw Γ).real {d | r ≤ d.1.2.bid ∧ d ∈ Bayes.aboveAt j b}

theorem anonymous_eligible_tail_le_value_tail
    (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hm : 0 < m) (hc : 0 < c)
    (hu : Bayes.UsersOptimal Γ)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    anonymousEligibleTail Γ r j b ≤ Γ.F.real (Ioi (Γ.g + b)) := by
  have hsub : {d | r ≤ d.1.2.bid ∧ d ∈ Bayes.aboveAt j b} ≤ᵐ[Bayes.userLaw Γ]
      {d : Bayes.UserDraw n | Γ.g + b < d.1.1} := by
    filter_upwards [anonymous_ae_no_overbid_eligible Γ r hm hc hu hT] with d hd hdE
    have hk : 0 < d.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hdE.2.1⟩
      rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
    have hmax := lt_of_lt_of_le hdE.2.2 (hd hdE.1 hk)
    rcases lt_max_iff.mp hmax with hval | hzero
    · change Γ.g + b < d.1.1
      linarith
    · exact (not_lt_of_ge hb hzero).elim
  have heq : Bayes.userLaw Γ {d : Bayes.UserDraw n | Γ.g + b < d.1.1} =
      Γ.F (Ioi (Γ.g + b)) := by
    rw [← Bayes.userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun d : Bayes.UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  change (Bayes.userLaw Γ {d | r ≤ d.1.2.bid ∧ d ∈ Bayes.aboveAt j b}).toReal ≤
    (Γ.F (Ioi (Γ.g + b))).toReal
  rw [← heq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)

end FCAppendix.CommonReserve
