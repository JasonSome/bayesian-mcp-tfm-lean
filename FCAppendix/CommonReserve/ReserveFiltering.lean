import FCAppendix.CommonReserve.TieSymmetry
import FCAppendix.Finite.IdentitySymmetry

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def reserveList (L : LocalList m) (r : ℝ) : LocalList m := by
  classical
  exact fun i => if i ∈ eligible L r then L i else none

def reserveRealization (r : ℝ) (x : Realization m n) : Realization m n := by
  classical
  refine {
    action := fun i => {
      bid := (x.action i).bid
      bid_nonneg := (x.action i).bid_nonneg
      routeCount := if r ≤ (x.action i).bid then (x.action i).routeCount else 0
      routeCount_le := ?_ }
    recipients := fun i => if r ≤ (x.action i).bid then x.recipients i else ∅
    chosen_size := ?_ }
  · split_ifs
    · exact (x.action _).routeCount_le
    · exact Nat.zero_le _
  · intro i
    by_cases hi : r ≤ (x.action i).bid
    · simp [hi, x.chosen_size i]
    · simp [hi]

theorem reserveRealization_eligible (r : ℝ) (x : Realization m n) :
    ∀ i, 0 < ((reserveRealization r x).action i).routeCount →
      r ≤ ((reserveRealization r x).action i).bid := by
  classical
  intro i hi
  by_cases hb : r ≤ (x.action i).bid
  · exact hb
  · simp [reserveRealization, hb] at hi

theorem observe_reserveRealization (r : ℝ) (x : Realization m n) (j : Fin n) :
    Game.observe (reserveRealization r x) j = reserveList (Game.observe x j) r := by
  classical
  funext i
  by_cases hb : r ≤ (x.action i).bid <;>
    by_cases hj : j ∈ x.recipients i <;>
    simp [Game.observe, reserveRealization, reserveList, eligible, Bayes.entryBid, hb, hj]

theorem positiveEligible_reserveList (L : LocalList m) (r : ℝ) :
    positiveEligible (reserveList L r) r = positiveEligible L r := by
  classical
  ext i
  by_cases he : i ∈ eligible L r
  · simp only [mem_positiveEligible_iff, reserveList, if_pos he]
  · have hp : i ∉ positiveEligible L r := fun hi => he (Finset.mem_filter.mp hi).1
    have hp' : i ∉ positiveEligible (reserveList L r) r := by
      simp [mem_positiveEligible_iff, reserveList, he]
    exact iff_of_false hp' hp

theorem positiveList_reserveList (L : LocalList m) (r : ℝ) :
    positiveList (reserveList L r) r = positiveList L r := by
  classical
  funext i
  by_cases hi : i ∈ positiveEligible L r
  · have he : i ∈ eligible L r := (Finset.mem_filter.mp hi).1
    simp [positiveList, positiveEligible_reserveList, hi, reserveList, he]
  · simp [positiveList, positiveEligible_reserveList, hi]

theorem topChoices_reserveList (L : LocalList m) (r : ℝ) :
    topChoices (reserveList L r) r c = topChoices L r c := by
  classical
  simp only [topChoices, TopChoice, positiveEligible_reserveList, positiveList_reserveList]

theorem reserveList_eq_of_nonneg (L : LocalList m)
    (hL : ∀ i b, L i = some b → 0 ≤ b) : reserveList L 0 = L := by
  classical
  funext i
  cases he : L i with
  | none => simp [reserveList, eligible, he]
  | some b => simp [reserveList, eligible, he, Bayes.entryBid, hL i b he]

theorem UniformReserveRule.ae_positiveSelection_eq {ν : Measure Seed}
    [IsProbabilityMeasure ν] {policy : LocalPolicy m c Seed} {r : ℝ}
    (hT : UniformReserveRule ν policy r) (hr : 0 < r) (L : LocalList m) :
    ∀ᵐ s ∂ν, positiveSelection L (policy L s).val = (policy L s).val := by
  classical
  filter_upwards [hT.eligible L] with s hs
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact hr.trans_le ((mem_eligible_iff L r i).mp (hs hi)).2

theorem selection_map_reserveList (ν : Measure Seed) [IsProbabilityMeasure ν]
    (policy : LocalPolicy m c Seed)
    (hp : Measurable (fun p : LocalList m × Seed => (policy p.1 p.2).val))
    (r : ℝ) (hr : 0 ≤ r) (hT : UniformReserveRule ν policy r)
    (L : LocalList m) (hL : ∀ i b, L i = some b → 0 ≤ b) :
    ν.map (fun s => (policy (reserveList L r) s).val) =
      ν.map (fun s => (policy L s).val) := by
  classical
  by_cases hz : r = 0
  · subst r
    rw [reserveList_eq_of_nonneg L hL]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hpm (L' : LocalList m) : Measurable
        (fun s => positiveSelection L' (policy L' s).val) :=
      (measurable_positiveSelection_policy policy hp).comp
        (measurable_const.prodMk measurable_id)
    have hm : ν.map (fun s => positiveSelection (reserveList L r)
          (policy (reserveList L r) s).val) =
        ν.map (fun s => positiveSelection L (policy L s).val) := by
      apply Measure.ext_of_singleton
      intro S
      rw [Measure.map_apply (hpm _) (measurableSet_singleton S),
        Measure.map_apply (hpm _) (measurableSet_singleton S)]
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      simp only [Set.preimage, Set.mem_singleton_iff, hT.positive_law,
        topChoices_reserveList]
    calc
      _ = ν.map (fun s => positiveSelection (reserveList L r)
          (policy (reserveList L r) s).val) :=
        Measure.map_congr ((hT.ae_positiveSelection_eq hrp _).mono fun _ hs => hs.symm)
      _ = ν.map (fun s => positiveSelection L (policy L s).val) := hm
      _ = _ := Measure.map_congr (hT.ae_positiveSelection_eq hrp L)

theorem selectionVector_map_reserveList (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (L : Fin n → LocalList m) (hL : ∀ j i b, L j i = some b → 0 ≤ b) :
    (Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (Bayes.selectionVector Γ (fun j => reserveList (L j) r)) =
      (Measure.pi fun _ : Fin n => Γ.seedLaw).map (Bayes.selectionVector Γ L) := by
  have hm (j : Fin n) (L' : LocalList m) : Measurable
      (fun s => (Γ.policy j L' s).val) :=
    (Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id)
  calc
    _ = Measure.pi (fun j => Γ.seedLaw.map
        (fun s => (Γ.policy j (reserveList (L j) r) s).val)) :=
      Measure.pi_map_pi (fun j => (hm j _).aemeasurable)
    _ = Measure.pi (fun j => Γ.seedLaw.map (fun s => (Γ.policy j (L j) s).val)) := by
      congr 1
      funext j
      exact selection_map_reserveList Γ.seedLaw (Γ.policy j) (Γ.policy_measurable j)
        r hr (hT j) (L j) (hL j)
    _ = _ := (Measure.pi_map_pi (fun j => (hm j _).aemeasurable)).symm

theorem integral_selectionCount_reserveList (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (L : Fin n → LocalList m) (hL : ∀ j i b, L j i = some b → 0 ≤ b)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ s, f (Bayes.selectionCount
      (Bayes.selectionVector Γ (fun j => reserveList (L j) r) s) i)
      ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
      ∫ s, f (Bayes.selectionCount (Bayes.selectionVector Γ L s) i)
        ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  let H := fun S : Fin n → Finset (Fin m) => f (Bayes.selectionCount S i)
  have hH : Measurable H := measurable_of_countable _
  calc
    _ = ∫ S, H S ∂(Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (Bayes.selectionVector Γ (fun j => reserveList (L j) r)) :=
      (integral_map_of_stronglyMeasurable
        (Bayes.measurable_selectionVector Γ _) hH.stronglyMeasurable).symm
    _ = ∫ S, H S ∂(Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (Bayes.selectionVector Γ L) := by rw [selectionVector_map_reserveList Γ r hr hT L hL]
    _ = _ := integral_map_of_stronglyMeasurable
      (Bayes.measurable_selectionVector Γ L) hH.stronglyMeasurable

end FCAppendix.CommonReserve
