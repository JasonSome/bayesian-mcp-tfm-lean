import FCAppendix.PayOnce.BroadcastRescue

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def fullBid (n : ℕ) (b : ℝ) (hb : 0 ≤ b) : JointAction n := ⟨b, hb, n, le_rfl⟩

theorem fullBid_success_pos_of_absence_mass (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (j : Fin n) (hrat : ProposerRationalAtFeasibleLists Γ j)
    (habs : userLaw Γ {d | j ∉ firstK d.2 d.1.2.routeCount} ≠ 0)
    (i : Fin m) (b : ℝ) (hb : 0 < b) :
    0 < ((problem Γ i).outcome (fullBid n b hb.le)).success := by
  classical
  by_contra hnpos
  have hz : ((problem Γ i).outcome (fullBid n b hb.le)).success = 0 :=
    le_antisymm (le_of_not_gt hnpos) (CountLaw.success_nonneg _)
  have hzero := ae_focalCount_zero_of_success_zero Γ i (fullBid n b hb.le) hz
  have hdrawzero := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod hzero)
  let D : Set (UserProfile m n) := Set.univ.pi fun _ : Fin m =>
    {d | j ∉ firstK d.2 d.1.2.routeCount}
  have hD : userProfileLaw Γ D ≠ 0 := by
    simp only [D, userProfileLaw, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => habs
  obtain ⟨d, hdD, hdz⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae hdrawzero)
  let ℓ := presentDrawList d i b j
  have hi : ℓ i = some b := by simp [ℓ, presentDrawList]
  have hother (l : Fin m) (hl : l ≠ i) : ℓ l = none := by
    have hlabs : j ∉ firstK (d l).2 (d l).1.2.routeCount := hdD l (Set.mem_univ l)
    simp [ℓ, presentDrawList, hl, observe, drawsRealization, hlabs]
  have hacc := ae_singleton_accepts Γ hc j hrat ℓ
    (presentDrawList_feasible d i b hb.le j) i b hb hi hother
  have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hacc
  obtain ⟨s, hsz, hsa⟩ := (hdz.and hs).exists
  obtain ⟨τ, hτ⟩ := hsz.exists
  have hroute : j ∈ firstK τ (fullBid n b hb.le).routeCount := by simp [fullBid, mem_firstK]
  have hin := (mem_allocation_deviated_iff Γ i (fullBid n b hb.le) ((d, s), τ) j).mpr
    ⟨hroute, hsa⟩
  have hpos : 0 < (focalCount Γ i (fullBid n b hb.le) ((d, s), τ)).val := by
    change 0 < (accepted (deviated i (fullBid n b hb.le) ((d, s), τ)) Γ.policy s i).card
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hin⟩⟩
  have hzv := congrArg Fin.val hτ
  change (focalCount Γ i (fullBid n b hb.le) ((d, s), τ)).val = 0 at hzv
  omega

theorem payoff_once (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) (v : ℝ) (a : JointAction n) :
    (problem Γ i).payoff v a =
      (v - a.bid - Γ.g) * ((problem Γ i).outcome a).success := by
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G = _
  rw [hA, hG, CountLaw.once_utility]

theorem bestResponse_positive_of_absence_mass (Γ : FiniteGame m n c Seed)
    (hc : 0 < c) (j : Fin n) (hrat : ProposerRationalAtFeasibleLists Γ j)
    (habs : userLaw Γ {d | j ∉ firstK d.2 d.1.2.routeCount} ≠ 0)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (i : Fin m) (v : ℝ) (hv : Γ.g < v) (a : JointAction n)
    (hbr : (problem Γ i).BestResponse v a) :
    0 < (problem Γ i).payoff v a ∧
      0 < ((problem Γ i).outcome a).success ∧ a.bid < v - Γ.g := by
  have hb : 0 < (v - Γ.g) / 2 := by linarith
  have hS := fullBid_success_pos_of_absence_mass Γ hc j hrat habs i _ hb
  have hdev : 0 < (problem Γ i).payoff v (fullBid n _ hb.le) := by
    rw [payoff_once Γ hA hG]
    apply mul_pos _ hS
    change 0 < v - (v - Γ.g) / 2 - Γ.g
    linarith
  have hpay : 0 < (problem Γ i).payoff v a := hdev.trans_le (hbr _)
  refine ⟨hpay, ?_, ?_⟩
  · rw [payoff_once Γ hA hG] at hpay
    exact lt_of_le_of_ne (CountLaw.success_nonneg _) (by
      intro he
      rw [← he, mul_zero] at hpay
      exact (lt_irrefl 0) hpay)
  · rw [payoff_once Γ hA hG] at hpay
    rcases mul_pos_iff.mp hpay with hpos | hneg
    · linarith [hpos.1]
    · exact False.elim ((not_lt_of_ge (CountLaw.success_nonneg _)) hneg.2)

theorem payoff_zero_of_no_routes (Γ : FiniteGame m n c Seed)
    (i : Fin m) (v : ℝ) (a : JointAction n) (ha : a.routeCount = 0) :
    (problem Γ i).payoff v a = 0 := by
  have hcount (ω : Sample m n Seed) : focalCount Γ i a ω = 0 := by
    apply Fin.ext
    have h := focalCount_le Γ i a ω
    rw [ha] at h
    exact Nat.eq_zero_of_le_zero h
  change (CountLaw.ofMeasure (sampleLaw Γ) (focalCount Γ i a)
    (measurable_focalCount Γ i a)).utility v a.bid Γ.g Γ.A Γ.G = 0
  unfold CountLaw.utility
  rw [CountLaw.expect_ofMeasure]
  simp_rw [hcount]
  simp [userPayoff_zero v a.bid Γ.g Γ.A.charge Γ.G.charge Γ.A.zero Γ.G.zero]

theorem ae_positive_value_routes_userLaw (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j) :
    ∀ᵐ d ∂userLaw Γ, Γ.g < d.1.1 → 0 < d.1.2.routeCount := by
  classical
  let i : Fin m := ⟨0, hm⟩
  let j : Fin n := ⟨0, hn⟩
  by_cases hmass : userLaw Γ {d | d.1.2.routeCount = 0} = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hmass] with d hd _
    exact Nat.pos_of_ne_zero hd
  · have habs : userLaw Γ {d | j ∉ firstK d.2 d.1.2.routeCount} ≠ 0 := by
      intro hzero
      apply hmass
      apply measure_mono_null _ hzero
      intro d hd
      simp only [Set.mem_setOf_eq] at hd ⊢
      simp [hd, mem_firstK]
    have hbest := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
      (ν := permLaw n)).quasiMeasurePreserving.ae (ae_bestResponse_compProd Γ hu i)
    filter_upwards [hbest] with d hd hv
    have hpay := (bestResponse_positive_of_absence_mass Γ hc j (hrat j) habs
      hA hG i d.1.1 hv d.1.2 hd).1
    by_contra hnot
    have hz : d.1.2.routeCount = 0 := Nat.eq_zero_of_not_pos hnot
    rw [payoff_zero_of_no_routes Γ i _ _ hz] at hpay
    exact (lt_irrefl 0) hpay

theorem ae_positive_value_routes_compProd (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), Γ.g < x.1 → 0 < x.2.routeCount := by
  have h := Measure.ae_ae_of_ae_prod (ae_positive_value_routes_userLaw Γ hm hn hc hA hG hu hrat)
  filter_upwards [h] with x hx
  exact hx.exists.choose_spec

theorem ae_positive_value_routes (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.once n) (hG : Γ.G = Schedule.once n)
    (hu : UsersOptimal Γ) (hrat : ∀ j, ProposerRationalAtFeasibleLists Γ j) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, Γ.g < v → 0 < a.routeCount :=
  Measure.ae_ae_of_ae_compProd (ae_positive_value_routes_compProd Γ hm hn hc hA hG hu hrat)

end FCAppendix.Bayes
