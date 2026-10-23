import FCAppendix.CommonReserve.ActualInterim
import FCAppendix.CommonReserve.Deletion
import FCAppendix.CommonReserve.Quantiles

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

theorem ae_weak_lower_mass_positive (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ x ∂μ, 0 < μ.real (Iic x) := by
  let S : Set ℝ := {x | μ (Iic x) = 0}
  have hm : Measurable (fun x : ℝ => μ (Iic x)) :=
    measurable_measure_prodMk_left
      (measurableSet_le (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))
        measurable_fst)
  have hS : MeasurableSet S := measurableSet_eq_fun hm measurable_const
  let ν : Measure ℝ := μ.restrict S
  have ha : ∀ᵐ y ∂ν, ∀ᵐ x ∂ν, ¬ x ≤ y := by
    filter_upwards [ae_restrict_mem hS] with y hy
    have hz : ν (Iic y) = 0 := by
      rw [Measure.restrict_apply measurableSet_Iic]
      exact measure_mono_null inter_subset_left hy
    exact measure_eq_zero_iff_ae_notMem.mp hz
  have hp : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ¬ p.2 ≤ p.1 :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_snd measurable_fst).compl).mpr ha
  have hq : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, ¬ p.1 ≤ p.2 :=
    (Measure.measurePreserving_swap (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hp
  have hz : ν.prod ν univ = 0 := by
    have hf : ∀ᵐ p : ℝ × ℝ ∂ν.prod ν, False := (hp.and hq).mono fun p h =>
      (le_total p.1 p.2).elim h.2 h.1
    simpa only [ae_iff, not_false_eq_true, setOf_true] using hf
  have hnull : μ S = 0 := by
    have he : μ S * μ S = 0 := by
      simpa only [← univ_prod_univ, Measure.prod_prod, ν, Measure.restrict_apply_univ] using hz
    exact (mul_eq_zero.mp he).elim id id
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  exact ENNReal.toReal_pos hx (measure_ne_top _ _)

theorem exists_topChoice_mem_of_maximal (L : LocalList m) (r : ℝ) (hc : 0 < c)
    (i : Fin m) (hi : i ∈ positiveEligible L r)
    (hmax : ∀ l, Bayes.entryBid (positiveList L r l) ≤
      Bayes.entryBid (positiveList L r i)) :
    ∃ S ∈ topChoices L r c, i ∈ S := by
  classical
  obtain ⟨S, hS⟩ := topChoices_nonempty L r c
  have hopt : TopChoice L r c S := (Finset.mem_filter.mp hS).2
  by_cases himem : i ∈ S
  · exact ⟨S, hS, himem⟩
  have hpos : 0 < Bayes.entryBid (positiveList L r i) := by
    rw [positiveList_entry_of_mem L r i hi]
    exact ((mem_positiveEligible_iff L r i).mp hi).2.2
  have hcard := Finite.optimal_fills c _ S hopt.2 i himem hpos
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (hcard.symm ▸ hc)
  have hin : i ∉ S.erase l := fun h => himem (Finset.mem_of_mem_erase h)
  have hweight : Bayes.entryBid (positiveList L r i) =
      Bayes.entryBid (positiveList L r l) :=
    le_antisymm (Finite.optimal_swap c _ S hopt.2 l i hl himem) (hmax l)
  let T := insert i (S.erase l)
  have hTc : T.card ≤ c := by
    rw [Finset.card_insert_of_notMem hin, Finset.card_erase_of_mem hl, hcard]
    omega
  have hsum : (∑ k ∈ T, Bayes.entryBid (positiveList L r k)) =
      ∑ k ∈ S, Bayes.entryBid (positiveList L r k) := by
    rw [Finset.sum_insert hin]
    rw [hweight]
    simpa only [add_comm] using Finset.sum_erase_add S
      (fun k => Bayes.entryBid (positiveList L r k)) hl
  refine ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_insert_self _ _⟩
  refine ⟨?_, hTc, ?_⟩
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · exact hopt.1 (Finset.mem_of_mem_erase hk)
  · intro A hA
    rw [hsum]
    exact hopt.2.2 A hA

theorem UniformReserveRule.positive_acceptance_of_maximal
    {ν : Measure Seed} [IsProbabilityMeasure ν] {policy : LocalPolicy m c Seed}
    (h : UniformReserveRule ν policy r) (hc : 0 < c) (L : LocalList m)
    (i : Fin m) (hi : i ∈ positiveEligible L r)
    (hmax : ∀ l, Bayes.entryBid (positiveList L r l) ≤
      Bayes.entryBid (positiveList L r i)) :
    0 < ν.real {s | i ∈ (policy L s).val} := by
  obtain ⟨S, hS, hiS⟩ := exists_topChoice_mem_of_maximal L r hc i hi hmax
  have hcard : 0 < ((topChoices L r c).card : ℝ) :=
    Nat.cast_pos.mpr (Finset.card_pos.mpr (topChoices_nonempty L r c))
  have hpos : 0 < ν.real {s | positiveSelection L (policy L s).val = S} := by
    rw [Measure.real, h.positive_law, if_pos hS]
    exact one_div_pos.mpr hcard
  apply hpos.trans_le
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  have hh : i ∈ positiveSelection L (policy L s).val := hs.symm ▸ hiS
  exact (Finset.mem_filter.mp hh).1

namespace FiniteGame

theorem coordinate_cdf_positive (Γ : FiniteGame m n c r Seed) (j : Fin n) :
    ∀ᵐ d ∂Γ.userLaw,
      0 < Γ.userLaw.real {e | Bayes.entryBid (e.2.val j) ≤ Bayes.entryBid (d.2.val j)} := by
  let f : UserDraw n r → ℝ := fun d => Bayes.entryBid (d.2.val j)
  have hf : Measurable f := measurable_coordinateBid j
  have h := ae_weak_lower_mass_positive (Γ.userLaw.map f)
  have hp := ae_of_ae_map hf.aemeasurable h
  filter_upwards [hp] with d hd
  simpa only [Measure.real, Measure.map_apply hf measurableSet_Iic, f,
    Set.preimage, mem_Iic] using hd

theorem focalIndicator_integral_pos (Γ : FiniteGame m n c r Seed)
    (hc : 0 < c) (hU : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (j : Fin n) (a : Action n r) (hb : 0 < Bayes.entryBid (a.val j))
    (hF : 0 < Γ.userLaw.real {d | Bayes.entryBid (d.2.val j) ≤ Bayes.entryBid (a.val j)}) :
    0 < ∫ ω, Γ.focalIndicator i j a ω ∂Γ.sampleLaw := by
  classical
  by_contra hpos
  have hz : (∫ ω, Γ.focalIndicator i j a ω ∂Γ.sampleLaw) = 0 :=
    le_antisymm (le_of_not_gt hpos) (integral_nonneg (Γ.focalIndicator_nonneg i j a))
  have hae := (integral_eq_zero_iff_of_nonneg (Γ.focalIndicator_nonneg i j a)
    (Γ.integrable_focalIndicator i j a)).mp hz
  have hdraw := Measure.ae_ae_of_ae_prod hae
  let D : Set (Fin m → UserDraw n r) := univ.pi fun _ =>
    {d | Bayes.entryBid (d.2.val j) ≤ Bayes.entryBid (a.val j)}
  have hD : (Measure.pi fun _ : Fin m => Γ.userLaw) D ≠ 0 := by
    rw [Measure.pi_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro _ _ he
    simp only [Measure.real, he, ENNReal.toReal_zero, lt_self_iff_false] at hF
  obtain ⟨d, hd, hs⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hD
    (ae_restrict_of_ae hdraw)
  let L : LocalList m := fun l => (Function.update (fun u => (d u).2) i a l).val j
  have hlist (s : Fin n → Seed) : observe (deviated i a (d, s)) j = L := rfl
  have hLi : L i = a.val j := by simp [L]
  have hLa (l : Fin m) (b : ℝ) (hl : L l = some b) : r ≤ b := by
    exact (Function.update (fun u => (d u).2) i a l).property j b hl
  have hip : i ∈ positiveEligible L r := by
    rw [mem_positiveEligible_iff, hLi]
    refine ⟨?_, ?_, hb⟩
    · intro he
      simp only [he, Bayes.entryBid, lt_self_iff_false] at hb
    · cases he : a.val j with
      | none => simp only [he, Bayes.entryBid, lt_self_iff_false] at hb
      | some b => exact a.property j b he
  have hmax (l : Fin m) : Bayes.entryBid (positiveList L r l) ≤
      Bayes.entryBid (positiveList L r i) := by
    simp only [positiveList_entry_eq Γ.reserve_nonneg hLa, hLi]
    by_cases hl : l = i
    · subst l
      simp only [hLi, le_refl]
    · have hdl : Bayes.entryBid ((d l).2.val j) ≤ Bayes.entryBid (a.val j) :=
        hd l (mem_univ l)
      simpa only [L, Function.update_of_ne hl] using hdl
  have hlocal := (hU j).positive_acceptance_of_maximal hc L i hip hmax
  have hE : MeasurableSet {s | i ∈ (Γ.policy j L s).val} :=
    (Measurable.of_uncurry_left (f := fun L s => (Γ.policy j L s).val) (x := L)
      (Γ.policy_measurable j))
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  have hzero : (Measure.pi fun _ : Fin n => Γ.seedLaw)
      {s | i ∈ (Γ.policy j L (s j)).val} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hs] with s hsz
    intro hm
    have he : Γ.focalIndicator i j a (d, s) = 1 := by
      change (if i ∈ (Γ.policy j (observe (deviated i a (d, s)) j) (s j)).val
        then (1 : ℝ) else 0) = 1
      rw [hlist s, if_pos hm]
    rw [he] at hsz
    norm_num at hsz
  have hmap := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).map_eq
  have he : Γ.seedLaw {s | i ∈ (Γ.policy j L s).val} = 0 := by
    rw [← hmap, Measure.map_apply (measurable_pi_apply j) hE]
    exact hzero
  simp only [Measure.real, he, ENNReal.toReal_zero, lt_self_iff_false] at hlocal

theorem ae_positive_coordinate_acceptance (Γ : FiniteGame m n c r Seed)
    (hc : 0 < c) (hU : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) : ∀ᵐ d ∂Γ.userLaw, ∀ j, 0 < Bayes.entryBid (d.2.val j) →
      0 < ∫ ω, Γ.focalIndicator i j d.2 ω ∂Γ.sampleLaw := by
  filter_upwards [ae_all_iff.mpr (Γ.coordinate_cdf_positive)] with d hd j hj
  exact Γ.focalIndicator_integral_pos hc hU i j d.2 hj (hd j)

end FiniteGame

omit [MeasurableSpace Seed] in
theorem payment_erase_add (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed)
    (hj : j ∈ accepted x policy seed i) :
    payment (eraseProfile x i j) policy seed i + Bayes.entryBid ((x i).val j) =
      payment x policy seed i := by
  classical
  unfold payment
  rw [accepted_erase]
  have he : (∑ l ∈ (accepted x policy seed i).erase j,
      Bayes.entryBid ((eraseProfile x i j i).val l)) =
      ∑ l ∈ (accepted x policy seed i).erase j, Bayes.entryBid ((x i).val l) := by
    apply Finset.sum_congr rfl
    intro l hl
    simp [eraseProfile, erase, Function.update, (Finset.mem_erase.mp hl).1]
  rw [he]
  exact Finset.sum_erase_add _ _ hj

omit [MeasurableSpace Seed] in
theorem count_erase_of_mem (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed)
    (hj : j ∈ accepted x policy seed i) :
    count (eraseProfile x i j) policy seed i = count x policy seed i - 1 := by
  rw [count, accepted_erase, Finset.card_erase_of_mem hj]
  rfl

omit [MeasurableSpace Seed] in
theorem payoff_erase_gain_singleton (v g : ℝ) (G : Schedule n)
    (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed)
    (hj : j ∈ accepted x policy seed i) (hK : count x policy seed i = 1) :
    payoff v g G (eraseProfile x i j) policy seed i - payoff v g G x policy seed i =
      Bayes.entryBid ((x i).val j) + g - v := by
  have hp := payment_erase_add x i j policy seed hj
  have hn : 1 ≤ n := by simpa only [hK] using count_le x policy seed i
  unfold payoff
  rw [count_erase_of_mem x i j policy seed hj, hK]
  simp only [Nat.sub_self, successIndicator, one_ne_zero, if_false, if_true, mul_one,
    mul_zero, G.zero, G.one hn]
  linarith

omit [MeasurableSpace Seed] in
theorem payoff_erase_gain_duplicate (v g : ℝ) (hg : 0 ≤ g) (G : Schedule n)
    (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed)
    (hj : j ∈ accepted x policy seed i) (hK : 2 ≤ count x policy seed i) :
    Bayes.entryBid ((x i).val j) - g * ((n : ℝ) - 2) ≤
      payoff v g G (eraseProfile x i j) policy seed i - payoff v g G x policy seed i := by
  have hp := payment_erase_add x i j policy seed hj
  have hG := mul_le_mul_of_nonneg_left
    (base_charge_deletion_bound G _ hK (count_le x policy seed i)) hg
  unfold payoff
  rw [count_erase_of_mem x i j policy seed hj]
  simp only [successIndicator, if_neg (show count x policy seed i ≠ 0 by omega),
    if_neg (show count x policy seed i - 1 ≠ 0 by omega), mul_one]
  nlinarith

omit [MeasurableSpace Seed] in

theorem payoff_erase_lower (v g : ℝ) (hg : 0 ≤ g) (G : Schedule n)
    (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) :
    payoff v g G x policy seed i +
      (Bayes.entryBid ((x i).val j) - max (v - g) 0 - (n : ℝ) * g) *
        (if j ∈ accepted x policy seed i then 1 else 0) ≤
      payoff v g G (eraseProfile x i j) policy seed i := by
  classical
  have hng : 0 ≤ (n : ℝ) * g := mul_nonneg (Nat.cast_nonneg n) hg
  by_cases hj : j ∈ accepted x policy seed i
  · rw [if_pos hj, mul_one]
    have hKpos : 0 < count x policy seed i := Finset.card_pos.mpr ⟨j, hj⟩
    by_cases hKone : count x policy seed i = 1
    · have hgain := payoff_erase_gain_singleton v g G x i j policy seed hj hKone
      linarith [le_max_left (v - g) 0]
    · have hKtwo : 2 ≤ count x policy seed i := by omega
      have hgain := payoff_erase_gain_duplicate v g hg G x i j policy seed hj hKtwo
      nlinarith [le_max_right (v - g) 0]
  · rw [if_neg hj, mul_zero, add_zero]
    have hS : accepted (eraseProfile x i j) policy seed i = accepted x policy seed i := by
      rw [accepted_erase, Finset.erase_eq_of_notMem hj]
    have hp : payment (eraseProfile x i j) policy seed i = payment x policy seed i := by
      unfold payment
      rw [hS]
      apply Finset.sum_congr rfl
      intro l hl
      have hlj : l ≠ j := fun h => hj (h ▸ hl)
      simp [eraseProfile, erase, Function.update, hlj]
    have hc : count (eraseProfile x i j) policy seed i = count x policy seed i :=
      congrArg Finset.card hS
    simp only [payoff, hp, hc, le_refl]

namespace FiniteGame

omit [MeasurableSpace Seed] in
theorem deviated_erase (i : Fin m) (a : Action n r) (j : Fin n)
    (ω : Sample m n r Seed) :
    deviated i (erase a j) ω = eraseProfile (deviated i a ω) i j := by
  classical
  ext l
  by_cases hl : l = i <;> simp [deviated, eraseProfile, Function.update, hl]

theorem purePayoff_erase_lower (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) (j : Fin n) :
    Γ.purePayoff i v a +
      (Bayes.entryBid (a.val j) - max (v - Γ.g) 0 - (n : ℝ) * Γ.g) *
        (∫ ω, Γ.focalIndicator i j a ω ∂Γ.sampleLaw) ≤
      Γ.purePayoff i v (erase a j) := by
  classical
  have hsum : Integrable (fun ω => payoff v Γ.g Γ.G (deviated i a ω) Γ.policy ω.2 i +
      (Bayes.entryBid (a.val j) - max (v - Γ.g) 0 - (n : ℝ) * Γ.g) *
        Γ.focalIndicator i j a ω) Γ.sampleLaw :=
    (Γ.integrable_purePayoff i v a).add ((Γ.integrable_focalIndicator i j a).const_mul
      (Bayes.entryBid (a.val j) - max (v - Γ.g) 0 - (n : ℝ) * Γ.g))
  have hh := integral_mono hsum
    (Γ.integrable_purePayoff i v (erase a j))
    (fun ω => show payoff v Γ.g Γ.G (deviated i a ω) Γ.policy ω.2 i +
        (Bayes.entryBid (a.val j) - max (v - Γ.g) 0 - (n : ℝ) * Γ.g) *
          Γ.focalIndicator i j a ω ≤
        payoff v Γ.g Γ.G (deviated i (erase a j) ω) Γ.policy ω.2 i from by
      have hpoint := payoff_erase_lower v Γ.g Γ.g_nonneg Γ.G
        (deviated i a ω) i j Γ.policy ω.2
      rw [← deviated_erase] at hpoint
      have hcoord : (deviated i a ω i).val j = a.val j := by
        simp only [deviated, Function.update_self]
      have hind : (if j ∈ accepted (deviated i a ω) Γ.policy ω.2 i
          then (1 : ℝ) else 0) = Γ.focalIndicator i j a ω := by
        simp only [accepted, Finset.mem_filter, Finset.mem_univ, true_and, focalIndicator]
      rw [hcoord, hind] at hpoint
      exact hpoint)
  rw [integral_add (Γ.integrable_purePayoff i v a)
    ((Γ.integrable_focalIndicator i j a).const_mul
      (Bayes.entryBid (a.val j) - max (v - Γ.g) 0 - (n : ℝ) * Γ.g)), integral_const_mul] at hh
  exact hh

theorem coordinate_bid_le_of_bestResponse (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (v : ℝ) (a : Action n r) (j : Fin n)
    (ha : (Γ.interim i).BestResponse v a)
    (hp : 0 < ∫ ω, Γ.focalIndicator i j a ω ∂Γ.sampleLaw) :
    Bayes.entryBid (a.val j) ≤ max (v - Γ.g) 0 + (n : ℝ) * Γ.g := by
  have hbr := (Γ.interim_bestResponse i v a).mp ha (erase a j)
  have hdel := Γ.purePayoff_erase_lower i v a j
  nlinarith

theorem ae_coordinate_bid_bound (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hc : 0 < c) (hΓ : Γ.UsersOptimal)
    (hU : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    ∀ᵐ d ∂Γ.userLaw, ∀ j,
      Bayes.entryBid (d.2.val j) ≤ max (d.1 - Γ.g) 0 + (n : ℝ) * Γ.g := by
  let i : Fin m := ⟨0, hm⟩
  filter_upwards [Γ.ae_bestResponse_userLaw hΓ i,
    Γ.ae_positive_coordinate_acceptance hc hU i] with d hd hp j
  by_cases hb : 0 < Bayes.entryBid (d.2.val j)
  · exact Γ.coordinate_bid_le_of_bestResponse i d.1 d.2 j hd (hp j hb)
  · exact (le_of_not_gt hb).trans (add_nonneg (le_max_right _ _)
      (mul_nonneg (Nat.cast_nonneg n) Γ.g_nonneg))

end FiniteGame

theorem bid_tail_from_values (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hc : 0 < c) (_hn : 2 ≤ n) (hΓ : Γ.UsersOptimal)
    (hU : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (j : Fin n) (b : ℝ) (hb : (n : ℝ) * Γ.g ≤ b) :
    bidTail Γ j b ≤ Γ.F.real (Ioi (Γ.g + b - (n : ℝ) * Γ.g)) := by
  have hsub : aboveAt j b ≤ᵐ[Γ.userLaw]
      {d : UserDraw n r | Γ.g + b - (n : ℝ) * Γ.g < d.1} := by
    filter_upwards [Γ.ae_coordinate_bid_bound hm hc hΓ hU] with d hd htail
    change Γ.g + b - (n : ℝ) * Γ.g < d.1
    have hmax : b - (n : ℝ) * Γ.g < max (d.1 - Γ.g) 0 := by
      have hh := hd j
      have hh' := htail.2
      linarith
    rcases lt_max_iff.mp hmax with hv | hz
    · linarith
    · linarith
  have hmeasure := measure_mono_ae hsub
  have hmap : Γ.userLaw.map Prod.fst = Γ.F := Measure.fst_compProd Γ.F Γ.σ
  have he : Γ.userLaw {d : UserDraw n r | Γ.g + b - (n : ℝ) * Γ.g < d.1} =
      Γ.F (Ioi (Γ.g + b - (n : ℝ) * Γ.g)) := by
    rw [← hmap, Measure.map_apply measurable_fst measurableSet_Ioi]
    rfl
  rw [he] at hmeasure
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure

end FCAppendix.CommonReserve
