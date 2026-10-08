import FCAppendix.Game.RealizedPlay
import FCAppendix.Finite.BalancedOrder

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def Overbid (g : ℝ) (x : ℝ × JointAction n) : Prop :=
  max (x.1 - g) 0 < x.2.bid

theorem measurableSet_overbid (g : ℝ) :
    MeasurableSet {x : ℝ × JointAction n | Overbid g x} :=
  measurableSet_lt ((measurable_fst.sub_const g).max measurable_const)
    ((measurable_bid n).comp measurable_snd)

theorem bestResponse_overbid_success_zero (P : Interim.Problem n) (x : ℝ × JointAction n)
    (hbr : P.BestResponse x.1 x.2) (hbad : Overbid P.g x) :
    (P.outcome x.2).success = 0 := by
  have hpay : 0 ≤ P.payoff x.1 x.2 := by
    simpa only [P.payoff_abstain] using hbr (Interim.abstain n)
  have hA := mul_le_mul_of_nonneg_left ((P.outcome x.2).success_le_charge P.A)
    x.2.bid_nonneg
  have hG := mul_le_mul_of_nonneg_left ((P.outcome x.2).success_le_charge P.G) P.g_nonneg
  have hbound : P.payoff x.1 x.2 ≤ (x.1 - P.g - x.2.bid) * (P.outcome x.2).success := by
    simp only [Interim.Problem.payoff, CountLaw.utility_eq]
    linarith
  have hneg : x.1 - P.g - x.2.bid < 0 :=
    sub_neg.mpr (lt_of_le_of_lt (le_max_left _ _) hbad)
  apply le_antisymm _ (P.outcome x.2).success_nonneg
  nlinarith

theorem ae_focalCount_zero_of_success_zero (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (hs : ((problem Γ i).outcome a).success = 0) :
    ∀ᵐ ω ∂(sampleLaw Γ), focalCount Γ i a ω = 0 := by
  have hload := (((problem Γ i).outcome a).zero_success_iff_zero_load).mp hs
  rw [problem_outcome, CountLaw.load, CountLaw.expect_ofMeasure] at hload
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun ω => Nat.cast_nonneg (focalCount Γ i a ω).val)
    (CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => (r.val : ℝ)))).mp hload
  filter_upwards [hae] with ω hω
  apply Fin.ext
  change ((focalCount Γ i a ω).val : ℝ) = 0 at hω
  change (focalCount Γ i a ω).val = 0
  exact Nat.cast_eq_zero.mp hω

theorem ae_played_overbid_zero (Γ : FiniteGame m n c Seed) (hΓ : UsersOptimal Γ)
    (i : Fin m) :
    ∀ᵐ ω ∂(backgroundLaw Γ), Overbid Γ.g (ω.1 i).1 → playedCount Γ i ω = 0 := by
  apply ae_played_of_ae_deviation Γ i (fun x r => Overbid Γ.g x → r = 0)
  · have hbad : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) |
        Overbid Γ.g p.1} := measurable_fst (measurableSet_overbid Γ.g)
    have hzero : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | p.2 = 0} :=
      measurable_snd (measurableSet_singleton 0)
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hbad.compl.union hzero
  · filter_upwards [ae_bestResponse_compProd Γ hΓ i] with x hx
    by_cases hbad : Overbid Γ.g x
    · filter_upwards [ae_focalCount_zero_of_success_zero Γ i x.2
        (bestResponse_overbid_success_zero (problem Γ i) x hx hbad)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ h => (hbad h).elim

def overbidAt (g : ℝ) (j : Fin n) : Set (UserDraw n) :=
  {d | j ∈ firstK d.2 d.1.2.routeCount ∧ Overbid g d.1}

theorem measurableSet_overbidAt (g : ℝ) (j : Fin n) :
    MeasurableSet (overbidAt g j) := by
  have hreach : MeasurableSet {d : UserDraw n | j ∈ firstK d.2 d.1.2.routeCount} :=
    (measurable_snd.prodMk
      ((measurable_routeCount n).comp (measurable_snd.comp measurable_fst)))
      (measurableSet_mem_firstK j)
  exact hreach.inter (measurable_fst (measurableSet_overbid g))

theorem measure_overbidAt_zero (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : UsersOptimal Γ) (j : Fin n) (hj : ProposerRational Γ j) :
    userLaw Γ (overbidAt Γ.g j) = 0 := by
  classical
  by_contra hmass
  have hall : ∀ᵐ ω ∂(backgroundLaw Γ), ∀ i,
      Overbid Γ.g (ω.1 i).1 → playedCount Γ i ω = 0 :=
    (ae_all_iff).mpr (ae_played_overbid_zero Γ hΓ)
  let E : Set (Background m n Seed) :=
    (Set.univ.pi fun _ : Fin m => overbidAt Γ.g j) ×ˢ Set.univ
  have hE : backgroundLaw Γ E ≠ 0 := by
    simp only [E, backgroundLaw, Measure.prod_prod, measure_univ, mul_one, Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hmass
  obtain ⟨ω, hωE, hω⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hE (ae_restrict_of_ae hall)
  have hbad (i : Fin m) : (ω.1 i) ∈ overbidAt Γ.g j := hωE.1 i (Set.mem_univ i)
  have hzero (i : Fin m) : playedCount Γ i ω = 0 := hω i (hbad i).2
  have hempty : allocation (drawsRealization ω.1) Γ.policy ω.2 j = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hmem : j ∈ accepted (drawsRealization ω.1) Γ.policy ω.2 i :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    have hz : inclusionCount (drawsRealization ω.1) Γ.policy ω.2 i = 0 :=
      congrArg Fin.val (hzero i)
    exact (Nat.ne_of_gt hpos) hz
  obtain ⟨belief, hopt⟩ := hj
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
  have hfill := Finite.optimal_fills c _ _ (hopt ℓ (ω.2 j)) i
    (by change i ∉ allocation (drawsRealization ω.1) Γ.policy ω.2 j; simp [hempty]) hpos
  change (allocation (drawsRealization ω.1) Γ.policy ω.2 j).card = c at hfill
  rw [hempty, Finset.card_empty] at hfill
  omega

theorem ae_no_overbid_userLaw (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsEquilibrium Γ) :
    ∀ᵐ d ∂(userLaw Γ), 0 < d.1.2.routeCount → d.1.2.bid ≤ max (d.1.1 - Γ.g) 0 := by
  classical
  have hall : ∀ᵐ d ∂(userLaw Γ), ∀ j : Fin n, d ∉ overbidAt Γ.g j :=
    ae_all_iff.mpr fun j => measure_eq_zero_iff_ae_notMem.mp
      (measure_overbidAt_zero Γ hm hc hΓ.users j (hΓ.proposers j))
  filter_upwards [hall] with d hd hk
  by_contra hb
  have hcard : 0 < (firstK d.2 d.1.2.routeCount).card := by
    rw [card_firstK _ _ d.1.2.routeCount_le]
    exact hk
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  exact hd j ⟨hj, lt_of_not_ge hb⟩

theorem ae_no_overbid_compProd (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsEquilibrium Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.routeCount → x.2.bid ≤ max (x.1 - Γ.g) 0 := by
  have h := Measure.ae_ae_of_ae_prod (ae_no_overbid_userLaw Γ hm hc hΓ)
  filter_upwards [h] with x hx
  obtain ⟨_, hτ⟩ := hx.exists
  exact hτ

theorem ae_no_overbid (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsEquilibrium Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂(Γ.σ v), 0 < a.routeCount → a.bid ≤ max (v - Γ.g) 0 :=
  Measure.ae_ae_of_ae_compProd (ae_no_overbid_compProd Γ hm hc hΓ)

theorem userLaw_value_map (Γ : FiniteGame m n c Seed) :
    (userLaw Γ).map (fun d => d.1.1) = Γ.F := by
  have hf : MeasurePreserving (Prod.fst : ℝ × JointAction n → ℝ) (Γ.F ⊗ₘ Γ.σ) Γ.F :=
    ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩
  exact (hf.comp (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n))).map_eq

theorem alphaGt_le_value_tail (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsEquilibrium Γ) (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    alphaGt Γ j b ≤ Γ.F.real (Set.Ioi (Γ.g + b)) := by
  have hsub : aboveAt j b ≤ᵐ[userLaw Γ] {d : UserDraw n | Γ.g + b < d.1.1} := by
    filter_upwards [ae_no_overbid_userLaw Γ hm hc hΓ] with d hd hreach
    have hk : 0 < d.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hreach.1⟩
      rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
    have hbid := hd hk
    have hmax : b < max (d.1.1 - Γ.g) 0 := lt_of_lt_of_le hreach.2 hbid
    rcases (lt_max_iff).mp hmax with hval | hzero
    · change Γ.g + b < d.1.1
      linarith
    · exact (not_lt_of_ge hb hzero).elim
  have hmeasure := measure_mono_ae hsub
  have heq : userLaw Γ {d : UserDraw n | Γ.g + b < d.1.1} = Γ.F (Set.Ioi (Γ.g + b)) := by
    rw [← userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  change (userLaw Γ (aboveAt j b)).toReal ≤ (Γ.F (Set.Ioi (Γ.g + b))).toReal
  rw [← heq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure

end FCAppendix.Bayes
