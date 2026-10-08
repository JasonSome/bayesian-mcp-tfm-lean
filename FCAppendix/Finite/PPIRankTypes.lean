import FCAppendix.Finite.PPINonrare

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem few_rivals_of_accepts_local_nonneg (Γ : FiniteGame m n c Seed) (j : Fin n)
    (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 ≤ b)
    (ω : Background m n Seed) (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c (beliefReceipts Γ.A belief (presentList ω i b j))
      (Γ.policy j (presentList ω i b j) (ω.2 j)).val) (hacc : Accepts Γ i b j ω) :
    rivals i (aboveAt j (b / a)) ω < c := by
  classical
  set ℓ := presentList ω i b j with hℓ
  set r := beliefReceipts Γ.A belief ℓ with hr
  have hri := beliefReceipts_bounds Γ.A belief ℓ a hA i b hb (presentList_self ω i b j)
  by_contra hmany
  push Not at hmany
  refine Finite.excluded_of_many_better c r _ hopt i ?_ hacc
  rw [rivals_eq_card] at hmany
  refine le_trans hmany (Finset.card_le_card ?_)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    and_true, aboveAt, Set.mem_setOf_eq] at hl
  obtain ⟨hli, hreach, hbid⟩ := hl
  have hsome : ℓ l = some (ω.1 l).1.2.bid := by
    rw [hℓ, presentList_other ω i l hli, if_pos hreach]
  have hrl := beliefReceipts_bounds Γ.A belief ℓ a hA l _ (ω.1 l).1.2.bid_nonneg hsome
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hab : b < a * (ω.1 l).1.2.bid := by
    have := mul_lt_mul_of_pos_left hbid ha
    rwa [mul_div_cancel₀ b (ne_of_gt ha)] at this
  linarith [hri.2, hrl.1]

theorem acceptProb_le_rank_nonneg (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalAtFeasibleLists Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b : ℝ) (hb : 0 ≤ b) :
    acceptProb Γ i b j ≤ binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
  have hu := measurableSet_rivals_lt (Seed := Seed) i (aboveAt j (b / a))
    (measurableSet_aboveAt j (b / a)) c
  have hac := measurableSet_accepts Γ i b j
  have hp : MeasurableSet {ω : Background m n Seed |
      Accepts Γ i b j ω → rivals i (aboveAt j (b / a)) ω < c} := by
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or] using hac.compl.union hu
  have hbounds : ∀ᵐ ω ∂backgroundLaw Γ,
      Accepts Γ i b j ω → rivals i (aboveAt j (b / a)) ω < c := by
    apply (Measure.ae_prod_iff_ae_ae hp).mpr
    obtain ⟨belief, hopt⟩ := hj
    apply Filter.Eventually.of_forall
    intro d
    let ℓ := presentDrawList d i b j
    have hs := hopt ℓ (presentDrawList_feasible d i b hb j)
    have hseeds := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hs
    filter_upwards [hseeds] with s hS
    exact few_rivals_of_accepts_local_nonneg Γ j i a ha hA b hb (d, s) (belief ℓ) hS
  rw [alphaGt, ← prob_rivals_lt Γ i _ (measurableSet_aboveAt j (b / a)) c, acceptProb]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hbounds)

theorem ppi_meanAcceptProb_le_rank (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    meanAcceptProb Γ i b ≤ binomBelow (m - 1) (alphaGt Γ j b) c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hbound (l : Fin n) : acceptProb Γ i b l ≤ binomBelow (m - 1) (alphaGt Γ j b) c := by
    have hh := acceptProb_le_rank_nonneg Γ l (hj l) i 1 (by norm_num)
      (fun r _ _ => by simp [hA, Schedule.ppi]) b hb
    simpa only [div_one, alphaGt_eq Γ l j b] using hh
  have hs := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hbound l)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  unfold meanAcceptProb
  have hh := mul_le_mul_of_nonneg_left hs (one_div_pos.mpr hn).le
  simpa only [← mul_assoc, one_div_mul_cancel hn.ne', one_mul] using hh

theorem singleton_success (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (a : JointAction n) (hk : a.routeCount = 1) :
    ((problem Γ i).outcome a).success = meanAcceptProb Γ i a.bid := by
  have hle := load_le_routeCount_mul_success Γ i a
  have hls : ((problem Γ i).outcome a).load = ((problem Γ i).outcome a).success := by
    simp only [hk, Nat.cast_one, one_mul] at hle
    exact le_antisymm hle ((problem Γ i).outcome a).success_le_load
  rw [← hls, load_eq_mean Γ hn i a, hk, Nat.cast_one, one_mul]

theorem singleton_bestResponse_bid_le (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (i : Fin m) {v w : ℝ} (hvw : v < w) {a b : JointAction n}
    (ha : (problem Γ i).BestResponse v a) (hb : (problem Γ i).BestResponse w b)
    (hka : a.routeCount = 1) (hkb : b.routeCount = 1)
    (hpos : 0 < ((problem Γ i).outcome a).success) : a.bid ≤ b.bid := by
  have hs := (problem Γ i).success_order v w hvw a b ha hb
  have hic := ha b
  have hnonneg := (problem Γ i).envelope_nonneg v
  rw [← (problem Γ i).bestResponse_iff_attains v a |>.mp ha,
    singleton_payoff Γ hn i a hka] at hnonneg
  rw [singleton_payoff Γ hn i a hka, singleton_payoff Γ hn i b hkb] at hic
  rw [singleton_success Γ hn i a hka, singleton_success Γ hn i b hkb] at hs
  rw [singleton_success Γ hn i a hka] at hpos
  have hsur : 0 ≤ v - Γ.g - a.bid := by nlinarith
  by_contra hnot
  have hlt : b.bid < a.bid := lt_of_not_ge hnot
  have hm := mul_le_mul_of_nonneg_left hs hsur
  have hp := mul_pos (sub_pos.mpr hlt) hpos
  nlinarith

theorem ppi_nonrare_bestResponse_order {N : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (i : Fin (N + 1)) (j : Fin n)
    (V : Set ℝ) (ε : ℝ) (hε : 0 < ε)
    (hroute : ∀ w ∈ V, ∀ b : JointAction n, (problem Γ i).BestResponse w b →
      1 ≤ b.routeCount → ε / n ≤ binomBelow N (alphaGt Γ j b.bid) c →
      b.routeCount = 1)
    (v : ℝ) (a : JointAction n) (ha : (problem Γ i).BestResponse v a)
    (hka : a.routeCount = 1) (hapos : 0 < a.bid)
    (haq : ε ≤ binomBelow N (alphaGt Γ j a.bid) c)
    (w : ℝ) (hw : w ∈ V) (b : JointAction n) (hb : (problem Γ i).BestResponse w b) :
    (v < w → b.routeCount = 1 ∧ a.bid ≤ b.bid) ∧
    (w < v → 1 ≤ b.routeCount → b.bid ≤ a.bid) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hasa : ε ≤ ((problem Γ i).outcome a).success := by
    rw [singleton_success Γ hn i a hka,
      ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j a.bid hapos]
    exact haq
  constructor
  · intro hvw
    have hsb := hasa.trans ((problem Γ i).success_order v w hvw a b ha hb)
    have hkb : 1 ≤ b.routeCount := by
      by_contra hh
      have hz : b.routeCount = 0 := by omega
      have hl := load_le_routeCount_mul_success Γ i b
      rw [hz, Nat.cast_zero, zero_mul] at hl
      linarith [((problem Γ i).outcome b).success_le_load]
    have hbrank := ppi_meanAcceptProb_le_rank Γ hA hj i j b.bid b.bid_nonneg
    simp only [Nat.add_sub_cancel] at hbrank
    have hbq : ε / n ≤ binomBelow N (alphaGt Γ j b.bid) c := by
      apply (div_le_iff₀ hnR).mpr
      have hc := success_le_n_meanAcceptProb Γ hn i b
      nlinarith
    have hk := hroute w hw b hb hkb hbq
    exact ⟨hk, singleton_bestResponse_bid_le Γ hn i hvw ha hb hka hk (hε.trans_le hasa)⟩
  · intro hwv hkb
    by_contra hnot
    have hab : a.bid < b.bid := lt_of_not_ge hnot
    have hbpos := hapos.trans hab
    have hrank := rank_probability_monotone_bid Γ i j hab.le
    simp only [Nat.add_sub_cancel] at hrank
    have hbq := haq.trans hrank
    have hbq' : ε / n ≤ binomBelow N (alphaGt Γ j b.bid) c := by
      apply (div_le_iff₀ hnR).mpr
      nlinarith
    have hk := hroute w hw b hb hkb hbq'
    have hsb : 0 < ((problem Γ i).outcome b).success := by
      rw [singleton_success Γ hn i b hk,
        ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j b.bid hbpos]
      exact hε.trans_le hbq
    exact hab.not_ge (singleton_bestResponse_bid_le Γ hn i hwv hb ha hk hka hsb)

theorem ppi_nonrare_rank_eq_value_tail {N : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    [NullSingletonClass Γ.F]
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hu : UsersOptimal Γ)
    (i : Fin (N + 1)) (j : Fin n) (V : Set ℝ) (hV : ∀ᵐ w ∂Γ.F, w ∈ V)
    (ε : ℝ) (hε : 0 < ε)
    (hroute : ∀ w ∈ V, ∀ b : JointAction n, (problem Γ i).BestResponse w b →
      1 ≤ b.routeCount → ε / n ≤ binomBelow N (alphaGt Γ j b.bid) c → b.routeCount = 1)
    (v : ℝ) (a : JointAction n) (ha : (problem Γ i).BestResponse v a)
    (hka : a.routeCount = 1) (hapos : 0 < a.bid)
    (haq : ε ≤ binomBelow N (alphaGt Γ j a.bid) c) :
    alphaGt Γ j a.bid = Γ.F.real (Ioi v) / n := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hbr : ∀ᵐ d ∂userLaw Γ, (problem Γ i).BestResponse d.1.1 d.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_bestResponse_compProd Γ hu i)
  have hpres : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw Γ) Γ.F :=
    ⟨measurable_fst.comp measurable_fst, userLaw_value_map Γ⟩
  have hvne : ∀ᵐ w ∂Γ.F, w ≠ v := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton v : Γ.F {v} = 0))
  have hvalues := hpres.quasiMeasurePreserving.ae (hV.and hvne)
  have hties := measure_eq_zero_iff_ae_notMem.mp (hatom j a.bid hapos)
  let E : Set (ℝ × JointAction n) := {x | v < x.1}
  let R : Set (Equiv.Perm (Fin n)) := {τ | j ∈ firstK τ 1}
  have hevents : aboveAt j a.bid =ᵐ[userLaw Γ] E ×ˢ R := by
    filter_upwards [hbr, hvalues, hties] with d hd hv hne
    have hord := ppi_nonrare_bestResponse_order Γ hA hatom hj i j V ε hε hroute
      v a ha hka hapos haq d.1.1 hv.1 d.1.2 hd
    apply propext
    constructor
    · intro habove
      have hk : 1 ≤ d.1.2.routeCount := by
        have hcard := Finset.card_pos.mpr ⟨j, habove.1⟩
        rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
      have hw : v < d.1.1 := by
        rcases lt_or_gt_of_ne hv.2 with hw | hw
        · exact (habove.2.not_ge (hord.2 hw hk)).elim
        · exact hw
      have hr := (hord.1 hw).1
      exact ⟨hw, by simpa only [R, mem_setOf_eq, ← hr] using habove.1⟩
    · rintro ⟨hw, hr⟩
      have hord' := hord.1 hw
      have hreach : j ∈ firstK d.2 d.1.2.routeCount := by
        simpa only [R, mem_setOf_eq, hord'.1] using hr
      have hneq : a.bid ≠ d.1.2.bid := fun he => hne ⟨hreach, he.symm⟩
      exact ⟨hreach, lt_of_le_of_ne hord'.2 hneq⟩
  have hE : (Γ.F ⊗ₘ Γ.σ) E = Γ.F (Ioi v) := by
    calc
      (Γ.F ⊗ₘ Γ.σ) E = (Γ.F ⊗ₘ Γ.σ).fst (Ioi v) := by
        rw [Measure.fst, Measure.map_apply measurable_fst measurableSet_Ioi]
        rfl
      _ = Γ.F (Ioi v) := by rw [Measure.fst_compProd]
  unfold alphaGt
  rw [measureReal_congr hevents, Measure.real, userLaw, Measure.prod_prod,
    ENNReal.toReal_mul, hE]
  change Γ.F.real (Ioi v) * (permLaw n).real R = _
  rw [permLaw_mem_firstK n 1 hn hn j, Nat.cast_one]
  ring

namespace NearPPIAssumptions

theorem ppi_nonrare_rank_value_uniform_on_compact
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ v ∈ V, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act → 1 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k)
        (⟨0, by have hn := h.proposers_two; omega⟩ : Fin n) act.bid) (C k) →
      ∀ j : Fin n, alphaGt (Γ k) j act.bid = F.real (Ioi v) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) h.proposers_two)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) h.proposers_two)
  have he : 0 < ε / n := div_pos hε hn
  have he' : ε / n ≤ ε := by apply (div_le_iff₀ hn).mpr; nlinarith
  filter_upwards [h.ppi_nonrare_one_route_uniform_on_compact i hA hV (ε / n) he,
    h.ppi_rank_nonrare_bids_pos i hA ε hε] with k hk hp
  intro v hv act hbr hroute hq j
  haveI : NullSingletonClass (Γ k).F := by rw [h.common_values k]; infer_instance
  have hact1 := hk v hv act hbr hroute (he'.trans hq)
  have hactpos := (half_pos h.price_pos).trans (hp act.bid hq)
  have hsupport : ∀ᵐ w ∂(Γ k).F, w ∈ V := by rw [h.common_values k]; exact hsupp
  let j₀ : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  rw [alphaGt_eq (Γ k) j j₀]
  have hid := ppi_nonrare_rank_eq_value_tail (Γ k) (hA k) (h.visible_atomless k)
    (h.feasible_continuations k) (h.equilibria k).users (i k) j₀ V hsupport ε hε hk
    v act hbr hact1 hactpos hq
  simpa only [h.common_values k] using hid

end NearPPIAssumptions
end FCAppendix.Bayes
