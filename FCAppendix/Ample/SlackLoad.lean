import FCAppendix.Ample.SlackSingleton
import FCAppendix.Ample.SlackMultiroute

noncomputable section
namespace FCAppendix.Bayes.FreeBaseAmpleSequence
open MeasureTheory ProbabilityTheory Game Set Finset Filter Topology Real
open scoped BigOperators
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)
include h

theorem submitted_limsup_le :
    ∀ d > 0, ∀ᶠ t in atTop, submittedMarginal (Γ t) ≤ ρ + d := by
  intro d hd
  let p : ℝ := F.real (Ioi g)
  have hp : 0 < p := h.active_pos
  let δ : ℝ := min (d / 4) (p / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδd : δ ≤ d / 4 := min_le_left _ _
  have hδp : δ ≤ p / 4 := min_le_right _ _
  obtain ⟨ε, H, hε, hεH, htight⟩ := h.compact_band (d := δ / 2) (by positivity)
  let J : ℝ := (d / 4) ^ 2
  have hJ : 0 < J := sq_pos_of_pos (by positivity)
  have hexp := (Ample.exp_neg_population_tendsto_zero h.population_grows hJ).const_mul (n : ℝ)
  simp only [mul_zero] at hexp
  filter_upwards [h.eventually_finite_guards, h.eventually_exact_participation,
    h.compact_service hε, h.eventually_capacity_below (d := d / 4) (by positivity),
    hexp.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)] with t ht hpart hs hcap hex
  by_contra hnot
  have hell : ρ + d < submittedMarginal (Γ t) := lt_of_not_ge hnot
  let i : Fin (M t) := ⟨0, by omega⟩
  obtain ⟨w, a, hw, ha, hb, hk, _, hlow, _⟩ :=
    select_supported_route_band (Γ t) (h.visible_atomless t) (h.users t) (h.abstention t)
      i (fun _ => True) (lo := p - δ) (hi := p - δ / 2)
      (by linarith) (by linarith) (by rw [hpart.1]; change p - δ / 2 < p; linarith)
      (by convert htight t using 1; ring)
  have hloss := arrivalMean_loss_le_removedMass (Γ t) h.proposers_pos a.bid hb.le
  rw [← hpart.2, hpart.1] at hloss
  have hmean : ρ + 3 * d / 4 < Ample.contactMarginal n (visibleClassMass (Γ t) a.bid) := by
    change submittedMarginal (Γ t) - _ ≤ p - _ at hloss
    linarith
  have hcap' : (C t : ℝ) ≤ ((M t - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass (Γ t) a.bid) - d / 4) := by
    exact hcap.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  have hq := ppi_acceptance_le_exp_of_mean_excess (Γ t) (by omega) h.proposers_pos
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) i a.bid hb
      (show 0 ≤ d / 4 by positivity) hcap'
  have hq' : meanAcceptProb (Γ t) i a.bid ≤ exp (-J * M t) :=
    hq.trans (Ample.rival_hoeffding_le_full (by omega) (d / 4))
  have hS := success_le_n_meanAcceptProb (Γ t) h.proposers_pos i a
  have hSS := hS.trans (mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg n))
  have hservice : (1 / 2 : ℝ) < ((problem (Γ t) i).outcome a).success :=
    hs i w hw a ha
  have hsmallSuccess : ((problem (Γ t) i).outcome a).success < 1 / 2 :=
    hSS.trans_lt hex
  exact (not_lt_of_ge hservice.le) hsmallSuccess

theorem upper_multiroute_control {a₂ : ℝ} (ha₂ : 0 < a₂)
    (hfloor : ∀ᶠ t in atTop, a₂ ≤ positiveRouteMass (Γ t) (fun k => 2 ≤ k)) :
    ∃ H J : ℝ, 0 < H ∧ 0 < J ∧ ∀ᶠ t in atTop, ∀ i : Fin (M t),
      ∃ w : ℝ, ∃ a : JointAction n,
        0 ≤ w ∧ w ≤ H ∧ (problem (Γ t) i).BestResponse (w + (Γ t).g) a ∧
        0 < a.bid ∧ 2 ≤ a.routeCount ∧
        1 - exp (-J * M t) ≤ meanAcceptProb (Γ t) i a.bid ∧
        a.bid ≤ H * exp (-J * M t) / (1 - exp (-J * M t)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr h.proposers_pos
  let d : ℝ := a₂ / (4 * n)
  have hd : 0 < d := div_pos ha₂ (by positivity)
  let J : ℝ := d ^ 2
  have hJ : 0 < J := sq_pos_of_pos hd
  obtain ⟨ε, H, hε, hεH, htight⟩ := h.compact_band (d := a₂ / 4) (by positivity)
  have hH : 0 < H := hε.trans hεH
  refine ⟨H, J, hH, hJ, ?_⟩
  filter_upwards [h.eventually_finite_guards, h.eventually_exact_participation,
    hfloor, h.submitted_limsup_le d hd, h.eventually_capacity_above hd,
    (Ample.exp_neg_population_tendsto_zero h.population_grows hJ).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with t ht hpart hf hell hc hr
  intro i
  obtain ⟨w, a, hw, ha, hb, hk, hk₂, _, htail⟩ :=
    select_supported_route_band (Γ t) (h.visible_atomless t) (h.users t) (h.abstention t)
      i (fun k => 2 ≤ k) (lo := a₂ / 4) (hi := a₂ / 2)
      (by positivity) (by linarith) (by linarith)
      (by convert htight t using 1; ring)
  have hloss := arrivalMean_loss_ge_removedMulti (Γ t) h.proposers_pos a.bid hb.le
  rw [← hpart.2] at hloss
  have ha₂n : (2 / (n : ℝ)) * (a₂ / 2) = 4 * d := by
    dsimp [d]
    field_simp [hnR.ne']
  have hremove : 4 * d ≤ submittedMarginal (Γ t) -
      Ample.contactMarginal n (visibleClassMass (Γ t) a.bid) := by
    rw [← ha₂n]
    exact (mul_le_mul_of_nonneg_left (by linarith) (by positivity)).trans hloss
  have hmean : Ample.contactMarginal n (visibleClassMass (Γ t) a.bid) ≤ ρ - 3 * d := by
    linarith
  have hc' : ((M t - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass (Γ t) a.bid) + d) ≤ C t := by
    exact (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)).trans hc
  have hq := ppi_rejection_le_exp_of_mean_gap (Γ t) (by omega) h.proposers_pos
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) i a.bid hb hd.le hc'
  have he := Ample.rival_hoeffding_le_full (by omega : 2 ≤ M t) d
  have hq' : 1 - exp (-J * M t) ≤ meanAcceptProb (Γ t) i a.bid := by
    have hh := hq.trans he
    linarith
  have hbid := ppi_free_multiroute_bid_bound (Γ t) (h.ppi t) (h.free t) h.proposers_pos i
    (hε.trans_le hw.1).le hw.2 (exp_pos _).le (by linarith) a ha hk₂ hq'
  exact ⟨w, a, (hε.trans_le hw.1).le, hw.2, ha, hb, hk₂, hq', hbid⟩

theorem strict_submitted_margin :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t in atTop, submittedMarginal (Γ t) ≤ ρ - η := by
  obtain ⟨a₁, ha₁, h₁⟩ := h.singleton_floor
  obtain ⟨a₂, ha₂, h₂⟩ := h.multiroute_floor
  obtain ⟨H₁, J, hH₁, hJ, hupper⟩ := h.upper_multiroute_control ha₂ h₂
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr h.proposers_pos
  let p : ℝ := F.real (Ioi g)
  have hp : 0 < p := h.active_pos
  let v : ℝ := exp (-(n : ℝ)) * min (a₁ / 2) (a₂ / 2) / 4
  have hv : 0 < v := div_pos (mul_pos (exp_pos _) (lt_min (by positivity) (by positivity)))
    (by norm_num)
  let δ : ℝ := min (p / 4) (min (a₁ / 4) (min (a₂ / 4)
    (min (v / (8 * n)) (J * v / (16 * (n : ℝ)^2)))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδp : δ ≤ p / 4 := min_le_left _ _
  have hδ₁ : δ ≤ a₁ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₂ : δ ≤ a₂ / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδv : δ ≤ v / (8 * n) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδJ : δ ≤ J * v / (16 * (n : ℝ)^2) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let θ : ℝ := 4 * n * δ / v
  let L : ℝ := θ * n
  have hθ : 0 < θ := div_pos (by positivity) hv
  have hL : 0 < L := mul_pos hθ hnR
  have hsmall : 4 * n * δ ≤ v := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 8 * n by positivity)).mp hδv
    nlinarith
  have hLJ : L < J := by
    have hh := (le_div_iff₀ (show (0 : ℝ) < 16 * (n : ℝ)^2 by positivity)).mp hδJ
    have hLq : L ≤ J / 4 := by
      dsimp [L, θ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hv).mpr
      nlinarith
    linarith
  obtain ⟨ε, H₀, hε, hεH, htight⟩ := h.compact_band (d := δ / 2) (by positivity)
  have hH₀ : 0 ≤ H₀ := (hε.trans hεH).le
  have hgain := Ample.eventually_two_error_gain h.population_grows
    (show 0 < ε / 2 by positivity) hH₀ hH₁.le hJ hLJ
  have hN : ∀ᶠ t in atTop, (n : ℝ) ≤ 2 * (M t - 1 : ℕ) * δ ^ 2 := by
    have hgrow := (tendsto_natCast_atTop_atTop.comp
      (SimultaneousCongestion.rival_population_scaling h.population_grows).1).const_mul_atTop
        (show 0 < 2 * δ ^ 2 by positivity)
    filter_upwards [hgrow.eventually_ge_atTop (n : ℝ)] with t ht
    dsimp only [Function.comp_def] at ht
    nlinarith
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [h.eventually_finite_guards, h.eventually_exact_participation,
    h₁, h₂, hupper, hgain, hN, h.eventually_capacity_below hδ]
    with t ht hpart hf₁ hf₂ hhi hg hNt hct
  by_contra hnot
  have hell : ρ - δ < submittedMarginal (Γ t) := lt_of_not_ge hnot
  let i : Fin (M t) := ⟨0, by omega⟩
  obtain ⟨w₀, lo, hw₀, hlo, hb₀, hk₀, _, htail₀, _⟩ :=
    select_supported_route_band (Γ t) (h.visible_atomless t) (h.users t) (h.abstention t)
      i (fun _ => True) (lo := p - δ) (hi := p - δ / 2)
      (by linarith) (by linarith) (by rw [hpart.1]; change p - δ / 2 < p; linarith)
      (by convert htight t using 1; ring)
  obtain ⟨w₁, hi, hw₁, hwH₁, hbr₁, hb₁, hk₁, hq₁, hbid₁⟩ := hhi i
  have hremoved : positiveRouteMass (Γ t) (fun _ => True) -
      positiveRouteTail (Γ t) (fun _ => True) lo.bid ≤ δ := by
    rw [hpart.1]
    change p - _ ≤ δ
    linarith
  have htail₁ : a₁ / 2 ≤ positiveRouteTail (Γ t) (fun k => k = 1) lo.bid := by
    have hh := (removedClass_le_removedAll (Γ t) (fun k => k = 1) lo.bid hb₀.le).trans hremoved
    linarith
  have htail₂ : a₂ / 2 ≤ positiveRouteTail (Γ t) (fun k => 2 ≤ k) lo.bid := by
    have hh := (removedClass_le_removedAll (Γ t) (fun k => 2 ≤ k) lo.bid hb₀.le).trans hremoved
    linarith
  have hmean : ρ - 2 * δ ≤ Ample.contactMarginal n (visibleClassMass (Γ t) lo.bid) := by
    have hh := (arrivalMean_loss_le_removedMass (Γ t) h.proposers_pos lo.bid hb₀.le).trans hremoved
    rw [← hpart.2] at hh
    linarith
  have htilt := ppi_failure_ge_small_tilt_of_tails (Γ t) (by omega) h.proposers_pos
    (h.ppi t) (h.visible_atomless t) (h.feasible_continuations t) i lo hb₀
    (show 0 < a₁ / 2 by positivity) (show 0 < a₂ / 2 by positivity) hδ
    htail₁ htail₂ hmean hsmall hct hNt
  have hspeed : exp (-L * M t) / 2 ≤
      exp (-(θ * (M t - 1 : ℕ) * n)) / 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply exp_le_exp.mpr
    have hmN : ((M t - 1 : ℕ) : ℝ) ≤ M t := by exact_mod_cast Nat.sub_le (M t) 1
    have hh := mul_le_mul_of_nonneg_left hmN hL.le
    dsimp [L] at *
    nlinarith
  have hfail : exp (-L * M t) / 2 ≤ 1 - ((problem (Γ t) i).outcome lo).success :=
    hspeed.trans htilt
  have hgain' : H₀ * exp (-J * M t) + H₁ * exp (-J * M t) / (1 - exp (-J * M t)) <
      ε * (exp (-L * M t) / 2) := by
    convert hg.2 using 1; ring
  exact (ppi_free_no_low_bestReply_of_gain (Γ t) (h.ppi t) (h.free t) h.proposers_pos i
    hε hw₀.1 hw₀.2 (by positivity) (exp_pos _).le
    (div_nonneg (mul_nonneg hH₁.le (exp_pos _).le) (by linarith [hg.1]))
    lo (sameBidSingleton h.proposers_pos hi) rfl hfail hq₁ hbid₁ hgain') hlo

end FCAppendix.Bayes.FreeBaseAmpleSequence
