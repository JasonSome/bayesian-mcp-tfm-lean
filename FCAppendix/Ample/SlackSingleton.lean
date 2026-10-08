import FCAppendix.Ample.SlackAsymptotics

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Finset Filter Topology Real
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma positiveMultiMass_sum (Γ : FiniteGame m n c Seed) (hn : 0 < n) :
    positiveRouteMass Γ (fun k => 2 ≤ k) =
      ∑ j ∈ Finset.Icc 2 n, positiveRouteMass Γ (fun k => k = j) := by
  have hsplit := positiveRouteMass_split Γ
  rw [positiveRouteMass_sum_classes, positiveRouteMass_class_eq Γ (by omega : 1 ≤ 1)] at hsplit
  have he : (Finset.Icc 1 n).erase 1 = Finset.Icc 2 n := by
    ext j
    simp only [mem_erase, Finset.mem_Icc]
    omega
  have hsum := Finset.sum_erase_add (s := Finset.Icc 1 n)
    (f := visibleClassMass Γ 0) (a := 1) (Finset.mem_Icc.mpr ⟨le_rfl, hn⟩)
  rw [he] at hsum
  have hclasses : (∑ j ∈ Finset.Icc 2 n, positiveRouteMass Γ (fun k => k = j)) =
      ∑ j ∈ Finset.Icc 2 n, visibleClassMass Γ 0 j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact positiveRouteMass_class_eq Γ (by have := (Finset.mem_Icc.mp hj).1; omega)
  rw [hclasses]
  linarith

lemma exists_large_multiroute_class (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    {H : ℝ} (hH : 0 < H) (hmass : H ≤ positiveRouteMass Γ (fun k => 2 ≤ k)) :
    ∃ k ∈ Finset.Icc 2 n, H / ((n : ℝ) + 1) < positiveRouteMass Γ (fun j => j = k) := by
  classical
  by_contra hh
  have hb : ∀ k ∈ Finset.Icc 2 n,
      positiveRouteMass Γ (fun j => j = k) ≤ H / ((n : ℝ) + 1) := by
    intro k hk
    exact le_of_not_gt (fun hx => hh ⟨k, hk, hx⟩)
  have hs := Finset.sum_le_sum hb
  rw [← positiveMultiMass_sum Γ hn] at hs
  have hcard : (Finset.Icc 2 n).card ≤ n := by simp
  have hbound : ((Finset.Icc 2 n).card : ℝ) * (H / ((n : ℝ) + 1)) ≤
      n * (H / ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hstrict : (n : ℝ) * (H / ((n : ℝ) + 1)) < H := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    nlinarith
  simp only [sum_const, nsmul_eq_mul] at hs
  linarith

theorem ppi_singleton_floor_of_source_sequence
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (F : Measure ℝ) (g ρ : ℝ) (hn : 0 < n) (hρ : 0 < ρ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hactive : 0 < F.real (Ioi g))
    (hpop : Tendsto M atTop atTop)
    (hcap : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 ρ))
    (hguards : ∀ᶠ t in atTop, 1 < M t ∧ 0 < C t ∧ C t ≤ M t - 1)
    (husers : ∀ t, UsersOptimal (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hppi : ∀ t, (Γ t).A = Schedule.ppi n)
    (hfree : ∀ t, FreeDuplicateBase (Γ t))
    (habstain : ∀ t, NonpositiveAbstention (Γ t))
    (hzero : ∀ t, RejectsZeroBids (Γ t)) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ ∀ᶠ t in atTop,
      a₁ ≤ positiveRouteMass (Γ t) (fun k => k = 1) := by
  letI : IsProbabilityMeasure F := by
    rw [← hF 0]
    infer_instance
  have hactive_one : F.real (Ioi g) ≤ 1 := measureReal_le_one
  have hpart : ∀ᶠ t in atTop,
      positiveRouteMass (Γ t) (fun _ => True) = F.real (Ioi g) ∧
      submittedMarginal (Γ t) = Ample.contactMarginal n (visibleClassMass (Γ t) 0) := by
    filter_upwards [hguards] with t ht
    refine ⟨?_, ppi_submitted_eq_positive (Γ t) (by omega) hn ht.2.1
      (hppi t) (hatom t) (hpolicy t) (husers t) (habstain t) (hzero t)⟩
    simpa only [hF t, hg t] using
      ppi_positiveParticipation_eq (Γ t) (by omega) hn ht.2.1
        (hppi t) (hatom t) (hpolicy t) (husers t) (habstain t) (hzero t)
  have hcompact {d : ℝ} (hd : 0 < d) :
      ∃ ε H : ℝ, 0 < ε ∧ ε < H ∧
        ∀ t, (Γ t).F.real {v | (Γ t).g < v ∧ v - (Γ t).g ∉ Set.Icc ε H} < d := by
    obtain ⟨ε, H, hε, hεH, ht⟩ := Ample.exists_compact_positive_band F g hd
    exact ⟨ε, H, hε, hεH, fun t => by simpa only [hF t, hg t] using ht⟩
  let H : ℝ := F.real (Ioi g)
  have hH : 0 < H := hactive
  have hH1 : H ≤ 1 := hactive_one
  let q : ℝ := (H / 2) / ((n : ℝ) + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  let s : ℝ := (q / 4) / Ample.subsetFactor n
  have hs : 0 < s := div_pos (by positivity) (Ample.subsetFactor_pos n)
  have hf1 : 1 ≤ Ample.subsetFactor n := by
    unfold Ample.subsetFactor
    exact le_add_of_nonneg_right (sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hs1 : s ≤ 1 := by
    dsimp [s]
    apply (div_le_iff₀ (Ample.subsetFactor_pos n)).mpr
    linarith
  let L : ℝ := -log s
  have hL : 0 ≤ L := neg_nonneg.mpr (log_nonpos hs.le hs1)
  let J : ℝ := L + 1
  have hJ : 0 < J := by dsimp [J]; linarith
  let θ : ℝ := 2 * (J + 1) / ρ
  have hθ : 0 < θ := div_pos (by positivity) hρ
  have hθeq : θ * (ρ / 2) = J + 1 := by
    dsimp [θ]
    field_simp [hρ.ne']
  let δ : ℝ := min (H / 8) (exp (-θ) / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδH : δ ≤ H / 8 := min_le_left _ _
  have hδθ : 2 * δ ≤ exp (-θ) := by
    have hh : δ ≤ exp (-θ) / 4 := min_le_right _ _
    have he := exp_pos (-θ)
    linarith
  obtain ⟨ε, H₀, hε, hεH, ht₀⟩ := hcompact (d := q / 4) (by positivity)
  obtain ⟨ε₁, H₁, hε₁, hεH₁, ht₁⟩ := hcompact (d := δ / 2) (by positivity)
  have hH₀ : 0 ≤ H₀ := (hε.trans hεH).le
  have hH₁ : 0 ≤ H₁ := (hε₁.trans hεH₁).le
  have hgain := Ample.eventually_two_error_gain hpop hε hH₀ hH₁ hJ
    (show L < J by dsimp [J]; linarith)
  have hcapLower : ∀ᶠ t in atTop, (ρ / 2) * M t ≤ C t := by
    filter_upwards [hguards,
      hcap.eventually_const_lt (show ρ / 2 < ρ by linarith [hρ])]
      with t ht hct
    have hmR : (0 : ℝ) < M t := by exact_mod_cast (show 0 < M t by omega)
    have hh := (lt_div_iff₀ hmR).mp hct
    linarith
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hguards, hpart,
    hgain, hcapLower] with t ht hp hg hct
  by_contra hnot
  have hsing : positiveRouteMass (Γ t) (fun k => k = 1) < δ := lt_of_not_ge hnot
  have hmulti : H / 2 ≤ positiveRouteMass (Γ t) (fun k => 2 ≤ k) := by
    have hh := positiveRouteMass_split (Γ t)
    rw [hp.1] at hh
    change H = _ at hh
    linarith
  obtain ⟨k, hk, hkmass⟩ := exists_large_multiroute_class (Γ t) hn
    (show 0 < H / 2 by positivity) hmulti
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
  change q < positiveRouteMass (Γ t) (fun j => j = k) at hkmass
  let i : Fin (M t) := ⟨0, by omega⟩
  obtain ⟨w₀, lo, hw₀, hlo, hb₀, hr₀, hk₀, hl₀, hu₀⟩ :=
    select_supported_route_band (Γ t) (hatom t) (husers t) (habstain t)
      i (fun j => j = k) (lo := q / 4) (hi := q / 2)
      (by positivity) (by linarith) (by linarith) (by convert ht₀ t using 1; ring)
  obtain ⟨w₁, hi, hw₁, hhi, hb₁, hr₁, hk₁, hl₁, hu₁⟩ :=
    select_supported_route_band (Γ t) (hatom t) (husers t) (habstain t)
      i (fun j => 2 ≤ j) (lo := δ / 2) (hi := δ)
      (by positivity) (by linarith) (by linarith) (by convert ht₁ t using 1; ring)
  have hchoose : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
  have htail : s ≤ positiveRouteTail (Γ t) (fun j => j = lo.routeCount) lo.bid /
      (n.choose lo.routeCount : ℝ) := by
    rw [hk₀]
    apply (le_div_iff₀ hchoose).mpr
    calc
      s * (n.choose k : ℝ) ≤ s * Ample.subsetFactor n :=
        mul_le_mul_of_nonneg_left (Ample.choose_le_subsetFactor hkn) hs.le
      _ = q / 4 := div_mul_cancel₀ _ (Ample.subsetFactor_pos n).ne'
      _ ≤ _ := hl₀
  have hfail₀ := ppi_failure_ge_same_count (Γ t) (by omega) (hppi t)
    (hatom t) (hpolicy t) i lo hb₀ (by omega) ht.2.2 hs.le htail
  have hfail : exp (-L * M t) ≤ 1 - ((problem (Γ t) i).outcome lo).success :=
    (Ample.exp_log_le_rival_power hs hs1 (by omega)).trans hfail₀
  have htail₁ : positiveRouteTail (Γ t) (fun _ => True) hi.bid ≤ exp (-θ) := by
    rw [positiveRouteTail_split (Γ t) hi.bid hb₁.le]
    have hh := positiveRouteTail_le_mass (Γ t) (fun k => k = 1) hi.bid
    linarith
  have hr₁' := ppi_rejection_le_small_tail (Γ t) (by omega) hn (hppi t)
    (hatom t) (hpolicy t) i hi.bid hb₁ hθ.le htail₁
  have he : exp (-θ * C t + (M t - 1 : ℕ)) ≤ exp (-J * M t) := by
    apply exp_le_exp.mpr
    have hcθ := mul_le_mul_of_nonneg_left hct hθ.le
    have hN : ((M t - 1 : ℕ) : ℝ) ≤ M t := by exact_mod_cast Nat.sub_le (M t) 1
    rw [← mul_assoc, hθeq] at hcθ
    nlinarith
  have hqhi : 1 - exp (-J * M t) ≤ meanAcceptProb (Γ t) i hi.bid := by
    have hh := hr₁'.trans he
    linarith
  have hbhi := ppi_free_multiroute_bid_bound (Γ t) (hppi t) (hfree t) hn i
    (hε₁.trans_le hw₁.1).le hw₁.2 (exp_pos _).le (by linarith [hg.1]) hi hhi hk₁ hqhi
  exact (ppi_free_no_low_bestReply_of_gain (Γ t) (hppi t) (hfree t) hn i
    hε hw₀.1 hw₀.2 (exp_pos _).le (exp_pos _).le (div_nonneg (mul_nonneg hH₁ (exp_pos _).le) (by linarith [hg.1]))
    lo (sameBidSingleton hn hi) rfl hfail hqhi hbhi hg.2) hlo

namespace FreeBaseAmpleSequence
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {B : ∀ t, PosteriorSystem (Γ t)} {F : Measure ℝ} {g ρ : ℝ}
  (h : FreeBaseAmpleSequence M C Γ B F g ρ)
include h

theorem singleton_floor :
    ∃ a₁ : ℝ, 0 < a₁ ∧ ∀ᶠ t in atTop,
      a₁ ≤ positiveRouteMass (Γ t) (fun k => k = 1) := by
  exact ppi_singleton_floor_of_source_sequence Γ F g ρ h.proposers_pos h.ratio_pos
    h.common_values h.common_fee h.active_pos h.population_grows h.capacity_ratio
    h.eventually_finite_guards h.users h.feasible_continuations h.visible_atomless
    h.ppi h.free h.abstention h.reject_zero

end FreeBaseAmpleSequence
end FCAppendix.Bayes
