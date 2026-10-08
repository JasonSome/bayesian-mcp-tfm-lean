import FCAppendix.PayOnce.ActualProfileWeights

namespace FCAppendix.PayOnce.TruncatedFOC
open MeasureTheory Filter Topology Set OwnImpact RareSuccessSlope
open scoped BigOperators

noncomputable def truncationFactor (w : ℝ) : ℝ := (1 + max w 0)⁻¹
noncomputable def truncatedValue (w : ℝ) : ℝ := truncationFactor w * max w 0
noncomputable def truncatedBid (w b : ℝ) : ℝ := min 1 (max 0 (truncationFactor w*b))

theorem measurable_truncationFactor : Measurable truncationFactor :=
  (measurable_const.add (measurable_id.max measurable_const)).inv

theorem truncationFactor_bounds (w : ℝ) : truncationFactor w ∈ Ioc (0 : ℝ) 1 := by
  have hh : (1 : ℝ) ≤ 1 + max w 0 := by linarith [le_max_right w 0]
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ hh⟩

theorem measurable_truncatedValue : Measurable truncatedValue :=
  measurable_truncationFactor.mul (measurable_id.max measurable_const)

theorem truncatedValue_bounds (w : ℝ) : truncatedValue w ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < 1 + max w 0 := by linarith [le_max_right w 0]
  change 0 ≤ (1+max w 0)⁻¹ * max w 0 ∧ (1+max w 0)⁻¹ * max w 0 ≤ 1
  rw [mul_comm, ← div_eq_mul_inv, div_le_one hd]
  exact ⟨div_nonneg (le_max_right w 0) hd.le, by linarith⟩

theorem truncatedValue_pos {w : ℝ} (hw : 0 < w) : 0 < truncatedValue w := by
  exact mul_pos (truncationFactor_bounds w).1 (lt_max_of_lt_left hw)

theorem measurable_truncatedBid : Measurable (fun z : ℝ × ℝ => truncatedBid z.1 z.2) :=
  measurable_const.min (measurable_const.max ((measurable_truncationFactor.comp measurable_fst).mul measurable_snd))

theorem truncatedBid_bounds (w b : ℝ) : truncatedBid w b ∈ Icc (0 : ℝ) 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem truncatedBid_eq {w b : ℝ} (hb : 0 ≤ b) (hbw : b ≤ max w 0) :
    truncatedBid w b = truncationFactor w*b := by
  have hb0 := mul_nonneg (truncationFactor_bounds w).1.le hb
  have hb1 := (mul_le_mul_of_nonneg_left hbw (truncationFactor_bounds w).1.le).trans
    (truncatedValue_bounds w).2
  unfold truncatedBid
  rw [max_eq_right hb0, min_eq_right hb1]

theorem truncatedBid_le_bid {w b : ℝ} (hb : 0 ≤ b) : truncatedBid w b ≤ b := by
  apply (min_le_right _ _).trans
  apply max_le hb
  exact mul_le_of_le_one_left hb (truncationFactor_bounds w).2

theorem integral_average_correction_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 2 ≤ n) (p T weight : Ω → ι → ℝ)
    (hp : ∀ i, Measurable (fun ω => p ω i))
    (hT : ∀ i, Measurable (fun ω => T ω i))
    (hw : ∀ i, Measurable (fun ω => weight ω i))
    {M : ℝ} (hM : 0 ≤ M)
    (hpb : ∀ ω i, p ω i ∈ Icc (0 : ℝ) 1)
    (hTb : ∀ ω i, T ω i ∈ Icc (0 : ℝ) M)
    (hwb : ∀ ω i, weight ω i ∈ Icc (0 : ℝ) 1)
    (hsum : ∀ᵐ ω ∂P, ∑ i ∈ interiorSet (p ω), weight ω i ≤ 1)
    {m : ℝ} (hm : 0 < m) :
    (∫ ω, (∑ i, T ω i*baseSlope n (p ω i))/m ∂P) ≤
      (∫ ω, (∑ i, T ω i*weightedSlope n (p ω i) (weight ω i))/m ∂P) + M*(n:ℝ)^2/m := by
  classical
  let L := fun ω => ∑ i, T ω i*baseSlope n (p ω i)
  let R := fun ω => ∑ i, T ω i*weightedSlope n (p ω i) (weight ω i)
  have hLI : Integrable L P := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.of_bound ((hT i).mul ((measurable_baseSlope n).comp (hp i))).aestronglyMeasurable (M*(n:ℝ)^2)
    exact Filter.Eventually.of_forall fun ω => by
      change ‖T ω i*baseSlope n (p ω i)‖ ≤ M*(n:ℝ)^2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hTb ω i).1 (baseSlope_bounds hn (hpb ω i)).1)]
      exact mul_le_mul (hTb ω i).2 (baseSlope_bounds hn (hpb ω i)).2
        (baseSlope_bounds hn (hpb ω i)).1 hM
  have hRI : Integrable R P := by
    apply integrable_finsetSum
    intro i _
    apply Integrable.of_bound ((hT i).mul ((measurable_weightedSlope n).comp ((hp i).prodMk (hw i)))).aestronglyMeasurable (M*(n:ℝ)^2)
    exact Filter.Eventually.of_forall fun ω => by
      change ‖T ω i*weightedSlope n (p ω i) (weight ω i)‖ ≤ M*(n:ℝ)^2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hTb ω i).1 (weightedSlope_bounds hn (hpb ω i) (hwb ω i)).1)]
      exact mul_le_mul (hTb ω i).2 (weightedSlope_bounds hn (hpb ω i) (hwb ω i)).2
        (weightedSlope_bounds hn (hpb ω i) (hwb ω i)).1 hM
  have hh := integral_mono_ae (hLI.div_const m) ((hRI.div_const m).add (integrable_const (M*(n:ℝ)^2/m)))
    (hsum.mono fun ω hω => by
      have he := sum_truncated_correction_le hn (p ω) (T ω) (weight ω) hM (hpb ω) (hTb ω)
        (fun i => (hwb ω i).1) hω
      change L ω/m ≤ R ω/m + M*(n:ℝ)^2/m
      rw [← add_div, div_le_div_iff_of_pos_right hm]
      dsimp only [L, R]
      linarith)
  simpa only [Pi.add_apply, integral_add (hRI.div_const m) (integrable_const _),
    integral_const, probReal_univ, one_smul] using hh

end FCAppendix.PayOnce.TruncatedFOC

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.TruncatedFOC PayOnce.OwnImpact PayOnce.RareSuccessSlope
open scoped BigOperators ProbabilityTheory
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def profileTruncatedValue {n : ℕ} (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (i : Fin m) : ℝ := truncatedValue ((d i).1.1-Γ.g)

noncomputable def profileTruncatedBid {n : ℕ} (Γ : FiniteGame m n c Seed)
    (d : UserProfile m n) (i : Fin m) : ℝ := truncatedBid ((d i).1.1-Γ.g) (d i).1.2.bid

theorem measurable_profileTruncatedValue {n : ℕ} (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun d => profileTruncatedValue Γ d i) :=
  measurable_truncatedValue.comp
    ((measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))).sub_const Γ.g)

theorem measurable_profileTruncatedBid {n : ℕ} (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun d => profileTruncatedBid Γ d i) :=
  measurable_truncatedBid.comp
    (((measurable_fst.comp (measurable_fst.comp (measurable_pi_apply i))).sub_const Γ.g).prodMk
      ((measurable_bid n).comp (measurable_snd.comp (measurable_fst.comp (measurable_pi_apply i)))))

theorem exists_bounded_actual_profile_FOC {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    let p := analyticalProfileMarginal Γ (by omega) hcm.le
    ∃ weight : UserProfile m (k+1) → Fin m → ℝ,
      (∀ i, Measurable (fun d => weight d i)) ∧
      (∀ d i, weight d i ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ d ∂userProfileLaw Γ, ∑ i ∈ interiorSet (p d), weight d i ≤ 1) ∧
      (∀ i, (∫ d, profileTruncatedValue Γ d i *
        weightedSlope (k+1) (p d i) (weight d i) ∂userProfileLaw Γ) =
        ∫ d, profileTruncatedBid Γ d i *
          (success (k+1) (p d i)+weightedSlope (k+1) (p d i) (weight d i)) ∂userProfileLaw Γ) := by
  dsimp only
  let hn : 2 ≤ k+1 := by omega
  obtain ⟨weight, hw, hwb, _, hderiv, _, hsum⟩ :=
    exists_actual_profile_weights Γ hk hcm.le hatom hroute hbid
  refine ⟨fun d i => weight i ((d i).1.2.bid,rivalBids i d),
    fun i => (hw i).comp (focalBid_rivalBids_measurePreserving Γ i).measurable, (fun d i => hwb i ((d i).1.2.bid,rivalBids i d)),
    hsum, ?_⟩
  have hno := ae_no_overbid_compProd_onPath Γ (hc.trans hcm) hc
    (posterior_isAEEquilibrium Γ hu B hB)
  have hbounded : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      0 < x.1-Γ.g ∧ x.2.bid ≤ max (x.1-Γ.g) 0 := by
    filter_upwards [hno, hroute, hbid] with x hx hr hb
    have hbn := hx (by rw [hr]; omega)
    refine ⟨?_, hbn⟩
    by_contra hnot
    rw [max_eq_right (le_of_not_gt hnot)] at hbn
    linarith
  let τ := fun v => truncationFactor (v-Γ.g)
  have hτ : Measurable τ := measurable_truncationFactor.comp (measurable_id.sub_const Γ.g)
  have hτw : Integrable (fun x : ℝ × JointAction (k+1) => τ x.1*(x.1-Γ.g)) (Γ.F ⊗ₘ Γ.σ) := by
    apply Integrable.of_bound ((hτ.comp measurable_fst).mul (measurable_fst.sub_const Γ.g)).aestronglyMeasurable 1
    filter_upwards [hbounded] with x hx
    change ‖truncationFactor (x.1-Γ.g)*(x.1-Γ.g)‖ ≤ 1
    have he : truncationFactor (x.1-Γ.g)*(x.1-Γ.g) = truncatedValue (x.1-Γ.g) := by
      simp only [truncatedValue, max_eq_left hx.1.le]
    rw [he, Real.norm_eq_abs, abs_of_nonneg (truncatedValue_bounds _).1]
    exact (truncatedValue_bounds _).2
  have hτb : Integrable (fun x : ℝ × JointAction (k+1) => τ x.1*x.2.bid) (Γ.F ⊗ₘ Γ.σ) := by
    apply Integrable.of_bound ((hτ.comp measurable_fst).mul ((measurable_bid (k+1)).comp measurable_snd)).aestronglyMeasurable 1
    filter_upwards [hbounded] with x hx
    change ‖truncationFactor (x.1-Γ.g)*x.2.bid‖ ≤ 1
    rw [← truncatedBid_eq x.2.bid_nonneg hx.2, Real.norm_eq_abs,
      abs_of_nonneg (truncatedBid_bounds _ _).1]
    exact (truncatedBid_bounds _ _).2
  intro i
  have hid := integral_actual_truncated_FOC Γ hk hcm.le hA hG hu B hB hsym hatom hroute hbid
    i τ hτ hτw hτb (weight i) (hw i) (hwb i) (hderiv i)
  have hpres : MeasurePreserving (fun d : UserProfile m (k+1) => (d i).1)
      (userProfileLaw Γ) (Γ.F ⊗ₘ Γ.σ) :=
    (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).comp
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i)
  have hprof := hpres.quasiMeasurePreserving.ae hbounded
  calc
    _ = (∫ d, (τ (d i).1.1*((d i).1.1-Γ.g))*
        weightedSlope (k+1) (analyticalProfileMarginal Γ hn hcm.le d i)
          (weight i ((d i).1.2.bid,rivalBids i d)) ∂userProfileLaw Γ) := by
      apply integral_congr_ae
      filter_upwards [hprof] with d hd
      simp only [profileTruncatedValue, truncatedValue, τ, max_eq_left hd.1.le]
    _ = _ := hid
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hprof] with d hd
      rw [profileTruncatedBid, truncatedBid_eq (d i).1.2.bid_nonneg hd.2]

end FCAppendix.Bayes
