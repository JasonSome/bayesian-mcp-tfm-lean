import FCAppendix.PayOnce.FullListAE

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def profileCountLaw (Γ : FiniteGame m n c Seed) (d : UserProfile m n) (i : Fin m) : CountLaw n :=
  CountLaw.ofMeasure (Measure.pi fun _ : Fin n => Γ.seedLaw) (fun s => playedCount Γ i (d, s))
    ((measurable_playedCount Γ i).comp (measurable_const.prodMk measurable_id))

theorem measurable_profile_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) : Measurable (fun d => (profileCountLaw Γ d i).expect f) := by
  have he : (fun d => (profileCountLaw Γ d i).expect f) =
      fun d => ∫ s, f (playedCount Γ i (d, s)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
    funext d
    exact CountLaw.expect_ofMeasure _ _ _ _
  rw [he]
  have hj := (measurable_of_countable f).comp (measurable_playedCount Γ i)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

noncomputable def profileCoverage (Γ : FiniteGame m n c Seed) (d : UserProfile m n) : ℝ :=
  (∑ i, (profileCountLaw Γ d i).success) / m

noncomputable def profileLoad (Γ : FiniteGame m n c Seed) (d : UserProfile m n) : ℝ :=
  (∑ i, (profileCountLaw Γ d i).load) / m

noncomputable def finiteCoverage (Γ : FiniteGame m n c Seed) : ℝ :=
  ∫ d, profileCoverage Γ d ∂userProfileLaw Γ

noncomputable def finiteLoad (Γ : FiniteGame m n c Seed) : ℝ :=
  ∫ d, profileLoad Γ d ∂userProfileLaw Γ

noncomputable def finiteMultiplicity (Γ : FiniteGame m n c Seed) : ℝ :=
  finiteLoad Γ / finiteCoverage Γ

theorem measurable_profileCoverage (Γ : FiniteGame m n c Seed) : Measurable (profileCoverage Γ) :=
  (Finset.measurable_sum _ (fun i _ => measurable_profile_expect Γ i _)).div_const m

theorem measurable_profileLoad (Γ : FiniteGame m n c Seed) : Measurable (profileLoad Γ) :=
  (Finset.measurable_sum _ (fun i _ => measurable_profile_expect Γ i _)).div_const m

theorem profileCoverage_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m) (d : UserProfile m n) :
    0 ≤ profileCoverage Γ d ∧ profileCoverage Γ d ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => CountLaw.success_nonneg _) hmR.le
  · apply (div_le_one hmR).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => CountLaw.success_le_one (profileCountLaw Γ d i))
    simpa using h

theorem profileLoad_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m) (d : UserProfile m n) :
    0 ≤ profileLoad Γ d ∧ profileLoad Γ d ≤ n := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun i _ => CountLaw.load_nonneg _) hmR.le
  · apply (div_le_iff₀ hmR).mpr
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => CountLaw.load_le_n (profileCountLaw Γ d i))
    simpa [mul_comm] using h

theorem integrable_profileCoverage (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Integrable (profileCoverage Γ) (userProfileLaw Γ) :=
  UnitInterval.integrable _ _ (measurable_profileCoverage Γ)
    (fun d => (profileCoverage_bounds Γ hm d).1) (fun d => (profileCoverage_bounds Γ hm d).2)

theorem integrable_profileLoad (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Integrable (profileLoad Γ) (userProfileLaw Γ) := by
  apply (integrable_const (n : ℝ)).mono' (measurable_profileLoad Γ).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_eq_abs, abs_of_nonneg (profileLoad_bounds Γ hm d).1]
  exact (profileLoad_bounds Γ hm d).2

theorem finiteCoverage_eq_actual (Γ : FiniteGame m n c Seed) :
    finiteCoverage Γ = (∑ i, ∫ ω, successIndicator (playedCount Γ i ω).val ∂backgroundLaw Γ) / m := by
  unfold finiteCoverage profileCoverage
  rw [integral_div, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold profileCountLaw CountLaw.success
    simp_rw [CountLaw.expect_ofMeasure]
    exact (integral_prod _ (CountLaw.integrable_comp (backgroundLaw Γ) _
      (measurable_playedCount Γ i) (fun r => successIndicator r.val))).symm
  · intro i _
    exact UnitInterval.integrable _ _ (measurable_profile_expect Γ i _)
      (fun d => CountLaw.success_nonneg _) (fun d => CountLaw.success_le_one _)

theorem finiteLoad_eq_actual (Γ : FiniteGame m n c Seed) :
    finiteLoad Γ = (∑ i, ∫ ω, ((playedCount Γ i ω).val : ℝ) ∂backgroundLaw Γ) / m := by
  unfold finiteLoad profileLoad
  rw [integral_div, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    unfold profileCountLaw CountLaw.load
    simp_rw [CountLaw.expect_ofMeasure]
    exact (integral_prod _ (CountLaw.integrable_comp (backgroundLaw Γ) _
      (measurable_playedCount Γ i) (fun r => (r.val : ℝ)))).symm
  · intro i _
    apply (integrable_const (n : ℝ)).mono' (measurable_profile_expect Γ i _).aestronglyMeasurable
    filter_upwards [] with d
    rw [Real.norm_eq_abs]
    change |(profileCountLaw Γ d i).load| ≤ n
    rw [abs_of_nonneg (CountLaw.load_nonneg _)]
    exact CountLaw.load_le_n _

theorem average_success_le (hm : 0 < m) (n : ℕ) (p : Fin m → ℝ)
    (hp1 : ∀ i, p i ≤ 1) :
    (∑ i, PayOnce.success n (p i)) / m ≤ PayOnce.success n ((∑ i, p i) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hweight : ∑ _i : Fin m, (1 / (m : ℝ)) = 1 := by simp [ne_of_gt hmR]
  have hpow := (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := (Finset.univ : Finset (Fin m))) (w := fun _ => 1 / (m : ℝ))
    (p := fun i => 1 - p i) (fun _ _ => (one_div_pos.mpr hmR).le) hweight
    (fun i _ => sub_nonneg.mpr (hp1 i))
  simp only [smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hpow
  have hmean : 1 / (m : ℝ) * ((m : ℝ) - ∑ i, p i) = 1 - (∑ i, p i) / m := by
    field_simp
  rw [hmean] at hpow
  have hsucc : (∑ i, PayOnce.success n (p i)) / m =
      1 - (1 / (m : ℝ)) * ∑ i, (1 - p i) ^ n := by
    simp only [PayOnce.success, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
  rw [hsucc]
  unfold PayOnce.success
  linarith

theorem profileCountLaw_binomial (Γ : FiniteGame m n c Seed) (d : UserProfile m n)
    (ℓ : LocalList m) (hcommon : ∀ j, observe (drawsRealization d) j = ℓ)
    (μ : FiniteLaw (Finset (Fin m))) (hμ : SymmetricAtList Γ ℓ μ) (i : Fin m) :
    profileCountLaw Γ d i = IndependentCounts.binomial n (Proposer.marginal μ i)
      (CommonList.marginal_nonneg μ i) (CommonList.marginal_le_one μ i) := by
  have he : (fun s => playedCount Γ i (d, s)) = commonSeedCount Γ ℓ i := by
    funext s
    exact boundedCount_eq_commonSeedCount Γ d ℓ hcommon i s
  calc
    profileCountLaw Γ d i = FiniteLaw.ofMeasure (Measure.pi fun _ : Fin n => Γ.seedLaw)
        (commonSeedCount Γ ℓ i) (measurable_commonSeedCount Γ ℓ i) :=
      by
        classical
        apply FiniteLaw.ext
        intro r
        simp only [profileCountLaw, CountLaw.ofMeasure, FiniteLaw.ofMeasure]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by
          dsimp only
          simp only [congrFun he s]
          split_ifs <;> rfl
    _ = _ := commonSeedCount_binomial Γ ℓ μ hμ i

theorem profileLoad_le_mul_coverage (Γ : FiniteGame m n c Seed) (d : UserProfile m n) :
    profileLoad Γ d ≤ (n : ℝ) * profileCoverage Γ d := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i _ => CountLaw.load_le_mul_success (profileCountLaw Γ d i))
  rw [← Finset.mul_sum] at hsum
  have h := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg m)
  simpa only [profileLoad, profileCoverage, mul_div_assoc] using h

theorem finiteLoad_le_mul_coverage (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    finiteLoad Γ ≤ (n : ℝ) * finiteCoverage Γ := by
  have h := integral_mono (integrable_profileLoad Γ hm)
    ((integrable_profileCoverage Γ hm).const_mul n) (profileLoad_le_mul_coverage Γ)
  simpa only [finiteLoad, finiteCoverage, integral_const_mul] using h

theorem ae_profile_moments_of_full_lists {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k + 1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    ∀ᵐ d ∂userProfileLaw Γ,
      profileLoad Γ d = (k + 1 : ℕ) * (c : ℝ) / m ∧
      profileCoverage Γ d ≤ PayOnce.success (k + 1) ((c : ℝ) / m) := by
  let j : Fin (k + 1) := ⟨0, by omega⟩
  have hgame := ae_fullList_equilibrium_of_full_routes Γ hA B hB hsym hroute j
  have huserbid := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw (k + 1))).quasiMeasurePreserving.ae hbid
  have hdrawbid : ∀ᵐ d ∂userProfileLaw Γ, ∀ l, 0 < (d l).1.2.bid :=
    ae_all_iff.mpr fun l => (measurePreserving_eval (fun _ : Fin m => userLaw Γ) l).quasiMeasurePreserving.ae huserbid
  filter_upwards [hgame, hdrawbid] with d hg hb
  let ℓ := observe (drawsRealization d) j
  let μ := seedLottery Γ j ℓ
  have hstruct := CommonList.equilibrium_structure (k + 1) (by omega)
    (fun i => (d i).1.2.bid) hb c (by simpa using hcm) μ hg.2.2
  have hsum : ∑ i, Proposer.marginal μ i = c := hstruct.2.1
  have hlaw (i : Fin m) := profileCountLaw_binomial Γ d ℓ hg.1 μ hg.2.1 i
  constructor
  · unfold profileLoad
    simp_rw [hlaw, IndependentCounts.binomial_load]
    rw [← Finset.mul_sum, hsum]
  · have hj := average_success_le hm (k + 1) (Proposer.marginal μ)
      (CommonList.marginal_le_one μ)
    rw [hsum] at hj
    unfold profileCoverage
    simp_rw [hlaw, IndependentCounts.binomial_success]
    exact hj

theorem finite_moments_jensen_of_full_lists {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k + 1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k + 1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    finiteLoad Γ = ((k + 1 : ℕ) : ℝ) * ((c : ℝ) / m) ∧
      0 < finiteCoverage Γ ∧
      finiteCoverage Γ ≤ PayOnce.success (k + 1) ((c : ℝ) / m) ∧
      (((k + 1 : ℕ) : ℝ) * ((c : ℝ) / m)) /
        PayOnce.success (k + 1) ((c : ℝ) / m) ≤ finiteMultiplicity Γ := by
  have hm : 0 < m := lt_of_lt_of_le hc hcm
  have hprof := ae_profile_moments_of_full_lists Γ hk hm hcm hA B hB hsym hroute hbid
  have hload : finiteLoad Γ = ((k + 1 : ℕ) : ℝ) * ((c : ℝ) / m) := by
    unfold finiteLoad
    rw [integral_congr_ae (hprof.mono fun _ h => h.1)]
    simp only [integral_const, probReal_univ, one_smul, mul_div_assoc]
  have hcover : finiteCoverage Γ ≤ PayOnce.success (k + 1) ((c : ℝ) / m) := by
    have h := integral_mono_ae (integrable_profileCoverage Γ hm)
      (integrable_const (PayOnce.success (k + 1) ((c : ℝ) / m))) (hprof.mono fun _ h => h.2)
    simpa only [finiteCoverage, integral_const, probReal_univ, one_smul] using h
  have hnR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hloadpos : 0 < finiteLoad Γ := by rw [hload]; exact mul_pos hnR (div_pos hcR hmR)
  have hcount := finiteLoad_le_mul_coverage Γ hm
  have hcoverpos : 0 < finiteCoverage Γ := by nlinarith
  refine ⟨hload, hcoverpos, hcover, ?_⟩
  unfold finiteMultiplicity
  rw [hload]
  exact div_le_div_of_nonneg_left (mul_pos hnR (div_pos hcR hmR)).le hcoverpos hcover

theorem finite_payOnce_jensen {k : ℕ} (Γ : FiniteGame m (k + 1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k + 1)) (hG : Γ.G = Schedule.once (k + 1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hactive : ∀ᵐ v ∂Γ.F, Γ.g < v) :
    finiteCoverage Γ ≤ 1 - (1 - (c : ℝ) / m) ^ (k + 1) ∧
      (((k + 1 : ℕ) : ℝ) * ((c : ℝ) / m)) /
        (1 - (1 - (c : ℝ) / m) ^ (k + 1)) ≤ finiteMultiplicity Γ := by
  have hfull := ae_full_routes_positive_bids_of_active Γ hc hcm hA hG hu B hB hsym hatom hactive
  have h := finite_moments_jensen_of_full_lists Γ hk hc hcm.le hA B hB hsym
    (hfull.mono fun _ h => h.2) (hfull.mono fun _ h => h.1)
  exact ⟨h.2.2.1, h.2.2.2⟩

end FCAppendix.Bayes
