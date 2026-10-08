import FCAppendix.PayOnce.ActualProfileWeights
import FCAppendix.PayOnce.EmpiricalCovariance
import FCAppendix.PayOnce.CovarianceConcentration

namespace FCAppendix.PayOnce.KernelTailEvent
open CommonList Set

theorem kernel_monotone_positive_bid {n : ℕ} (hn : 2 ≤ n) {a b L : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hL : 0 < L) : kernel n a L ≤ kernel n b L := by
  have hp := scalarThreshold_kernel n hn ha hL
  by_cases hp0 : kernel n a L = 0
  · rw [hp0]
    exact kernel_nonneg n hn (ha.trans_le hab) hL
  have hpPos := lt_of_le_of_ne hp.1 (Ne.symm hp0)
  apply (le_kernel_iff hn (ha.trans_le hab) hL hpPos hp.2.1).mpr
  exact ((le_kernel_iff hn ha hL hpPos hp.2.1).mp le_rfl).trans
    (mul_le_mul_of_nonneg_right hab (H_pos n (by omega) _ hp.1 hp.2.1).le)

end FCAppendix.PayOnce.KernelTailEvent

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.AnalyticalKernel
open scoped ProbabilityTheory BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_common_profile_root (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) (hcm : c ≤ m)
    (d : UserProfile m n) (hpos : ∀ i, 0 < (d i).1.2.bid) :
    ∃ L, 0 < L ∧ (∀ i, analyticalProfileMarginal Γ hn hcm d i =
      CommonList.kernel n (d i).1.2.bid L) ∧
      ∑ i, analyticalProfileMarginal Γ hn hcm d i = c := by
  obtain ⟨μ, hμ, _⟩ := CommonList.exists_equilibrium n hn (fun i => (d i).1.2.bid)
    hpos c (by simpa using hcm)
  obtain ⟨L, hL, _, hcap⟩ := CommonList.equilibrium_kernel n hn (fun i => (d i).1.2.bid)
    hpos c (by simpa using hcm) μ hμ
  have hp (i : Fin m) : analyticalProfileMarginal Γ hn hcm d i = CommonList.kernel n (d i).1.2.bid L :=
    allocation_eq_kernel hn _ (rivalBids i d) (fun j => hpos j.val) (hpos i) hL
      ((sum_focal_rivals i (fun j => CommonList.kernel n (d j).1.2.bid L)).trans hcap)
  refine ⟨L, hL, hp, ?_⟩
  simpa only [hp] using hcap

theorem ae_all_profile_bids_pos (Γ : FiniteGame m n c Seed)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i, 0 < (d i).1.2.bid := by
  have hu := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw n)).quasiMeasurePreserving.ae hbid
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

theorem ae_all_profile_bids_eq_type (Γ : FiniteGame m n c Seed) (bid : ℝ → ℝ)
    (hmeas : Measurable bid) (hpos : ∀ v, 0 ≤ bid v)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v)) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i, (d i).1.2.bid = bid (d i).1.1 := by
  have he : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid = bid x.1 := by
    apply Measure.ae_compProd_of_ae_ae
      (measurableSet_eq_fun ((measurable_bid n).comp measurable_snd) (hmeas.comp measurable_fst))
    filter_upwards [hpure] with v hv
    filter_upwards [hv] with a ha
    simp only [Function.comp_apply, ha, safeFullBid, fullBid, max_eq_left (hpos v)]
  have hu := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ)
    (ν := permLaw n)).quasiMeasurePreserving.ae he
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

theorem ae_profile_marginal_coordered (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) (hcm : c ≤ m)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (bid : ℝ → ℝ) (hmono : Monotone bid) (hpos : ∀ v, 0 ≤ bid v)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v))
    (h : ℝ → ℝ) (hh : Monotone h) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i j,
      0 ≤ (h (d i).1.1-h (d j).1.1)*
        (analyticalProfileMarginal Γ hn hcm d i-analyticalProfileMarginal Γ hn hcm d j) := by
  filter_upwards [ae_all_profile_bids_pos Γ hbid,
    ae_all_profile_bids_eq_type Γ bid hmono.measurable hpos hpure] with d hd htype
  obtain ⟨L, hL, hp, _⟩ := exists_common_profile_root Γ hn hcm d hd
  intro i j
  rw [hp i, hp j]
  rcases le_total (d j).1.1 (d i).1.1 with hij | hij
  · apply mul_nonneg (sub_nonneg.mpr (hh hij))
    apply sub_nonneg.mpr
    exact KernelTailEvent.kernel_monotone_positive_bid hn (hd j)
      (by rw [htype i, htype j]; exact hmono hij) hL
  · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hh hij))
    apply sub_nonpos.mpr
    exact KernelTailEvent.kernel_monotone_positive_bid hn (hd i)
      (by rw [htype i, htype j]; exact hmono hij) hL

theorem ae_profile_success_coordered (Γ : FiniteGame m n c Seed) (hn : 2 ≤ n) (hcm : c ≤ m)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (bid : ℝ → ℝ) (hmono : Monotone bid) (hpos : ∀ v, 0 ≤ bid v)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid n (bid v))
    (h : ℝ → ℝ) (hh : Monotone h) :
    ∀ᵐ d ∂userProfileLaw Γ, ∀ i j,
      0 ≤ (h (d i).1.1-h (d j).1.1)*
        (success n (analyticalProfileMarginal Γ hn hcm d i)-
          success n (analyticalProfileMarginal Γ hn hcm d j)) := by
  filter_upwards [ae_profile_marginal_coordered Γ hn hcm hbid bid hmono hpos hpure h hh]
    with d hd
  intro i j
  have hp := analyticalProfileMarginal_bounds Γ hn hcm d i
  have hq := analyticalProfileMarginal_bounds Γ hn hcm d j
  have hs {p q : ℝ} (hp1 : p ≤ 1) (hq1 : q ≤ 1) (hpq : p ≤ q) : success n p ≤ success n q := by
    unfold success
    exact sub_le_sub_left (pow_le_pow_left₀ (sub_nonneg.mpr hq1) (by linarith) n) 1
  rcases le_total (analyticalProfileMarginal Γ hn hcm d j) (analyticalProfileMarginal Γ hn hcm d i) with hij | hij
  · by_cases he : analyticalProfileMarginal Γ hn hcm d j = analyticalProfileMarginal Γ hn hcm d i
    · simp only [he, sub_self, mul_zero, le_refl]
    · have hval : 0 ≤ h (d i).1.1-h (d j).1.1 :=
        nonneg_of_mul_nonneg_left (hd i j) (sub_pos.mpr (lt_of_le_of_ne hij he))
      exact mul_nonneg hval (sub_nonneg.mpr (hs hq.2 hp.2 hij))
  · by_cases he : analyticalProfileMarginal Γ hn hcm d i = analyticalProfileMarginal Γ hn hcm d j
    · simp only [he, sub_self, mul_zero, le_refl]
    · have hval : h (d i).1.1-h (d j).1.1 ≤ 0 :=
        nonpos_of_mul_nonneg_left (hd i j) (sub_neg.mpr (lt_of_le_of_ne hij he))
      exact mul_nonneg_of_nonpos_of_nonpos hval (sub_nonpos.mpr (hs hp.2 hq.2 hij))

theorem ae_profileTypeCovariance_nonneg {k : ℕ} (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hm : 0 < m) (hcm : c ≤ m)
    (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = k+1)
    (hbid : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), 0 < x.2.bid)
    (bid : ℝ → ℝ) (hmono : Monotone bid) (hpos : ∀ v, 0 ≤ bid v)
    (hpure : ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, a = safeFullBid (k+1) (bid v))
    (h : ℝ → ℝ) (hh : Monotone h) :
    ∀ᵐ d ∂userProfileLaw Γ, 0 ≤ profileTypeCovariance Γ h d := by
  have hsuccess : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, (profileCountLaw Γ d i).success =
      success (k+1) (analyticalProfileMarginal Γ (by omega) hcm d i) :=
    ae_all_iff.mpr fun i => ae_profile_success_eq_analytical Γ hk hcm hA B hB hsym hroute hbid i
  filter_upwards [hsuccess, ae_profile_success_coordered Γ (by omega) hcm hbid bid hmono hpos hpure h hh]
    with d hd ho
  have hcov := CovarianceConcentration.empirical_covariance_nonneg
    (fun i => h (d i).1.1) (fun i => (profileCountLaw Γ d i).success)
    (fun i j => by simpa only [hd] using ho i j)
  simp only [Fintype.card_fin] at hcov
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold profileTypeCovariance profileWeightedSuccess profileMeanType profileCoverage
  have he : (∑ i, h (d i).1.1 * (profileCountLaw Γ d i).success) / (m : ℝ) -
      ((∑ i, h (d i).1.1) / m) * ((∑ i, (profileCountLaw Γ d i).success) / m) =
      ((m : ℝ) * (∑ i, h (d i).1.1 * (profileCountLaw Γ d i).success) -
        (∑ i, h (d i).1.1) * (∑ i, (profileCountLaw Γ d i).success)) / (m : ℝ)^2 := by
    field_simp
  rw [he]
  exact div_nonneg hcov (sq_pos_of_pos hmR).le

theorem profile_type_pair_measurePreserving (Γ : FiniteGame m n c Seed)
    (h : ℝ → ℝ) (hh : Measurable h) {i j : Fin m} (hij : i ≠ j) :
    MeasurePreserving (fun d : UserProfile m n => (h (d i).1.1,h (d j).1.1))
      (userProfileLaw Γ) ((Γ.F.map h).prod (Γ.F.map h)) := by
  have he : MeasurePreserving (fun d : UserProfile m n => (d i,d j))
      (userProfileLaw Γ) ((userLaw Γ).prod (userLaw Γ)) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    have hind := (iIndepFun_pi (μ := fun _ : Fin m => userLaw Γ)
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
    change (Measure.pi (fun _ : Fin m => userLaw Γ)).map (fun d => (d i,d j)) = _
    rw [hind.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable]
    rw [(measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).map_eq,
      (measurePreserving_eval (fun _ : Fin m => userLaw Γ) j).map_eq]
  have hv : MeasurePreserving (fun d : UserDraw n => d.1.1) (userLaw Γ) Γ.F :=
    (show MeasurePreserving (Prod.fst : ℝ × JointAction n → ℝ) (Γ.F ⊗ₘ Γ.σ) Γ.F from
      ⟨measurable_fst, Measure.fst_compProd Γ.F Γ.σ⟩).comp
      (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n))
  have hhP : MeasurePreserving h Γ.F (Γ.F.map h) := ⟨hh, rfl⟩
  exact ((hhP.comp hv).prod (hhP.comp hv)).comp he

end FCAppendix.Bayes
