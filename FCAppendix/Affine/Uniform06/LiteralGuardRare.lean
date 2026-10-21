import FCAppendix.Affine.Uniform06.LiteralSeedRare

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralGuardRare

open Set MeasureTheory Filter
open scoped Topology BigOperators
open LowBody LiteralExperiment LiteralGuardEmpirical GuardProfileLipschitz
open RareEmpiricalReplacement LiteralSeedRare

def currentMeans (μ : Measure RowRival) (N : ℕ) (ξ : ℝ) (g : GuardData) : Fin 8 → ℝ :=
  fun j => ((N:ℝ)/g.population)*(∫ r,statistic ξ g j r ∂μ)

def currentCoefficient (μ : Measure RowRival) (N : ℕ) (ξ : ℝ) (g : GuardData)
    (c : ℕ) (cm : ℝ) : ℝ :=
  profileAlpha g.margin (populationProfile (currentMeans μ N ξ g) ((c:ℝ)/g.population) cm)

def rawGuard {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  guardAlpha ξ {g with countMargin := cm (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)

def deviationSum {N : ℕ} (μ : Measure RowRival) (ξ : ℝ) (g : GuardData)
    (ω : Fin N → RowRival) : ℝ :=
  ∑ j : Fin 8,|empirical (statistic ξ g j) N ω-∫ r,statistic ξ g j r ∂μ|

theorem currentCoefficient_bounds (μ : Measure RowRival) (N : ℕ) (ξ : ℝ)
    (g : GuardData) (c : ℕ) (cm : ℝ) : currentCoefficient μ N ξ g c cm ∈ Icc (0:ℝ) 1 :=
  profileAlpha_bounds _ _

theorem rawGuard_bounds {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) :
    rawGuard ξ g c cm b ω ∈ Icc (0:ℝ) 1 := guardAlpha_bounds _ _ _ _

theorem measurable_rawGuard {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) : Measurable (rawGuard ξ g c cm b) := by
  apply LiteralCoarseMeasurable.measurable_pattern_choice
    (fun kind ω => guardAlpha ξ {g with countMargin := cm kind}
      (patternTemplate c kind) (rowBids b ω))
  intro kind
  exact LiteralCoarseMeasurable.measurable_guard ξ _ _ _
    (LiteralCoarseMeasurable.measurable_raw_rowBids N b)

theorem measurable_deviationSum {N : ℕ} (μ : Measure RowRival) (ξ : ℝ) (g : GuardData) :
    Measurable (@deviationSum N μ ξ g) :=
  Finset.measurable_sum _ fun j _ =>
    ((measurable_empirical (statistic_measurable ξ g j) N).sub_const _).abs

lemma sums_current_difference {N : ℕ} (μ : Measure RowRival) (ξ : ℝ) (g : GuardData)
    (hN : 0 < N) (ω : Fin N → RowRival) (j : Fin 8) :
    sums ξ g ω j-currentMeans μ N ξ g j=
      ((N:ℝ)/g.population)*(empirical (statistic ξ g j) N ω-
        ∫ r,statistic ξ g j r ∂μ) := by
  unfold sums currentMeans empirical
  by_cases hM : g.population=0
  · simp [hM]
  · field_simp [Nat.cast_ne_zero.mpr hN.ne',hM]

theorem actual_guard_deviation {N : ℕ} (μ : Measure RowRival)
    {ξ : ℝ} (hξ : 0 < ξ) (g : GuardData) (c : ℕ)
    (cm : (Fin N → Fin 4) → ℝ) (cmbar : ℝ)
    (hN : 0 < N) (hM : 0 < g.population) (hNM : (N:ℝ) ≤ g.population)
    (hε : 0 < g.margin) (hlo : 0 < g.multiplier-g.radius)
    (hhi : 0 < g.multiplier+g.radius) (hd : 0 < g.rejectionScale)
    {K : ℝ} (_hK : 0 ≤ K) (ω : Fin N → RowRival)
    (hcm : |cm (fun j => (ω j).1)/g.population-cmbar| ≤
      K*(deviationSum μ ξ g ω+g.population⁻¹)) :
    ∀ b,|rawGuard ξ g c cm b ω-currentCoefficient μ N ξ g c cmbar| ≤
      (5/g.margin)*((10+K)*deviationSum μ ξ g ω+(6+K)/g.population)+
        (noRivalSeed g.seedCutoff).indicator (fun _ => (1:ℝ)) ω := by
  classical
  intro b
  let g' : GuardData := {g with countMargin := cm (fun j => (ω j).1)}
  let E := deviationSum μ ξ g ω
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hratio : (N:ℝ)/g.population ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (Nat.cast_nonneg _) hM.le,(div_le_one hM).mpr hNM⟩
  have hs (j : Fin 8) : |sums ξ g' ω j-currentMeans μ N ξ g j| ≤ E := by
    rw [sums_countMargin,sums_current_difference μ ξ g hN ω j,
      abs_mul,abs_of_nonneg hratio.1]
    have hj : |empirical (statistic ξ g j) N ω-∫ r,statistic ξ g j r ∂μ|≤E := by
      exact Finset.single_le_sum
        (fun j _ => abs_nonneg (empirical (statistic ξ g j) N ω-
          ∫ r,statistic ξ g j r ∂μ)) (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_right hratio.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hj)
  have hp := profile_error ξ g' c b ω (currentMeans μ N ξ g) hM
    (focal_unit hξ g hlo hhi hd b) hs
    (show |(c:ℝ)/g'.population-(c:ℝ)/g.population| ≤ (0:ℝ) by simp [g']) hcm
  have hg := actual_guard_error ξ g' (patternTemplate c (fun j => (ω j).1))
    (rowBids b ω) hM hε
    (populationProfile (currentMeans μ N ξ g) ((c:ℝ)/g.population) cmbar)
  have hseed : (if seeded g' (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      then (0:ℝ) else 1) ≤
        (noRivalSeed g.seedCutoff).indicator (fun _ => (1:ℝ)) ω := by
    classical
    by_cases hs : seeded g' (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
    · simp only [if_pos hs]
      by_cases hn : ω ∈ noRivalSeed g.seedCutoff
      · simp only [indicator_of_mem hn,zero_le_one]
      · simp only [indicator_of_notMem hn,le_refl]
    · have hn := no_seed_subset g' c b hs
      change ω∈noRivalSeed g.seedCutoff at hn
      simpa only [if_neg hs,indicator_of_mem hn] using (le_refl (1:ℝ))
  have h5 : 0 ≤ 5/g.margin := by positivity
  have hb := add_le_add (mul_le_mul_of_nonneg_left hp h5) hseed
  calc
    _ ≤ (5/g.margin)*(∑ j : Fin 7,|normalizedProfile ξ g'
        (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) j-
          populationProfile (currentMeans μ N ξ g) ((c:ℝ)/g.population) cmbar j|)+
          (if seeded g' (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) then 0 else 1) := hg
    _ ≤ (5/g.margin)*(10*E+2*0+6/g.population+K*(E+g.population⁻¹))+
        (noRivalSeed g.seedCutoff).indicator (fun _ => (1:ℝ)) ω := hb
    _ = _ := by dsimp [E]; ring

theorem relative_current_guard
    (μ : ℕ → Measure RowRival) [∀ n,IsProbabilityMeasure (μ n)]
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (ξ : ℝ) (hξ : 0 < ξ) (g : ℕ → GuardData) (c : ℕ → ℕ)
    (cm : (n : ℕ) → (Fin (N n) → Fin 4) → ℝ) (cmbar b : ℕ → ℝ)
    (hM : ∀ n,0 < (g n).population) (hNM : ∀ n,(N n:ℝ) ≤ (g n).population)
    {ε K B Q C a : ℝ} (hε : 0 < ε) (hgε : ∀ n,ε ≤ (g n).margin)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hQ : 0 < Q) (hC : 0 ≤ C) (ha : 0 < a)
    (hlo : ∀ n,0 < (g n).multiplier-(g n).radius)
    (hhi : ∀ n,0 < (g n).multiplier+(g n).radius)
    (hd : ∀ n,0 < (g n).rejectionScale)
    (T : (n : ℕ) → (Fin (N n) → RowRival) → ℝ) (hT : ∀ n,Measurable (T n))
    (k : ℕ)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B*(N n:ℝ)^k)
    (hrare : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n) ≤ Q)
    (hcm : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      |cm n (fun j => (ω j).1)/(g n).population-cmbar n| ≤
        K*(deviationSum (μ n) ξ (g n) ω+(g n).population⁻¹))
    (hseed : ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin (N n) => μ n)).real (noRivalSeed (g n).seedCutoff) ≤
        C*Real.exp (-a*(N n:ℝ))) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      |rawGuard ξ (g n) (c n) (cm n) (b n) ω-
        currentCoefficient (μ n) (N n) ξ (g n) (c n) (cmbar n)|
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  classical
  let P := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let E : (n : ℕ)→Set (Fin (N n)→RowRival) := fun n => noRivalSeed (g n).seedCutoff
  let Z := fun n j => (N n:ℝ)*∫ ω,T n ω*
    |empirical (statistic ξ (g n) j) (N n) ω-
      ∫ r,statistic ξ (g n) j r ∂μ n| ∂P n
  have hz (j : Fin 8) : Tendsto (fun n => Z n j) atTop (𝓝 0) := by
    exact rare_current_mean_replacement μ (fun n => statistic ξ (g n) j)
      (fun n => statistic_measurable ξ (g n) j)
      (fun n => ae_of_all _ (statistic_unit hξ (g n) (hlo n) (hhi n) (hd n) j))
      N hNpos hN T hT k hB hQ hTb hrare
  have hsum : Tendsto (fun n => ∑ j : Fin 8,Z n j) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => hz j)
  have hinv : Tendsto (fun n => (g n).population⁻¹) atTop (𝓝 0) := by
    have hle (n : ℕ) : (g n).population⁻¹≤(N n:ℝ)⁻¹ := by
      have hh := one_div_le_one_div_of_le (Nat.cast_pos.mpr (hNpos n)) (hNM n)
      simpa only [one_div] using hh
    apply squeeze_zero' (Eventually.of_forall fun n => (inv_pos.mpr (hM n)).le)
      (Eventually.of_forall hle)
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hbad := rare_bad_event_replacement μ N hN T hT E
    (fun n => measurable_noRivalSeed (N n) (g n).seedCutoff) k hB hC ha hTb hseed
  have hupper : Tendsto (fun n =>
      (5/ε)*((10+K)*(∑ j : Fin 8,Z n j)+(6+K)*Q*(g n).population⁻¹)+
        (N n:ℝ)*∫ ω,(E n).indicator (T n) ω ∂P n) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add,add_zero] using
      (((hsum.const_mul (10+K)).add (hinv.const_mul ((6+K)*Q))).const_mul (5/ε)).add hbad
  have hbound : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,T n ω*
      |rawGuard ξ (g n) (c n) (cm n) (b n) ω-
        currentCoefficient (μ n) (N n) ξ (g n) (c n) (cmbar n)| ∂P n ≤
      (5/ε)*((10+K)*(∑ j : Fin 8,Z n j)+(6+K)*Q*(g n).population⁻¹)+
        (N n:ℝ)*∫ ω,(E n).indicator (T n) ω ∂P n := by
    filter_upwards [hrare] with n hRn
    let α := currentCoefficient (μ n) (N n) ξ (g n) (c n) (cmbar n)
    have hTi : Integrable (T n) (P n) := Integrable.of_mem_Icc 0 _ (hT n).aemeasurable (hTb n)
    have hdevi (j : Fin 8) : Integrable (fun ω => T n ω*
        |empirical (statistic ξ (g n) j) (N n) ω-
          ∫ r,statistic ξ (g n) j r ∂μ n|) (P n) := by
      have hbstat := ae_of_all (μ n) (statistic_unit hξ (g n) (hlo n) (hhi n) (hd n) j)
      have hv := empirical_unit_bounds (μ n) hbstat (hNpos n)
      have hm := integral_unit_bounds (μ n) (statistic_measurable ξ (g n) j) hbstat
      apply Integrable.of_bound ((hT n).mul
        (((measurable_empirical (statistic_measurable ξ (g n) j) (N n)).sub_const _).abs)).aestronglyMeasurable
        (B*(N n:ℝ)^k)
      filter_upwards [hTb n,hv] with ω hω hvω
      change ‖T n ω*|empirical (statistic ξ (g n) j) (N n) ω-
        ∫ r,statistic ξ (g n) j r ∂μ n|‖≤B*(N n:ℝ)^k
      rw [Real.norm_of_nonneg (mul_nonneg hω.1 (abs_nonneg _))]
      have he : |empirical (statistic ξ (g n) j) (N n) ω-
          ∫ r,statistic ξ (g n) j r ∂μ n| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [hvω.1,hvω.2,hm.1,hm.2]
      exact (mul_le_mul_of_nonneg_left he hω.1).trans (by simpa using hω.2)
    have hFi : Integrable (fun ω => T n ω*
        |rawGuard ξ (g n) (c n) (cm n) (b n) ω-α|) (P n) := by
      apply Integrable.of_bound ((hT n).mul
        (((measurable_rawGuard ξ (g n) (c n) (cm n) (b n)).sub_const α).abs)).aestronglyMeasurable
        (B*(N n:ℝ)^k)
      filter_upwards [hTb n] with ω hω
      change ‖T n ω*|rawGuard ξ (g n) (c n) (cm n) (b n) ω-α|‖≤B*(N n:ℝ)^k
      have hα := currentCoefficient_bounds (μ n) (N n) ξ (g n) (c n) (cmbar n)
      have hωα := rawGuard_bounds ξ (g n) (c n) (cm n) (b n) ω
      have he : |rawGuard ξ (g n) (c n) (cm n) (b n) ω-α| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [α] at * <;> linarith [hα.1,hα.2,hωα.1,hωα.2]
      rw [Real.norm_of_nonneg (mul_nonneg hω.1 (abs_nonneg _))]
      exact (mul_le_mul_of_nonneg_left he hω.1).trans (by simpa using hω.2)
    have hpoint : ∀ᵐ ω ∂P n,T n ω*|rawGuard ξ (g n) (c n) (cm n) (b n) ω-α| ≤
        (5/ε)*((10+K)*(∑ j : Fin 8,T n ω*
          |empirical (statistic ξ (g n) j) (N n) ω-
            ∫ r,statistic ξ (g n) j r ∂μ n|)+
          ((6+K)/(g n).population)*T n ω)+(E n).indicator (T n) ω := by
      filter_upwards [hTb n,hcm n] with ω hω hcmω
      have hg := actual_guard_deviation (μ n) hξ (g n) (c n) (cm n) (cmbar n)
        (hNpos n) (hM n) (hNM n) (hε.trans_le (hgε n)) (hlo n) (hhi n) (hd n)
        hK ω hcmω (b n)
      have h5 : 5/(g n).margin ≤ 5/ε :=
        div_le_div_of_nonneg_left (by norm_num) hε (hgε n)
      have hU : 0≤(10+K)*deviationSum (μ n) ξ (g n) ω+(6+K)/(g n).population := by
        have hpop := hM n
        unfold deviationSum
        positivity
      have hg' := hg.trans (add_le_add (mul_le_mul_of_nonneg_right h5 hU) le_rfl)
      have hh := mul_le_mul_of_nonneg_left hg' hω.1
      convert! hh using 1
      dsimp only [E]
      rw [deviationSum,←Finset.mul_sum]
      by_cases he : ω ∈ noRivalSeed (g n).seedCutoff
      · simp only [indicator_of_mem he]
        ring
      · simp only [indicator_of_notMem he]
        ring
    have hRi : Integrable (fun ω => (5/ε)*((10+K)*(∑ j : Fin 8,T n ω*
        |empirical (statistic ξ (g n) j) (N n) ω-
          ∫ r,statistic ξ (g n) j r ∂μ n|)+
        ((6+K)/(g n).population)*T n ω)+(E n).indicator (T n) ω) (P n) :=
      ((((integrable_finsetSum _ fun j _ => hdevi j).const_mul (10+K)).add
        (hTi.const_mul _)).const_mul (5/ε)).add
          (hTi.indicator (measurable_noRivalSeed (N n) (g n).seedCutoff))
    have hi := mul_le_mul_of_nonneg_left (integral_mono_ae hFi hRi hpoint)
      (Nat.cast_nonneg (N n) : 0 ≤ (N n:ℝ))
    have hsumI := integrable_finsetSum Finset.univ (fun j _=>hdevi j)
    have hinner := integral_add (hsumI.const_mul (10+K))
      (hTi.const_mul ((6+K)/(g n).population))
    have houter := integral_add
      (((hsumI.const_mul (10+K)).add (hTi.const_mul ((6+K)/(g n).population))).const_mul (5/ε))
      (hTi.indicator (measurable_noRivalSeed (N n) (g n).seedCutoff))
    dsimp only [Pi.add_apply,Pi.mul_apply] at hinner houter
    rw [houter,
      integral_const_mul,
      hinner,integral_const_mul,integral_const_mul,
      integral_finsetSum _ (fun j _ => hdevi j)] at hi
    have he : (N n:ℝ)*((5/ε)*((10+K)*(∑ j : Fin 8,∫ ω,T n ω*
        |empirical (statistic ξ (g n) j) (N n) ω-
          ∫ r,statistic ξ (g n) j r ∂μ n| ∂P n)+
        ((6+K)/(g n).population)*(∫ ω,T n ω ∂P n))+
        ∫ ω,(E n).indicator (T n) ω ∂P n)=
      (5/ε)*((10+K)*(∑ j : Fin 8,Z n j)+
        ((6+K)/(g n).population)*((N n:ℝ)*∫ ω,T n ω ∂P n))+
        (N n:ℝ)*∫ ω,(E n).indicator (T n) ω ∂P n := by
      simp only [Z,← Finset.mul_sum]
      ring
    rw [he] at hi
    have htail : ((6+K)/(g n).population)*((N n:ℝ)*∫ ω,T n ω ∂P n)≤
        (6+K)*Q*(g n).population⁻¹ := by
      have hpop := hM n
      have h := mul_le_mul_of_nonneg_left hRn
        (by positivity : 0 ≤ (6+K)/(g n).population)
      convert! h using 1
      ring
    exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl htail) (by positivity : 0 ≤ 5/ε)) le_rfl)
  exact squeeze_zero' (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
    (integral_nonneg_of_ae ((hTb n).mono fun ω hω => mul_nonneg hω.1 (abs_nonneg _)))) hbound hupper

end FCAppendix.Affine.Uniform06.LiteralGuardRare
