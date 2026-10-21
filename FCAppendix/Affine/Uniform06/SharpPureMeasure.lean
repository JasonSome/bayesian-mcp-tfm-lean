import FCAppendix.Affine.Uniform06.SharpPureDerivative
import FCAppendix.Affine.Uniform06.CompactStieltjes
import FCAppendix.Affine.Uniform06.LiteralRankIC

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpPureMeasure

open MeasureTheory Set Filter Topology LowBody
open PureRankCounts PureRankProbability PurePivotalSource PureDuplicateIntervals
open SharpPureSelector SharpPureDerivative CompactStieltjes SupportIntervalDomination
open FCAppendix.Affine.Uniform07
open scoped BigOperators

theorem source_iid_cap (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (N : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => sourceRivalLaw (cutoff i) G),
      ∀ j,(ω j).1=0 → (ω j).2 ≤ ReceiptGap.cap i := by
  let μ := sourceRivalLaw (cutoff i) G
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  have hsingle : ∀ᵐ r ∂μ,r.1=0 → r.2 ≤ ReceiptGap.cap i := by
    have hmap : Measurable (fun b : ℝ => ((0 : Fin 4), b)) :=
      measurable_const.prodMk measurable_id
    have hset : MeasurableSet {r : RowRival | r.1=0 → r.2 ≤ ReceiptGap.cap i} := by
      measurability
    have hm : ∀ᵐ r ∂G.map (fun b => ((0:Fin 4),b)),r.1=0 → r.2 ≤ ReceiptGap.cap i :=
      (ae_map_iff hmap.aemeasurable hset).mpr (by
        filter_upwards [hcap] with b hb
        exact fun _ => hb)
    simp only [μ,sourceRivalLaw,rivalLaw,ae_add_measure_iff]
    refine ⟨⟨⟨Measure.ae_smul_measure hm _,?_⟩,?_⟩,?_⟩ <;>
      apply Measure.ae_smul_measure <;> rw [ae_dirac_eq] <;> intro htag <;>
        have hv := congrArg Fin.val htag <;> norm_num at hv
  exact ae_all_iff.mpr fun j =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => μ) (i := j)) hsingle

theorem rowFirst_zero_or_one {N : ℕ} (κ : ℝ) (c : ℕ) (b : ℝ)
    (ω : Fin N → RowRival) :
    rowUnequalPureFirst κ c b ω=0 ∨ rowUnequalPureFirst κ c b ω=1 := by
  unfold rowUnequalPureFirst
  rw [LiteralExperiment.first_eq_indicator]
  split_ifs <;> simp

theorem source_first_increment_cluster (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (N c : ℕ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hcross : kappa i*ReceiptGap.cap i < x)
    (hatomx : G {x}=0) (hatomy : G {y}=0) :
    expectedUnequalPureFirst N c (kappa i) (cutoff i) G y-
      expectedUnequalPureFirst N c (kappa i) (cutoff i) G x ≤
      (N:ℝ)*(sourceRank (cutoff i) G y-sourceRank (cutoff i) G x) := by
  rcases hxy.eq_or_lt with hxy | hxy
  · subst y
    simp
  let μ := sourceRivalLaw (cutoff i) G
  let P := Measure.pi fun _ : Fin N => μ
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  let A := {ω : Fin N → RowRival | ∃ j,ω j ∈ lowCluster (Ioc x y)}
  have hA : MeasurableSet A := by
    have he : A=⋃ j : Fin N,{ω | ω j ∈ lowCluster (Ioc x y)} := by ext ω; simp [A]
    rw [he]
    exact MeasurableSet.iUnion fun j =>
      (measurable_pi_apply j) (measurableSet_lowCluster _ measurableSet_Ioc)
  have hp : ∀ᵐ ω ∂P,rowUnequalPureFirst (kappa i) c y ω-rowUnequalPureFirst (kappa i) c x ω ≤
      A.indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [source_iid_row_no_tie (cutoff_mem i) G hatomx,
      source_iid_row_no_tie (cutoff_mem i) G hatomy,source_iid_cap i G hcap N]
      with ω htx hty hU
    by_cases ha : ω ∈ A
    · rw [indicator_of_mem ha]
      linarith [(rowUnequalPureFirst_bounds (kappa i) c y ω).2,
        (rowUnequalPureFirst_bounds (kappa i) c x ω).1]
    · rw [indicator_of_notMem ha]
      rcases rowFirst_zero_or_one (kappa i) c x ω with hx0 | hx1
      · rcases rowFirst_zero_or_one (kappa i) c y ω with hy0 | hy1
        · rw [hx0,hy0]; norm_num
        · have hh := first_acquisition_crosses_ordinary_low c
            (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
            (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) hx hxy hcross ω hU htx.2 hty.2 hx0 hy1
          exact False.elim (ha hh)
      · rw [hx1]
        linarith [(rowUnequalPureFirst_bounds (kappa i) c y ω).2]
  have hh := integral_mono_ae
    ((integrable_rowUnequalPureFirst (kappa i) c y P).sub
      (integrable_rowUnequalPureFirst (kappa i) c x P))
    ((integrable_const (1:ℝ)).indicator hA) hp
  change (∫ ω, rowUnequalPureFirst (kappa i) c y ω -
    rowUnequalPureFirst (kappa i) c x ω ∂P) ≤ _ at hh
  have hAI := integral_indicator_one (μ := P) hA
  change (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P) = _ at hAI
  rw [integral_sub (integrable_rowUnequalPureFirst (kappa i) c y P)
    (integrable_rowUnequalPureFirst (kappa i) c x P),hAI] at hh
  have hu := PivotalCrossing.any_coordinate_probability_le μ (lowCluster (Ioc x y))
    (measurableSet_lowCluster _ measurableSet_Ioc) N
  dsimp only [μ,sourceRivalLaw] at hu
  rw [lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le G
    (Ioc x y) measurableSet_Ioc] at hu
  rw [rank_increment G hxy.le]
  exact hh.trans hu

theorem source_first_distance (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (hatom : ∀ b : ℝ,G {b}=0) (N c : ℕ)
    {lo x y : ℝ} (hlo : 0 < lo) (hc : kappa i*ReceiptGap.cap i < lo)
    (hx : lo ≤ x) (hy : lo ≤ y) :
    dist (expectedUnequalPureFirst N c (kappa i) (cutoff i) G x)
      (expectedUnequalPureFirst N c (kappa i) (cutoff i) G y) ≤
      (N:ℝ)*dist (sourceRank (cutoff i) G x) (sourceRank (cutoff i) G y) := by
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hM := monotone_rank (cutoff_pos i).le G
  have hP := monotone_pure (cutoff_mem i) hκ G N c
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hP hxy)),neg_sub,
      Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr (hM hxy)),neg_sub]
    exact source_first_increment_cluster i G hcap N c (hlo.trans_le hx) hxy
      (hc.trans_le hx) (hatom x) (hatom y)
  · rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hP hyx)),
      Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hM hyx))]
    exact source_first_increment_cluster i G hcap N c (hlo.trans_le hy) hyx
      (hc.trans_le hy) (hatom y) (hatom x)

theorem source_first_continuousOn (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (hatom : ∀ b : ℝ,G {b}=0) (N c : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hc : kappa i*ReceiptGap.cap i < lo) :
    ContinuousOn (expectedUnequalPureFirst N c (kappa i) (cutoff i) G) (Icc lo hi) := by
  have hM := LiteralRankIC.continuous_sourceRank (cutoff i) G hatom
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/((N:ℝ)+1) := by positivity
  have hm := (hM.continuousAt.tendsto.mono_left
    (show 𝓝[Icc lo hi] x ≤ 𝓝 x from nhdsWithin_le_nhds))
      (Metric.ball_mem_nhds (sourceRank (cutoff i) G x) he)
  filter_upwards [self_mem_nhdsWithin,hm] with y hy hMy
  have hdist := source_first_distance i G hcap hatom N c hlo hc hy.1 hx.1
  have hsmall : dist (sourceRank (cutoff i) G y) (sourceRank (cutoff i) G x) <
      ε/((N:ℝ)+1) := hMy
  have hδ0 : 0 ≤ dist (sourceRank (cutoff i) G y) (sourceRank (cutoff i) G x) := dist_nonneg
  have hmul := (lt_div_iff₀ (by positivity : 0 < (N:ℝ)+1)).mp hsmall
  exact hdist.trans_lt (by nlinarith)

theorem source_first_bounds (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) (b : ℝ) :
    expectedUnequalPureFirst N c (kappa i) (cutoff i) G b ∈ Icc (0:ℝ) 1 := by
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  let P := Measure.pi (fun _ : Fin N => sourceRivalLaw (cutoff i) G)
  constructor
  · exact integral_nonneg fun ω => (rowUnequalPureFirst_bounds (kappa i) c b ω).1
  · have hh := integral_mono (integrable_rowUnequalPureFirst (kappa i) c b P)
      (integrable_const (1:ℝ) (μ := P)) (fun ω => (rowUnequalPureFirst_bounds (kappa i) c b ω).2)
    simpa [P,expectedUnequalPureFirst] using hh

theorem source_pure_measure_domination (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (hatom : ∀ b : ℝ,G {b}=0) (N c : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hc : kappa i*ReceiptGap.cap i < lo) (hlh : lo ≤ hi) :
    ∃ F : StieltjesFunction ℝ, Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
      (∀ b ∈ Icc lo hi,F b=expectedUnequalPureFirst N c (kappa i) (cutoff i) G b) ∧
      F.measure.restrict (Ioc lo hi) ≤
        (ENNReal.ofReal ((N:ℝ)*cutoff i) • G).restrict (Ioc lo hi) := by
  let P := expectedUnequalPureFirst N c (kappa i) (cutoff i) G
  have hm := (monotone_pure (κ := kappa i) (cutoff_mem i)
    (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) G N c).monotoneOn (s := Icc lo hi)
  have hco := source_first_continuousOn i G hcap hatom N c hlo hc (hi := hi)
  let F := ofMonotoneOn P hlh hm hco
  have hFcont : Continuous F := ofMonotoneOn_continuous P hlh hm hco
  have hFb : ∀ b,F b ∈ Icc (0:ℝ) 1 := fun b => source_first_bounds i G N c (clip lo hi b)
  have hFe : ∀ b ∈ Icc lo hi,F b=P b := fun b hb => ofMonotoneOn_eq P hlh hm hco hb
  letI : IsFiniteMeasure F.measure := finite_of_bounds F hFb
  let ν : Measure ℝ := ENNReal.ofReal ((N:ℝ)*cutoff i) • G
  letI : IsFiniteMeasure ν := G.smul_finite ENNReal.ofReal_ne_top
  refine ⟨F,hFcont,hFb,hFe,?_⟩
  apply measure_restrict_le_of_Ioc_real_le F.measure ν
    (continuous_measure_atomless F hFcont)
    (fun b => by simp [ν,hatom b])
  intro a ha b hb hab
  rw [measure_real_Ioc F hab,hFe a ha,hFe b hb]
  have hν : ν.real (Ioc a b)=(N:ℝ)*(sourceRank (cutoff i) G b-sourceRank (cutoff i) G a) := by
    simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg N) (cutoff_pos i).le)]
    rw [rank_increment G hab]
    simp only [Measure.real]
    ring
  rw [hν]
  exact source_first_increment_cluster i G hcap N c (hlo.trans_le ha.1) hab
    (hc.trans_le ha.1) (hatom a) (hatom b)

theorem source_pure_measure_AC (i : Row) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) (hatom : ∀ b : ℝ,G {b}=0) (N c : ℕ)
    {lo hi : ℝ} (hlo : 0 < lo) (hc : kappa i*ReceiptGap.cap i < lo) (hlh : lo ≤ hi)
    (hAC : (ENNReal.ofReal (cutoff i) • G).restrict (Ioc lo hi) ≪ volume) :
    ∃ F : StieltjesFunction ℝ, Continuous F ∧ (∀ b,F b ∈ Icc (0:ℝ) 1) ∧
      (∀ b ∈ Icc lo hi,F b=expectedUnequalPureFirst N c (kappa i) (cutoff i) G b) ∧
      F.measure.restrict (Ioc lo hi) ≪ volume := by
  obtain ⟨F,hcF,hbF,heF,hd⟩ := source_pure_measure_domination i G hcap hatom N c hlo hc hlh
  refine ⟨F,hcF,hbF,heF,?_⟩
  intro A hA
  have hR := hAC hA
  have he : (ENNReal.ofReal ((N:ℝ)*cutoff i) • G).restrict (Ioc lo hi)=
      ENNReal.ofReal (N:ℝ) • ((ENNReal.ofReal (cutoff i) • G).restrict (Ioc lo hi)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg N),mul_smul,Measure.restrict_smul]
  rw [he] at hd
  exact le_antisymm ((hd A).trans (by simp only [Measure.smul_apply,smul_eq_mul,hR,mul_zero,le_refl])) zero_le

theorem eventually_source_used_pure_derivative (i : Row) :
    ∃ γ : ℝ,0 < γ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) (_ : IsProbabilityMeasure G),
      (∀ᵐ b ∂G,b ≤ ReceiptGap.cap i) → (∀ b : ℝ,G {b}=0) →
      ∀ lo H : ℝ,0 < lo → kappa i*ReceiptGap.cap i < lo → lo < H →
      (∀ b,b ≤ H → sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i) →
      ((ENNReal.ofReal (cutoff i) • G).restrict (Ioc lo H) ≪ volume) →
      ∀ᵐ b ∂(ENNReal.ofReal (cutoff i) • G).restrict (Ioo lo H),
        DifferentiableAt ℝ (sourceRank (cutoff i) G) b ∧
        DifferentiableAt ℝ (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b ∧
        |deriv (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b-
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b| ≤
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b*
            relativeError γ m := by
  obtain ⟨γ,hγ,hh⟩ := eventually_source_pure_derivative_ae i
  refine ⟨γ,hγ,hh.mono ?_⟩
  intro m hm G hG hcap hatom lo H hlo hc hlH hM hAC
  letI := hG
  have hAE : ∀ᵐ b ∂(ENNReal.ofReal (cutoff i) • G).restrict (Ioc lo H),
      b ∈ Ioo (max 0 (kappa i*ReceiptGap.cap i)) H →
        DifferentiableAt ℝ (sourceRank (cutoff i) G) b ∧
        DifferentiableAt ℝ (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b ∧
        |deriv (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b-
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b| ≤
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b*
            relativeError γ m := by
    have hh := hm G hG hcap hatom H hM
    rw [ae_iff] at hh ⊢
    exact hAC hh
  have hsub : (ENNReal.ofReal (cutoff i) • G).restrict (Ioo lo H) ≤
      (ENNReal.ofReal (cutoff i) • G).restrict (Ioc lo H) :=
    Measure.restrict_mono_set _ (fun _ hb => ⟨hb.1,hb.2.le⟩)
  filter_upwards [hAE.filter_mono (ae_mono hsub),ae_restrict_mem measurableSet_Ioo] with b hd hb
  apply hd
  exact ⟨max_lt (hlo.trans hb.1) (hc.trans hb.1),hb.2⟩

end FCAppendix.Affine.Uniform06.SharpPureMeasure
