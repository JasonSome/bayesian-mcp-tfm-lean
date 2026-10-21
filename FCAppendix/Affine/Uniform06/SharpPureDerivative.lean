import FCAppendix.Affine.Uniform06.SharpPurePivotal
import Mathlib.Analysis.Calculus.Monotone

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpPureDerivative

open MeasureTheory Set Filter Topology LowBody
open PureRankCounts PurePivotalSource PureRankProbability PivotalCrossing
open SharpPureIntervals SharpPurePivotal SourcePivotalRates SourceRankRates
open FCAppendix.Affine.Uniform07
open scoped BigOperators

theorem monotone_rank {t : ℝ} (ht : 0 ≤ t) (G : Measure ℝ) [IsFiniteMeasure G] :
    Monotone (sourceRank t G) := by
  intro x y hxy
  exact mul_le_mul_of_nonneg_left (measureReal_mono (Iic_subset_Iic.mpr hxy)) ht

theorem rank_increment {t : ℝ} (G : Measure ℝ) [IsFiniteMeasure G]
    {x y : ℝ} (hxy : x ≤ y) : sourceRank t G y-sourceRank t G x=t*G.real (Ioc x y) := by
  unfold sourceRank
  rw [← mul_sub]
  congr 1
  rw [← measureReal_sdiff (Iic_subset_Iic.mpr hxy) measurableSet_Iic]
  congr 1
  ext z
  simp only [Set.mem_sdiff,mem_Iic,mem_Ioc,not_le]
  tauto

theorem monotone_pure {t κ : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hκ : 0 < κ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) :
    Monotone (expectedUnequalPureFirst N c κ t G) := by
  letI := sourceRivalLaw_probability ht G
  intro x y hxy
  exact integral_mono (integrable_rowUnequalPureFirst κ c x _)
    (integrable_rowUnequalPureFirst κ c y _) (fun ω => rowUnequalPureFirst_monotone hκ c ω hxy)

theorem derivative_nonnegative_of_monotone {f : ℝ → ℝ} (hm : Monotone f)
    {b f' : ℝ} (hd : HasDerivAt f f' b) : 0 ≤ f' := by
  have ht := hd.tendsto_slope.mono_left
    (nhdsWithin_mono b (show Ioi b ⊆ {b}ᶜ from fun y hy => ne_of_gt hy))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_field]
  exact div_nonneg (sub_nonneg.mpr (hm hy.le)) (sub_nonneg.mpr hy.le)

theorem derivative_interval_sandwich
    {M S Q K : ℝ → ℝ} {b H M' S' Q' A R n : ℝ}
    (hM : HasDerivAt M M' b) (hS : HasDerivAt S S' b) (hQ : HasDerivAt Q Q' b)
    (hK : ContinuousAt K b) (hbH : b < H)
    (hlo : ∀ y, b < y → y < H →
      A*(M y-M b)*(K y-n*(M y-M b)) ≤ S y-S b)
    (hhi : ∀ y, b < y → y < H →
      S y-S b ≤ 2*(Q y-Q b)+R*(M y-M b)) :
    A*M'*K b ≤ S' ∧ S' ≤ 2*Q'+R*M' := by
  let L := 𝓝[>] b
  have hfilter : L ≤ 𝓝[≠] b :=
    nhdsWithin_mono b (show Ioi b ⊆ {b}ᶜ from fun y hy => ne_of_gt hy)
  have hslope (F : ℝ → ℝ) : slope F b=(fun y => (F y-F b)/(y-b)) :=
    funext (slope_def_field F b)
  have htM : Tendsto (fun y => (M y-M b)/(y-b)) L (𝓝 M') := by
    simpa only [hslope] using! hM.tendsto_slope.mono_left hfilter
  have htS : Tendsto (fun y => (S y-S b)/(y-b)) L (𝓝 S') := by
    simpa only [hslope] using! hS.tendsto_slope.mono_left hfilter
  have htQ : Tendsto (fun y => (Q y-Q b)/(y-b)) L (𝓝 Q') := by
    simpa only [hslope] using! hQ.tendsto_slope.mono_left hfilter
  have htΔ : Tendsto (fun y => M y-M b) L (𝓝 0) := by
    simpa only [sub_self] using (hM.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub_const (M b)
  have htK := hK.tendsto.mono_left (show L ≤ 𝓝 b from nhdsWithin_le_nhds)
  have hyH : ∀ᶠ y in L, y < H := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbH)
  constructor
  · have ht := (htM.const_mul A).mul (htK.sub (htΔ.const_mul n))
    simp only [mul_zero,sub_zero] at ht
    apply le_of_tendsto_of_tendsto ht htS
    filter_upwards [self_mem_nhdsWithin,hyH] with y hy hyH'
    have hh := div_le_div_of_nonneg_right (hlo y hy hyH') (sub_nonneg.mpr hy.le)
    convert! hh using 1
    ring
  · have ht := (htQ.const_mul 2).add (htM.const_mul R)
    apply le_of_tendsto_of_tendsto htS ht
    filter_upwards [self_mem_nhdsWithin,hyH] with y hy hyH'
    have hh := div_le_div_of_nonneg_right (hhi y hy hyH') (sub_nonneg.mpr hy.le)
    convert! hh using 1
    ring

theorem source_boundary_mass_lower (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (b : ℝ),
      sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i →
      (1/20000:ℝ)*Real.exp (-(3/1000000:ℝ)*m) ≤
        PiBinomial.pmf (m-2) ((1+cutoff i)/2-sourceRank (cutoff i) G b) (capacity m-1) := by
  filter_upwards [eventually_boundary_lower i,eventually_Lm_lower i] with m hb hLm
  intro G hG b hM
  letI := hG
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  have hboundary := hb G hG b hM
  have hupper := measureReal_mono (μ := Measure.pi fun _ : Fin (m-2) => sourceRivalLaw (cutoff i) G)
    (show boundarySet (higherAtSet b) otherUpper (capacity m-1) (capacity m) ⊆
      {ω | PiBinomial.count (higherAtSet b) Finset.univ ω=capacity m-1} from fun _ h => h.1)
  rw [PiBinomial.measureReal_count_eq _ _ (measurableSet_higherAtSet b),
    Finset.card_univ,Fintype.card_fin,source_higher_probability (cutoff_pos i).le (cutoff_lt_one i).le G b] at hupper
  have hQ := unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) G b (m-1) (capacity m)
  have hL : Real.exp (-(3/1000000:ℝ)*m) ≤
      Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b) := by
    change Lm i m ≤ _ at hQ
    have hh : Real.exp (-(3/1000000:ℝ)*m) ≤ Lm i m := by
      simpa only [mul_comm,neg_mul,mul_neg] using! hLm
    exact hh.trans hQ
  nlinarith

def rankSlope (i : Row) (m : ℕ) (w : ℝ) : ℝ :=
  (m-1:ℕ)*PiBinomial.pmf (m-2) ((1+cutoff i)/2-w) (capacity m-1)

def relativeError (γ : ℝ) (m : ℕ) : ℝ :=
  Real.exp (1-γ*m)+10000*Real.exp (1/10-(6/1000000:ℝ)*m)

theorem relativeError_tendsto {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (relativeError γ) atTop (𝓝 0) := by
  have hbase (a : ℝ) (ha : 0 < a) (c : ℝ) :
      Tendsto (fun m : ℕ => Real.exp (c-a*m)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop ha)
    have he : (fun m : ℕ => Real.exp (c-a*m))=(fun m : ℕ => Real.exp c*Real.exp (-(a*m))) := by
      funext m
      rw [← Real.exp_add]
      congr 1
    rw [he]
    simpa only [mul_zero,Function.comp_def] using! h.const_mul (Real.exp c)
  simpa only [relativeError,mul_zero,add_zero] using!
    (hbase γ hγ 1).add ((hbase (6/1000000) (by norm_num) (1/10)).const_mul 10000)

theorem eventually_source_derivative_bounds (i : Row) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      (∀ᵐ z ∂G, z ≤ ReceiptGap.cap i) → (∀ z : ℝ, G {z}=0) →
      ∀ H : ℝ, (∀ y, y ≤ H → sourceRank (cutoff i) G y ≤ RankCutoff.Mstar i) →
      ∀ b M' P' : ℝ, 0 < b → kappa i*ReceiptGap.cap i < b → b < H →
      HasDerivAt (sourceRank (cutoff i) G) M' b →
      HasDerivAt (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) P' b →
      0 ≤ M' ∧ 0 < rankSlope i m (sourceRank (cutoff i) G b) ∧
        |P'-2*rankSlope i m (sourceRank (cutoff i) G b)*M'| ≤
          2*rankSlope i m (sourceRank (cutoff i) G b)*M'*relativeError γ m := by
  obtain ⟨θ,γ,hθ,hγ,hdef⟩ := source_conditional_tilt i
  refine ⟨γ,hγ,?_⟩
  filter_upwards [source_boundary_mass_lower i,eventually_ge_atTop (2000:ℕ)] with m hmass hm
  intro G hG hcap hatom H hH b M' P' hb hcross hbH hdM hdP
  letI := hG
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hM' := derivative_nonnegative_of_monotone (monotone_rank (cutoff_pos i).le G) hdM
  have hcnt : m-2+1=m-1 := by omega
  have hcntR : ((m-2:ℕ):ℝ)+1=((m-1:ℕ):ℝ) := by exact_mod_cast hcnt
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcn := PhysicalRates.capacity_strictly_below_rivals (show 4 ≤ m by omega)
  have hk : capacity m-1 ≤ m-2 := by omega
  let M := sourceRank (cutoff i) G
  let Q := fun b => Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (M b)
  let J := fun b => PiBinomial.pmf (m-2) ((1+cutoff i)/2-M b) (capacity m-1)
  have hdQ : HasDerivAt Q (rankSlope i m (M b)*M') b := by
    have hh := (BinomialPivotal.hasDerivAt_binomBelow (m-2) (capacity m-1) hk
      ((1+cutoff i)/2-M b)).comp b (hdM.const_sub ((1+cutoff i)/2))
    rw [hcnt,show capacity m-1+1=capacity m by omega] at hh
    convert! hh using 1
    simp only [rankSlope]
    rw [← hcntR]
    ring
  have hJ : ContinuousAt J b := by
    have hp : ContinuousAt (fun z : ℝ => (1+cutoff i)/2-M z) b :=
      continuousAt_const.sub hdM.continuousAt
    dsimp only [J,PiBinomial.pmf]
    exact ((continuousAt_const.mul (hp.pow _)).mul ((continuousAt_const.sub hp).pow _))
  have hsand := derivative_interval_sandwich hdM hdP hdQ
    (continuousAt_const.mul hJ) hbH
    (A := 2*(m-1:ℕ)) (R := (m-1:ℕ)*Real.exp (1/10-(9/1000000:ℝ)*m)) (n := (m-2:ℕ))
    (K := fun y => (1-Real.exp (1-γ*m))*J y) (by
      intro y hby hyH
      have hh := actual_two_pivotal_interval (cutoff_pos i).le (cutoff_lt_one i) hκ hb hby hθ.le
        G (hatom b) (hatom y) (m-2) (capacity m) hc
      rw [hcnt,← rank_increment G hby.le,hcntR] at hh
      have hw : 0 ≤ M y := mul_nonneg (cutoff_pos i).le measureReal_nonneg
      have he := source_deleted_conditional_exponent i (show 4 ≤ m by omega) hw (hH y hyH.le) hθ.le hdef
      have hp := source_prefix_rank_parameter i hw (hH y hyH.le)
      have hj0 : 0 ≤ J y := BinomialPivotal.pmf_nonneg _ _ ⟨hp.1.1.le,hp.1.2.le⟩
      have hΔ : 0 ≤ M y-M b := sub_nonneg.mpr (monotone_rank (cutoff_pos i).le G hby.le)
      have hcoeff := mul_le_mul_of_nonneg_right (sub_le_sub_left (Real.exp_le_exp.mpr he) 1) hj0
      have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_right hcoeff ((m-2:ℕ)*(M y-M b)))
        (show 0 ≤ 2*(m-1:ℕ)*(M y-M b) by positivity)
      convert! hmul.trans hh using 1)
    (by
      intro y hby hyH
      have hh := source_sharp_pure_upper_interval i hm G hcap hb hby hcross
        (hatom b) (hatom y) (hH y hyH.le)
      rw [← rank_increment G hby.le] at hh
      convert! hh using 1
      dsimp only [Q]
      ring)
  have hJlower := hmass G hG b (hH b hbH.le)
  have hJpos : 0 < J b := (mul_pos (by norm_num) (Real.exp_pos _)).trans_le hJlower
  have hNpos : (0:ℝ) < (m-1:ℕ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hApos : 0 < rankSlope i m (M b) := mul_pos hNpos hJpos
  refine ⟨hM',hApos,abs_le.mpr ⟨?_,?_⟩⟩
  · have he0 : 0 ≤ 10000*Real.exp (1/10-(6/1000000:ℝ)*m) := by positivity
    have hA0 : 0 ≤ 2*rankSlope i m (M b)*M' := by positivity
    have hmore := mul_le_mul_of_nonneg_left
      (show Real.exp (1-γ*m) ≤ relativeError γ m by unfold relativeError; linarith) hA0
    dsimp only [rankSlope,J,M] at hsand hmore ⊢
    nlinarith only [hsand.1,hmore]
  · have hrare : Real.exp (1/10-(9/1000000:ℝ)*m) ≤
        2*J b*(10000*Real.exp (1/10-(6/1000000:ℝ)*m)) := by
      have hh := mul_le_mul_of_nonneg_right hJlower
        (show 0 ≤ 20000*Real.exp (1/10-(6/1000000:ℝ)*m) by positivity)
      have he : ((1/20000:ℝ)*Real.exp (-(3/1000000:ℝ)*m))*
          (20000*Real.exp (1/10-(6/1000000:ℝ)*m))=
          Real.exp (1/10-(9/1000000:ℝ)*m) := by
        rw [show (1/20000:ℝ)*Real.exp (-(3/1000000:ℝ)*m)*
          (20000*Real.exp (1/10-(6/1000000:ℝ)*m))=
          Real.exp (-(3/1000000:ℝ)*m)*Real.exp (1/10-(6/1000000:ℝ)*m) by ring,
          ← Real.exp_add]
        congr 1
        ring
      rw [he] at hh
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hrare (mul_nonneg hNpos.le hM')
    have hmore : 10000*Real.exp (1/10-(6/1000000:ℝ)*m) ≤ relativeError γ m := by
      unfold relativeError
      linarith [Real.exp_pos (1-γ*m)]
    have hmore' := mul_le_mul_of_nonneg_left hmore
      (show 0 ≤ 2*rankSlope i m (M b)*M' by positivity)
    dsimp only [rankSlope,J,M] at hsand ⊢ hmore' hmul
    nlinarith [hsand.2]

theorem eventually_source_pure_derivative_ae (i : Row) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      (∀ᵐ z ∂G, z ≤ ReceiptGap.cap i) → (∀ z : ℝ, G {z}=0) →
      ∀ H : ℝ, (∀ y, y ≤ H → sourceRank (cutoff i) G y ≤ RankCutoff.Mstar i) →
      ∀ᵐ b ∂volume, b ∈ Ioo (max 0 (kappa i*ReceiptGap.cap i)) H →
        DifferentiableAt ℝ (sourceRank (cutoff i) G) b ∧
        DifferentiableAt ℝ
          (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b ∧
        |deriv (expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G) b-
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b| ≤
          2*rankSlope i m (sourceRank (cutoff i) G b)*deriv (sourceRank (cutoff i) G) b*
            relativeError γ m := by
  obtain ⟨γ,hγ,hevent⟩ := eventually_source_derivative_bounds i
  refine ⟨γ,hγ,hevent.mono ?_⟩
  intro m hm G hG hcap hatom H hH
  letI := hG
  have hM := monotone_rank (cutoff_pos i).le G
  have hP := monotone_pure (cutoff_mem i)
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) G (m-1) (capacity m)
  filter_upwards [hM.ae_differentiableAt,hP.ae_differentiableAt] with b hdM hdP hb
  have hh := hm G hG hcap hatom H hH b _ _
    ((le_max_left _ _).trans_lt hb.1) ((le_max_right _ _).trans_lt hb.1) hb.2
    hdM.hasDerivAt hdP.hasDerivAt
  exact ⟨hdM,hdP,hh.2.2⟩

end FCAppendix.Affine.Uniform06.SharpPureDerivative
