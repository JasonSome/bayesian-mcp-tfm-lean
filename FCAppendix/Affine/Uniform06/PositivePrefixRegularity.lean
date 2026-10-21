import FCAppendix.Affine.Uniform06.CanonicalPrefixLipschitz
import FCAppendix.Affine.Uniform06.LiteralPrefixContinuity
import FCAppendix.Affine.Uniform06.CompactStieltjes
import FCAppendix.Affine.Uniform06.EqualCanonicalExpected

noncomputable section
namespace FCAppendix.Affine.Uniform06.PositivePrefixRegularity

open MeasureTheory Set Filter Topology LowBody
open LiteralExperiment LiteralKernelDecomposition LiteralPrefixStieltjes
open LiteralPureComponents LiteralKernelMeasurable LiteralPrefixContinuity
open CanonicalPrefixLipschitz PureRankCounts PurePivotalSource PureDuplicateIntervals
open EqualCanonicalRegularity
open FCAppendix.Affine.Uniform07

theorem lipschitzOn_positive_band (F : ℝ → ℝ) {L lo B : ℝ}
    (hL : 0 ≤ L) (hlo : 0 < lo)
    (hm : MonotoneOn F (Icc (0:ℝ) B))
    (hi : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ B → F y-F x ≤ L*(y-x)/x) :
    LipschitzOnWith (Real.toNNReal (L/lo)) F (Icc lo B) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.coe_toNNReal _ (div_nonneg hL hlo.le),Real.dist_eq,Real.dist_eq]
  have ordered (a b : ℝ) (ha : a ∈ Icc lo B) (hb : b ∈ Icc lo B) (hab : a ≤ b) :
      |F a-F b| ≤ (L/lo)*|a-b| := by
    have ha0 : 0 < a := hlo.trans_le ha.1
    have hmo := hm ⟨ha0.le,ha.2⟩ ⟨(ha0.trans_le hab).le,hb.2⟩ hab
    rw [abs_of_nonpos (sub_nonpos.mpr hmo),abs_of_nonpos (sub_nonpos.mpr hab),neg_sub,neg_sub]
    have hh := hi a b ha0 hab hb.2
    have hd : L*(b-a)/a ≤ L*(b-a)/lo :=
      div_le_div_of_nonneg_left (mul_nonneg hL (sub_nonneg.mpr hab)) hlo ha.1
    calc
      _ ≤ L*(b-a)/lo := hh.trans hd
      _ = (L/lo)*(b-a) := by ring
  rcases le_total x y with hxy | hyx
  · exact ordered x y hx hy hxy
  · simpa only [abs_sub_comm] using ordered y x hy hx hyx

def upperCap (B b : ℝ) : ℝ := min B b

theorem upperCap_continuous (B : ℝ) : Continuous (upperCap B) := by
  unfold upperCap
  fun_prop

theorem upperCap_positive {B b : ℝ} (hB : 0 < B) (hb : 0 < b) :
    0 < upperCap B b := lt_min hB hb

@[simp] theorem upperCap_eq {B b : ℝ} (hb : b ≤ B) : upperCap B b=b := min_eq_right hb

theorem upper_capped_continuous (F : ℝ → ℝ) {L B : ℝ}
    (hL : 0 ≤ L) (hB : 0 < B)
    (hm : MonotoneOn F (Icc (0:ℝ) B))
    (hi : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ B → F y-F x ≤ L*(y-x)/x) :
    ContinuousOn (fun b => F (upperCap B b)) (Ioi 0) := by
  intro b hb
  let lo := upperCap B b/2
  have hlo : 0 < lo := half_pos (upperCap_positive hB hb)
  have hloB : lo ≤ B := by
    have hc : upperCap B b ≤ B := min_le_left _ _
    dsimp [lo]
    linarith
  have hlob : lo < b := by
    have hc : upperCap B b ≤ b := min_le_right _ _
    dsimp [lo]
    linarith [upperCap_positive hB hb]
  have hc := (lipschitzOn_positive_band F hL hlo hm hi).continuousOn
  have hglobal : Continuous (fun x => F (CompactStieltjes.clip lo B x)) :=
    hc.comp_continuous (CompactStieltjes.clip_continuous lo B) (CompactStieltjes.clip_mem hloB)
  have he : (fun x => F (CompactStieltjes.clip lo B x)) =ᶠ[𝓝 b]
      (fun x => F (upperCap B x)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hlob] with x hx
    unfold CompactStieltjes.clip upperCap
    rw [max_eq_right (le_min hloB hx.le)]
  exact (hglobal.continuousAt.congr_of_eventuallyEq he.symm).continuousWithinAt

section Row
variable {N : ℕ}

def equalFirst (ξ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  if rowResidual c 0 ω=rowResidual c 1 ω then
    2*equalMarginal ξ c b ω-(equalMarginal ξ c b ω)^2 else 0

theorem equalFirst_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : equalFirst ξ c b ω ∈ Icc (0:ℝ) 1 := by
  have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids b ω)
  have hp0 : 0 ≤ equalMarginal ξ c b ω := hp.1 (0:Fin (N+1))
  have hp1 : equalMarginal ξ c b ω ≤ 1 := hp.2.1 (0:Fin (N+1))
  unfold equalFirst
  split_ifs
  · constructor <;> nlinarith [sq_nonneg (1-equalMarginal ξ c b ω)]
  · norm_num

theorem measurable_equalFirst {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) : Measurable (equalFirst (N := N) ξ c b) :=
  Measurable.ite (EqualCanonicalRegularity.measurableSet_equalResidual c)
    ((measurable_const.mul (measurable_equalMarginal hξ hξ1 c b)).sub
      ((measurable_equalMarginal hξ hξ1 c b).pow_const 2)) measurable_const

theorem integrable_equalFirst {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (b : ℝ) (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (equalFirst ξ c b) P := by
  apply Integrable.of_bound (C := 1) (measurable_equalFirst hξ hξ1 c b).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (equalFirst_bounds hξ hξ1 c b ω).1]
    exact (equalFirst_bounds hξ hξ1 c b ω).2

theorem equal_moment_increments {ξ x y : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (ω : Fin N → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2) (hx : 0 < x) (hxy : x ≤ y) :
    (0 ≤ equalFirst ξ c y ω-equalFirst ξ c x ω ∧
      equalFirst ξ c y ω-equalFirst ξ c x ω ≤ (2/ξ)*(y-x)/x) ∧
    (0 ≤ equalDuplicate ξ c y ω-equalDuplicate ξ c x ω ∧
      equalDuplicate ξ c y ω-equalDuplicate ξ c x ω ≤ (2/ξ)*(y-x)/x) := by
  have hm := equalMarginal_increment hξ hξ1 c ω hω hx hxy
  have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids x ω)
  have hq := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids y ω)
  have hp0 : 0 ≤ equalMarginal ξ c x ω := hp.1 (0:Fin (N+1))
  have hp1 : equalMarginal ξ c x ω ≤ 1 := hp.2.1 (0:Fin (N+1))
  have hq0 : 0 ≤ equalMarginal ξ c y ω := hq.1 (0:Fin (N+1))
  have hq1 : equalMarginal ξ c y ω ≤ 1 := hq.2.1 (0:Fin (N+1))
  have hmul₀ := mul_nonneg hm.1 (add_nonneg hp0 hq0)
  have hmul₁ := mul_nonneg hm.1 (show 0 ≤ 2-equalMarginal ξ c x ω-
    equalMarginal ξ c y ω by linarith)
  have he : (2/ξ)*(y-x)/x=2*((y-x)/(ξ*x)) := by ring
  unfold equalFirst equalDuplicate
  split_ifs
  · rw [he]
    constructor <;> constructor <;> nlinarith
  · have hnn : 0 ≤ (2/ξ)*(y-x)/x := by positivity
    exact ⟨⟨by norm_num,by simpa using hnn⟩,⟨by norm_num,by simpa using hnn⟩⟩

def expectedEqualFirst (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, equalFirst ξ c b ω
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

def equalD (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, equalDuplicate ξ c b ω
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

theorem expected_equal_increments {t ξ x y : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c N : ℕ) (hx : 0 < x) (hxy : x ≤ y) :
    (0 ≤ expectedEqualFirst t ξ G c N y-expectedEqualFirst t ξ G c N x ∧
      expectedEqualFirst t ξ G c N y-expectedEqualFirst t ξ G c N x ≤ (2/ξ)*(y-x)/x) ∧
    (0 ≤ equalD t ξ G c N y-equalD t ξ G c N x ∧
      equalD t ξ G c N y-equalD t ξ G c N x ≤ (2/ξ)*(y-x)/x) := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hn := iid_rows_ae_bid_nonnegative (N := N) (sourceRivalLaw t G)
    (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  have hsx := integrable_equalFirst hξ hξ1 c x P
  have hsy := integrable_equalFirst hξ hξ1 c y P
  have hdx := integrable_equalDuplicate hξ hξ1 c x P
  have hdy := integrable_equalDuplicate hξ hξ1 c y P
  have hh := hn.mono fun ω hω => equal_moment_increments hξ hξ1 c ω (fun k _ => hω k) hx hxy
  unfold expectedEqualFirst equalD
  rw [← integral_sub hsy hsx,← integral_sub hdy hdx]
  refine ⟨⟨integral_nonneg_of_ae (hh.mono fun _ h => h.1.1),?_⟩,
    ⟨integral_nonneg_of_ae (hh.mono fun _ h => h.2.1),?_⟩⟩
  · have hi := integral_mono_ae (hsy.sub hsx) (integrable_const ((2/ξ)*(y-x)/x))
      (hh.mono fun _ h => h.1.2)
    simpa using hi
  · have hi := integral_mono_ae (hdy.sub hdx) (integrable_const ((2/ξ)*(y-x)/x))
      (hh.mono fun _ h => h.2.2)
    simpa using hi

theorem capped_continuous_of_positive_increments (F : ℝ → ℝ) {L B : ℝ}
    (hL : 0 ≤ L) (hB : 0 < B)
    (hi : ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ B →
      0 ≤ F y-F x ∧ F y-F x ≤ L*(y-x)/x) :
    ContinuousOn (fun b => F (upperCap B b)) (Ioi 0) := by
  let F₀ := fun b : ℝ => if 0 < b then F b else F (B/2)
  intro b hb
  let lo := upperCap B b/2
  have hlo : 0 < lo := half_pos (upperCap_positive hB hb)
  have hcapB : upperCap B b ≤ B := min_le_left B b
  have hcapb : upperCap B b ≤ b := min_le_right B b
  have hloB : lo ≤ B := by dsimp [lo]; linarith [hcapB,upperCap_positive hB hb]
  have hlob : lo < b := by dsimp [lo]; linarith [hcapb,upperCap_positive hB hb]
  have hLip : LipschitzOnWith (Real.toNNReal (L/lo)) F (Icc lo B) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.coe_toNNReal _ (div_nonneg hL hlo.le),Real.dist_eq,Real.dist_eq]
    have ordered (a d : ℝ) (ha : a ∈ Icc lo B) (hd : d ∈ Icc lo B) (had : a ≤ d) :
        |F a-F d| ≤ (L/lo)*|a-d| := by
      have hh := hi a d (hlo.trans_le ha.1) had hd.2
      rw [abs_of_nonpos (by linarith : F a-F d ≤ 0),
        abs_of_nonpos (sub_nonpos.mpr had),neg_sub,neg_sub]
      calc
        _ ≤ L*(d-a)/a := hh.2
        _ ≤ L*(d-a)/lo := div_le_div_of_nonneg_left
          (mul_nonneg hL (sub_nonneg.mpr had)) hlo ha.1
        _ = (L/lo)*(d-a) := by ring
    rcases le_total x y with hxy | hyx
    · exact ordered x y hx hy hxy
    · simpa only [abs_sub_comm] using ordered y x hy hx hyx
  have hc := hLip.continuousOn.comp_continuous
    (CompactStieltjes.clip_continuous lo B) (CompactStieltjes.clip_mem hloB)
  have he : (fun x => F (CompactStieltjes.clip lo B x)) =ᶠ[𝓝 b]
      (fun x => F (upperCap B x)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hlob] with x hx
    unfold CompactStieltjes.clip upperCap
    rw [max_eq_right (le_min hloB hx.le)]
  exact (hc.continuousAt.congr_of_eventuallyEq he.symm).continuousWithinAt

theorem equal_capped_continuous {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hB : 0 < B)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c N : ℕ) :
    ContinuousOn (fun b => expectedEqualFirst t ξ G c N (upperCap B b)) (Ioi 0) ∧
      ContinuousOn (fun b => equalD t ξ G c N (upperCap B b)) (Ioi 0) := by
  constructor
  · apply capped_continuous_of_positive_increments _ (by positivity : 0 ≤ 2/ξ) hB
    intro x y hx hxy _
    exact (expected_equal_increments ht hξ hξ1 G hG c N hx hxy).1
  · apply capped_continuous_of_positive_increments _ (by positivity : 0 ≤ 2/ξ) hB
    intro x y hx hxy _
    exact (expected_equal_increments ht hξ hξ1 G hG c N hx hxy).2

theorem canonical_capped_continuous {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hB : 0 < B)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c N : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    ContinuousOn (fun b => actualCanonicalFirst t ξ G c N g margin (upperCap B b)) (Ioi 0) ∧
      ContinuousOn (fun b => actualCanonicalDuplicate t ξ G c N g margin (upperCap B b)) (Ioi 0) := by
  have hL := (canonicalConstant_pos hξ hB.le hg).le
  have hmS : MonotoneOn (actualCanonicalFirst t ξ G c N g margin) (Icc (0:ℝ) B) := by
    have hm := actual_canonical_first_monotone ht hξ hξ1 G hG c g hg margin
    intro x hx y hy hxy
    simpa only [actual_canonical_first_eq ht hξ hξ1] using hm hx hy hxy
  have hmD := actual_canonical_duplicate_monotone ht hξ hξ1 G hG c g hg margin
  exact ⟨upper_capped_continuous _ hL hB hmS
    (fun x y hx hxy hy => (actual_canonical_increments ht hξ hξ1 G hG c g hg margin hx hxy hy).1),
    upper_capped_continuous _ hL hB hmD
    (fun x y hx hxy hy => (actual_canonical_increments ht hξ hξ1 G hG c g hg margin hx hxy hy).2)⟩

theorem baseline_row_payoff {ξ : ℝ} (_hξ : 0 < ξ) (_hξ1 : ξ < 1)
    (c : ℕ) (w b : ℝ) (ω : Fin N → RowRival) :
    literalRowPayoff ξ c w (b,ω)=Rank.payoff (1-2*ξ) w b
      (rowUnequalPureFirst (1-ξ) c b ω+equalFirst ξ c b ω)
      (rowUnequalPureDuplicate (1-ξ) c b ω+equalDuplicate ξ c b ω) := by
  rw [literalRowPayoff,patternPayoff_outcomes]
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    simp only [patternServed,patternDuplicate,rowUnequalPureFirst,rowUnequalPureDuplicate,
      equalFirst,equalDuplicate,if_pos he,if_pos heT,zero_add,Rank.payoff,equalMarginal]
    rfl
  · have heT : ¬(patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    simp only [patternServed,patternDuplicate,rowUnequalPureFirst,rowUnequalPureDuplicate,
      equalFirst,equalDuplicate,if_neg he,if_neg heT,add_zero,rowPureSelection,rowPureDuplicate,
      first_eq_pureServed,Rank.payoff]
    rfl

theorem baseline_expected_payoff {t ξ : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ) (w b : ℝ) :
    literalExpectedPayoff t ξ G c N w b=Rank.payoff (1-2*ξ) w b
      (expectedUnequalPureFirst N c (1-ξ) t G b+expectedEqualFirst t ξ G c N b)
      (expectedUnequalPureDuplicate N c (1-ξ) t G b+equalD t ξ G c N b) := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hS₀ := integrable_rowUnequalPureFirst (1-ξ) c b P
  have hS₁ := integrable_equalFirst hξ hξ1 c b P
  have hD₀ := integrable_rowUnequalPureDuplicate (1-ξ) c b P
  have hD₁ := integrable_equalDuplicate hξ hξ1 c b P
  unfold literalExpectedPayoff
  simp_rw [baseline_row_payoff hξ hξ1 c w b,Rank.payoff]
  have hS : Integrable (fun ω => rowUnequalPureFirst (1-ξ) c b ω+equalFirst ξ c b ω) P := hS₀.add hS₁
  have hD : Integrable (fun ω => rowUnequalPureDuplicate (1-ξ) c b ω+equalDuplicate ξ c b ω) P := hD₀.add hD₁
  change (∫ ω, (w-b)*(rowUnequalPureFirst (1-ξ) c b ω+equalFirst ξ c b ω)-
    (1-2*ξ)*b*(rowUnequalPureDuplicate (1-ξ) c b ω+equalDuplicate ξ c b ω) ∂P)=_
  rw [integral_sub (hS.const_mul (w-b))
    (hD.const_mul ((1-2*ξ)*b)),integral_const_mul,integral_const_mul,
    integral_add hS₀ hS₁,integral_add hD₀ hD₁]
  rfl

theorem baseline_extensions_eq {t ξ : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ) {b : ℝ} (hb : 0 < b) :
    extendedSuccess t ξ G c N b=
      expectedUnequalPureFirst N c (1-ξ) t G b+expectedEqualFirst t ξ G c N b ∧
    extendedDuplicate t ξ G c N b=
      expectedUnequalPureDuplicate N c (1-ξ) t G b+equalD t ξ G c N b := by
  have h₀ := baseline_expected_payoff ht hξ hξ1 G c N 0 b
  have h₁ := baseline_expected_payoff ht hξ hξ1 G c N 1 b
  unfold Rank.payoff at h₀ h₁
  have hs : extendedSuccess t ξ G c N b=
      expectedUnequalPureFirst N c (1-ξ) t G b+expectedEqualFirst t ξ G c N b := by
    unfold extendedSuccess
    linarith
  refine ⟨hs,?_⟩
  unfold extendedDuplicate
  apply (div_eq_iff (mul_ne_zero hη hb.ne')).mpr
  rw [hs]
  nlinarith

theorem baseline_success_eq {t ξ : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ) (b : ℝ) :
    extendedSuccess t ξ G c N b=
      expectedUnequalPureFirst N c (1-ξ) t G b+expectedEqualFirst t ξ G c N b := by
  have h₀ := baseline_expected_payoff ht hξ hξ1 G c N 0 b
  have h₁ := baseline_expected_payoff ht hξ hξ1 G c N 1 b
  unfold Rank.payoff at h₀ h₁
  unfold extendedSuccess
  linarith

def fullSuccessExtension (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ)
    (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (B b : ℝ) : ℝ :=
  extendedSuccess t ξ G c N (upperCap B b)-expectedEqualFirst t ξ G c N (upperCap B b)+
    actualCanonicalFirst t ξ G c N g margin (upperCap B b)

def fullDuplicateExtension (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ)
    (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (B b : ℝ) : ℝ :=
  extendedDuplicate t ξ G c N (upperCap B b)-equalD t ξ G c N (upperCap B b)+
    actualCanonicalDuplicate t ξ G c N g margin (upperCap B b)

theorem full_extensions_agree {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ)
    (g : GuardData) (hg : PrefixConditions ξ g B) (margin : (Fin N → Fin 4) → ℝ)
    {b : ℝ} (hb : 0 < b) (hbB : b ≤ B) :
    actualSuccess t ξ (1-ξ) G c N g margin b=fullSuccessExtension t ξ G c N g margin B b ∧
      actualDuplicate t ξ (1-ξ) G c N g margin b=fullDuplicateExtension t ξ G c N g margin B b := by
  have he := baseline_extensions_eq ht hξ hξ1 hη G c N hb
  have hS := actual_first_decomposition ht hξ hξ1 (by linarith : 1-ξ ≤ 1)
    G c g hg margin ⟨hb.le,hbB⟩
  have hD := actual_duplicate_decomposition ht hξ hξ1 (by linarith : 1-ξ ≤ 1)
    G c g hg margin ⟨hb.le,hbB⟩
  have hC := actual_canonical_first_eq ht hξ hξ1 G c g margin b
  unfold fullSuccessExtension fullDuplicateExtension
  rw [upperCap_eq hbB,he.1,he.2]
  exact ⟨by linarith [hS,hC],by linarith [hD]⟩

theorem full_extensions_continuous {t ξ U B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (hU : 0 ≤ U) (hB : 0 < B) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hbound : ∀ᵐ b ∂G, b ∈ Icc (0:ℝ) U) (hatom : ∀ b : ℝ, G {b}=0)
    (c N : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    ContinuousOn (fullSuccessExtension t ξ G c N g margin B) (Ioi 0) ∧
      ContinuousOn (fullDuplicateExtension t ξ G c N g margin B) (Ioi 0) := by
  have hG : ∀ᵐ b ∂G, 0 ≤ b := hbound.mono fun _ h => h.1
  have hb := extensions_continuous_positive ht hξ hξ1 hη hU G hbound hatom c N
  have hmap : MapsTo (upperCap B) (Ioi (0:ℝ)) (Ioi 0) := fun b hb => upperCap_positive hB hb
  have hbS := hb.1.comp (upperCap_continuous B).continuousOn hmap
  have hbD := hb.2.comp (upperCap_continuous B).continuousOn hmap
  have he := equal_capped_continuous ht hξ hξ1 hB G hG c N
  have hc := canonical_capped_continuous ht hξ hξ1 hB G hG c N g hg margin
  exact ⟨(hbS.sub he.1).add hc.1,(hbD.sub he.2).add hc.2⟩

theorem full_extension_payoff {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hη : 1-2*ξ ≠ 0)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c N : ℕ)
    (g : GuardData) (hg : PrefixConditions ξ g B) (margin : (Fin N → Fin 4) → ℝ)
    (w : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) B) :
    Rank.payoff (1-2*ξ) w b (actualSuccess t ξ (1-ξ) G c N g margin b)
      (actualDuplicate t ξ (1-ξ) G c N g margin b)=
    Rank.payoff (1-2*ξ) w b (fullSuccessExtension t ξ G c N g margin B b)
      (fullDuplicateExtension t ξ G c N g margin B b) := by
  by_cases hb0 : 0 < b
  · obtain ⟨hs,hd⟩ := full_extensions_agree ht hξ hξ1 hη G c N g hg margin hb0 hb.2
    rw [hs,hd]
  · have he : b=0 := le_antisymm (le_of_not_gt hb0) hb.1
    subst b
    have hs := actual_first_decomposition ht hξ hξ1 (by linarith : 1-ξ ≤ 1)
      G c g hg margin hb
    have hc := actual_canonical_first_eq ht hξ hξ1 G c g margin 0
    have hs' : actualSuccess t ξ (1-ξ) G c N g margin 0=
        fullSuccessExtension t ξ G c N g margin B 0 := by
      unfold fullSuccessExtension
      rw [upperCap_eq hb.2,baseline_success_eq ht hξ hξ1 G c N 0]
      linarith
    simp only [Rank.payoff,zero_mul,mul_zero,sub_zero,hs']

end Row

end FCAppendix.Affine.Uniform06.PositivePrefixRegularity
