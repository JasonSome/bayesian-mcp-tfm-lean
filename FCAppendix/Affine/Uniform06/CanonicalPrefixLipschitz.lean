import FCAppendix.Affine.Uniform06.LiteralPureComponents

noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalPrefixLipschitz

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelDecomposition LiteralPrefixStieltjes
open LiteralPureComponents LiteralKernelMeasurable GuardPrefix SourceGuardGeometry
open PureRankCounts PurePivotalSource EqualCanonicalRegularity
open FCAppendix.Affine.WeightedSampling FCAppendix.Affine.Uniform07

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def guardConstant (ξ : ℝ) (g : GuardData) : ℝ :=
  FiniteGuards.ownGuardConstant ξ g.multiplier g.radius g.requiredDemand
    g.rejectionScale/(g.margin*g.population)

def canonicalConstant (ξ : ℝ) (g : GuardData) (B : ℝ) : ℝ :=
  B*guardConstant ξ g+2/ξ

theorem guardConstant_nonnegative {ξ B : ℝ} (hξ : 0 < ξ)
    {g : GuardData} (hg : PrefixConditions ξ g B) : 0 ≤ guardConstant ξ g := by
  have hL : 0 < g.multiplier := by linarith [hg.lower_pos,hg.radius_nonneg]
  have hhi : 0 < g.multiplier+g.radius := by linarith [hg.radius_nonneg]
  have hlo := hg.lower_pos
  have hr := hg.requiredDemand_pos
  have hd := hg.rejectionScale_pos
  have hm := hg.margin_pos
  have hpop := hg.population_pos
  unfold guardConstant FiniteGuards.ownGuardConstant
  positivity

theorem canonicalConstant_pos {ξ B : ℝ} (hξ : 0 < ξ) (hB : 0 ≤ B)
    {g : GuardData} (hg : PrefixConditions ξ g B) : 0 < canonicalConstant ξ g B := by
  have hK := guardConstant_nonnegative hξ hg
  unfold canonicalConstant
  positivity

@[simp] theorem guardConstant_update (ξ : ℝ) (g : GuardData) (s : ℝ) :
    guardConstant ξ {g with countMargin := s}=guardConstant ξ g := rfl

@[simp] theorem canonicalConstant_update (ξ : ℝ) (g : GuardData) (B s : ℝ) :
    canonicalConstant ξ {g with countMargin := s} B=canonicalConstant ξ g B := rfl

omit [Nonempty ι] in
theorem complement_marginal_increment {ξ x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hb : ∀ k, k ≠ j → 0 ≤ b k)
    (E : Finset ι) (hx : 0 < x) (hxy : x ≤ y) :
    0 ≤ complementMarginal ξ T (Function.update b j y) E j-
      complementMarginal ξ T (Function.update b j x) E j ∧
    complementMarginal ξ T (Function.update b j y) E j-
      complementMarginal ξ T (Function.update b j x) E j ≤ (y-x)/(ξ*x) := by
  by_cases hj : j ∈ T.support \ E
  · have hh := actual_marginal_increment hξ hξ1 (small T) (maskedBids T b E) j
      (fun k hkj => by
        unfold maskedBids
        split_ifs
        · exact hb k hkj
        · rfl) hx hxy
    simpa only [PrefixMonotonicity.clippedMarginal,complementMarginal,
      masked_update T b E j hj] using hh
  · have hz (z : ℝ) : complementMarginal ξ T (Function.update b j z) E j=0 := by
      apply EqualCapacity.onSupport_outside
      simp [Existence.PayOnceBounded.mem_positiveSupport,maskedBids,hj]
    rw [hz x,hz y,sub_self]
    exact ⟨le_rfl,div_nonneg (sub_nonneg.mpr hxy) (mul_pos hξ hx).le⟩

omit [Nonempty ι] in
theorem complement_moment_increments {ξ x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hb : ∀ k, k ≠ j → 0 ≤ b k)
    (E : Finset ι) (hx : 0 < x) (hxy : x ≤ y) :
    let p := complementMarginal ξ T (Function.update b j x) E j
    let q := complementMarginal ξ T (Function.update b j y) E j
    (2*q-q^2)-(2*p-p^2) ≤ 2*(y-x)/(ξ*x) ∧
      q^2-p^2 ≤ 2*(y-x)/(ξ*x) := by
  dsimp only
  have hh := complement_marginal_increment hξ hξ1 T b j hb E hx hxy
  have hp := complement_bounds hξ hξ1 T (Function.update b j x) E j
  have hq := complement_bounds hξ hξ1 T (Function.update b j y) E j
  have hs := mul_nonneg hh.1 (add_nonneg hp.1 hq.1)
  have ht := mul_nonneg hh.1 (show 0 ≤ 2-
    complementMarginal ξ T (Function.update b j x) E j-
    complementMarginal ξ T (Function.update b j y) E j by linarith [hp.2,hq.2])
  have he : 2*((y-x)/(ξ*x))=2*(y-x)/(ξ*x) := by ring
  rw [← he]
  constructor <;> nlinarith

theorem raw_canonical_increments {ξ x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hb : ∀ k, k ≠ j → 0 ≤ b k)
    (hx : 0 < x) (hxy : x ≤ y)
    (hxw : FiniteGuards.eligibility ξ g.multiplier g.requiredDemand x=0)
    (hyw : FiniteGuards.eligibility ξ g.multiplier g.requiredDemand y=0) :
    (canonicalLaw ξ g T (Function.update b j y)).expect (first j)-
      (canonicalLaw ξ g T (Function.update b j x)).expect (first j) ≤ 2*(y-x)/(ξ*x) ∧
    (canonicalLaw ξ g T (Function.update b j y)).expect (duplicate j)-
      (canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j) ≤ 2*(y-x)/(ξ*x) := by
  have hw := weights_update_eq ξ g T b j hxw hyw
  constructor
  · rw [canonical_path_first hξ hξ1,canonical_path_first hξ hξ1,hw,
      ← FiniteLaw.expect_sub]
    apply FiniteLaw.expect_le_const
    intro path
    dsimp only
    split_ifs
    · simpa only [sub_self] using
        div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (sub_nonneg.mpr hxy)) (mul_pos hξ hx).le
    · exact (complement_moment_increments hξ hξ1 T b j hb
        (finalSet (imbalance T) ∅ path) hx hxy).1
  · rw [canonical_path_duplicate hξ hξ1,canonical_path_duplicate hξ hξ1,hw,
      ← FiniteLaw.expect_sub]
    apply FiniteLaw.expect_le_const
    intro path
    exact (complement_moment_increments hξ hξ1 T b j hb
      (finalSet (imbalance T) ∅ path) hx hxy).2

theorem product_increment {a₀ a₁ f₀ f₁ K L : ℝ}
    (_ha₀ : a₀ ∈ Icc (0:ℝ) 1) (ha₁ : a₁ ∈ Icc (0:ℝ) 1)
    (hf₀ : f₀ ∈ Icc (0:ℝ) 1) (hf : f₀ ≤ f₁)
    (hd : f₁-f₀ ≤ L) (ha : |a₁-a₀| ≤ K) : a₁*f₁-a₀*f₀ ≤ L+K := by
  have h₀ := mul_nonneg (sub_nonneg.mpr ha₁.2) (sub_nonneg.mpr hf)
  have h₁ := mul_le_mul_of_nonneg_right (le_abs_self (a₁-a₀)) hf₀.1
  have h₂ := mul_le_of_le_one_right (abs_nonneg (a₁-a₀)) hf₀.2
  nlinarith

theorem guarded_increments_above_seed {ξ B x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData) (hg : PrefixConditions ξ g B)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hx : 0 < x) (hseed : g.seedCutoff < x)
    (hxy : x ≤ y) (hyB : y ≤ B) :
    guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (first j)-
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (first j)
      ≤ guardConstant ξ g*(y-x)+2*(y-x)/(ξ*x) ∧
    guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (duplicate j)-
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j)
      ≤ guardConstant ξ g*(y-x)+2*(y-x)/(ξ*x) := by
  have hα := actual_guard_increment hξ g T b j hj hg.lower_pos
    (by linarith [hg.lower_pos,hg.radius_nonneg])
    (by linarith [hg.lower_pos,hg.radius_nonneg]) hg.requiredDemand_pos
    hg.rejectionScale_pos hg.margin_pos hg.population_pos hseed (hseed.trans_le hxy)
  have hα' : |guardAlpha ξ g T (Function.update b j y)-
      guardAlpha ξ g T (Function.update b j x)| ≤ guardConstant ξ g*(y-x) := by
    calc
      _ = |guardAlpha ξ g T (Function.update b j x)-
        guardAlpha ξ g T (Function.update b j y)| := abs_sub_comm _ _
      _ ≤ guardConstant ξ g*|x-y| := hα
      _ = guardConstant ξ g*(y-x) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy),neg_sub]
  have hxw := PrefixConditions.zero_eligibility hξ hg x (hxy.trans hyB)
  have hyw := PrefixConditions.zero_eligibility hξ hg y hyB
  have hi := raw_canonical_increments hξ hξ1 g T b j hb hx hxy hxw hyw
  have hm := canonical_update_monotone hξ hξ1 g T b j hb hx.le hxy hxw hyw
  have ha₀ := guardAlpha_bounds ξ g T (Function.update b j x)
  have ha₁ := guardAlpha_bounds ξ g T (Function.update b j y)
  constructor
  · have hh := product_increment ha₀ ha₁ (expect_first_bounds _ j) hm.1 hi.1 hα'
    linarith
  · have hh := product_increment ha₀ ha₁ (expect_duplicate_bounds _ j) hm.2 hi.2 hα'
    linarith

theorem guarded_canonical_increments {ξ B x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData) (hg : PrefixConditions ξ g B)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hout : ∀ k, k ∉ T.support → b k=0)
    (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (first j)-
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (first j)
      ≤ canonicalConstant ξ g B*(y-x)/x ∧
    guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (duplicate j)-
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j)
      ≤ canonicalConstant ξ g B*(y-x)/x := by
  have hK := guardConstant_nonnegative hξ hg
  have hB : 0 < B := hx.trans_le (hxy.trans hyB)
  have hc := (canonicalConstant_pos hξ hB.le hg).le
  have hout' (z : ℝ) : ∀ k, k ∉ T.support → Function.update b j z k=0 := by
    intro k hk
    have hkj : k ≠ j := fun he => hk (he ▸ hj)
    rw [Function.update_of_ne hkj,hout k hk]
  have hz (z : ℝ) (hz : z ≤ g.multiplier-g.radius) :=
    canonical_low_focal_zero hξ hξ1 g T (Function.update b j z)
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.lower_pos (hout' z) j (by simpa using hz)
  have hconvert : guardConstant ξ g*(y-x)+2*(y-x)/(ξ*x) ≤
      canonicalConstant ξ g B*(y-x)/x := by
    apply (le_div_iff₀ hx).mpr
    have ht := mul_le_mul_of_nonneg_left (hxy.trans hyB)
      (mul_nonneg hK (sub_nonneg.mpr hxy))
    have he : (guardConstant ξ g*(y-x)+2*(y-x)/(ξ*x))*x=
        guardConstant ξ g*(y-x)*x+(2/ξ)*(y-x) := by
      field_simp [hx.ne',hξ.ne']
    rw [he]
    unfold canonicalConstant
    nlinarith
  by_cases hyl : y ≤ g.multiplier-g.radius
  · have hxz := hz x (hxy.trans hyl)
    have hyz := hz y hyl
    rw [hxz.1,hyz.1,hxz.2,hyz.2,sub_self]
    exact ⟨div_nonneg (mul_nonneg hc (sub_nonneg.mpr hxy)) hx.le,
      div_nonneg (mul_nonneg hc (sub_nonneg.mpr hxy)) hx.le⟩
  by_cases hxl : g.multiplier-g.radius ≤ x
  · have hi := guarded_increments_above_seed hξ hξ1 g hg T b j hj hb hx
      (hg.seed_below_lower.trans_le hxl) hxy hyB
    exact ⟨hi.1.trans hconvert,hi.2.trans hconvert⟩
  · let z := g.multiplier-g.radius
    have hxz : x ≤ z := (lt_of_not_ge hxl).le
    have hzy : z ≤ y := (lt_of_not_ge hyl).le
    have hi := guarded_increments_above_seed hξ hξ1 g hg T b j hj hb
      hg.lower_pos hg.seed_below_lower hzy hyB
    have hzx := hz x hxz
    have hzz := hz z le_rfl
    have hlinear : guardConstant ξ g*(y-z) ≤ guardConstant ξ g*(y-x) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    have hfrac : 2*(y-z)/(ξ*z) ≤ 2*(y-x)/(ξ*x) := by
      apply (div_le_div_iff₀ (mul_pos hξ hg.lower_pos) (mul_pos hξ hx)).mpr
      have hh := mul_nonneg (sub_nonneg.mpr hxz) (hx.trans_le hxy).le
      nlinarith [mul_nonneg hξ.le hh]
    rcases hi with ⟨hfirst,hduplicate⟩
    rw [hzz.1] at hfirst
    rw [hzz.2] at hduplicate
    rw [hzx.1,hzx.2]
    exact ⟨(hfirst.trans (add_le_add hlinear hfrac)).trans hconvert,
      (hduplicate.trans (add_le_add hlinear hfrac)).trans hconvert⟩

section Row
variable {N : ℕ}

theorem row_canonical_duplicate_monotone {ξ B : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (g : GuardData)
    (hg : PrefixConditions ξ g B) (margin : (Fin N → Fin 4) → ℝ)
    (ω : Fin N → RowRival) (hω : ∀ k, (ω k).1=0 → 0 ≤ (ω k).2) :
    MonotoneOn (fun b => rowCanonicalDuplicate ξ c g margin b ω) (Icc 0 B) := by
  let T := patternTemplate c (fun k => (ω k).1)
  by_cases he : T.residual₀=T.residual₁
  · have heT : (patternTemplate c (fun k => (ω k).1)).residual₀=
        (patternTemplate c (fun k => (ω k).1)).residual₁ := he
    intro x hx y hy hxy
    have hm := complement_marginal_update_monotone hξ hξ1 T (rowBids 0 ω) 0
      (fun k _ => rowBids_nonneg 0 ω le_rfl hω k) ∅ hx.1 hxy
    simp only [rowBids_update] at hm
    have hp := complement_bounds hξ hξ1 T (rowBids x ω) ∅ 0
    have hq := complement_bounds hξ hξ1 T (rowBids y ω) ∅ 0
    simp only [rowCanonicalDuplicate,if_pos heT]
    change (complementMarginal ξ T (rowBids x ω) ∅ 0)^2 ≤
      (complementMarginal ξ T (rowBids y ω) ∅ 0)^2
    nlinarith [hp.1,hq.1]
  · have heT : ¬(patternTemplate c (fun k => (ω k).1)).residual₀=
        (patternTemplate c (fun k => (ω k).1)).residual₁ := he
    have hm := (guarded_canonical_prefix_monotone hξ hξ1
      {g with countMargin := margin (fun k => (ω k).1)} T (rowBids 0 ω) 0
      (focal_mem_patternTemplate c _) (fun k _ => rowBids_nonneg 0 ω le_rfl hω k)
      (rowBids_outside c 0 ω) hg.margin_pos hg.population_pos hg.radius_nonneg
      hg.requiredDemand_pos hg.lower_pos hg.seed_below_lower hg.upper hg.rejection
      (PrefixConditions.zero_eligibility hξ (hg.update_countMargin _))).2
    simpa only [rowCanonicalDuplicate,if_neg heT,rowBids_update,
      canonicalLaw_update_countMargin,T] using! hm

theorem actual_canonical_duplicate_monotone {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    MonotoneOn (actualCanonicalDuplicate t ξ G c N g margin) (Icc 0 B) := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hn := iid_rows_ae_bid_nonnegative (N := N) (sourceRivalLaw t G)
    (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  intro x hx y hy hxy
  apply integral_mono_ae (integrable_rowCanonical hξ hξ1 c g margin x P).2.2
    (integrable_rowCanonical hξ hξ1 c g margin y P).2.2
  filter_upwards [hn] with ω hω
  exact row_canonical_duplicate_monotone hξ hξ1 c g hg margin ω
    (fun k _ => hω k) hx hy hxy

theorem row_canonical_increments {ξ B x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (g : GuardData)
    (hg : PrefixConditions ξ g B) (margin : (Fin N → Fin 4) → ℝ)
    (ω : Fin N → RowRival) (hω : ∀ k, (ω k).1=0 → 0 ≤ (ω k).2)
    (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    rowCanonicalFirst ξ c g margin y ω-rowCanonicalFirst ξ c g margin x ω ≤
      canonicalConstant ξ g B*(y-x)/x ∧
    rowCanonicalDuplicate ξ c g margin y ω-rowCanonicalDuplicate ξ c g margin x ω ≤
      canonicalConstant ξ g B*(y-x)/x := by
  let T := patternTemplate c (fun k => (ω k).1)
  by_cases he : T.residual₀=T.residual₁
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have hi := complement_moment_increments hξ hξ1 T (rowBids 0 ω) 0
      (fun k _ => rowBids_nonneg 0 ω le_rfl hω k) ∅ hx hxy
    simp only [rowBids_update] at hi
    have hu : 2*(y-x)/(ξ*x) ≤ canonicalConstant ξ g B*(y-x)/x := by
      have hK := guardConstant_nonnegative hξ hg
      have hB : 0 ≤ B := (hx.trans_le (hxy.trans hyB)).le
      have hg' := mul_nonneg (mul_nonneg hB hK) (sub_nonneg.mpr hxy)
      apply (div_le_div_iff₀ (mul_pos hξ hx) hx).mpr
      unfold canonicalConstant
      field_simp [hξ.ne']
      nlinarith [mul_nonneg hξ.le hg']
    simp only [rowCanonicalFirst,rowCanonicalDuplicate,if_pos heT]
    simpa only [T] using! (And.intro (hi.1.trans hu) (hi.2.trans hu))
  · have heT : ¬(patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have hi := guarded_canonical_increments hξ hξ1
      {g with countMargin := margin (fun k => (ω k).1)} (hg.update_countMargin _)
      T (rowBids 0 ω) 0 (focal_mem_patternTemplate c _)
      (fun k _ => rowBids_nonneg 0 ω le_rfl hω k) (rowBids_outside c 0 ω) hx hxy hyB
    simpa only [rowCanonicalFirst,rowCanonicalDuplicate,if_neg heT,rowBids_update,
      canonicalLaw_update_countMargin,canonicalConstant_update,T] using! hi

theorem original_common_conull_canonical_increments {t ξ B : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => sourceRivalLaw t G),
      ∀ x y : ℝ, 0 < x → x ≤ y → y ≤ B →
      rowCanonicalFirst ξ c g margin y ω-rowCanonicalFirst ξ c g margin x ω ≤
        canonicalConstant ξ g B*(y-x)/x ∧
      rowCanonicalDuplicate ξ c g margin y ω-rowCanonicalDuplicate ξ c g margin x ω ≤
        canonicalConstant ξ g B*(y-x)/x := by
  letI := sourceRivalLaw_probability ht G
  have hn := iid_rows_ae_bid_nonnegative (N := N) (sourceRivalLaw t G)
    (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  filter_upwards [hn] with ω hω
  intro x y hx hxy hyB
  exact row_canonical_increments hξ hξ1 c g hg margin ω (fun k _ => hω k) hx hxy hyB

theorem actual_canonical_increments {t ξ B x y : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    actualCanonicalFirst t ξ G c N g margin y-actualCanonicalFirst t ξ G c N g margin x ≤
      canonicalConstant ξ g B*(y-x)/x ∧
    actualCanonicalDuplicate t ξ G c N g margin y-actualCanonicalDuplicate t ξ G c N g margin x ≤
      canonicalConstant ξ g B*(y-x)/x := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hi₀ := integrable_rowCanonical hξ hξ1 c g margin x P
  have hi₁ := integrable_rowCanonical hξ hξ1 c g margin y P
  have hh := original_common_conull_canonical_increments ht hξ hξ1 G hG c g hg margin
  constructor
  · unfold actualCanonicalFirst
    rw [← integral_sub hi₁.1 hi₀.1]
    have hi := integral_mono_ae (hi₁.1.sub hi₀.1) (integrable_const
      (canonicalConstant ξ g B*(y-x)/x)) (hh.mono fun ω hω => (hω x y hx hxy hyB).1)
    simpa using hi
  · change (∫ ω, rowCanonicalDuplicate ξ c g margin y ω ∂P)-
      (∫ ω, rowCanonicalDuplicate ξ c g margin x ω ∂P) ≤ _
    rw [← integral_sub hi₁.2.2 hi₀.2.2]
    have hi := integral_mono_ae (hi₁.2.2.sub hi₀.2.2) (integrable_const
      (canonicalConstant ξ g B*(y-x)/x)) (hh.mono fun ω hω => (hω x y hx hxy hyB).2)
    simpa using hi

end Row

theorem source_canonical_increments (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (margin : (Fin (m-1) → Fin 4) → ℝ)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyB : y ≤ B) :
    (2*sourceCanonicalMarginal i m G g margin y-sourceCanonicalDuplicate i m G g margin y)-
      (2*sourceCanonicalMarginal i m G g margin x-sourceCanonicalDuplicate i m G g margin x) ≤
        canonicalConstant (xi i) g B*(y-x)/x ∧
    sourceCanonicalDuplicate i m G g margin y-sourceCanonicalDuplicate i m G g margin x ≤
      canonicalConstant (xi i) g B*(y-x)/x := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hi := actual_canonical_increments (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) (G.map Prod.snd)
    (source_floor_bid_nonnegative i G hfloor) (capacity m) g hg margin hx hxy hyB
  rw [actual_canonical_first_eq (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]),
    actual_canonical_first_eq (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ])] at hi
  exact hi

end FCAppendix.Affine.Uniform06.CanonicalPrefixLipschitz
