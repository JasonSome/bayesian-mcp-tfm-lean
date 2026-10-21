import FCAppendix.Affine.Uniform06.SourceGuardGeometry

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardPrefix
open Set MeasureTheory LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment FiniteGuards SourceGuardGeometry
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem totalWeight_eq_sum_support (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) : totalWeight (weights ξ g T b)=
      ∑ j ∈ T.support, eligibility ξ g.multiplier g.requiredDemand (b j) := by
  classical
  simp [totalWeight,weights]

omit [Fintype ι] [Nonempty ι] in
theorem sum_update_split (S : Finset ι) (b : ι → ℝ) (f : ℝ → ℝ)
    (j : ι) (hj : j ∈ S) (x : ℝ) :
    (∑ k ∈ S, f (Function.update b j x k))=(∑ k ∈ S.erase j, f (b k))+f x := by
  rw [← Finset.sum_erase_add _ _ hj]
  have he : (∑ k ∈ S.erase j, f (Function.update b j x k))=
      ∑ k ∈ S.erase j, f (b k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [he,Function.update_self]

def rivalSlacks (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) : Fin 5 → ℝ :=
  ![(∑ k ∈ T.support.erase j, exposure ξ (g.multiplier-g.radius) (b k))-
      (small T : ℝ)-imbalance T,
    (small T : ℝ)-(∑ k ∈ T.support.erase j, exposure ξ (g.multiplier+g.radius) (b k)),
    (∑ k ∈ T.support.erase j, eligibility ξ g.multiplier g.requiredDemand (b k))-
      (imbalance T : ℝ),
    (∑ k ∈ T.support.erase j, PrefixRoot.psi g.rejectionScale g.rejectionRoot (b k))-
      (T.residual₀ : ℝ)-T.residual₁,g.countMargin]

set_option maxHeartbeats 1000000 in
omit [Nonempty ι] in
theorem slackVector_update (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hj : j ∈ T.support) (x : ℝ) :
    slackVector ξ g T (Function.update b j x)=
      slacks ξ g.multiplier g.radius g.requiredDemand g.rejectionScale
        g.rejectionRoot (rivalSlacks ξ g T b j) x := by
  funext k
  fin_cases k <;>
    simp [slackVector,slacks,rivalSlacks,demand,totalWeight_eq_sum_support,
      sum_update_split _ _ _ j hj] <;> ring

omit [Nonempty ι] in

theorem actual_guard_increment {ξ : ℝ} (hξ : 0 < ξ)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hlo : 0 < g.multiplier-g.radius) (hhi : 0 < g.multiplier+g.radius)
    (hL : 0 < g.multiplier) (hr : 0 < g.requiredDemand)
    (hd : 0 < g.rejectionScale) (hε : 0 < g.margin) (hM : 0 < g.population)
    {x y : ℝ} (hx : g.seedCutoff < x) (hy : g.seedCutoff < y) :
    |guardAlpha ξ g T (Function.update b j x)-guardAlpha ξ g T (Function.update b j y)| ≤
      ownGuardConstant ξ g.multiplier g.radius g.requiredDemand g.rejectionScale/
        (g.margin*g.population)*|x-y| := by
  classical
  have hsx := seed_availability_rival_only T.support b j hx
  have hsy := seed_availability_rival_only T.support b j hy
  have he : seeded g T (Function.update b j x) ↔ seeded g T (Function.update b j y) :=
    hsx.trans hsy.symm
  unfold guardAlpha
  rw [propext he,slackVector_update ξ g T b j hj x,slackVector_update ξ g T b j hj y]
  exact actual_five_slack_increment hξ hlo hhi hL hr hd hε hM
    (rivalSlacks ξ g T b j) _ x y

theorem eligibility_zero_on_small_prefix {ξ L r a B : ℝ}
    (hξ : 0 < ξ) (hL : 0 < L) (hr : 0 < r) (_ha : 0 ≤ a)
    (hsmall : a ≤ ξ*r*L/4) (hB : B ≤ L+a) :
    ∀ x, x ≤ B → eligibility ξ L r x=0 := by
  intro x hx
  apply eligibility_zero hr
  by_cases hxl : x ≤ L
  · rw [exposure_zero hxl]
    positivity
  have hlx := lt_of_not_ge hxl
  have hx0 := hL.trans hlx
  unfold exposure
  rw [max_eq_left hlx.le,max_eq_right (sub_nonneg.mpr hlx.le)]
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ (mul_pos hξ hx0)).mpr
  have hfactor : 0 ≤ ξ*r/4 := by positivity
  have hg := mul_le_mul_of_nonneg_left hlx.le hfactor
  nlinarith

omit [Fintype ι] [Nonempty ι] in
theorem weights_update_eq (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) {x y : ℝ}
    (hx : eligibility ξ g.multiplier g.requiredDemand x=0)
    (hy : eligibility ξ g.multiplier g.requiredDemand y=0) :
    weights ξ g T (Function.update b j x)=weights ξ g T (Function.update b j y) := by
  apply Subtype.ext
  funext k
  by_cases hkj : k=j
  · subst k
    simp only [weights,Function.update_self,hx,hy]
  · simp only [weights,Function.update_of_ne hkj]

omit [Nonempty ι] in
theorem alpha_monotone_on_seeded_prefix {ξ : ℝ} (hξ : 0 < ξ)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hL : 0 < g.multiplier-g.radius) (hε : 0 < g.margin) (hM : 0 < g.population)
    {x y : ℝ} (hx : g.seedCutoff < x) (hxy : x ≤ y)
    (hyhi : y ≤ g.multiplier+g.radius) (hyz : y ≤ g.rejectionRoot)
    (hxw : eligibility ξ g.multiplier g.requiredDemand x=0)
    (hyw : eligibility ξ g.multiplier g.requiredDemand y=0) :
    guardAlpha ξ g T (Function.update b j x) ≤ guardAlpha ξ g T (Function.update b j y) := by
  classical
  have hsl : ∀ k, slackVector ξ g T (Function.update b j x) k ≤
      slackVector ξ g T (Function.update b j y) k := by
    rw [slackVector_update ξ g T b j hj x,slackVector_update ξ g T b j hj y]
    intro k
    fin_cases k
    · change rivalSlacks ξ g T b j 0 + exposure ξ (g.multiplier-g.radius) x ≤
        rivalSlacks ξ g T b j 0 + exposure ξ (g.multiplier-g.radius) y
      linarith only [LowChernoff.exposure_monotone_bid hξ hL hxy]
    · simp [slacks,exposure_zero (hxy.trans hyhi),exposure_zero hyhi]
    · simp [slacks,hxw,hyw]
    · have hxz : x ≤ g.rejectionRoot := hxy.trans hyz
      simp [slacks,PrefixRoot.psi,max_eq_left (sub_nonpos.mpr hxz),
        max_eq_left (sub_nonpos.mpr hyz)]
    · simp [slacks]
  have hseed : seeded g T (Function.update b j x) ↔ seeded g T (Function.update b j y) :=
    (seed_availability_rival_only T.support b j hx).trans
      (seed_availability_rival_only T.support b j (hx.trans_le hxy)).symm
  unfold guardAlpha alpha
  rw [propext hseed]
  split_ifs
  · apply Finset.prod_le_prod
    · intro k _
      exact (ramp_bounds _ _ _).1
    · intro k _
      exact ramp_monotone (show g.margin*g.population < 2*g.margin*g.population by
        nlinarith [mul_pos hε hM]) (hsl k)
  · rfl

omit [Fintype ι] [Nonempty ι] in
theorem masked_update (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι)
    (j : ι) (hj : j ∈ T.support \ E) (x : ℝ) :
    maskedBids T (Function.update b j x) E=Function.update (maskedBids T b E) j x := by
  funext k
  by_cases hkj : k=j
  · subst k
    simp [maskedBids,hj]
  · simp [maskedBids,Function.update_of_ne hkj]

omit [Nonempty ι] in
theorem complement_marginal_update_monotone {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (E : Finset ι) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    complementMarginal ξ T (Function.update b j x) E j ≤
      complementMarginal ξ T (Function.update b j y) E j := by
  by_cases hj : j ∈ T.support \ E
  · unfold complementMarginal
    rw [masked_update T b E j hj x,masked_update T b E j hj y]
    apply LowBody.positiveMarginal_update_mono hξ hξ1 _ _ j _ hx hxy
    intro k hkj
    unfold maskedBids
    split_ifs
    · exact hb k hkj
    · rfl
  · have hz (z : ℝ) : complementMarginal ξ T (Function.update b j z) E j=0 := by
      apply EqualCapacity.onSupport_outside
      simp [Existence.PayOnceBounded.mem_positiveSupport,maskedBids,hj]
    rw [hz x,hz y]

theorem canonical_update_monotone {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hxw : eligibility ξ g.multiplier g.requiredDemand x=0)
    (hyw : eligibility ξ g.multiplier g.requiredDemand y=0) :
    (canonicalLaw ξ g T (Function.update b j x)).expect (first j) ≤
      (canonicalLaw ξ g T (Function.update b j y)).expect (first j) ∧
    (canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j) ≤
      (canonicalLaw ξ g T (Function.update b j y)).expect (duplicate j) := by
  have hw := weights_update_eq ξ g T b j hxw hyw
  have hp (E : Finset ι) (z : ℝ) : complementMarginal ξ T (Function.update b j z) E j ∈ Icc (0:ℝ) 1 := by
    have hh := EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1
      (maskedBids T (Function.update b j z) E)
    exact ⟨hh.1 j,hh.2.1 j⟩
  constructor
  · rw [canonical_path_first hξ hξ1,canonical_path_first hξ hξ1,hw]
    apply FiniteLaw.expect_mono
    intro path
    dsimp only
    split_ifs
    · rfl
    · have hm := complement_marginal_update_monotone hξ hξ1 T b j hb
        (finalSet (imbalance T) ∅ path) hx hxy
      have hpx := hp (finalSet (imbalance T) ∅ path) x
      have hpy := hp (finalSet (imbalance T) ∅ path) y
      nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤ 2-
        complementMarginal ξ T (Function.update b j x) (finalSet (imbalance T) ∅ path) j-
        complementMarginal ξ T (Function.update b j y) (finalSet (imbalance T) ∅ path) j by linarith [hpx.2,hpy.2])]
  · rw [canonical_path_duplicate hξ hξ1,canonical_path_duplicate hξ hξ1,hw]
    apply FiniteLaw.expect_mono
    intro path
    have hm := complement_marginal_update_monotone hξ hξ1 T b j hb
      (finalSet (imbalance T) ∅ path) hx hxy
    have hpx := hp (finalSet (imbalance T) ∅ path) x
    have hpy := hp (finalSet (imbalance T) ∅ path) y
    nlinarith [hpx.1,hpy.1]

omit [Fintype ι] [Nonempty ι] in
theorem first_nonneg (j : ι) (AB : Finset ι × Finset ι) : 0 ≤ first j AB := by
  rw [first_eq_indicator]
  split_ifs <;> norm_num

omit [Fintype ι] [Nonempty ι] in
theorem duplicate_nonneg (j : ι) (AB : Finset ι × Finset ι) : 0 ≤ duplicate j AB := by
  rw [duplicate_eq_indicator]
  split_ifs <;> norm_num

theorem guarded_canonical_prefix_monotone {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hout : ∀ k, k ∉ T.support → b k=0)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 ≤ g.radius)
    (hr : 0 < g.requiredDemand) (hlo : 0 < g.multiplier-g.radius)
    (hseed : g.seedCutoff < g.multiplier-g.radius)
    {B : ℝ} (hBhi : B ≤ g.multiplier+g.radius) (hBz : B ≤ g.rejectionRoot)
    (hw : ∀ x, x ≤ B → eligibility ξ g.multiplier g.requiredDemand x=0) :
    MonotoneOn (fun x => guardAlpha ξ g T (Function.update b j x)*
      (canonicalLaw ξ g T (Function.update b j x)).expect (first j)) (Icc 0 B) ∧
    MonotoneOn (fun x => guardAlpha ξ g T (Function.update b j x)*
      (canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j)) (Icc 0 B) := by
  have hout' (x : ℝ) : ∀ k, k ∉ T.support → Function.update b j x k=0 := by
    intro k hk
    have hkj : k ≠ j := fun he => hk (he ▸ hj)
    rw [Function.update_of_ne hkj,hout k hk]
  have htwo {x y : ℝ} (hx : x ∈ Icc (0:ℝ) B) (hy : y ∈ Icc (0:ℝ) B) (hxy : x ≤ y) :
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (first j) ≤
        guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (first j) ∧
      guardAlpha ξ g T (Function.update b j x)*(canonicalLaw ξ g T (Function.update b j x)).expect (duplicate j) ≤
        guardAlpha ξ g T (Function.update b j y)*(canonicalLaw ξ g T (Function.update b j y)).expect (duplicate j) := by
    by_cases hxl : x ≤ g.multiplier-g.radius
    · have hz := canonical_low_focal_zero hξ hξ1 g T (Function.update b j x)
        hε hM ha hr hlo (hout' x) j (by simpa using hxl)
      rw [hz.1,hz.2]
      exact ⟨mul_nonneg (guardAlpha_bounds _ _ _ _).1 (FiniteLaw.expect_nonneg _ (first_nonneg j)),
        mul_nonneg (guardAlpha_bounds _ _ _ _).1 (FiniteLaw.expect_nonneg _ (duplicate_nonneg j))⟩
    · have ham := alpha_monotone_on_seeded_prefix hξ g T b j hj hlo hε hM
        (hseed.trans (lt_of_not_ge hxl)) hxy (hy.2.trans hBhi) (hy.2.trans hBz) (hw x hx.2) (hw y hy.2)
      have hcm := canonical_update_monotone hξ hξ1 g T b j hb hx.1 hxy (hw x hx.2) (hw y hy.2)
      exact ⟨mul_le_mul ham hcm.1 (FiniteLaw.expect_nonneg _ (first_nonneg j)) (guardAlpha_bounds _ _ _ _).1,
        mul_le_mul ham hcm.2 (FiniteLaw.expect_nonneg _ (duplicate_nonneg j)) (guardAlpha_bounds _ _ _ _).1⟩
  exact ⟨fun _ hx _ hy hxy => (htwo hx hy hxy).1,fun _ hx _ hy hxy => (htwo hx hy hxy).2⟩

omit [Nonempty ι] in
theorem pure_first_duplicate_monotone {κ : ℝ} (hκ : 0 < κ)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) :
    Monotone (fun x => first j (T.selection κ (Function.update b j x))) ∧
    Monotone (fun x => duplicate j (T.selection κ (Function.update b j x))) := by
  have he (AB : Finset ι × Finset ι) : first j AB=PrefixMonotonicity.successOfCopies (focalCopy AB j) ∧
      duplicate j AB=PrefixMonotonicity.duplicateOfCopies (focalCopy AB j) := by
    by_cases h0 : j ∈ AB.1 <;> by_cases h1 : j ∈ AB.2 <;>
      simp [first,duplicate,LiteralExperiment.indicator,focalCopy,PrefixMonotonicity.successOfCopies,
        PrefixMonotonicity.duplicateOfCopies,h0,h1]
  have hh := PrefixMonotonicity.actual_pure_success_duplicate_monotone T hκ b j
  constructor
  · intro x y hxy
    dsimp only
    rw [(he _).1,(he _).1]
    exact hh.1 hxy
  · intro x y hxy
    dsimp only
    rw [(he _).2,(he _).2]
    exact hh.2 hxy

theorem unequal_prefix_add {ξ κ : ℝ} (hκ1 : κ ≤ 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hd : 0 < g.rejectionScale)
    (hout : ∀ j, j ∉ T.support → b j=0) (j : ι)
    (hb0 : 0 ≤ b j) (hbz : b j ≤ g.rejectionRoot) (hne : T.residual₀ ≠ T.residual₁) :
    (continuationLaw ξ κ g T b).expect (first j)=first j (T.selection κ b)+
      guardAlpha ξ g T b*(canonicalLaw ξ g T b).expect (first j) ∧
    (continuationLaw ξ κ g T b).expect (duplicate j)=duplicate j (T.selection κ b)+
      guardAlpha ξ g T b*(canonicalLaw ξ g T b).expect (duplicate j) := by
  have hz : guardAlpha ξ g T b*first j (T.selection κ b)=0 ∧
      guardAlpha ξ g T b*duplicate j (T.selection κ b)=0 := by
    by_cases hα : 0 < guardAlpha ξ g T b
    · have hreject := pure_rejects_under_positive_guard hκ1 g T b hε hM hd hout j hb0 hbz hα
      have hj0 : j ∉ (T.selection κ b).1 := fun hh => hreject (Finset.mem_union_left _ hh)
      have hj1 : j ∉ (T.selection κ b).2 := fun hh => hreject (Finset.mem_union_right _ hh)
      simp [first,duplicate,LiteralExperiment.indicator,hj0,hj1]
    · have hzero : guardAlpha ξ g T b=0 := le_antisymm (le_of_not_gt hα) (guardAlpha_bounds _ _ _ _).1
      simp [hzero]
  simp only [continuationLaw,if_neg hne,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  constructor <;> nlinarith [hz.1,hz.2]

theorem actual_unequal_prefix_monotone {ξ κ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hout : ∀ k, k ∉ T.support → b k=0)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 ≤ g.radius)
    (hr : 0 < g.requiredDemand) (hd : 0 < g.rejectionScale)
    (hlo : 0 < g.multiplier-g.radius) (hseed : g.seedCutoff < g.multiplier-g.radius)
    {B : ℝ} (hBhi : B ≤ g.multiplier+g.radius) (hBz : B ≤ g.rejectionRoot)
    (hw : ∀ x, x ≤ B → eligibility ξ g.multiplier g.requiredDemand x=0)
    (hne : T.residual₀ ≠ T.residual₁) :
    MonotoneOn (fun x => (continuationLaw ξ κ g T (Function.update b j x)).expect (first j)) (Icc 0 B) ∧
    MonotoneOn (fun x => (continuationLaw ξ κ g T (Function.update b j x)).expect (duplicate j)) (Icc 0 B) := by
  have hmono := guarded_canonical_prefix_monotone hξ hξ1 g T b j hj hb hout
    hε hM ha hr hlo hseed hBhi hBz hw
  have hP := pure_first_duplicate_monotone hκ T b j
  have he (x : ℝ) (hx : x ∈ Icc (0:ℝ) B) := unequal_prefix_add (ξ := ξ) hκ1 g T
    (Function.update b j x) hε hM hd (by
      intro k hk
      have hkj : k ≠ j := fun h => hk (h ▸ hj)
      rw [Function.update_of_ne hkj,hout k hk]) j (by simpa using hx.1)
      (by simpa using hx.2.trans hBz) hne
  constructor
  · intro x hx y hy hxy
    dsimp only
    rw [(he x hx).1,(he y hy).1]
    exact add_le_add (hP.1 hxy) (hmono.1 hx hy hxy)
  · intro x hx y hy hxy
    dsimp only
    rw [(he x hx).2,(he y hy).2]
    exact add_le_add (hP.2 hxy) (hmono.2 hx hy hxy)

end FCAppendix.Affine.Uniform06.GuardPrefix
