import FCAppendix.Affine.Uniform06.FiniteGuards
import FCAppendix.Affine.Uniform06.PureRankSelector
import FCAppendix.Affine.Uniform06.LowRoute
import FCAppendix.Affine.EqualCapacityLottery
import FCAppendix.Affine.WeightedSampling

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralExperiment

open Set MeasureTheory LowBody
open FCAppendix.Affine.WeightedSampling FCAppendix.Affine.ClippedResidual
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure GuardData where
  multiplier : ℝ
  radius : ℝ
  rejectionRoot : ℝ
  rejectionScale : ℝ
  requiredDemand : ℝ
  margin : ℝ
  population : ℝ
  seedCutoff : ℝ
  countMargin : ℝ

def small (T : PureTemplate ι) : ℕ := min T.residual₀ T.residual₁
def imbalance (T : PureTemplate ι) : ℕ := max T.residual₀ T.residual₁-small T

def weights (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) : Weights ι :=
  ⟨fun j => if j ∈ T.support then
      FiniteGuards.eligibility ξ g.multiplier g.requiredDemand (b j) else 0,
    by intro j; dsimp only; split_ifs; exact FiniteGuards.eligibility_bounds _ _ _ _; norm_num⟩

def maskedBids (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι) : ι → ℝ :=
  fun j => if j ∈ T.support \ E then b j else 0

def complementMarginal (ξ : ℝ) (T : PureTemplate ι) (b : ι → ℝ)
    (E : Finset ι) (j : ι) : ℝ :=
  EqualCapacity.positiveMarginal ξ (small T) (maskedBids T b E) j

def complementLaw (ξ : ℝ) (T : PureTemplate ι) (b : ι → ℝ)
    (E : Finset ι) : FiniteLaw (Finset ι) :=
  EqualCapacity.canonicalLottery ξ (small T) (maskedBids T b E)

def attachExclusive (T : PureTemplate ι) (E : Finset ι)
    (AB : Finset ι × Finset ι) : Finset ι × Finset ι :=
  if T.residual₀ < T.residual₁ then (AB.1,E ∪ AB.2) else (E ∪ AB.1,AB.2)

def canonicalLaw (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) : FiniteLaw (Finset ι × Finset ι) :=
  (pairLaw (pathLaw (weights ξ g T b) (imbalance T) ∅) (fun path =>
    let E := finalSet (imbalance T) ∅ path
    (complementLaw ξ T b E).prod (complementLaw ξ T b E))).map
      (fun out => attachExclusive T (finalSet (imbalance T) ∅ out.1) out.2)

def demand (ξ : ℝ) (T : PureTemplate ι) (b : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ T.support, exposure ξ z (b j)

def slackVector (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) : Fin 5 → ℝ :=
  ![demand ξ T b (g.multiplier-g.radius)-(small T : ℝ)-imbalance T,
    (small T : ℝ)-demand ξ T b (g.multiplier+g.radius),
    totalWeight (weights ξ g T b)-(imbalance T : ℝ),
    (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (b j))-
      (T.residual₀ : ℝ)-T.residual₁,
    g.countMargin]

def seeded (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) : Prop :=
  ∃ j ∈ T.support, b j ≤ g.seedCutoff

def guardAlpha (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) : ℝ := by
  classical
  exact FiniteGuards.alpha g.margin g.population (seeded g T b) (slackVector ξ g T b)

omit [Nonempty ι] in
theorem guardAlpha_bounds (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) :
    guardAlpha ξ g T b ∈ Icc (0:ℝ) 1 := by
  classical
  exact FiniteGuards.alpha_bounds _ _ _ _

def continuationLaw (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) : FiniteLaw (Finset ι × Finset ι) :=
  if T.residual₀=T.residual₁ then
    (complementLaw ξ T b ∅).prod (complementLaw ξ T b ∅)
  else (canonicalLaw ξ g T b).mixture (FiniteLaw.dirac (T.selection κ b))
    (guardAlpha ξ g T b) (guardAlpha_bounds ξ g T b).1 (guardAlpha_bounds ξ g T b).2

def indicator (j : ι) (S : Finset ι) : ℝ := if j ∈ S then 1 else 0
def first (j : ι) (AB : Finset ι × Finset ι) : ℝ :=
  indicator j AB.1+indicator j AB.2-indicator j AB.1*indicator j AB.2
def duplicate (j : ι) (AB : Finset ι × Finset ι) : ℝ := indicator j AB.1*indicator j AB.2
def fairMarginal (j : ι) (AB : Finset ι × Finset ι) : ℝ :=
  (indicator j AB.1+indicator j AB.2)/2

omit [Fintype ι] [Nonempty ι] in
theorem first_eq_indicator (j : ι) (AB : Finset ι × Finset ι) :
    first j AB=if j ∈ AB.1 ∪ AB.2 then 1 else 0 := by
  by_cases h0 : j ∈ AB.1 <;> by_cases h1 : j ∈ AB.2 <;> simp [first,indicator,h0,h1]

omit [Fintype ι] [Nonempty ι] in
theorem duplicate_eq_indicator (j : ι) (AB : Finset ι × Finset ι) :
    duplicate j AB=if j ∈ AB.1 ∩ AB.2 then 1 else 0 := by
  by_cases h0 : j ∈ AB.1 <;> by_cases h1 : j ∈ AB.2 <;> simp [duplicate,indicator,h0,h1]

omit [Fintype ι] [Nonempty ι] in
theorem first_add_duplicate (j : ι) (AB : Finset ι × Finset ι) :
    first j AB+duplicate j AB=2*fairMarginal j AB := by
  unfold first duplicate fairMarginal
  ring

omit [Nonempty ι] in
theorem complement_marginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    (complementLaw ξ T b E).expect (indicator j)=complementMarginal ξ T b E j := by
  have hh := (EqualCapacity.canonicalLottery_implements hξ hξ1 (small T) (maskedBids T b E)).2 j
  rw [FiniteLaw.prob_eq_expect] at hh
  convert! hh using 1

omit [Nonempty ι] in
theorem complement_marginal_zero (ξ : ℝ) (T : PureTemplate ι) (b : ι → ℝ)
    (E : Finset ι) (j : ι) (hj : j ∈ E) : complementMarginal ξ T b E j=0 := by
  have hb : maskedBids T b E j=0 := by simp [maskedBids,hj]
  apply EqualCapacity.onSupport_outside
  rw [Existence.PayOnceBounded.mem_positiveSupport,hb]
  exact lt_irrefl _

omit [Nonempty ι] in
theorem completion_pair_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    ((complementLaw ξ T b E).prod (complementLaw ξ T b E)).expect
      (fun AB => first j (attachExclusive T E AB)) =
      if j ∈ E then 1 else 2*complementMarginal ξ T b E j-(complementMarginal ξ T b E j)^2 := by
  have hm := complement_marginal hξ hξ1 T b E j
  by_cases hj : j ∈ E
  · have he : (fun AB : Finset ι × Finset ι => first j (attachExclusive T E AB))=fun _ => (1:ℝ) := by
      ext AB
      unfold attachExclusive
      split_ifs <;> simp [first,indicator,hj]
    rw [he,FiniteLaw.expect_const,if_pos hj]
  · have he : (fun AB : Finset ι × Finset ι => first j (attachExclusive T E AB))=first j := by
      ext AB
      unfold attachExclusive
      split_ifs <;> simp [first,indicator,hj]
    rw [he,if_neg hj]
    unfold first
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_add,FiniteLaw.expect_prod_mul]
    have hleft : ((complementLaw ξ T b E).prod (complementLaw ξ T b E)).expect
        (fun AB => indicator j AB.1)=complementMarginal ξ T b E j := by
      rw [FiniteLaw.expect_prod]
      simp only [FiniteLaw.expect_const,hm]
    have hright : ((complementLaw ξ T b E).prod (complementLaw ξ T b E)).expect
        (fun AB => indicator j AB.2)=complementMarginal ξ T b E j := by
      rw [FiniteLaw.expect_prod]
      simp only [hm,FiniteLaw.expect_const]
    rw [hleft,hright,hm]
    ring

omit [Nonempty ι] in
theorem completion_pair_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    ((complementLaw ξ T b E).prod (complementLaw ξ T b E)).expect
      (fun AB => duplicate j (attachExclusive T E AB)) = (complementMarginal ξ T b E j)^2 := by
  have hm := complement_marginal hξ hξ1 T b E j
  by_cases hj : j ∈ E
  · have hz := complement_marginal_zero ξ T b E j hj
    unfold attachExclusive
    split_ifs
    · have he : (fun AB : Finset ι × Finset ι => duplicate j (AB.1,E ∪ AB.2))=
          fun AB => indicator j AB.1 := by ext AB; simp [duplicate,indicator,hj]
      rw [he,FiniteLaw.expect_prod]
      simp only [FiniteLaw.expect_const,hm,hz,zero_pow (by decide : 2 ≠ 0)]
    · have he : (fun AB : Finset ι × Finset ι => duplicate j (E ∪ AB.1,AB.2))=
          fun AB => indicator j AB.2 := by ext AB; simp [duplicate,indicator,hj]
      rw [he,FiniteLaw.expect_prod]
      simp only [hm,hz,FiniteLaw.expect_const,zero_pow (by decide : 2 ≠ 0)]
  · have he : (fun AB : Finset ι × Finset ι => duplicate j (attachExclusive T E AB))=
        fun AB => indicator j AB.1*indicator j AB.2 := by
      ext AB
      unfold attachExclusive
      split_ifs <;> simp [duplicate,indicator,hj]
    rw [he,FiniteLaw.expect_prod_mul,hm,pow_two]

theorem canonical_path_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι) :
    (canonicalLaw ξ g T b).expect (first j)=
      (pathLaw (weights ξ g T b) (imbalance T) ∅).expect (fun path =>
        let E := finalSet (imbalance T) ∅ path
        if j ∈ E then 1 else 2*complementMarginal ξ T b E j-(complementMarginal ξ T b E j)^2) := by
  rw [canonicalLaw,FiniteLaw.expect_map,expect_pairLaw]
  apply FiniteLaw.expect_congr
  intro path
  exact completion_pair_first hξ hξ1 T b _ j

theorem canonical_path_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι) :
    (canonicalLaw ξ g T b).expect (duplicate j)=
      (pathLaw (weights ξ g T b) (imbalance T) ∅).expect (fun path =>
        (complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j)^2) := by
  rw [canonicalLaw,FiniteLaw.expect_map,expect_pairLaw]
  apply FiniteLaw.expect_congr
  intro path
  exact completion_pair_duplicate hξ hξ1 T b _ j

theorem focal_not_sampled_of_zero_weight (ξ : ℝ) (g : GuardData)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι)
    (hW : (imbalance T : ℝ) < totalWeight (weights ξ g T b))
    (hj : (weights ξ g T b).1 j=0)
    (path : Path ι (imbalance T))
    (hp : 0 < (pathLaw (weights ξ g T b) (imbalance T) ∅).mass path) :
    j ∉ finalSet (imbalance T) ∅ path := by
  intro hmem
  have hw := finalSet_weight_pos (weights ξ g T b) (imbalance T) ∅
    (by simpa using hW) (by simp) path hp j hmem
  rw [hj] at hw
  exact lt_irrefl _ hw

theorem canonical_path_fair_marginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ) (j : ι)
    (hW : (imbalance T : ℝ) < totalWeight (weights ξ g T b))
    (hj : (weights ξ g T b).1 j=0) :
    (canonicalLaw ξ g T b).expect (fairMarginal j)=
      (pathLaw (weights ξ g T b) (imbalance T) ∅).expect (fun path =>
        complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j) := by
  have he : (canonicalLaw ξ g T b).expect (first j)+
      (canonicalLaw ξ g T b).expect (duplicate j)=
      2*(canonicalLaw ξ g T b).expect (fairMarginal j) := by
    rw [← FiniteLaw.expect_add,← FiniteLaw.expect_const_mul]
    exact FiniteLaw.expect_congr _ (first_add_duplicate j)
  rw [canonical_path_first hξ hξ1,canonical_path_duplicate hξ hξ1,
    ← FiniteLaw.expect_add] at he
  have hc : (pathLaw (weights ξ g T b) (imbalance T) ∅).expect
      (fun path => (if j ∈ finalSet (imbalance T) ∅ path then 1 else
        2*complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j-
          (complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j)^2)+
          (complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j)^2)=
      2*(pathLaw (weights ξ g T b) (imbalance T) ∅).expect
        (fun path => complementMarginal ξ T b (finalSet (imbalance T) ∅ path) j) := by
    rw [← FiniteLaw.expect_const_mul]
    apply le_antisymm
    · apply expect_le_of_support
      intro path hp
      rw [if_neg (focal_not_sampled_of_zero_weight ξ g T b j hW hj path hp)]
      ring_nf
      exact le_rfl
    · apply expect_le_of_support
      intro path hp
      rw [if_neg (focal_not_sampled_of_zero_weight ξ g T b j hW hj path hp)]
      ring_nf
      exact le_rfl
  rw [hc] at he
  linarith

def copies (j : ι) (AB : Finset ι × Finset ι) : LowRoute.Copies :=
  (decide (j ∈ AB.1),decide (j ∈ AB.2))

def copyLaw (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (j : ι) : FiniteLaw LowRoute.Copies := (continuationLaw ξ κ g T b).map (copies j)

theorem copyLaw_success (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (j : ι) : LowRoute.success (copyLaw ξ κ g T b j)=
      (continuationLaw ξ κ g T b).expect (first j) := by
  rw [LowRoute.success,copyLaw,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro AB
  by_cases h0 : j ∈ AB.1 <;> by_cases h1 : j ∈ AB.2 <;>
    simp [copies,first,indicator,LowRoute.copySuccess,LowRoute.bit,h0,h1]

theorem copyLaw_duplicate (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι) (b : ι → ℝ)
    (j : ι) : LowRoute.duplicate (copyLaw ξ κ g T b j)=
      (continuationLaw ξ κ g T b).expect (duplicate j) := by
  rw [LowRoute.duplicate,copyLaw,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro AB
  by_cases h0 : j ∈ AB.1 <;> by_cases h1 : j ∈ AB.2 <;>
    simp [copies,duplicate,indicator,LowRoute.copyDuplicate,LowRoute.bit,h0,h1]

section OriginalRow
variable {N : ℕ}

def rowLaw (ξ κ : ℝ) (c : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (ω : Fin N → RowRival) : FiniteLaw (Finset (Fin (N+1)) × Finset (Fin (N+1))) :=
  continuationLaw ξ κ {g with countMargin := countMargin (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)

def actualSuccess (t ξ κ : ℝ) (G : Measure ℝ) (c N : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, (rowLaw ξ κ c g countMargin b ω).expect (first 0)
    ∂(Measure.pi fun _ : Fin N => rivalLaw t 0 (1-t) G)

def actualDuplicate (t ξ κ : ℝ) (G : Measure ℝ) (c N : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, (rowLaw ξ κ c g countMargin b ω).expect (duplicate 0)
    ∂(Measure.pi fun _ : Fin N => rivalLaw t 0 (1-t) G)

def actualCanonicalMarginal (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival,
    let T := patternTemplate c (fun j => (ω j).1)
    let B := rowBids b ω
    if T.residual₀=T.residual₁ then complementMarginal ξ T B ∅ 0
    else guardAlpha ξ {g with countMargin := countMargin (fun j => (ω j).1)} T B*(canonicalLaw ξ g T B).expect (fairMarginal 0)
    ∂(Measure.pi fun _ : Fin N => rivalLaw t 0 (1-t) G)

def actualCanonicalDuplicate (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival,
    let T := patternTemplate c (fun j => (ω j).1)
    let B := rowBids b ω
    if T.residual₀=T.residual₁ then (complementMarginal ξ T B ∅ 0)^2
    else guardAlpha ξ {g with countMargin := countMargin (fun j => (ω j).1)} T B*(canonicalLaw ξ g T B).expect (duplicate 0)
    ∂(Measure.pi fun _ : Fin N => rivalLaw t 0 (1-t) G)

def sourceSuccess (i : Uniform07.Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  actualSuccess (Uniform07.cutoff i) (Uniform07.xi i) (Uniform07.kappa i)
    (G.map Prod.snd) (Uniform07.capacity m) (m-1) g countMargin b

def sourceDuplicate (i : Uniform07.Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  actualDuplicate (Uniform07.cutoff i) (Uniform07.xi i) (Uniform07.kappa i)
    (G.map Prod.snd) (Uniform07.capacity m) (m-1) g countMargin b

def sourceCanonicalMarginal (i : Uniform07.Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  actualCanonicalMarginal (Uniform07.cutoff i) (Uniform07.xi i)
    (G.map Prod.snd) (Uniform07.capacity m) (m-1) g countMargin b

def sourceCanonicalDuplicate (i : Uniform07.Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  actualCanonicalDuplicate (Uniform07.cutoff i) (Uniform07.xi i)
    (G.map Prod.snd) (Uniform07.capacity m) (m-1) g countMargin b

end OriginalRow
end FCAppendix.Affine.Uniform06.LiteralExperiment
