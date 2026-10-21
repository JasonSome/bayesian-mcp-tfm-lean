import FCAppendix.Affine.Uniform06.ReceiptGap
import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.CanonicalCoarse
import FCAppendix.Affine.Uniform06.LiteralKernelIdentity
import FCAppendix.Affine.Uniform06.CoarseIntegralBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralCoarsePath

open MeasureTheory Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment SourceGuardGeometry EntryOwnImpact
open ReciprocalSecantBounds CanonicalCoarse LiteralKernelIdentity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def branchWeight (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) : ℝ :=
  if T.residual₀=T.residual₁ then 1 else guardAlpha ξ g T B

def numericMarginal (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι) : ℝ :=
  if T.residual₀=T.residual₁ then complementMarginal ξ T B ∅ j
  else guardAlpha ξ g T B*(canonicalLaw ξ g T B).expect (fairMarginal j)

def numericDuplicate (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι) : ℝ :=
  if T.residual₀=T.residual₁ then (complementMarginal ξ T B ∅ j)^2
  else guardAlpha ξ g T B*(canonicalLaw ξ g T B).expect (duplicate j)

omit [Nonempty ι] in
lemma branchWeight_bounds (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) :
    branchWeight ξ g T B ∈ Icc (0 : ℝ) 1 := by
  unfold branchWeight
  split_ifs
  · norm_num
  · exact guardAlpha_bounds ξ g T B

omit [Fintype ι] [Nonempty ι] in
private lemma empty_finalSet_of_length_zero {n : ℕ} (hn : n=0) (p : Path ι n) :
    finalSet n (∅ : Finset ι) p=∅ := by
  subst n
  rfl

theorem numeric_path_moments {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : B j ≤ g.multiplier) :
    numericMarginal ξ g T B j=branchWeight ξ g T B*
      (pathLaw (weights ξ g T B) (imbalance T) ∅).expect
        (fun path => complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j) ∧
    numericDuplicate ξ g T B j=branchWeight ξ g T B*
      (pathLaw (weights ξ g T B) (imbalance T) ∅).expect
        (fun path => (complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j)^2) := by
  classical
  by_cases he : T.residual₀=T.residual₁
  · have hd : imbalance T=0 := by simp [imbalance,small,he]
    have hfinal (path : Path ι (imbalance T)) : finalSet (imbalance T) ∅ path=∅ :=
      empty_finalSet_of_length_zero hd path
    simp only [numericMarginal,numericDuplicate,branchWeight,if_pos he,one_mul]
    constructor
    · simpa only [hfinal] using (FiniteLaw.expect_const
        (pathLaw (weights ξ g T B) (imbalance T) ∅) (complementMarginal ξ T B ∅ j)).symm
    · simpa only [hfinal] using (FiniteLaw.expect_const
        (pathLaw (weights ξ g T B) (imbalance T) ∅) ((complementMarginal ξ T B ∅ j)^2)).symm
  · simp only [numericMarginal,numericDuplicate,branchWeight,if_neg he]
    by_cases hα : guardAlpha ξ g T B=0
    · simp [hα]
    · have hαp : 0 < guardAlpha ξ g T B :=
        lt_of_le_of_ne (guardAlpha_bounds ξ g T B).1 (Ne.symm hα)
      have hW : (imbalance T : ℝ) < totalWeight (weights ξ g T B) := by
        have hh := positive_guard_weight g T B hε hM hαp
        nlinarith [mul_pos hε hM]
      exact ⟨congrArg (fun x => guardAlpha ξ g T B*x)
        (canonical_path_fair_marginal hξ hξ1 g T B j hW (low_focal_weight_zero g T B j hr hb)),
        congrArg (fun x => guardAlpha ξ g T B*x) (canonical_path_duplicate hξ hξ1 g T B j)⟩

theorem numeric_moments_upper {ξ A D : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : B j ≤ g.multiplier) (hA : 0 < A)
    (hpoint : 0 < branchWeight ξ g T B → ∀ path : Path ι (imbalance T),
      0 < (pathLaw (weights ξ g T B) (imbalance T) ∅).mass path →
        complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j ≤ max 0 D/A) :
    numericMarginal ξ g T B j ≤ max 0 D/A ∧
      numericDuplicate ξ g T B j ≤ (max 0 D)^2/A^2 := by
  have he := numeric_path_moments hξ hξ1 g T B j hε hM hr hb
  rw [he.1,he.2]
  have hα := branchWeight_bounds ξ g T B
  have hD : 0 ≤ max 0 D/A := div_nonneg (le_max_left _ _) hA.le
  by_cases hz : branchWeight ξ g T B=0
  · simp only [hz,zero_mul]
    exact ⟨hD,by positivity⟩
  · have hp : 0 < branchWeight ξ g T B := lt_of_le_of_ne hα.1 (Ne.symm hz)
    have hfirst := expect_le_const
      (pathLaw (weights ξ g T B) (imbalance T) ∅) _ (max 0 D/A) (hpoint hp)
    have hsecond := expect_le_const
      (pathLaw (weights ξ g T B) (imbalance T) ∅)
      (fun path => (complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j)^2)
      (C := (max 0 D/A)^2) (fun path hpath => by
        have hc0 := (EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1
          (maskedBids T B (finalSet (imbalance T) ∅ path))).1 j
        have hc := hpoint hp path hpath
        change 0 ≤ complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j at hc0
        nlinarith)
    constructor
    · exact (mul_le_mul_of_nonneg_left hfirst hα.1).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hα.2 hD)
    · have hh := (mul_le_mul_of_nonneg_left hsecond hα.1).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hα.2 (sq_nonneg _))
      simpa only [div_pow] using hh

omit [Nonempty ι] in
lemma demand_after_removal (ξ z : ℝ) (B : ι → ℝ) (E : Finset ι) (j : ι) (hj : j ∉ E) :
    remainingDemand ξ B (insert j E) z=
      remainingDemand ξ B {j} z-∑ k ∈ E,exposure ξ z (B k) := by
  have he : remainingDemand ξ B (insert j E) z+
      (∑ k ∈ E,exposure ξ z (B k))=remainingDemand ξ B {j} z := by
    rw [show (∑ k ∈ E,exposure ξ z (B k))=
      ∑ k,if k ∈ E then exposure ξ z (B k) else 0 by simp]
    unfold remainingDemand
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkj : k=j
    · subst k
      simp [hj]
    · by_cases hkE : k ∈ E <;> simp [hkj,hkE]
  linarith

def balancedTemplateDeficit (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ) (j : ι) : ℝ :=
  (small T : ℝ)+(imbalance T : ℝ)/2-remainingDemand ξ B {j} (B j)

omit [Nonempty ι] in

theorem focalDeficit_eq_balanced (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (hj : j ∉ E) (hcard : E.card=imbalance T) :
    focalDeficit ξ T B E j=balancedTemplateDeficit ξ T B j-
      ∑ k ∈ E,((1 : ℝ)/2-exposure ξ (B j) (B k)) := by
  rw [focalDeficit,demand_after_removal ξ (B j) B E j hj,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,hcard,balancedTemplateDeficit]
  ring

omit [Nonempty ι] in
lemma masked_demand_eq {ξ z : ℝ} (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (hz : 0 < z)
    (hout : ∀ k,k ∉ T.support → B k=0) :
    remainingDemand ξ (maskedBids T B E) {j} z=remainingDemand ξ B (insert j E) z := by
  unfold remainingDemand
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k=j
  · simp [hkj]
  · by_cases hkE : k ∈ E
    · simp [hkj,hkE,maskedBids,exposure_zero hz.le]
    · by_cases hkT : k ∈ T.support
      · simp [hkj,hkE,hkT,maskedBids]
      · simp [hkj,hkE,hkT,maskedBids,hout k hkT,exposure_zero hz.le]

omit [Nonempty ι] in
lemma masked_reciprocal_eq (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) {z : ℝ} (hz : 0 < z)
    (hout : ∀ k,k ∉ T.support → B k=0) :
    reciprocalSum (maskedBids T B E) {j} z=reciprocalSum B (insert j E) z := by
  unfold reciprocalSum
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k=j
  · simp [hkj]
  · by_cases hkE : k ∈ E
    · simp [hkj,hkE,maskedBids,reciprocalTerm,not_lt.mpr hz.le]
    · by_cases hkT : k ∈ T.support
      · simp [hkj,hkE,hkT,maskedBids]
      · simp [hkj,hkE,hkT,maskedBids,hout k hkT,reciprocalTerm,not_lt.mpr hz.le]

omit [Nonempty ι] in

theorem complement_upper_from_active_strip {ξ lo U q : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hU : 0 < U) (hq : 0 < q)
    (T : PureTemplate ι) (B : ι → ℝ) (E S : Finset ι) (j : ι)
    (hjT : j ∈ T.support) (hjE : j ∉ E) (hlb : lo < B j)
    (hBU : ∀ k,B k ≤ U) (hout : ∀ k,k ∉ T.support → B k=0)
    (hguard : (1-ξ)*U ≤ lo)
    (hS : ∀ k ∈ S,B j < B k ∧ B k ≤ U)
    (hcount : q ≤ (S.card : ℝ)-(E.card : ℝ)-1) :
    complementMarginal ξ T B E j ≤ max 0 (focalDeficit ξ T B E j)/
      ((B j-lo)*q/(ξ*U)) := by
  have hb : 0 < B j := hlo.trans hlb
  have hBf : maskedBids T B E j=B j := by simp [maskedBids,hjT,hjE]
  have hmask : ∀ k,maskedBids T B E k ≤ U := by
    intro k
    unfold maskedBids
    split_ifs
    · exact hBU k
    · exact hU.le
  have hcard : ((insert j E).card : ℝ)=(E.card : ℝ)+1 := by
    rw [Finset.card_insert_of_notMem hjE]
    push_cast
    rfl
  have hR := reciprocalSum_active_strip_lower B (insert j E) S hb hU hS
  have hqR : q/U ≤ reciprocalSum (maskedBids T B E) {j} (B j) := by
    rw [masked_reciprocal_eq T B E j hb hout]
    rw [hcard] at hR
    exact (div_le_div_of_nonneg_right (by linarith : q ≤ (S.card : ℝ)-((E.card : ℝ)+1)) hU.le).trans hR
  have hRp : 0 < reciprocalSum (maskedBids T B E) {j} (maskedBids T B E j) := by
    rw [hBf]
    exact (div_pos hq hU).trans_le hqR
  have hp := actual_marginal_upper hξ hξ1 hlo (small T) (maskedBids T B E) j
    (by simpa only [hBf] using hlb) hmask hguard hRp
  rw [hBf,masked_demand_eq T B E j hb hout] at hp
  have hA : 0 < (B j-lo)*q/(ξ*U) := by positivity
  have hgain : (B j-lo)*q/(ξ*U) ≤
      gain ξ lo (B j) (reciprocalSum (maskedBids T B E) {j} (B j)) := by
    have hh := mul_le_mul_of_nonneg_left hqR (sub_pos.mpr hlb).le
    have ht := div_le_div_of_nonneg_right hh hξ.le
    unfold gain
    convert! ht using 1
    ring
  exact hp.trans (div_le_div_of_nonneg_left (le_max_left _ _) hA hgain)

omit [Nonempty ι] in

theorem complement_upper_balanced_gap {ξ lo U q a : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hU : 0 < U) (hq : 0 < q)
    (T : PureTemplate ι) (B : ι → ℝ) (E S : Finset ι) (j : ι)
    (hjT : j ∈ T.support) (hjE : j ∉ E) (hlb : lo < B j)
    (hBU : ∀ k,B k ≤ U) (hout : ∀ k,k ∉ T.support → B k=0)
    (hguard : (1-ξ)*U ≤ lo)
    (hS : ∀ k ∈ S,B j < B k ∧ B k ≤ U)
    (hcount : q ≤ (S.card : ℝ)-(E.card : ℝ)-1)
    (hcard : E.card=imbalance T)
    (hgap : ∀ k ∈ E,a ≤ 1/2-exposure ξ (B j) (B k)) :
    complementMarginal ξ T B E j ≤
      max 0 (balancedTemplateDeficit ξ T B j-a*(imbalance T : ℝ))/
        ((B j-lo)*q/(ξ*U)) := by
  have h := complement_upper_from_active_strip hξ hξ1 hlo hU hq T B E S j
    hjT hjE hlb hBU hout hguard hS hcount
  rw [focalDeficit_eq_balanced ξ T B E j hjE hcard] at h
  have hs : a*(imbalance T : ℝ) ≤ ∑ k ∈ E,((1 : ℝ)/2-exposure ξ (B j) (B k)) := by
    have hh := Finset.sum_le_sum hgap
    simpa only [Finset.sum_const,nsmul_eq_mul,hcard,mul_comm] using hh
  have hA : 0 ≤ (B j-lo)*q/(ξ*U) := by positivity
  exact h.trans (div_le_div_of_nonneg_right
    (max_le_max_left 0 (sub_le_sub_left hs _)) hA)

theorem branch_path_geometry {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hr : 0 < g.requiredDemand) (hb : B j ≤ g.multiplier)
    (hbranch : 0 < branchWeight ξ g T B)
    (path : Path ι (imbalance T))
    (hp : 0 < (pathLaw (weights ξ g T B) (imbalance T) ∅).mass path) :
    (finalSet (imbalance T) ∅ path).card=imbalance T ∧
      j ∉ finalSet (imbalance T) ∅ path := by
  by_cases he : T.residual₀=T.residual₁
  · have hd : imbalance T=0 := by simp [imbalance,small,he]
    have hE : finalSet (imbalance T) ∅ path=∅ := empty_finalSet_of_length_zero hd path
    simp only [hE,hd,Finset.card_empty,Finset.notMem_empty,not_false_eq_true,and_self]

  · have hα : 0 < guardAlpha ξ g T B := by
      simpa only [branchWeight,if_neg he] using hbranch
    have hW : (imbalance T : ℝ) < totalWeight (weights ξ g T B) := by
      have hh := positive_guard_weight g T B hε hM hα
      nlinarith [mul_pos hε hM]
    refine ⟨?_,focal_not_sampled_of_zero_weight ξ g T B j hW
      (low_focal_weight_zero g T B j hr hb) path hp⟩
    simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using
      finalSet_card (weights ξ g T B) (imbalance T) ∅ (by simpa using hW) path hp

theorem numeric_moments_from_active_strip (i : Uniform07.Row)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (S : Finset ι) (j : ι)
    {lo q : ℝ} (hlo : 0 < lo) (hq : 0 < q)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hroot : Uniform07.entry i-Uniform07.cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ Uniform07.cutoff i/100)
    (hguardLower : 0 < g.multiplier-g.radius)
    (hjT : j ∈ T.support) (hlb : lo < B j) (hb : B j ≤ g.multiplier)
    (hcap : ∀ k,B k ≤ ReceiptGap.cap i)
    (hout : ∀ k,k ∉ T.support → B k=0)
    (hloGuard : (1-Uniform07.xi i)*ReceiptGap.cap i ≤ lo)
    (hS : ∀ k ∈ S,B j < B k ∧ B k ≤ ReceiptGap.cap i)
    (hcount : q ≤ (S.card : ℝ)-(imbalance T : ℝ)-1) :
    let a := Uniform07.cutoff i/(25*Uniform07.xi i*ReceiptGap.cap i)
    let D := balancedTemplateDeficit (Uniform07.xi i) T B j-a*(imbalance T : ℝ)
    let A := (B j-lo)*q/(Uniform07.xi i*ReceiptGap.cap i)
    numericMarginal (Uniform07.xi i) g T B j ≤ max 0 D/A ∧
      numericDuplicate (Uniform07.xi i) g T B j ≤ (max 0 D)^2/A^2 := by
  let a := Uniform07.cutoff i/(25*Uniform07.xi i*ReceiptGap.cap i)
  have hξ := Uniform07.xi_pos i
  have hξ1 : Uniform07.xi i < 1 := by cases i <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hA : 0 < (B j-lo)*q/(Uniform07.xi i*ReceiptGap.cap i) := by
    have hu := (ReceiptGap.cap_bounds i).1
    positivity
  apply numeric_moments_upper hξ hξ1 g T B j hε hM hr hb hA
  intro hbranch path hp
  let E := finalSet (imbalance T) ∅ path
  have he := branch_path_geometry g T B j hε hM hr hb hbranch path hp
  have hp0 : 0 ≤ complementMarginal (Uniform07.xi i) T B E j :=
    (EqualCapacity.positiveMarginal_spec (Uniform07.xi i) (small T) hξ hξ1
      (maskedBids T B E)).1 j
  by_cases hz : complementMarginal (Uniform07.xi i) T B E j=0
  · rw [hz]
    exact div_nonneg (le_max_left _ _) hA.le
  · have hpPos : 0 < complementMarginal (Uniform07.xi i) T B E j :=
      lt_of_le_of_ne hp0 (Ne.symm hz)
    have hgap : ∀ k ∈ E,a ≤ 1/2-exposure (Uniform07.xi i) (B j) (B k) := by
      intro k hk
      by_cases hEq : T.residual₀=T.residual₁
      · have hd : imbalance T=0 := by simp [imbalance,small,hEq]
        have hE0 : E=∅ := Finset.card_eq_zero.mp (he.1.trans hd)
        rw [hE0] at hk
        exact (Finset.notMem_empty k hk).elim
      · have hα : 0 < guardAlpha (Uniform07.xi i) g T B := by
          simpa only [branchWeight,if_neg hEq] using hbranch
        exact ReceiptGap.supported_sample_h_lower i g T B j E hroot hradius hε hM
          hguardLower hout hα he.1.le hpPos k (hcap k) (hcap j)
    exact complement_upper_balanced_gap hξ hξ1 hlo (ReceiptGap.cap_bounds i).1 hq
      T B E S j hjT he.2 hlb hcap hout hloGuard hS
      (by
        have hEcard : E.card=imbalance T := he.1
        simpa only [hEcard] using hcount) he.1 hgap

section Original

def originalRowMarginal {N : ℕ} (ξ : ℝ) (c : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  numericMarginal ξ {g with countMargin := countMargin (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0

def originalRowDuplicate {N : ℕ} (ξ : ℝ) (c : ℕ) (g : GuardData)
    (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  numericDuplicate ξ {g with countMargin := countMargin (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0

theorem sourceCanonicalMarginal_eq_integral (i : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) (g : GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) :
    sourceCanonicalMarginal i m G g countMargin b=
      ∫ ω : Fin (m-1) → RowRival,
        originalRowMarginal (Uniform07.xi i) (Uniform07.capacity m) g countMargin b ω
          ∂Measure.pi (fun _ => RawMixedSource.source i G) := by
  rfl

theorem sourceCanonicalDuplicate_eq_integral (i : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) (g : GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) :
    sourceCanonicalDuplicate i m G g countMargin b=
      ∫ ω : Fin (m-1) → RowRival,
        originalRowDuplicate (Uniform07.xi i) (Uniform07.capacity m) g countMargin b ω
          ∂Measure.pi (fun _ => RawMixedSource.source i G) := by
  rfl

theorem original_row_path_moments {N : ℕ} {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (countMargin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : b ≤ g.multiplier) (ω : Fin N → RowRival) :
    let T := patternTemplate c (fun j => (ω j).1)
    let B := rowBids b ω
    let g' := {g with countMargin := countMargin (fun j => (ω j).1)}
    originalRowMarginal ξ c g countMargin b ω=branchWeight ξ g' T B*
      (pathLaw (weights ξ g' T B) (imbalance T) ∅).expect
        (fun path => complementMarginal ξ T B (finalSet (imbalance T) ∅ path) 0) ∧
    originalRowDuplicate ξ c g countMargin b ω=branchWeight ξ g' T B*
      (pathLaw (weights ξ g' T B) (imbalance T) ∅).expect
        (fun path => (complementMarginal ξ T B (finalSet (imbalance T) ∅ path) 0)^2) := by
  dsimp only
  exact numeric_path_moments hξ hξ1 _ _ _ 0 hε hM hr
    (by simpa only [rowBids,Fin.cons_zero] using hb)

end Original
end FCAppendix.Affine.Uniform06.LiteralCoarsePath
