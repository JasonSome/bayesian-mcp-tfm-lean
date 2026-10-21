import FCAppendix.Affine.Uniform06.RawTiltedSource
import FCAppendix.Affine.Uniform06.BalancedDeficit

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawDeficitGeometry

open Set MeasureTheory LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralCoarsePath RawMixedSource RawTiltedSource
open CanonicalCoarse LiteralKernelIdentity

variable {N : ℕ}

theorem residuals_literal (c : ℕ) (ω : Fin N → RowRival) :
    (patternTemplate c (fun j => (ω j).1)).residual₀=
      min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω) ∧
    (patternTemplate c (fun j => (ω j).1)).residual₁=
      min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) := by
  constructor <;> rfl

theorem residuals_unclamped (c : ℕ) (ω : Fin N → RowRival)
    (hroom₀ : c-classCount 1 ω-classCount 2 ω ≤ 1+classCount 0 ω)
    (hroom₁ : c-classCount 1 ω-classCount 3 ω ≤ 1+classCount 0 ω) :
    (patternTemplate c (fun j => (ω j).1)).residual₀=c-classCount 1 ω-classCount 2 ω ∧
    (patternTemplate c (fun j => (ω j).1)).residual₁=c-classCount 1 ω-classCount 3 ω := by
  rw [(residuals_literal c ω).1,(residuals_literal c ω).2]
  exact ⟨min_eq_right hroom₀,min_eq_right hroom₁⟩

theorem small_plus_half_imbalance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : PureTemplate ι) :
    (small T : ℝ)+(imbalance T : ℝ)/2=
      ((T.residual₀ : ℝ)+(T.residual₁ : ℝ))/2 := by
  rcases le_total T.residual₀ T.residual₁ with h | h
  · simp only [small,imbalance,min_eq_left h,max_eq_right h,Nat.cast_sub h]
    ring
  · simp only [small,imbalance,min_eq_right h,max_eq_left h,Nat.cast_sub h]
    ring

theorem raw_lower_demand (ξ : ℝ) {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival) :
    remainingDemand ξ (rowBids b ω) {0} b=
      ∑ j,if (ω j).1=0 then exposure ξ b (ω j).2 else 0 := by
  unfold remainingDemand
  rw [Fin.sum_univ_succ]
  simp only [rowBids,Fin.cons_zero,Fin.cons_succ,Finset.mem_singleton,
    Fin.succ_ne_zero,if_false,if_true,zero_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω j).1=0
  · simp [hj]
  · simp [hj,exposure_zero hb.le]

theorem raw_demand_decomposition (ξ : ℝ) {b : ℝ} (hb : 0 < b)
    (ω : Fin N → RowRival) :
    FCAppendix.ExponentialTilt.iidSum (RawMixedSource.demand ξ b) N ω=
      remainingDemand ξ (rowBids b ω) {0} b+(classCount 1 ω : ℝ)+
        ((classCount 2 ω : ℝ)+(classCount 3 ω : ℝ))/2 := by
  rw [raw_lower_demand ξ hb]
  have hcoord (r : RowRival) : RawMixedSource.demand ξ b r=
      (if r.1=0 then exposure ξ b r.2 else 0)+
        (if r.1=1 then (1 : ℝ) else 0)+
        ((if r.1=2 then (1 : ℝ) else 0)+(if r.1=3 then (1 : ℝ) else 0))/2 := by
    generalize h : r.1=k
    fin_cases k <;> norm_num [RawMixedSource.demand,h,Fin.ext_iff]
  simp only [FCAppendix.ExponentialTilt.iidSum,hcoord,Finset.sum_add_distrib]
  rw [← Finset.sum_div,Finset.sum_add_distrib]
  simp [classCount]

theorem template_deficit_eq_raw (i : Uniform07.Row) (c : ℕ) {b : ℝ} (hb : 0 < b)
    (ω : Fin N → RowRival)
    (hcap₀ : classCount 1 ω+classCount 2 ω ≤ c)
    (hcap₁ : classCount 1 ω+classCount 3 ω ≤ c)
    (hroom₀ : c-classCount 1 ω-classCount 2 ω ≤ 1+classCount 0 ω)
    (hroom₁ : c-classCount 1 ω-classCount 3 ω ≤ 1+classCount 0 ω) :
    balancedTemplateDeficit (Uniform07.xi i)
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0=deficit i b c ω := by
  have hr := residuals_unclamped c ω hroom₀ hroom₁
  have hA : classCount 1 ω ≤ c := by omega
  have h0 : classCount 2 ω ≤ c-classCount 1 ω := by omega
  have h1 : classCount 3 ω ≤ c-classCount 1 ω := by omega
  unfold balancedTemplateDeficit deficit
  rw [small_plus_half_imbalance,hr.1,hr.2,
    Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub hA,
    raw_demand_decomposition (Uniform07.xi i) hb]
  simp only [rowBids,Fin.cons_zero]
  ring

theorem template_imbalance_eq_draws (c : ℕ) (ω : Fin N → RowRival)
    (hcap₀ : classCount 1 ω+classCount 2 ω ≤ c)
    (hcap₁ : classCount 1 ω+classCount 3 ω ≤ c)
    (hroom₀ : c-classCount 1 ω-classCount 2 ω ≤ 1+classCount 0 ω)
    (hroom₁ : c-classCount 1 ω-classCount 3 ω ≤ 1+classCount 0 ω) :
    imbalance (patternTemplate c (fun j => (ω j).1))=draws ω := by
  have hr := residuals_unclamped c ω hroom₀ hroom₁
  rw [imbalance,small,hr.1,hr.2]
  unfold draws
  rcases le_total (classCount 2 ω) (classCount 3 ω) with h | h
  · rw [max_eq_left (by omega),min_eq_right (by omega)]
    omega
  · rw [max_eq_right (by omega),min_eq_left (by omega)]
    omega

theorem equal_residuals_of_zero_sign (c : ℕ) (ω : Fin N → RowRival)
    (hy : imbalanceSum ω=0) :
    (patternTemplate c (fun j => (ω j).1)).residual₀=
      (patternTemplate c (fun j => (ω j).1)).residual₁ := by
  have hh : (classCount 2 ω : ℝ)=(classCount 3 ω : ℝ) := by
    have hs := imbalanceSum_cast ω
    rw [hy,Int.cast_zero,RawMixedSource.sign_count] at hs
    linarith
  have hc : classCount 2 ω=classCount 3 ω := by exact_mod_cast hh
  rw [(residuals_literal c ω).1,(residuals_literal c ω).2,hc]

theorem template_deficit_le_raw_of_positive_small (i : Uniform07.Row) (c : ℕ)
    {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival)
    (hs : 0 < small (patternTemplate c (fun j => (ω j).1))) :
    balancedTemplateDeficit (Uniform07.xi i)
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0 ≤ deficit i b c ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hr0 : 0 < T.residual₀ := lt_of_lt_of_le hs (min_le_left _ _)
  have hr1 : 0 < T.residual₁ := lt_of_lt_of_le hs (min_le_right _ _)
  have hres0 : T.residual₀ ≤ c-classCount 1 ω-classCount 2 ω := by
    rw [(residuals_literal c ω).1]
    exact min_le_right _ _
  have hres1 : T.residual₁ ≤ c-classCount 1 ω-classCount 3 ω := by
    rw [(residuals_literal c ω).2]
    exact min_le_right _ _
  have hA : classCount 1 ω ≤ c := by omega
  have h0 : classCount 2 ω ≤ c-classCount 1 ω := by omega
  have h1 : classCount 3 ω ≤ c-classCount 1 ω := by omega
  have hres0R : (T.residual₀ : ℝ) ≤ (c : ℝ)-classCount 1 ω-classCount 2 ω := by
    have hh : (T.residual₀ : ℝ) ≤ ((c-classCount 1 ω-classCount 2 ω : ℕ) : ℝ) := by
      exact_mod_cast hres0
    simpa only [Nat.cast_sub h0,Nat.cast_sub hA] using hh
  have hres1R : (T.residual₁ : ℝ) ≤ (c : ℝ)-classCount 1 ω-classCount 3 ω := by
    have hh : (T.residual₁ : ℝ) ≤ ((c-classCount 1 ω-classCount 3 ω : ℕ) : ℝ) := by
      exact_mod_cast hres1
    simpa only [Nat.cast_sub h1,Nat.cast_sub hA] using hh
  unfold balancedTemplateDeficit deficit
  rw [small_plus_half_imbalance,raw_demand_decomposition (Uniform07.xi i) hb]
  simp only [rowBids,Fin.cons_zero]
  dsimp [T] at hres0R hres1R
  linarith

section PositiveKernels

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
lemma positive_marginal_capacity {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (B : ι → ℝ) (j : ι) (hp : 0 < EqualCapacity.positiveMarginal ξ c B j) :
    0 < c := by
  have hs := EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 B
  have hle : EqualCapacity.positiveMarginal ξ c B j ≤
      ∑ k, EqualCapacity.positiveMarginal ξ c B k :=
    Finset.single_le_sum (fun k _ => hs.1 k) (Finset.mem_univ j)
  rw [hs.2.2] at hle
  have hc : ((min c (Existence.PayOnceBounded.positiveSupport B).card : ℕ) : ℝ) ≤ c := by
    exact_mod_cast min_le_left c (Existence.PayOnceBounded.positiveSupport B).card
  exact_mod_cast hp.trans_le (hle.trans hc)

lemma exists_positive_path {α : Type*} [Fintype α]
    (P : FCAppendix.FiniteLaw α) (f : α → ℝ) (hf : 0 < P.expect f) :
    ∃ p, 0 < P.mass p ∧ 0 < f p := by
  by_contra hn
  push Not at hn
  have hh := FCAppendix.Affine.WeightedSampling.expect_le_const P f 0 hn
  exact (not_le_of_gt hf) hh

theorem numeric_unit_and_duplicate_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hb : B j ≤ g.multiplier) :
    numericMarginal ξ g T B j ∈ Icc (0 : ℝ) 1 ∧
      numericDuplicate ξ g T B j ∈ Icc (0 : ℝ) 1 ∧
      numericDuplicate ξ g T B j ≤ numericMarginal ξ g T B j := by
  have he := numeric_path_moments hξ hξ1 g T B j hε hM hr hb
  rw [he.1,he.2]
  let P := pathLaw (weights ξ g T B) (imbalance T) ∅
  let p := fun path => complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j
  have hp (path) : p path ∈ Icc (0 : ℝ) 1 := by
    have hh := EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1
      (maskedBids T B (finalSet (imbalance T) ∅ path))
    exact ⟨hh.1 j,hh.2.1 j⟩
  have hα := branchWeight_bounds ξ g T B
  have hp0 := FCAppendix.Affine.WeightedSampling.expect_nonneg P p (fun x => (hp x).1)
  have hp1 := FCAppendix.Affine.WeightedSampling.expect_le_const P p 1 (fun x _ => (hp x).2)
  have hq0 := FCAppendix.Affine.WeightedSampling.expect_nonneg P (fun x => (p x)^2)
    (fun x => sq_nonneg _)
  have hqp := expect_le_of_support P (fun x => (p x)^2) p (fun x _ => by
    nlinarith [(hp x).1,(hp x).2])
  have hq1 : P.expect (fun x => (p x)^2) ≤ 1 := hqp.trans hp1
  refine ⟨⟨mul_nonneg hα.1 hp0,?_⟩,⟨mul_nonneg hα.1 hq0,?_⟩,?_⟩
  · exact (mul_le_mul_of_nonneg_left hp1 hα.1).trans (by simpa using hα.2)
  · exact (mul_le_mul_of_nonneg_left hq1 hα.1).trans (by simpa using hα.2)
  · exact mul_le_mul_of_nonneg_left hqp hα.1

end PositiveKernels

theorem original_positive_implies_raw_deficit (i : Uniform07.Row) (c : ℕ)
    (g : GuardData) (countMargin : (Fin N → Fin 4) → ℝ)
    {b : ℝ} (hb : 0 < b) (hbL : b ≤ g.multiplier)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hroot : Uniform07.entry i-Uniform07.cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ Uniform07.cutoff i/100)
    (hguardLower : 0 < g.multiplier-g.radius)
    (ω : Fin N → RowRival)
    (hcap : ∀ k,rowBids b ω k ≤ ReceiptGap.cap i)
    (hpos : 0 < originalRowMarginal (Uniform07.xi i) c g countMargin b ω) :
    0 < deficit i b c ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' : GuardData := {g with countMargin := countMargin (fun j => (ω j).1)}
  have hξ := Uniform07.xi_pos i
  have hξ1 : Uniform07.xi i < 1 := by
    cases i <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hB : B 0=b := rfl
  have hout : ∀ k,k ∉ T.support → B k=0 := rowBids_outside c b ω
  have hT : (0 : Fin (N+1)) ∈ T.support := focal_mem_patternTemplate c _
  have he := numeric_path_moments hξ hξ1 g' T B 0 hε hM hr (by simpa [hB] using hbL)
  change 0 < numericMarginal (Uniform07.xi i) g' T B 0 at hpos
  rw [he.1] at hpos
  have hα : 0 < branchWeight (Uniform07.xi i) g' T B := by
    by_contra hn
    have hz : branchWeight (Uniform07.xi i) g' T B=0 :=
      le_antisymm (le_of_not_gt hn) (branchWeight_bounds _ _ _ _).1
    rw [hz,zero_mul] at hpos
    exact lt_irrefl _ hpos
  have hEp : 0 < (pathLaw (weights (Uniform07.xi i) g' T B) (imbalance T) ∅).expect
      (fun path => complementMarginal (Uniform07.xi i) T B (finalSet (imbalance T) ∅ path) 0) := by
    rcases mul_pos_iff.mp hpos with hh | hh
    · exact hh.2
    · exact False.elim ((not_lt_of_ge hα.le) hh.1)
  obtain ⟨path,hpath,hp⟩ := exists_positive_path _ _ hEp
  let E := finalSet (imbalance T) ∅ path
  have hE := branch_path_geometry g' T B 0 hε hM hr (by simpa [hB] using hbL) hα path hpath
  have hnot : (0 : Fin (N+1)) ∉ E := hE.2
  have hmask : maskedBids T B E 0=b := by simp [maskedBids,hT,hnot,hB]
  have hs : 0 < small T := positive_marginal_capacity hξ hξ1 (small T)
    (maskedBids T B E) 0 hp
  have hD : 0 < focalDeficit (Uniform07.xi i) T B E 0 := by
    have hh := actual_positive_implies_deficit_positive hξ hξ1 (small T)
      (maskedBids T B E) 0 (by simpa only [hmask] using hb) hp
    rw [hmask,masked_demand_eq T B E 0 hb hout] at hh
    simpa only [focalDeficit,hB] using hh
  have hsum : 0 ≤ ∑ k ∈ E,((1 : ℝ)/2-exposure (Uniform07.xi i) (B 0) (B k)) := by
    apply Finset.sum_nonneg
    intro k hk
    by_cases hEq : T.residual₀=T.residual₁
    · have hd : imbalance T=0 := by simp [imbalance,small,hEq]
      have hE0 : E=∅ := Finset.card_eq_zero.mp (hE.1.trans hd)
      rw [hE0] at hk
      exact (Finset.notMem_empty k hk).elim
    · have hα' : 0 < guardAlpha (Uniform07.xi i) g' T B := by
        simpa only [branchWeight,if_neg hEq] using hα
      have hg := ReceiptGap.supported_sample_h_lower i g' T B 0 E hroot hradius hε hM
        hguardLower hout hα' hE.1.le hp k (hcap k) (hcap 0)
      exact (div_nonneg (Uniform07.cutoff_pos i).le (by
        have hu := (ReceiptGap.cap_bounds i).1
        positivity)).trans hg
  rw [focalDeficit_eq_balanced _ T B E 0 hE.2 hE.1] at hD
  have htemplate : 0 < balancedTemplateDeficit (Uniform07.xi i) T B 0 := by linarith
  exact htemplate.trans_le (template_deficit_le_raw_of_positive_small i c hb ω hs)

theorem original_duplicate_positive_implies_raw_deficit (i : Uniform07.Row) (c : ℕ)
    (g : GuardData) (countMargin : (Fin N → Fin 4) → ℝ)
    {b : ℝ} (hb : 0 < b) (hbL : b ≤ g.multiplier)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hroot : Uniform07.entry i-Uniform07.cutoff i/200 ≤ g.multiplier)
    (hradius : g.radius ≤ Uniform07.cutoff i/100)
    (hguardLower : 0 < g.multiplier-g.radius)
    (ω : Fin N → RowRival)
    (hcap : ∀ k,rowBids b ω k ≤ ReceiptGap.cap i)
    (hpos : 0 < originalRowDuplicate (Uniform07.xi i) c g countMargin b ω) :
    0 < deficit i b c ω := by
  have hξ1 : Uniform07.xi i < 1 := by
    cases i <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hh := numeric_unit_and_duplicate_le (Uniform07.xi_pos i) hξ1
    {g with countMargin := countMargin (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0 hε hM hr
    (by simpa only [rowBids,Fin.cons_zero] using hbL)
  exact original_positive_implies_raw_deficit i c g countMargin hb hbL hε hM hr
    hroot hradius hguardLower ω hcap (hpos.trans_le hh.2.2)

end FCAppendix.Affine.Uniform06.RawDeficitGeometry
