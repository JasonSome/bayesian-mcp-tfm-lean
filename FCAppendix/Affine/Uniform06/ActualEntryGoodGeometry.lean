import FCAppendix.Affine.Uniform06.RivalGood
import FCAppendix.Affine.Uniform06.RawGoodGeometry
import FCAppendix.Affine.Uniform06.LiteralKernelIdentity
import FCAppendix.Affine.Uniform06.LiteralPrefixStieltjes

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ActualEntryGoodGeometry

open MeasureTheory Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment RivalGood RawGoodGeometry RawDeficitGeometry
open ReciprocalSecantBounds LiteralKernelIdentity EntryOwnImpact

variable {N : ℕ}

def tests (ξ : ℝ) (g : GuardData) (A U : ℝ) : Fin 9 → RowRival → ℝ :=
  statistics ξ g.multiplier g.radius g.requiredDemand g.rejectionScale
    g.rejectionRoot g.seedCutoff A U

def error (N : ℕ) (ε : ℝ) : ℝ := ε*(N:ℝ)+2

structure MeanMargins (μ : Measure RowRival) (ξ : ℝ) (g : GuardData)
    (A U t h ρ γ w s q : ℝ) : Prop where
  lower : (∫ r, tests ξ g A U 0 r ∂μ)=t
  upper0 : (∫ r, tests ξ g A U 1 r ∂μ)=h
  upper1 : (∫ r, tests ξ g A U 2 r ∂μ)=h
  lowerDemand : ρ-h+γ ≤ ∫ r, tests ξ g A U 3 r ∂μ
  upperDemand : (∫ r, tests ξ g A U 4 r ∂μ) ≤ ρ-h-γ
  weight : w ≤ ∫ r, tests ξ g A U 5 r ∂μ
  rejection : 3*(ρ-h) ≤ ∫ r, tests ξ g A U 6 r ∂μ
  seed : s ≤ ∫ r, tests ξ g A U 7 r ∂μ
  strip : q ≤ ∫ r, tests ξ g A U 8 r ∂μ

theorem supported_sum (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) (f : ℝ → ℝ) :
    (∑ j ∈ (patternTemplate c (fun k => (ω k).1)).support,
      f (rowBids b ω j))=f b+∑ j, lowerTest f (ω j) := by
  simp only [patternTemplate,Finset.sum_filter,Fin.sum_univ_succ,
    rowLowList,patternRow,rowBids,Fin.cons_zero,Fin.cons_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω j).1=0 <;> simp [hj,lowerTest]

theorem totalWeight_eq (ξ : ℝ) (g : GuardData) (c : ℕ)
    (b : ℝ) (ω : Fin N → RowRival) :
    totalWeight (weights ξ g (patternTemplate c (fun k => (ω k).1)) (rowBids b ω))=
      FiniteGuards.eligibility ξ g.multiplier g.requiredDemand b+
        ∑ j, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) (ω j) := by
  change (∑ j, if j ∈ (patternTemplate c (fun k => (ω k).1)).support then
    FiniteGuards.eligibility ξ g.multiplier g.requiredDemand (rowBids b ω j) else 0)=_
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_of_subset (Finset.subset_univ _)]
  exact supported_sum c b ω (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand)

def strip (A U : ℝ) (ω : Fin N → RowRival) : Finset (Fin (N+1)) :=
  (Finset.univ.filter (fun j => (ω j).1=0 ∧ (ω j).2 ∈ Icc A U)).image Fin.succ

theorem strip_card (A U : ℝ) (ω : Fin N → RowRival) :
    ((strip A U ω).card:ℝ)=
      ∑ j, lowerTest (fun b => if b ∈ Icc A U then (1:ℝ) else 0) (ω j) := by
  rw [strip,Finset.card_image_of_injective _ (Fin.succ_injective N)]
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ht : (ω j).1=0 <;> by_cases hb : (ω j).2 ∈ Icc A U <;> simp [lowerTest,ht,hb]

theorem strip_bids {A U b z : ℝ} (hzA : z < A)
    (ω : Fin N → RowRival) :
    ∀ j ∈ strip A U ω,z < rowBids b ω j ∧ rowBids b ω j ≤ U := by
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
  have hj' := (Finset.mem_filter.mp hj).2
  simp only [rowBids,Fin.cons_succ,if_pos hj'.1]
  exact ⟨hzA.trans_le hj'.2.1,hj'.2.2⟩

theorem empirical_errors (μ : Measure RowRival) {ξ ε A U : ℝ} (g : GuardData)
    (hN : 0 < N) (ω : Fin N → RowRival)
    (hg : ω ∈ good μ (tests ξ g A U) N ε) :
    ∀ k, |(∑ j, tests ξ g A U k (ω j))-
      (N:ℝ)*(∫ r, tests ξ g A U k r ∂μ)| < ε*(N:ℝ) := by
  intro k
  exact scaled_empirical_error hN (hg k)

theorem seeded_of_positive_sum (c : ℕ) (g : GuardData)
    (ω : Fin N → RowRival) (b : ℝ)
    (hs : 0 < ∑ j, lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) (ω j)) :
    seeded g (patternTemplate c (fun k => (ω k).1)) (rowBids b ω) := by
  obtain ⟨j,hj⟩ : ∃ j,0 < lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) (ω j) := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hs) (Finset.sum_nonpos fun j _ => hn j)
  have hk : (ω j).1=0 := by
    by_contra h
    simp [lowerTest,h] at hj
  have hb : (ω j).2 ≤ g.seedCutoff := by
    by_contra h
    simp [lowerTest,hk,h] at hj
  refine ⟨j.succ,?_,?_⟩
  · simp [patternTemplate,rowLowList,patternRow,hk]
  · simpa [rowBids,hk] using hb

theorem all_action_guard_and_strip
    (μ : Measure RowRival) {ξ A U t h ρ γ w s q ε : ℝ}
    (g : GuardData) {c : ℕ} (hN : 0 < N)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (_hε : 0 ≤ ε)
    (hgε : 0 < g.margin) (hgM : 0 < g.population)
    (hlo : 0 < g.multiplier-g.radius) (_hhi : 0 < g.multiplier+g.radius)
    (hrootScale : 0 < g.rejectionScale)
    (hm : MeanMargins μ ξ g A U t h ρ γ w s q)
    (hfloor : |(c:ℝ)-(N:ℝ)*ρ| ≤ 1)
    (hpos : ε*(N:ℝ)+2 < (N:ℝ)*(ρ-h))
    (hroom : 2*ε*(N:ℝ)+3 ≤ (N:ℝ)*(t-(ρ-h)))
    (hγ : 2*g.margin*g.population ≤ γ*(N:ℝ)-2*error N ε-1)
    (hw : 2*g.margin*g.population ≤ w*(N:ℝ)-3*error N ε)
    (hψ : 2*g.margin*g.population ≤ (ρ-h)*(N:ℝ)-3*error N ε)
    (hseed : 0 < (s-ε)*(N:ℝ))
    (hstrip : 6*error N ε+2 ≤ q*(N:ℝ))
    (hcount : 2*g.margin*g.population ≤ g.countMargin)
    (ω : Fin N → RowRival) (hno : ∀ j,(ω j).1 ≠ 1)
    (hgood : ω ∈ good μ (tests ξ g A U) N ε) :
    let T := patternTemplate c (fun j => (ω j).1)
    (T.residual₀=c-classCount 2 ω ∧ T.residual₁=c-classCount 3 ω) ∧
      (∀ b : ℝ, guardAlpha ξ g T (rowBids b ω)=1) ∧
      q*(N:ℝ)/2 ≤ ((strip A U ω).card:ℝ)-(imbalance T:ℝ)-1 := by
  let T := patternTemplate c (fun j => (ω j).1)
  let e := error N ε
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have he := empirical_errors μ g hN ω hgood
  have he0 : |(classCount 0 ω:ℝ)-(N:ℝ)*t| < ε*(N:ℝ) := by
    have hh := he 0
    rw [hm.lower] at hh
    simpa only [tests,statistics,Matrix.cons_val_zero,sum_tag_eq_count] using hh
  have he2 : |(classCount 2 ω:ℝ)-(N:ℝ)*h| < ε*(N:ℝ) := by
    have hh := he 1
    rw [hm.upper0] at hh
    change |(∑ j, tag 2 (ω j))-(N:ℝ)*h| < ε*(N:ℝ) at hh
    simpa only [sum_tag_eq_count] using hh
  have he3 : |(classCount 3 ω:ℝ)-(N:ℝ)*h| < ε*(N:ℝ) := by
    have hh := he 2
    rw [hm.upper1] at hh
    change |(∑ j, tag 3 (ω j))-(N:ℝ)*h| < ε*(N:ℝ) at hh
    simpa only [sum_tag_eq_count] using hh
  have hl : |((1+classCount 0 ω:ℕ):ℝ)-(N:ℝ)*t| ≤ ε*(N:ℝ)+1 := by
    rw [Nat.cast_add,Nat.cast_one]
    have hh := abs_add_le ((classCount 0 ω:ℝ)-(N:ℝ)*t) 1
    norm_num only [abs_one] at hh
    have ee : (1:ℝ)+classCount 0 ω-(N:ℝ)*t=((classCount 0 ω:ℝ)-(N:ℝ)*t)+1 := by ring
    rw [ee]
    linarith
  have hr0 := residual_of_counts hfloor hl
    (he2.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith) (by linarith)
  have hr1 := residual_of_counts hfloor hl
    (he3.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith) (by linarith)
  have hc1 : classCount 1 ω=0 := by simp [classCount,hno]
  have hres : T.residual₀=c-classCount 2 ω ∧ T.residual₁=c-classCount 3 ω := by
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=c-classCount 2 ω ∧
      min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)=c-classCount 3 ω
    rw [hc1,Nat.sub_zero]
    exact ⟨hr0.1,hr1.1⟩
  have h0 : |(T.residual₀:ℝ)-(ρ-h)*(N:ℝ)| ≤ e := by
    rw [hres.1]
    have hh := hr0.2.2
    rw [hr0.1] at hh
    convert! hh using 1
    · congr 1
      ring
    · dsimp [e,error]
      ring
  have h1 : |(T.residual₁:ℝ)-(ρ-h)*(N:ℝ)| ≤ e := by
    rw [hres.2]
    have hh := hr1.2.2
    rw [hr1.1] at hh
    convert! hh using 1
    · congr 1
      ring
    · dsimp [e,error]
      ring
  have hlo' : (ρ-h+γ)*(N:ℝ)-e ≤ (∑ j, lowerTest (exposure ξ (g.multiplier-g.radius)) (ω j)) := by
    have hh0 := he 3
    change |(∑ j, lowerTest (exposure ξ (g.multiplier-g.radius)) (ω j))-(N:ℝ)*(∫ r, lowerTest (exposure ξ (g.multiplier-g.radius)) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).1
    have hm0 : (ρ-h+γ) ≤ (∫ r, lowerTest (exposure ξ (g.multiplier-g.radius)) r ∂μ) := hm.lowerDemand
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    dsimp only [e,error]
    nlinarith only [hh,hm']
  have hhi' : (∑ j, lowerTest (exposure ξ (g.multiplier+g.radius)) (ω j)) ≤ (ρ-h-γ)*(N:ℝ)+e := by
    have hh0 := he 4
    change |(∑ j, lowerTest (exposure ξ (g.multiplier+g.radius)) (ω j))-(N:ℝ)*(∫ r, lowerTest (exposure ξ (g.multiplier+g.radius)) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).2
    have hm0 : (∫ r, lowerTest (exposure ξ (g.multiplier+g.radius)) r ∂μ) ≤ (ρ-h-γ) := hm.upperDemand
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    dsimp only [e,error]
    nlinarith only [hh,hm']
  have hw' : (w)*(N:ℝ)-e ≤ (∑ j, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) (ω j)) := by
    have hh0 := he 5
    change |(∑ j, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) (ω j))-(N:ℝ)*(∫ r, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).1
    have hm0 : (w) ≤ (∫ r, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) r ∂μ) := hm.weight
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    dsimp only [e,error]
    nlinarith only [hh,hm']
  have hψ' : (3*(ρ-h))*(N:ℝ)-e ≤ (∑ j, lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) (ω j)) := by
    have hh0 := he 6
    change |(∑ j, lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) (ω j))-(N:ℝ)*(∫ r, lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).1
    have hm0 : (3*(ρ-h)) ≤ (∫ r, lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) r ∂μ) := hm.rejection
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    dsimp only [e,error]
    nlinarith only [hh,hm']
  have hs' : 0 < ∑ j, lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) (ω j) := by
    have hh0 := he 7
    change |(∑ j, lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) (ω j))-
      (N:ℝ)*(∫ r, lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).1
    have hm0 : s ≤ ∫ r, lowerTest (fun z => if z ≤ g.seedCutoff then (1:ℝ) else 0) r ∂μ := hm.seed
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    nlinarith only [hh,hm',hseed]
  have hq' : q*(N:ℝ)-ε*(N:ℝ) ≤ ((strip A U ω).card:ℝ) := by
    have hh0 := he 8
    change |(∑ j, lowerTest (fun z => if z ∈ Icc A U then (1:ℝ) else 0) (ω j))-
      (N:ℝ)*(∫ r, lowerTest (fun z => if z ∈ Icc A U then (1:ℝ) else 0) r ∂μ)| < ε*(N:ℝ) at hh0
    have hh := (abs_lt.mp hh0).1
    have hm0 : q ≤ ∫ r, lowerTest (fun z => if z ∈ Icc A U then (1:ℝ) else 0) r ∂μ := hm.strip
    have hm' := mul_le_mul_of_nonneg_right hm0 hn
    rw [strip_card]
    nlinarith only [hh,hm']
  change 2*g.margin*g.population ≤ γ*(N:ℝ)-2*e-1 at hγ
  change 2*g.margin*g.population ≤ w*(N:ℝ)-3*e at hw
  change 2*g.margin*g.population ≤ (ρ-h)*(N:ℝ)-3*e at hψ
  refine ⟨hres,?_,?_⟩
  · intro b
    have hs := four_slacks h0 h1 hlo' hhi' hw' hψ'
      (exposure ξ (g.multiplier-g.radius) b) (exposure ξ (g.multiplier+g.radius) b)
      (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand b)
      (PrefixRoot.psi g.rejectionScale g.rejectionRoot b)
      (exposure_nonneg hξ hlo) (exposure_le_one _ _ _)
      (FiniteGuards.eligibility_bounds _ _ _ _).1 (PrefixRoot.psi_bounds hrootScale).1
    apply actual_guard_one ξ g T (rowBids b ω) hgε hgM (seeded_of_positive_sum c g ω b hs')
    have hLow : (∑ j ∈ T.support, exposure ξ (g.multiplier-g.radius) (rowBids b ω j))=
        exposure ξ (g.multiplier-g.radius) b+∑ j, lowerTest (exposure ξ (g.multiplier-g.radius)) (ω j) :=
      supported_sum c b ω _
    have hHigh : (∑ j ∈ T.support, exposure ξ (g.multiplier+g.radius) (rowBids b ω j))=
        exposure ξ (g.multiplier+g.radius) b+∑ j, lowerTest (exposure ξ (g.multiplier+g.radius)) (ω j) :=
      supported_sum c b ω _
    have hWeight : totalWeight (weights ξ g T (rowBids b ω))=
        FiniteGuards.eligibility ξ g.multiplier g.requiredDemand b+
        ∑ j, lowerTest (FiniteGuards.eligibility ξ g.multiplier g.requiredDemand) (ω j) :=
      totalWeight_eq ξ g c b ω
    have hPsi : (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (rowBids b ω j))=
        PrefixRoot.psi g.rejectionScale g.rejectionRoot b+
        ∑ j, lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) (ω j) :=
      supported_sum c b ω _
    have hm0 : min T.residual₀ T.residual₁ ≤ max T.residual₀ T.residual₁ := min_le_max
    rw [Nat.cast_sub hm0] at hs
    intro k
    fin_cases k
    · change 2*g.margin*g.population ≤
        (∑ j ∈ T.support, exposure ξ (g.multiplier-g.radius) (rowBids b ω j))-
        ((min T.residual₀ T.residual₁:ℕ):ℝ)-(max T.residual₀ T.residual₁-min T.residual₀ T.residual₁:ℕ)
      rw [hLow,Nat.cast_sub hm0]
      nlinarith only [hs.1,hγ]
    · change 2*g.margin*g.population ≤ ((min T.residual₀ T.residual₁:ℕ):ℝ)-
        (∑ j ∈ T.support, exposure ξ (g.multiplier+g.radius) (rowBids b ω j))
      rw [hHigh]
      nlinarith only [hs.2.1,hγ]
    · change 2*g.margin*g.population ≤ totalWeight (weights ξ g T (rowBids b ω))-
        (max T.residual₀ T.residual₁-min T.residual₀ T.residual₁:ℕ)
      rw [hWeight,Nat.cast_sub hm0]
      nlinarith only [hs.2.2.1,hw]
    · change 2*g.margin*g.population ≤
        (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (rowBids b ω j))-
        (T.residual₀:ℝ)-(T.residual₁:ℝ)
      rw [hPsi]
      nlinarith only [hs.2.2.2,hψ]
    · exact hcount
  · have hd := (residual_gap_le h0 h1).2.2
    change (imbalance T:ℝ) ≤ 2*e at hd
    dsimp only [e,error] at hd
    dsimp only [error] at hstrip
    nlinarith

theorem all_action_roots_and_reciprocals
    {ξ A U q : ℝ} (g : GuardData) {c : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 < g.radius)
    (hlo : 0 < g.multiplier-g.radius)
    (hguard : (1-ξ)*U ≤ g.multiplier-g.radius)
    (hA : g.multiplier+g.radius < A)
    (ω : Fin N → RowRival)
    (hω : ∀ j,(ω j).1=0 → (ω j).2 ≤ U)
    (hα : ∀ b, guardAlpha ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)=1)
    (hstrip : q*(N:ℝ)/2 ≤ ((strip A U ω).card:ℝ)-
      (imbalance (patternTemplate c (fun j => (ω j).1)):ℝ)-1) :
    ∀ b ∈ Icc (g.multiplier-g.radius) (g.multiplier+g.radius), b ≤ U →
      ∀ path : Path (Fin (N+1)) (imbalance (patternTemplate c (fun j => (ω j).1))),
      0 < (pathLaw (weights ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω))
        (imbalance (patternTemplate c (fun j => (ω j).1))) ∅).mass path →
      ∃ Λ ∈ Ioo (g.multiplier-g.radius) (g.multiplier+g.radius),
        IsLargestPositiveRoot ξ (rowBids b ω)
          (finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ path)
          (small (patternTemplate c (fun j => (ω j).1)):ℝ) Λ ∧
        ∀ z ∈ Icc (g.multiplier-g.radius) (g.multiplier+g.radius),
          q*(N:ℝ)/(2*U) ≤ reciprocalSum (rowBids b ω)
            (insert 0 (finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ path)) z := by
  intro b hb hbU path hp
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let E := finalSet (imbalance T) ∅ path
  have hBU : ∀ j,B j ≤ U := by
    intro j
    refine Fin.cases hbU (fun k => ?_) j
    by_cases hk : (ω k).1=0
    · simpa [B,rowBids,hk] using hω k hk
    · simp [B,rowBids,hk,hU.le]
  have hpos : 0 < guardAlpha ξ g T B := by rw [hα b]; norm_num
  obtain ⟨Λ,hΛ,hr,_⟩ := supported_path_root hξ hξ1 g T B hε hM ha hU hlo
    hguard hBU (rowBids_outside c b ω) hpos path hp
  refine ⟨Λ,hΛ,hr,?_⟩
  intro z hz
  have hW : (imbalance T:ℝ) < totalWeight (weights ξ g T B) := by
    nlinarith [SourceGuardGeometry.positive_guard_weight g T B hε hM hpos,mul_pos hε hM]
  have hE : E.card=imbalance T := by
    simpa only [E,Finset.card_empty,zero_add] using
      finalSet_card (weights ξ g T B) (imbalance T) ∅ (by simpa using hW) path hp
  have hIns : ((insert (0:Fin (N+1)) E).card:ℝ) ≤ (imbalance T:ℝ)+1 := by
    have hh := Finset.card_insert_le (0:Fin (N+1)) E
    rw [hE] at hh
    exact_mod_cast hh
  have hS := reciprocalSum_active_strip_lower B (insert 0 E) (strip A U ω)
    (hlo.trans_le hz.1) hU (strip_bids (hz.2.trans_lt hA) ω)
  have hnum : q*(N:ℝ)/2 ≤ ((strip A U ω).card:ℝ)-((insert (0:Fin (N+1)) E).card:ℝ) := by
    nlinarith [hstrip]
  have hh := (div_le_div_of_nonneg_right hnum hU.le).trans hS
  convert! hh using 1
  ring

theorem all_action_focal_not_sampled
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {ξ u : ℝ} (hξ : 0 < ξ) (g : GuardData)
    (hg : LiteralPrefixStieltjes.PrefixConditions ξ g u)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hb : B j ≤ u) (hα : 0 < guardAlpha ξ g T B)
    (path : Path ι (imbalance T))
    (hp : 0 < (pathLaw (weights ξ g T B) (imbalance T) ∅).mass path) :
    j ∉ finalSet (imbalance T) ∅ path := by
  have hw : (weights ξ g T B).val j=0 := by
    unfold weights
    dsimp only
    split_ifs
    · exact hg.zero_eligibility hξ _ hb
    · rfl
  have hW : (imbalance T:ℝ) < totalWeight (weights ξ g T B) := by
    nlinarith [SourceGuardGeometry.positive_guard_weight g T B hg.margin_pos
      hg.population_pos hα,mul_pos hg.margin_pos hg.population_pos]
  exact focal_not_sampled_of_zero_weight ξ g T B j hW hw path hp

end FCAppendix.Affine.Uniform06.ActualEntryGoodGeometry
