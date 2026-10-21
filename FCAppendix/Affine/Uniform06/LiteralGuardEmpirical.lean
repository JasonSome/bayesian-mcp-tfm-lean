import FCAppendix.Affine.Uniform06.GuardProfileLipschitz

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralGuardEmpirical

open MeasureTheory Set
open scoped BigOperators
open LowBody LiteralExperiment FiniteGuards GuardProfileLipschitz
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling

def statistic (ξ : ℝ) (g : GuardData) : Fin 8 → RowRival → ℝ :=
  ![RivalGood.tag 0,RivalGood.tag 1,RivalGood.tag 2,RivalGood.tag 3,
    RivalGood.lowerTest (exposure ξ (g.multiplier-g.radius)),
    RivalGood.lowerTest (exposure ξ (g.multiplier+g.radius)),
    RivalGood.lowerTest (eligibility ξ g.multiplier g.requiredDemand),
    RivalGood.lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot)]

def focal (ξ : ℝ) (g : GuardData) (b : ℝ) : Fin 4 → ℝ :=
  ![exposure ξ (g.multiplier-g.radius) b,exposure ξ (g.multiplier+g.radius) b,
    eligibility ξ g.multiplier g.requiredDemand b,PrefixRoot.psi g.rejectionScale g.rejectionRoot b]

def sums {N : ℕ} (ξ : ℝ) (g : GuardData) (ω : Fin N → RowRival) : Fin 8 → ℝ :=
  fun j => (∑ q,statistic ξ g j (ω q))/g.population

def empiricalProfile {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ) (b : ℝ)
    (ω : Fin N → RowRival) : Fin 7 → ℝ :=
  ![focal ξ g b 0/g.population+sums ξ g ω 4,
    focal ξ g b 1/g.population+sums ξ g ω 5,
    focal ξ g b 2/g.population+sums ξ g ω 6,
    focal ξ g b 3/g.population+sums ξ g ω 7,
    clampedResidual (g.population⁻¹+sums ξ g ω 0) ((c:ℝ)/g.population)
      (sums ξ g ω 1+sums ξ g ω 2),
    clampedResidual (g.population⁻¹+sums ξ g ω 0) ((c:ℝ)/g.population)
      (sums ξ g ω 1+sums ξ g ω 3),
    g.countMargin/g.population]

def populationProfile (a : Fin 8 → ℝ) (ρ cm : ℝ) : Fin 7 → ℝ :=
  ![a 4,a 5,a 6,a 7,clampedResidual (a 0) ρ (a 1+a 2),
    clampedResidual (a 0) ρ (a 1+a 3),cm]

theorem statistic_measurable (ξ : ℝ) (g : GuardData) :
    ∀ j,Measurable (statistic ξ g j) := by
  intro j
  fin_cases j
  · exact RivalGood.measurable_tag 0
  · exact RivalGood.measurable_tag 1
  · exact RivalGood.measurable_tag 2
  · exact RivalGood.measurable_tag 3
  · apply RivalGood.measurable_lowerTest
    unfold exposure
    fun_prop
  · apply RivalGood.measurable_lowerTest
    unfold exposure
    fun_prop
  · apply RivalGood.measurable_lowerTest
    unfold eligibility clip01 exposure
    fun_prop
  · apply RivalGood.measurable_lowerTest
    unfold PrefixRoot.psi
    fun_prop

theorem focal_unit {ξ : ℝ} (hξ : 0 < ξ) (g : GuardData)
    (hlo : 0 < g.multiplier-g.radius) (hhi : 0 < g.multiplier+g.radius)
    (hd : 0 < g.rejectionScale) : ∀ b j,focal ξ g b j ∈ Icc (0:ℝ) 1 := by
  intro b j
  fin_cases j
  · exact ⟨exposure_nonneg hξ hlo,exposure_le_one _ _ _⟩
  · exact ⟨exposure_nonneg hξ hhi,exposure_le_one _ _ _⟩
  · exact eligibility_bounds _ _ _ _
  · exact PrefixRoot.psi_bounds hd

theorem statistic_unit {ξ : ℝ} (hξ : 0 < ξ) (g : GuardData)
    (hlo : 0 < g.multiplier-g.radius) (hhi : 0 < g.multiplier+g.radius)
    (hd : 0 < g.rejectionScale) : ∀ j r,statistic ξ g j r ∈ Icc (0:ℝ) 1 := by
  intro j r
  fin_cases j
  · change (if r.1=0 then (1:ℝ) else 0)∈Icc (0:ℝ) 1
    split_ifs <;> norm_num
  · change (if r.1=1 then (1:ℝ) else 0)∈Icc (0:ℝ) 1
    split_ifs <;> norm_num
  · change (if r.1=2 then (1:ℝ) else 0)∈Icc (0:ℝ) 1
    split_ifs <;> norm_num
  · change (if r.1=3 then (1:ℝ) else 0)∈Icc (0:ℝ) 1
    split_ifs <;> norm_num
  · exact RivalGood.lowerTest_unit (fun b => (focal_unit hξ g hlo hhi hd b 0)) r
  · exact RivalGood.lowerTest_unit (fun b => (focal_unit hξ g hlo hhi hd b 1)) r
  · exact RivalGood.lowerTest_unit (fun b => (focal_unit hξ g hlo hhi hd b 2)) r
  · exact RivalGood.lowerTest_unit (fun b => (focal_unit hξ g hlo hhi hd b 3)) r

@[simp] lemma statistic_countMargin (ξ : ℝ) (g : GuardData) (cm : ℝ) :
    statistic ξ {g with countMargin := cm}=statistic ξ g := rfl

@[simp] lemma focal_countMargin (ξ : ℝ) (g : GuardData) (cm b : ℝ) :
    focal ξ {g with countMargin := cm} b=focal ξ g b := rfl

@[simp] lemma sums_countMargin {N : ℕ} (ξ : ℝ) (g : GuardData) (cm : ℝ)
    (ω : Fin N → RowRival) : sums ξ {g with countMargin := cm} ω=sums ξ g ω := rfl

lemma raw_lower_sum {N : ℕ} (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) (F : ℝ → ℝ) :
    (∑ j ∈ (patternTemplate c (fun q => (ω q).1)).support,F (rowBids b ω j))=
      F b+∑ q,RivalGood.lowerTest F (ω q) := by
  simp only [patternTemplate,Finset.sum_filter,Fin.sum_univ_succ,rowLowList,
    patternRow,Fin.cons_zero,Option.isSome_some,ite_true,rowBids,Fin.cons_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : (ω q).1=0 <;> simp [hq,RivalGood.lowerTest]

lemma weight_support_sum {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) :
    totalWeight (weights ξ g T B)=
      ∑ j ∈ T.support,eligibility ξ g.multiplier g.requiredDemand (B j) := by
  simp [totalWeight,weights]

lemma sum_tag_cast {N : ℕ} (j : Fin 4) (ω : Fin N → RowRival) :
    (∑ q,RivalGood.tag j (ω q))=(classCount j ω:ℝ) := by
  simp [classCount,RivalGood.tag]

theorem actual_profile_eq {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ)
    (b : ℝ) (ω : Fin N → RowRival) (hM : 0 < g.population) :
    normalizedProfile ξ g (patternTemplate c (fun q => (ω q).1)) (rowBids b ω)=
      empiricalProfile ξ g c b ω := by
  have hr := RawDeficitGeometry.residuals_literal c ω
  have h0 := normalized_residual (1+classCount 0 ω) c (classCount 1 ω+classCount 2 ω) hM
  have h1 := normalized_residual (1+classCount 0 ω) c (classCount 1 ω+classCount 3 ω) hM
  rw [← Nat.sub_sub] at h0 h1
  funext j
  fin_cases j
  · change demand ξ _ _ (g.multiplier-g.radius)/g.population=
      exposure ξ (g.multiplier-g.radius) b/g.population+
        (∑q,RivalGood.lowerTest (exposure ξ (g.multiplier-g.radius)) (ω q))/g.population
    rw [demand,raw_lower_sum,add_div]
  · change demand ξ _ _ (g.multiplier+g.radius)/g.population=
      exposure ξ (g.multiplier+g.radius) b/g.population+
        (∑q,RivalGood.lowerTest (exposure ξ (g.multiplier+g.radius)) (ω q))/g.population
    rw [demand,raw_lower_sum,add_div]
  · change totalWeight (weights ξ g _ _)/g.population=
      eligibility ξ g.multiplier g.requiredDemand b/g.population+
        (∑q,RivalGood.lowerTest (eligibility ξ g.multiplier g.requiredDemand) (ω q))/g.population
    rw [weight_support_sum,raw_lower_sum,add_div]
  · change (∑j∈(patternTemplate c (fun q=>(ω q).1)).support,
      PrefixRoot.psi g.rejectionScale g.rejectionRoot (rowBids b ω j))/g.population=
      PrefixRoot.psi g.rejectionScale g.rejectionRoot b/g.population+
        (∑q,RivalGood.lowerTest (PrefixRoot.psi g.rejectionScale g.rejectionRoot) (ω q))/g.population
    rw [raw_lower_sum,add_div]
  · change ((patternTemplate c (fun q=>(ω q).1)).residual₀:ℝ)/g.population=
      clampedResidual (g.population⁻¹+(∑q,RivalGood.tag 0 (ω q))/g.population)
        ((c:ℝ)/g.population)
        ((∑q,RivalGood.tag 1 (ω q))/g.population+(∑q,RivalGood.tag 2 (ω q))/g.population)
    rw [sum_tag_cast,sum_tag_cast,sum_tag_cast,hr.1]
    simpa only [Nat.cast_add,Nat.cast_one,add_div,one_div] using h0
  · change ((patternTemplate c (fun q=>(ω q).1)).residual₁:ℝ)/g.population=
      clampedResidual (g.population⁻¹+(∑q,RivalGood.tag 0 (ω q))/g.population)
        ((c:ℝ)/g.population)
        ((∑q,RivalGood.tag 1 (ω q))/g.population+(∑q,RivalGood.tag 3 (ω q))/g.population)
    rw [sum_tag_cast,sum_tag_cast,sum_tag_cast,hr.2]
    simpa only [Nat.cast_add,Nat.cast_one,add_div,one_div] using h1
  · rfl

theorem profile_error {N : ℕ} (ξ : ℝ) (g : GuardData) (c : ℕ)
    (b : ℝ) (ω : Fin N → RowRival) (a : Fin 8 → ℝ)
    {ρ cm ε δ ecm : ℝ} (hM : 0 < g.population)
    (hfocal : ∀ j,focal ξ g b j ∈ Icc (0:ℝ) 1)
    (hs : ∀ j,|sums ξ g ω j-a j| ≤ ε)
    (hcap : |(c:ℝ)/g.population-ρ| ≤ δ)
    (hcm : |g.countMargin/g.population-cm| ≤ ecm) :
    (∑ j : Fin 7,|normalizedProfile ξ g (patternTemplate c (fun q => (ω q).1))
      (rowBids b ω) j-populationProfile a ρ cm j|) ≤
        10*ε+2*δ+6/g.population+ecm := by
  have hMinv : 0 ≤ g.population⁻¹ := (inv_pos.mpr hM).le
  have hfb (j : Fin 4) : |focal ξ g b j/g.population| ≤ g.population⁻¹ := by
    rw [abs_of_nonneg (div_nonneg (hfocal j).1 hM.le)]
    simpa only [one_div] using div_le_div_of_nonneg_right (hfocal j).2 hM.le
  have hF (j : Fin 4) (q : Fin 8) :
      |focal ξ g b j/g.population+sums ξ g ω q-a q| ≤ g.population⁻¹+ε := by
    have he : focal ξ g b j/g.population+sums ξ g ω q-a q=
        focal ξ g b j/g.population+(sums ξ g ω q-a q) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add (hfb j) (hs q))
  have hlo : |g.population⁻¹+sums ξ g ω 0-a 0| ≤ g.population⁻¹+ε := by
    have he : g.population⁻¹+sums ξ g ω 0-a 0=g.population⁻¹+(sums ξ g ω 0-a 0) := by ring
    rw [he]
    exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg hMinv]
      exact add_le_add le_rfl (hs 0))
  have hu (q : Fin 8) : |(sums ξ g ω 1+sums ξ g ω q)-(a 1+a q)| ≤ 2*ε := by
    have he : (sums ξ g ω 1+sums ξ g ω q)-(a 1+a q)=
        (sums ξ g ω 1-a 1)+(sums ξ g ω q-a q) := by ring
    rw [he]
    linarith [abs_add_le (sums ξ g ω 1-a 1) (sums ξ g ω q-a q),hs 1,hs q]
  have hr (q : Fin 8) :
      |clampedResidual (g.population⁻¹+sums ξ g ω 0) ((c:ℝ)/g.population)
        (sums ξ g ω 1+sums ξ g ω q)-clampedResidual (a 0) ρ (a 1+a q)| ≤
        3*ε+δ+g.population⁻¹ := by
    have hh := clampedResidual_l1 (g.population⁻¹+sums ξ g ω 0)
      ((c:ℝ)/g.population) (sums ξ g ω 1+sums ξ g ω q) (a 0) ρ (a 1+a q)
    linarith [hlo,hcap,hu q]
  rw [actual_profile_eq ξ g c b ω hM]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change (|focal ξ g b 0/g.population+sums ξ g ω 4-a 4|+
    (|focal ξ g b 1/g.population+sums ξ g ω 5-a 5|+
    (|focal ξ g b 2/g.population+sums ξ g ω 6-a 6|+
    (|focal ξ g b 3/g.population+sums ξ g ω 7-a 7|+
    (|clampedResidual (g.population⁻¹+sums ξ g ω 0) ((c:ℝ)/g.population)
      (sums ξ g ω 1+sums ξ g ω 2)-clampedResidual (a 0) ρ (a 1+a 2)|+
    (|clampedResidual (g.population⁻¹+sums ξ g ω 0) ((c:ℝ)/g.population)
      (sums ξ g ω 1+sums ξ g ω 3)-clampedResidual (a 0) ρ (a 1+a 3)|+
    |g.countMargin/g.population-cm|))))))≤_
  have he : 6/g.population=6*g.population⁻¹ := rfl
  rw [he]
  linarith [hF 0 4,hF 1 5,hF 2 6,hF 3 7,hr 2,hr 3]

end FCAppendix.Affine.Uniform06.LiteralGuardEmpirical
