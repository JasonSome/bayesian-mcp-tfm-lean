import FCAppendix.Affine.Uniform06.RegularRootDifferentiability

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RootFlatFaces

open Set Filter Topology
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open EntryOwnImpact ActualRootDerivative RegularRootDifferentiability CanonicalInterior CanonicalCoarse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuousAt_remaining {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (B : ι → ℝ) (j : ι) : ContinuousAt (remainingDemand ξ B {j}) z := by
  unfold remainingDemand
  apply tendsto_finsetSum Finset.univ
  intro k _
  by_cases hk : k ∈ ({j}:Finset ι)
  · simp only [if_pos hk]
    exact continuousAt_const
  · simp only [if_neg hk]
    exact continuousAt_exposure_price hξ hz (B k)

lemma remaining_nonnegative {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (B : ι → ℝ) (j : ι) : 0 ≤ remainingDemand ξ B {j} z := by
  unfold remainingDemand
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact le_rfl
  · exact exposure_nonneg hξ hz

theorem zero_implies_capacity_le {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hp : marginal ξ c B j b=0) :
    (c:ℝ) ≤ remainingDemand ξ B {j} b := by
  have hp1 : EqualCapacity.positiveMarginal ξ c (Function.update B j b) j < 1 := by
    change marginal ξ c B j b < 1
    rw [hp]
    norm_num
  have he := actual_interior_positive_part hξ hξ1 c (Function.update B j b) j
    (by simpa using hb) hp1
  have hK : 0 ≤ EntryOwnImpact.rightSecant ξ (Function.update B j b) {j}
      (b*(1-ξ*marginal ξ c B j b)) b :=
    EntryOwnImpact.rightSecant_nonneg _ _ hξ (by simpa only [hp,mul_zero,sub_zero,mul_one] using hb)
  have hden : 0 < 1+b*EntryOwnImpact.rightSecant ξ (Function.update B j b) {j}
      (b*(1-ξ*marginal ξ c B j b)) b := by positivity
  rw [Function.update_self] at he
  change marginal ξ c B j b=
    max 0 ((c:ℝ)-remainingDemand ξ (Function.update B j b) {j} b)/
      (1+b*EntryOwnImpact.rightSecant ξ (Function.update B j b) {j}
        (b*(1-ξ*marginal ξ c B j b)) b) at he
  rw [hp,remaining_update_focal] at he
  have hm : max 0 ((c:ℝ)-remainingDemand ξ B {j} b)=0 :=
    (div_eq_zero_iff.mp he.symm).resolve_right (by simpa only [hp] using hden.ne')
  have hh := le_max_right 0 ((c:ℝ)-remainingDemand ξ B {j} b)
  rw [hm] at hh
  linarith

theorem zero_of_capacity_le {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hcap : (c:ℝ) ≤ remainingDemand ξ B {j} b) :
    marginal ξ c B j b=0 := by
  apply le_antisymm _ (marginal_bounds hξ hξ1 c B j b).1
  by_contra hn
  have hh := actual_positive_implies_deficit_positive hξ hξ1 c
    (Function.update B j b) j (by simpa using hb) (lt_of_not_ge hn)
  rw [Function.update_self,remaining_update_focal] at hh
  linarith

theorem full_implies_capacity_le {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hp : marginal ξ c B j b=1) :
    1+remainingDemand ξ B {j} ((1-ξ)*b) ≤ (c:ℝ) := by
  have hh := actual_saturation_deficit_lower hξ hξ1 c (Function.update B j b) j
    (by simpa using hb) hp
  rw [Function.update_self,remaining_update_focal,remaining_update_focal] at hh
  linarith

theorem full_of_capacity_le {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hcap : 1+remainingDemand ξ B {j} ((1-ξ)*b) ≤ (c:ℝ)) :
    marginal ξ c B j b=1 := by
  have hp := marginal_bounds hξ hξ1 c B j b
  have hκb : 0 < (1-ξ)*b := mul_pos (sub_pos.mpr hξ1) hb
  by_contra hne
  have hp1 : marginal ξ c B j b < 1 := lt_of_le_of_ne hp.2 hne
  by_cases hp0 : marginal ξ c B j b=0
  · have hc := zero_implies_capacity_le hξ hξ1 c B j hb hp0
    have hm := remainingDemand_antitone_price ξ B {j} hξ hκb
      (show (1-ξ)*b ≤ b by nlinarith [mul_pos hξ hb])
    linarith
  · have hpp : 0 < marginal ξ c B j b := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    have he := actual_interior_equation hξ hξ1 c B j hb ⟨hpp,hp1⟩
    have hreceipt : (1-ξ)*b ≤ receipt ξ c B j b := by
      unfold receipt
      nlinarith [mul_nonneg (mul_pos hb hξ).le (sub_nonneg.mpr hp.2)]
    have hm := remainingDemand_antitone_price ξ B {j} hξ hκb hreceipt
    linarith

theorem full_iff {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι) (hb : 0 < b) :
    marginal ξ c B j b=1 ↔ 1+remainingDemand ξ B {j} ((1-ξ)*b) ≤ (c:ℝ) :=
  ⟨full_implies_capacity_le hξ hξ1 c B j hb,full_of_capacity_le hξ hξ1 c B j hb⟩

theorem remaining_eventually_constant {ξ z : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (B : ι → ℝ) (j : ι) (hz : 0 < z)
    (hfaces : ∀ k,k ≠ j → z ≠ B k ∧ z ≠ (1-ξ)*B k)
    (hflat : ∀ k,k ≠ j → ¬ ((1-ξ)*B k < z ∧ z < B k)) :
    remainingDemand ξ B {j}=ᶠ[𝓝 z] fun _ => remainingDemand ξ B {j} z := by
  have hK : reciprocal ξ B j z=0 := by
    unfold reciprocal
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k=j
    · simp [hk]
    · have hn : ¬ (k ≠ j ∧ (1-ξ)*B k < z ∧ z < B k) :=
        fun h => hflat k hk h.2
      simp [hn]
  filter_upwards [remaining_eventually_affine hξ hξ1 B j hz hfaces] with a ha
  simpa only [hK,zero_mul,zero_div,sub_zero] using ha

theorem zero_face_hasDerivAt_of_flat {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hp : marginal ξ c B j b=0)
    (hfaces : ∀ k,k ≠ j → b ≠ B k ∧ b ≠ (1-ξ)*B k)
    (hflat : ∀ k,k ≠ j → ¬ ((1-ξ)*B k < b ∧ b < B k)) :
    HasDerivAt (marginal ξ c B j) 0 b := by
  have hc := zero_implies_capacity_le hξ hξ1 c B j hb hp
  have he : marginal ξ c B j=ᶠ[𝓝 b] fun _ => (0:ℝ) := by
    filter_upwards [eventually_gt_nhds hb,
      remaining_eventually_constant hξ hξ1 B j hb hfaces hflat] with a ha hHa
    exact zero_of_capacity_le hξ hξ1 c B j ha (by simpa only [hHa] using hc)
  exact (hasDerivAt_const b 0).congr_of_eventuallyEq he

theorem full_face_hasDerivAt {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hstrict : 1+remainingDemand ξ B {j} ((1-ξ)*b) < (c:ℝ)) :
    HasDerivAt (marginal ξ c B j) 0 b := by
  have hκb : 0 < (1-ξ)*b := mul_pos (sub_pos.mpr hξ1) hb
  have hH : ContinuousAt (fun a => 1+remainingDemand ξ B {j} ((1-ξ)*a)) b :=
    continuousAt_const.add ((continuousAt_remaining hξ hκb B j).comp
      (continuousAt_const.mul continuousAt_id))
  have he : marginal ξ c B j=ᶠ[𝓝 b] fun _ => (1:ℝ) := by
    filter_upwards [eventually_gt_nhds hb,
      hH.preimage_mem_nhds (Iio_mem_nhds hstrict)] with a ha hHa
    change 1+remainingDemand ξ B {j} ((1-ξ)*a) < (c:ℝ) at hHa
    exact full_of_capacity_le hξ hξ1 c B j ha hHa.le
  exact (hasDerivAt_const b 1).congr_of_eventuallyEq he

theorem full_face_hasDerivAt_of_flat {ξ b : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (B : ι → ℝ) (j : ι)
    (hb : 0 < b) (hp : marginal ξ c B j b=1)
    (hfaces : ∀ k,k ≠ j → (1-ξ)*b ≠ B k ∧ (1-ξ)*b ≠ (1-ξ)*B k)
    (hflat : ∀ k,k ≠ j → ¬ ((1-ξ)*B k < (1-ξ)*b ∧ (1-ξ)*b < B k)) :
    HasDerivAt (marginal ξ c B j) 0 b := by
  have hκb : 0 < (1-ξ)*b := mul_pos (sub_pos.mpr hξ1) hb
  have hc := full_implies_capacity_le hξ hξ1 c B j hb hp
  have hH := remaining_eventually_constant hξ hξ1 B j hκb hfaces hflat
  have hcpt : ContinuousAt (fun a : ℝ => (1-ξ)*a) b := by fun_prop
  have he : marginal ξ c B j=ᶠ[𝓝 b] fun _ => (1:ℝ) := by
    filter_upwards [eventually_gt_nhds hb,hcpt.tendsto.eventually hH] with a ha hHa
    exact full_of_capacity_le hξ hξ1 c B j ha (by simpa only [hHa] using hc)
  exact (hasDerivAt_const b 1).congr_of_eventuallyEq he

end FCAppendix.Affine.Uniform06.RootFlatFaces
