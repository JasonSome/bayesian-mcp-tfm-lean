import FCAppendix.Affine.Uniform06.CanonicalRootAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralKernelIdentity

open Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment SourceGuardGeometry EntryOwnImpact CanonicalRootAdapter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def focalPrice (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) : ℝ :=
  B j*(1-ξ*complementMarginal ξ T B E j)

def focalSlope (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) : ℝ :=
  rightSecant ξ B (insert j E) (focalPrice ξ T B E j) (B j)

def focalDeficit (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) : ℝ :=
  (small T : ℝ)-remainingDemand ξ B (insert j E) (B j)

def pathResponse (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) : ℝ :=
  max 0 (focalDeficit ξ T B E j)/(1+B j*focalSlope ξ T B E j)

omit [Nonempty ι] in
lemma focalPrice_pos {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι) (hb : 0 < B j) :
    0 < focalPrice ξ T B E j := by
  have hp := (EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1
    (maskedBids T B E)).2.1 j
  change complementMarginal ξ T B E j ≤ 1 at hp
  unfold focalPrice
  apply mul_pos hb
  have hh := mul_le_mul_of_nonneg_left hp hξ.le
  nlinarith [hh]

omit [Nonempty ι] in
lemma focalSlope_nonneg {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι) (hb : 0 < B j) :
    0 ≤ focalSlope ξ T B E j :=
  rightSecant_nonneg B (insert j E) hξ (focalPrice_pos hξ hξ1 T B E j hb)

omit [Nonempty ι] in

theorem positive_guard_upper_demand {ξ : ℝ} (hξ : 0 < ξ)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population)
    (hhi : 0 < g.multiplier+g.radius)
    (hα : 0 < guardAlpha ξ g T B) :
    demand ξ T B (g.multiplier+g.radius) < (small T : ℝ)-g.margin*g.population ∧
      0 < small T := by
  have hs := (positive_guard_slacks g T B hε hM hα).2 (1 : Fin 5)
  change g.margin*g.population < (small T : ℝ)-demand ξ T B (g.multiplier+g.radius) at hs
  have hd : 0 ≤ demand ξ T B (g.multiplier+g.radius) := by
    apply Finset.sum_nonneg
    intro j _
    exact exposure_nonneg hξ hhi
  refine ⟨by linarith,?_⟩
  have hh : (0 : ℝ) < small T := by nlinarith [mul_pos hε hM]
  exact_mod_cast hh

theorem supported_path_root {ξ U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 < g.radius)
    (hU : 0 < U) (hlo : 0 < g.multiplier-g.radius)
    (hguard : (1-ξ)*U ≤ g.multiplier-g.radius)
    (hBU : ∀ j, B j ≤ U) (hout : ∀ j, j ∉ T.support → B j=0)
    (hα : 0 < guardAlpha ξ g T B)
    (path : Path ι (imbalance T))
    (hp : 0 < (pathLaw (weights ξ g T B) (imbalance T) ∅).mass path) :
    ∃ Λ ∈ Ioo (g.multiplier-g.radius) (g.multiplier+g.radius),
      IsLargestPositiveRoot ξ B (finalSet (imbalance T) ∅ path) (small T : ℝ) Λ ∧
      complementMarginal ξ T B (finalSet (imbalance T) ∅ path) =
        fun j => if j ∈ finalSet (imbalance T) ∅ path then 0 else exposure ξ Λ (B j) := by
  have hW : (imbalance T : ℝ) < totalWeight (weights ξ g T B) := by
    nlinarith [positive_guard_weight g T B hε hM hα,mul_pos hε hM]
  have hcard : (finalSet (imbalance T) ∅ path).card=imbalance T := by
    simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using
      finalSet_card (weights ξ g T B) (imbalance T) ∅ (by simpa using hW) path hp
  have hhi : 0 < g.multiplier+g.radius := by linarith
  have hu := positive_guard_upper_demand hξ g T B hε hM hhi hα
  apply exists_literal_complement_root T B _ hξ hξ1 hU hlo (by linarith)
    hguard hBU hout hu.2 (mul_pos hε hM)
  · rw [hcard, ← demand_eq_full hlo T B hout]
    exact positive_guard_lower_demand g T B hε hM hα
  · rw [← demand_eq_full hhi T B hout]
    exact hu.1

omit [Nonempty ι] in

theorem complement_eq_pathResponse_of_root {ξ U Λ : ℝ}
    (T : PureTemplate ι) (B : ι → ℝ) (E : Finset ι) (j : ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hΛ : 0 < Λ)
    (hguard : (1-ξ)*U ≤ Λ) (hBU : ∀ k, B k ≤ U)
    (hout : ∀ k, k ∉ T.support → B k=0)
    (hroot : remainingDemand ξ B E Λ = (small T : ℝ))
    (hj : j ∉ E) (hb : 0 < B j) :
    complementMarginal ξ T B E j = pathResponse ξ T B E j := by
  have he := complementMarginal_at_root T B E hξ hξ1 hU hΛ hguard hBU hout hroot
  have hp : complementMarginal ξ T B E j = exposure ξ Λ (B j) := by
    rw [congrFun he j,if_neg hj]
  have hfinite := exposure_eq_positive_deficit (small T) B E j hξ hξ1 hΛ
    hguard hBU hj hb hroot
  by_cases hpos : 0 < complementMarginal ξ T B E j
  · have hΛb : Λ < B j := by
      by_contra hnot
      rw [hp,exposure_zero (le_of_not_gt hnot)] at hpos
      exact lt_irrefl _ hpos
    have hprice : focalPrice ξ T B E j = Λ := by
      unfold focalPrice
      rw [hp]
      exact exposure_receipt hξ hΛ hΛb
        ((mul_le_mul_of_nonneg_left (hBU j) (by linarith)).trans hguard)
    unfold pathResponse focalDeficit focalSlope
    rw [hprice,hp]
    exact hfinite
  · have hp0 : complementMarginal ξ T B E j=0 := le_antisymm (le_of_not_gt hpos)
      ((EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1 (maskedBids T B E)).1 j)
    have hden : 0 < 1+B j*rightSecant ξ B (insert j E) Λ (B j) := by
      have hk := rightSecant_nonneg (b := B j) B (insert j E) hξ hΛ
      positivity
    rw [← hp,hp0] at hfinite
    have hnum : max 0 ((small T : ℝ)-remainingDemand ξ B (insert j E) (B j))=0 := by
      have hmul := (eq_div_iff hden.ne').mp hfinite
      simpa only [zero_mul] using hmul.symm
    rw [hp0]
    unfold pathResponse focalDeficit
    rw [hnum,zero_div]

lemma expect_congr_on_positive_mass {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ ω, 0 < P.mass ω → f ω=g ω) : P.expect f=P.expect g := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : 0 < P.mass ω
  · rw [h ω hp]
  · have hz : P.mass ω=0 := le_antisymm (le_of_not_gt hp) (P.nonneg ω)
    rw [hz,zero_mul,zero_mul]

theorem actual_guarded_path_moments {ξ U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hε : 0 < g.margin) (hM : 0 < g.population) (ha : 0 < g.radius)
    (hr : 0 < g.requiredDemand) (hU : 0 < U) (hlo : 0 < g.multiplier-g.radius)
    (hguard : (1-ξ)*U ≤ g.multiplier-g.radius)
    (hBU : ∀ k, B k ≤ U) (hout : ∀ k, k ∉ T.support → B k=0)
    (hb : 0 < B j) (hbL : B j ≤ g.multiplier) :
    guardAlpha ξ g T B*(canonicalLaw ξ g T B).expect (fairMarginal j) =
      guardAlpha ξ g T B*(pathLaw (weights ξ g T B) (imbalance T) ∅).expect
        (fun path => pathResponse ξ T B (finalSet (imbalance T) ∅ path) j) ∧
    guardAlpha ξ g T B*(canonicalLaw ξ g T B).expect (duplicate j) =
      guardAlpha ξ g T B*(pathLaw (weights ξ g T B) (imbalance T) ∅).expect
        (fun path => (pathResponse ξ T B (finalSet (imbalance T) ∅ path) j)^2) := by
  by_cases hα : 0 < guardAlpha ξ g T B
  · have hW : (imbalance T : ℝ) < totalWeight (weights ξ g T B) := by
      nlinarith [positive_guard_weight g T B hε hM hα,mul_pos hε hM]
    have hw : (weights ξ g T B).val j=0 := low_focal_weight_zero g T B j hr hbL
    have he (path : Path ι (imbalance T))
        (hp : 0 < (pathLaw (weights ξ g T B) (imbalance T) ∅).mass path) :
        complementMarginal ξ T B (finalSet (imbalance T) ∅ path) j =
          pathResponse ξ T B (finalSet (imbalance T) ∅ path) j := by
      obtain ⟨Λ,hΛ,hroot,_⟩ := supported_path_root hξ hξ1 g T B hε hM ha hU hlo
        hguard hBU hout hα path hp
      exact complement_eq_pathResponse_of_root T B _ j hξ hξ1 hU hroot.1
        (hguard.trans hΛ.1.le) hBU hout hroot.2.1
        (focal_not_sampled_of_zero_weight ξ g T B j hW hw path hp) hb
    constructor
    · rw [canonical_path_fair_marginal hξ hξ1 g T B j hW hw]
      congr 1
      exact expect_congr_on_positive_mass _ _ _ he
    · rw [canonical_path_duplicate hξ hξ1]
      congr 1
      apply expect_congr_on_positive_mass
      intro path hp
      rw [he path hp]
  · have hz : guardAlpha ξ g T B=0 := le_antisymm (le_of_not_gt hα)
      (guardAlpha_bounds ξ g T B).1
    simp only [hz,zero_mul,and_self]

end FCAppendix.Affine.Uniform06.LiteralKernelIdentity
