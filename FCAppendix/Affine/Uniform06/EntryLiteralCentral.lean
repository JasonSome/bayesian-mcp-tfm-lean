import FCAppendix.Affine.Uniform06.ActualEntryGoodGeometry
import FCAppendix.Affine.Uniform06.EntryRawCentralTransfer
import FCAppendix.Affine.Uniform06.LiteralKernelMeasurable

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralCentral

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelIdentity EntryEarlySourceLimits EntryRawCentral
open EntryProfileMean EntrySamplingLaw EntryReciprocalLimit ReciprocalSecantBounds
open scoped BigOperators

lemma weights_eq_profile {N : ℕ} (i : Row) (g : GuardData)
    (hr : g.requiredDemand=PrefixRoot.requiredDemand i)
    (C : ℕ) (b : ℝ) (r : Fin N → RowRival) :
    weights (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)=
      profileWeights (focalWeight i b g.multiplier) (rawWeight i g.multiplier)
        (focalWeight_bounds i b g.multiplier) (rawWeight_bounds i g.multiplier) r := by
  apply Subtype.ext
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [weights,patternTemplate,patternRow,rowLowList,rowBids,profileWeights,focalWeight,hr]
  · by_cases hj : (r j).1=0 <;>
      simp [weights,patternTemplate,patternRow,rowLowList,rowBids,profileWeights,rawWeight,
        RivalGood.lowerTest,hj,hr]

lemma rowBids_eq_listBids {N : ℕ} (b : ℝ) (r : Fin N → RowRival) :
    rowBids b r=EntryDeletedReciprocal.listBids b r := rfl

lemma exposure_le_half_of_receipt {ξ b U B : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hb : 0 < b)
    (hBU : B ≤ U) (hreceipt : (1-ξ/2)*U ≤ b) : exposure ξ b B ≤ 1/2 := by
  by_cases hBb : B ≤ b
  · rw [exposure_zero hBb]
    norm_num
  · have hbB : b < B := lt_of_not_ge hBb
    have hB := hb.trans hbB
    have hcoef : 0 ≤ 1-ξ/2 := by linarith
    have hhalf : (1-ξ/2)*B ≤ b :=
      (mul_le_mul_of_nonneg_left hBU hcoef).trans hreceipt
    have hguard : (1-ξ)*B ≤ b := by nlinarith [mul_nonneg hξ.le hB.le]
    rw [exposure_of_between hξ hb hbB hguard]
    apply (div_le_iff₀ hξ).mpr
    have hratio : 1-ξ/2 ≤ b/B := (le_div_iff₀ hB).mpr hhalf
    linarith

lemma profileH_eq_literal {N : ℕ} (i : Row) {b U : ℝ} (hb : 0 < b)
    (r : Fin N → RowRival) (hBU : ∀ j, rowBids b r j ≤ U)
    (hreceipt : (1-xi i/2)*U ≤ b) :
    profileH (1/2) (rawH i b) r=fun j => (1/2:ℝ)-exposure (xi i) b (rowBids b r j) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [profileH,rowBids,exposure_zero le_rfl]
  · by_cases hj : (r j).1=0
    · have hh := exposure_le_half_of_receipt (xi_pos i) hξ1 hb (hBU j.succ) hreceipt
      simp only [rowBids,Fin.cons_succ,if_pos hj] at hh
      simp only [profileH,Fin.cons_succ,rawH,if_pos hj,clippedH,rowBids,
        max_eq_left (sub_nonneg.mpr hh)]
    · simp [profileH,rawH,rowBids,hj,exposure_zero hb.le]

def pathDeficit {N : ℕ} (i : Row) (C : ℕ) (b : ℝ)
    (r : Fin N → RowRival) {d : ℕ} (p : Path (Fin (N+1)) d) : ℝ :=
  (C:ℝ)-(∑ j, RawMixedSource.demand (xi i) b (r j))-
    selectedSum (profileH (1/2) (rawH i b) r) d p

theorem exact_path_deficit {N : ℕ} (i : Row) (g : GuardData)
    {C : ℕ} {b U : ℝ} (hb : 0 < b)
    (r : Fin N → RowRival)
    (hcap₀ : classCount 1 r+classCount 2 r ≤ C)
    (hcap₁ : classCount 1 r+classCount 3 r ≤ C)
    (hroom₀ : C-classCount 1 r-classCount 2 r ≤ 1+classCount 0 r)
    (hroom₁ : C-classCount 1 r-classCount 3 r ≤ 1+classCount 0 r)
    (hBU : ∀ j, rowBids b r j ≤ U) (hreceipt : (1-xi i/2)*U ≤ b)
    (p : Path (Fin (N+1)) (imbalance (patternTemplate C (fun j => (r j).1))))
    (hW : (imbalance (patternTemplate C (fun j => (r j).1)):ℝ)<
      totalWeight (weights (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)))
    (hp : 0 < (pathLaw (weights (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r))
      (imbalance (patternTemplate C (fun j => (r j).1))) ∅).mass p)
    (hfocal : (0:Fin (N+1)) ∉ finalSet (imbalance (patternTemplate C (fun j => (r j).1))) ∅ p) :
    focalDeficit (xi i) (patternTemplate C (fun j => (r j).1)) (rowBids b r)
      (finalSet (imbalance (patternTemplate C (fun j => (r j).1))) ∅ p) 0=
        pathDeficit i C b r p := by
  let T := patternTemplate C (fun j => (r j).1)
  let B := rowBids b r
  let E := finalSet (imbalance T) ∅ p
  let w := weights (xi i) g T B
  have hcard : E.card=imbalance T := by
    simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using finalSet_card w _ ∅ (by simpa using hW) p hp
  have hs := selectedSum_eq_setSum w (profileH (1/2) (rawH i b) r) (imbalance T) ∅
    (by simpa using hW) p hp
  simp only [Finset.sum_empty,sub_zero] at hs
  rw [profileH_eq_literal i hb r hBU hreceipt] at hs
  have hd := RawDeficitGeometry.template_deficit_eq_raw i C hb r hcap₀ hcap₁ hroom₀ hroom₁
  rw [LiteralCoarsePath.focalDeficit_eq_balanced _ T B E 0 hfocal hcard,hd]
  have he : (∑ k ∈ E, (1/2-exposure (xi i) (B 0) (B k))) =
      selectedSum (profileH (1/2) (rawH i b) r) (imbalance T) p := by
    rw [profileH_eq_literal i hb r hBU hreceipt]
    exact hs.symm
  rw [he]
  rfl

theorem literal_response_from_guards {N : ℕ} (i : Row) (g : GuardData)
    {C : ℕ} {b U : ℝ} (hb : 0 < b) (hU : 0 < U)
    (hmargin : 0 < g.margin) (hpopulation : 0 < g.population)
    (hradius : 0 < g.radius) (hlo : 0 < g.multiplier-g.radius)
    (hguard : (1-xi i)*U ≤ g.multiplier-g.radius)
    (r : Fin N → RowRival)
    (hcap₀ : classCount 1 r+classCount 2 r ≤ C)
    (hcap₁ : classCount 1 r+classCount 3 r ≤ C)
    (hroom₀ : C-classCount 1 r-classCount 2 r ≤ 1+classCount 0 r)
    (hroom₁ : C-classCount 1 r-classCount 3 r ≤ 1+classCount 0 r)
    (hBU : ∀ j, rowBids b r j ≤ U) (hreceipt : (1-xi i/2)*U ≤ b)
    (hα : 0 < guardAlpha (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r))
    (p : Path (Fin (N+1)) (imbalance (patternTemplate C (fun j => (r j).1))))
    (hp : 0 < (pathLaw (weights (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r))
      (imbalance (patternTemplate C (fun j => (r j).1))) ∅).mass p)
    (hfocal : (0:Fin (N+1)) ∉ finalSet (imbalance (patternTemplate C (fun j => (r j).1))) ∅ p) :
    let T := patternTemplate C (fun j => (r j).1)
    let E := finalSet (imbalance T) ∅ p
    let q := complementMarginal (xi i) T (rowBids b r) E 0
    let K := focalSlope (xi i) T (rowBids b r) E 0
    q=max (pathDeficit i C b r p) 0/(1+b*K) ∧
      (0< q ↔ 0< pathDeficit i C b r p) ∧
      (0< q → focalPrice (xi i) T (rowBids b r) E 0 ∈
        Ioo (g.multiplier-g.radius) (min b (g.multiplier+g.radius))) := by
  let T := patternTemplate C (fun j => (r j).1)
  let B := rowBids b r
  let E := finalSet (imbalance T) ∅ p
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hW : (imbalance T:ℝ)< totalWeight (weights (xi i) g T B) := by
    nlinarith [SourceGuardGeometry.positive_guard_weight g T B hmargin hpopulation hα,
      mul_pos hmargin hpopulation]
  obtain ⟨Λ,hΛ,hr,hm⟩ := supported_path_root hξ hξ1 g T B hmargin hpopulation hradius hU hlo
    hguard hBU (rowBids_outside C b r) hα p hp
  have he := complement_eq_pathResponse_of_root T B E 0 hξ hξ1 hU hr.1
    (hguard.trans hΛ.1.le) hBU (rowBids_outside C b r) hr.2.1 hfocal hb
  have hD := exact_path_deficit i g hb r hcap₀ hcap₁ hroom₀ hroom₁ hBU hreceipt p hW hp hfocal
  have hk := focalSlope_nonneg hξ hξ1 T B E 0 hb
  have hden : 0<1+b*focalSlope (xi i) T B E 0 := by positivity
  dsimp only
  have hq : complementMarginal (xi i) T B E 0=max (pathDeficit i C b r p) 0/
      (1+b*focalSlope (xi i) T B E 0) := by
    rw [he,pathResponse,hD,max_comm]
    rfl
  refine ⟨hq,?_,?_⟩
  · rw [hq,div_pos_iff_of_pos_right hden,lt_max_iff]
    simp
  · intro hqpos
    have hpΛ : complementMarginal (xi i) T B E 0=exposure (xi i) Λ b := by
      rw [congrFun hm 0,if_neg hfocal]
      rfl
    have hΛb : Λ < b := by
      by_contra hnot
      rw [hpΛ,exposure_zero (le_of_not_gt hnot)] at hqpos
      exact lt_irrefl _ hqpos
    have hprice : focalPrice (xi i) T B E 0=Λ := by
      unfold focalPrice
      rw [hpΛ]
      exact exposure_receipt hξ hr.1 hΛb
        ((mul_le_mul_of_nonneg_left (hBU 0) (by linarith)).trans (hguard.trans hΛ.1.le))
    rw [hprice]
    exact ⟨hΛ.1,lt_min hΛb hΛ.2⟩

lemma sampler_positive_mass_ae {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (n : ℕ) (w : Weights ι) :
    ∀ᵐ u : unitInterval ∂volume, 0 < (pathLaw w n ∅).mass (sampler n w u) := by
  have hm : Measurable (sampler n w) :=
    (measurable_sampler n).comp (measurable_const.prodMk measurable_id)
  have ha : ∀ᵐ p ∂FiniteLaw.probabilityMeasure (pathLaw w n ∅), 0 < (pathLaw w n ∅).mass p :=
    (FiniteLaw.probabilityMeasure_ae_mass_ne_zero _).mono fun p hp =>
      lt_of_le_of_ne ((pathLaw w n ∅).nonneg p) hp.symm
  rw [← sampler_law n w] at ha
  exact (ae_map_iff hm.aemeasurable (by measurability)).mp ha

theorem actual_sampler_positive_ae {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → Weights ι) (d : Ω → ℕ) (hw : Measurable w) (hd : Measurable d) :
    ∀ᵐ x ∂μ.prod (volume : Measure unitInterval),
      0 < (pathLaw (w x.1) (d x.1) ∅).mass (sampler (d x.1) (w x.1) x.2) := by
  have hmN (n : ℕ) : Measurable (fun x : Ω × unitInterval =>
      (pathLaw (w x.1) n ∅).mass (sampler n (w x.1) x.2)) := by
    have hmass : Measurable (fun z : Weights ι × Path ι n => (pathLaw z.1 n ∅).mass z.2) :=
      measurable_from_prod_countable_left (fun p => measurable_pathLaw_mass n ∅ p)
    exact hmass.comp ((hw.comp measurable_fst).prodMk
      ((measurable_sampler n).comp ((hw.comp measurable_fst).prodMk measurable_snd)))
  have hm : Measurable (fun x : Ω × unitInterval =>
      (pathLaw (w x.1) (d x.1) ∅).mass (sampler (d x.1) (w x.1) x.2)) :=
    (measurable_from_prod_countable_right (f := fun x : ℕ × (Ω × unitInterval) =>
      (pathLaw (w x.2.1) x.1 ∅).mass (sampler x.1 (w x.2.1) x.2.2)) hmN).comp
      ((hd.comp measurable_fst).prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const hm)).mpr
  exact ae_of_all _ fun r => sampler_positive_mass_ae (d r) (w r)

end FCAppendix.Affine.Uniform06.EntryLiteralCentral
