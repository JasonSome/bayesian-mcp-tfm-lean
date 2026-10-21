import FCAppendix.Affine.Uniform06.EntryCornerNull
import FCAppendix.Affine.Uniform06.MaskedRootDerivative
import FCAppendix.Affine.Uniform06.EntryLiteralResponseGeometry

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceRawDerivative

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment LiteralKernelIdentity ActualRootDerivative
open RegularRootDifferentiability EntryThresholdNull EntryCornerNull
open EntryLiteralResponseGeometry CanonicalInterior EntryOwnImpact

variable {N : ℕ}

def rivalDeletion (E : Finset (Fin (N+1))) : Finset (Fin N) :=
  Finset.univ.filter (fun j => j.succ ∈ E)

@[simp] lemma mem_rivalDeletion (E : Finset (Fin (N+1))) (j : Fin N) :
    j ∈ rivalDeletion E ↔ j.succ ∈ E := by simp [rivalDeletion]

lemma rowBids_update (r : Fin N → RowRival) (a b : ℝ) :
    rowBids a r=Function.update (rowBids b r) 0 a := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [rowBids]
  · simp [rowBids,Fin.succ_ne_zero]

lemma focal_mem (C : ℕ) (r : Fin N → RowRival) :
    (0:Fin (N+1)) ∈ (patternTemplate C (fun j => (r j).1)).support := by
  simp [patternTemplate,patternRow,rowLowList]

lemma succ_mem (C : ℕ) (r : Fin N → RowRival) (j : Fin N) :
    j.succ ∈ (patternTemplate C (fun k => (r k).1)).support ↔ (r j).1=0 := by
  simp [patternTemplate,patternRow,rowLowList]

lemma remaining_masked_eq (i : Row) (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {z : ℝ} (hz : 0 < z) (b : ℝ) :
    remainingDemand (xi i)
      (maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids b r) E) {0} z=
        EntryThresholdNull.demand (xi i) z (rivalDeletion E) r := by
  unfold remainingDemand EntryThresholdNull.demand
  rw [Fin.sum_univ_succ]
  simp only [Finset.mem_singleton,if_true,zero_add,Fin.succ_ne_zero,if_false]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : j.succ ∈ E
  · simp [maskedBids,EntryThresholdNull.contribution,he,exposure_zero hz.le]
  · by_cases ht : (r j).1=0
    · simp [maskedBids,EntryThresholdNull.contribution,he,ht,succ_mem,rowBids]
    · simp [maskedBids,EntryThresholdNull.contribution,he,ht,succ_mem,
        exposure_zero hz.le]

lemma complement_eq_marginal (i : Row) (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) (hE : (0:Fin (N+1)) ∉ E) (a : ℝ) :
    complementMarginal (xi i) (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0=
      marginal (xi i) (small (patternTemplate C (fun j => (r j).1)))
        (maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E) 0 a := by
  have hf : (0:Fin (N+1)) ∈ (patternTemplate C (fun j => (r j).1)).support \ E :=
    Finset.mem_sdiff.mpr ⟨focal_mem C r,hE⟩
  rw [rowBids_update r a 0,complementMarginal,
    MaskedRootDerivative.masked_update _ _ E 0 hf a]
  rfl

lemma masked_nonnegative (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1)))
    (hr : ∀ j,(r j).1=0 → 0 ≤ (r j).2) :
    ∀ k,0 ≤ maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E k := by
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [maskedBids,rowBids]
  · by_cases ht : (r j).1=0
    · by_cases he : j.succ ∈ E
      · simp [maskedBids,he]
      · simpa [maskedBids,succ_mem,he,ht,rowBids] using hr j ht
    · simp [maskedBids,succ_mem,ht]

lemma exposure_at_receipt {ξ b p : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hb : 0 < b) (hp : p ∈ Ioo (0:ℝ) 1) :
    exposure ξ (b*(1-ξ*p)) b=p := by
  have hz : 0 < b*(1-ξ*p) := by
    apply mul_pos hb
    nlinarith [mul_le_mul_of_nonneg_left hp.2.le hξ.le]
  have hzb : b*(1-ξ*p)< b := by nlinarith [mul_pos hb (mul_pos hξ hp.1)]
  have hκ : (1-ξ)*b ≤ b*(1-ξ*p) := by
    nlinarith [mul_nonneg (mul_pos hb hξ).le (sub_nonneg.mpr hp.2.le)]
  rw [exposure_of_between hξ hz hzb hκ]
  field_simp [hξ.ne',hb.ne']
  ring

theorem raw_lower_nonnegative (i : Row) (G : Measure (ℝ × ℝ))
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) :
    ∀ᵐ u ∂ RawMixedSource.source i G,u.1=0 → 0 ≤ u.2 := by
  have hbids : ∀ᵐ z ∂G.map Prod.snd,0 ≤ z :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr hnon
  unfold RawMixedSource.source rivalLaw
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero,ae_add_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    filter_upwards [hbids] with z hz
    exact fun _ => hz
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]

theorem original_all_removed_derivatives (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (C : ℕ) (E : Finset (Fin (N+1))), (0:Fin (N+1)) ∉ E →
        complementMarginal (xi i) (patternTemplate C (fun j => (r j).1))
          (rowBids b r) E 0 < 1 →
        (∃ j : Fin N,j.succ ∉ E ∧ (r j).1=0 ∧
          b<(r j).2 ∧ (1-xi i)*(r j).2≤ b) →
        HasDerivAt (fun a => complementMarginal (xi i)
          (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0)
          (MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (r j).1))
            (rowBids 0 r) E 0 b) b := by
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hraw := raw_lower_nonnegative i G hnon
  have hrnon : ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ j,(r j).1=0 → 0 ≤ (r j).2 :=
    ae_all_iff.mpr fun j => (measurePreserving_eval
      (fun _ : Fin N => RawMixedSource.source i G) j).quasiMeasurePreserving.ae hraw
  filter_upwards [original_fixed_price_threshold_null i G hnull N hb,
    original_fixed_price_corner_null i G hnull N hb,hrnon] with r hthreshold hcorner hr
  intro C E hE hp1 hwitness
  let T := patternTemplate C (fun j => (r j).1)
  let B := maskedBids T (rowBids 0 r) E
  let p := marginal (xi i) (small T) B 0
  let z := receipt (xi i) (small T) B 0 b
  have heq (a : ℝ) : complementMarginal (xi i) T (rowBids a r) E 0=p a :=
    complement_eq_marginal i C r E hE a
  have hf : (0:Fin (N+1)) ∈ T.support \ E :=
    Finset.mem_sdiff.mpr ⟨focal_mem C r,hE⟩
  have hB : ∀ k,0 ≤ B k := masked_nonnegative C r E hr
  have hp0 : 0 ≤ p b := (marginal_bounds hξ hξ1 (small T) B 0 b).1
  have hp1' : p b < 1 := by
    change complementMarginal (xi i) T (rowBids b r) E 0 < 1 at hp1
    rw [heq] at hp1
    exact hp1
  have hz : 0 < z := receipt_pos hξ hξ1 (small T) B 0 hb
  have hremain (a : ℝ) (ha : 0 < a) : remainingDemand (xi i) B {0} a=
      EntryThresholdNull.demand (xi i) a (rivalDeletion E) r :=
    remaining_masked_eq i C r E ha 0
  by_cases hp : 0 < p b
  · have hstrip : z ∈ Ioo ((1-xi i)*b) b := by
      dsimp only [z,receipt]
      constructor
      · nlinarith [mul_pos (mul_pos hb hξ) (sub_pos.mpr hp1')]
      · nlinarith [mul_pos hb (mul_pos hξ hp)]
    have he : exposure (xi i) z b+
        EntryThresholdNull.demand (xi i) z (rivalDeletion E) r=(small T:ℝ) := by
      have hh := actual_interior_equation hξ hξ1 (small T) B 0 hb ⟨hp,hp1'⟩
      rw [hremain z hz] at hh
      have hx : exposure (xi i) z b=p b :=
        exposure_at_receipt hξ hξ1 hb ⟨hp,hp1'⟩
      rw [hx]
      linarith
    have hfaces : ∀ k,k ≠ (0:Fin (N+1)) → z ≠ B k ∧ z ≠ (1-xi i)*B k := by
      intro k hk
      refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) k hk
      by_cases he' : j.succ ∈ E
      · have hzero : B j.succ=0 := by simp [B,maskedBids,he']
        simp [hzero,hz.ne']
      · by_cases ht : (r j).1=0
        · have hbid : B j.succ=(r j).2 := by
            simp [B,T,maskedBids,succ_mem,he',ht,rowBids]
          rw [hbid]
          have hc := hcorner (rivalDeletion E) (small T) j ht
          constructor
          · intro hzj
            exact hc.1 (hzj ▸ hstrip) (hzj ▸ he)
          · intro hzj
            exact hc.2 (hzj ▸ hstrip) (hzj ▸ he)
        · have hzero : B j.succ=0 := by simp [B,T,maskedBids,succ_mem,ht]
          simp [hzero,hz.ne']
    have hd := actual_interior_hasDerivAt hξ hξ1 (small T) B 0
      (fun k _ => hB k) hb ⟨hp,hp1'⟩ hfaces
    have hfun : (fun a => complementMarginal (xi i) T (rowBids a r) E 0)=p := funext heq
    rw [hfun]
    change HasDerivAt p (if (0:Fin (N+1)) ∈ T.support \ E then
      derivative (xi i) (small T) B 0 b else 0) b
    rw [if_pos hf]
    simpa only [derivative, if_pos (show 0 < marginal (xi i) (small T) B 0 b ∧
      marginal (xi i) (small T) B 0 b < 1 from ⟨hp,hp1'⟩)] using hd
  · have hpz : p b=0 := le_antisymm (le_of_not_gt hp) hp0
    have hpp := actual_interior_positive_part hξ hξ1 (small T)
      (Function.update B 0 b) 0 (by simpa using hb) hp1'
    have hκ : 0 ≤ rightSecant (xi i) (Function.update B 0 b) {0}
        (b*(1-xi i*p b)) b :=
      EntryOwnImpact.rightSecant_nonneg _ _ hξ (by simpa only [hpz,mul_zero,sub_zero,mul_one] using hb)
    have hden : 0 < 1+b*rightSecant (xi i) (Function.update B 0 b) {0}
        (b*(1-xi i*p b)) b := by positivity
    have hcle : (small T:ℝ) ≤ remainingDemand (xi i) B {0} b := by
      change p b=max 0 ((small T:ℝ)-remainingDemand (xi i) (Function.update B 0 b) {0} b)/
        (1+b*rightSecant (xi i) (Function.update B 0 b) {0} (b*(1-xi i*p b)) b) at hpp
      rw [hpz,remaining_update_focal] at hpp
      rw [hpz] at hden
      have hm : max 0 ((small T:ℝ)-remainingDemand (xi i) B {0} b)=0 :=
        (div_eq_zero_iff.mp hpp.symm).resolve_right hden.ne'
      have hh := le_max_right 0 ((small T:ℝ)-remainingDemand (xi i) B {0} b)
      rw [hm] at hh
      linarith
    have hne : remainingDemand (xi i) B {0} b ≠ (small T:ℝ) := by
      rw [hremain b hb]
      apply hthreshold (rivalDeletion E) (small T)
      obtain ⟨j,hj,ht,hb',hg⟩ := hwitness
      exact ⟨j,by simpa using hj,ht,hb',hg⟩
    have hstrict : (small T:ℝ)< remainingDemand (xi i) B {0} b :=
      lt_of_le_of_ne hcle hne.symm
    have hd := zero_face_hasDerivAt hξ hξ1 (small T) B 0 hb hstrict
    have hfun : (fun a => complementMarginal (xi i) T (rowBids a r) E 0)=p := funext heq
    rw [hfun]
    change HasDerivAt p (if (0:Fin (N+1)) ∈ T.support \ E then
      derivative (xi i) (small T) B 0 b else 0) b
    rw [if_pos hf]
    have hpz' : marginal (xi i) (small T) B 0 b=0 := hpz
    simpa only [derivative,hpz',lt_self_iff_false,false_and,if_false] using hd

end FCAppendix.Affine.Uniform06.FixedPriceRawDerivative
