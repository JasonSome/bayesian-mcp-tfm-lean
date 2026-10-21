import FCAppendix.Affine.Uniform06.FixedPriceRawDerivative
import FCAppendix.Affine.Uniform06.RootFlatFaces

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceAllFaces

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment LiteralKernelIdentity ActualRootDerivative
open RegularRootDifferentiability EntryThresholdNull EntryCornerNull
open FixedPriceRawDerivative RootFlatFaces

variable {N : ℕ}

lemma masked_fixed_faces (i : Row) (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {z : ℝ} (hz : 0 < z)
    (hr : ∀ j,(r j).1=0 → z ≠ (r j).2 ∧ z ≠ (1-xi i)*(r j).2) :
    ∀ k,k ≠ (0:Fin (N+1)) →
      z ≠ maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E k ∧
      z ≠ (1-xi i)*maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E k := by
  intro k hk
  refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) k hk
  by_cases he : j.succ ∈ E
  · simp [maskedBids,he,hz.ne']
  · by_cases ht : (r j).1=0
    · simpa [maskedBids,succ_mem,he,ht,rowBids] using hr j ht
    · simp [maskedBids,succ_mem,ht,hz.ne']

lemma masked_flat_of_no_witness (i : Row) (C : ℕ) (r : Fin N → RowRival)
    (E : Finset (Fin (N+1))) {z : ℝ} (hz : 0 < z)
    (hn : ¬ ∃ j : Fin N,j.succ ∉ E ∧ (r j).1=0 ∧
      z<(r j).2 ∧ (1-xi i)*(r j).2≤ z) :
    ∀ k,k ≠ (0:Fin (N+1)) →
      ¬ ((1-xi i)*maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E k < z ∧
        z < maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E k) := by
  intro k hk
  refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) k hk
  by_cases he : j.succ ∈ E
  · simp [maskedBids,he,not_lt.mpr hz.le]
  · by_cases ht : (r j).1=0
    · intro hp
      have hbid : maskedBids (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E j.succ=
          (r j).2 := by simp [maskedBids,succ_mem,he,ht,rowBids]
      rw [hbid] at hp
      exact hn ⟨j,he,ht,hp.2,hp.1.le⟩
    · simp [maskedBids,succ_mem,ht,not_lt.mpr hz.le]

theorem original_raw_fixed_faces (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (z : ℝ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ j,(r j).1=0 → z ≠ (r j).2 ∧ z ≠ (1-xi i)*(r j).2 := by
  have hκ : 0 < 1-xi i := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hu : ∀ᵐ u ∂ RawMixedSource.source i G,u.1=0 →
      z ≠ u.2 ∧ z ≠ (1-xi i)*u.2 := by
    filter_upwards [raw_lower_bid_ne i G hnull z,
      raw_lower_bid_ne i G hnull (z/(1-xi i))] with u hz hκz ht
    refine ⟨(hz ht).symm,?_⟩
    intro he
    apply hκz ht
    apply (eq_div_iff hκ.ne').mpr
    nlinarith
  exact ae_all_iff.mpr fun j => (measurePreserving_eval
    (fun _ : Fin N => RawMixedSource.source i G) j).quasiMeasurePreserving.ae hu

theorem original_all_removed_derivatives (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (C : ℕ) (E : Finset (Fin (N+1))), (0:Fin (N+1)) ∉ E →
        HasDerivAt (fun a => complementMarginal (xi i)
          (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0)
          (MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (r j).1))
            (rowBids 0 r) E 0 b) b := by
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hκb : 0 < (1-xi i)*b := mul_pos (sub_pos.mpr hξ1) hb
  have hrnon : ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ j,(r j).1=0 → 0 ≤ (r j).2 :=
    ae_all_iff.mpr fun j => (measurePreserving_eval
      (fun _ : Fin N => RawMixedSource.source i G) j).quasiMeasurePreserving.ae
        (raw_lower_nonnegative i G hnon)
  filter_upwards [original_fixed_price_threshold_null i G hnull N hb,
    original_fixed_price_threshold_null i G hnull N hκb,
    original_fixed_price_corner_null i G hnull N hb,
    original_raw_fixed_faces i G hnull b,
    original_raw_fixed_faces i G hnull ((1-xi i)*b),hrnon]
      with r hthreshold hthresholdκ hcorner hfacesb hfacesκ hr
  intro C E hE
  let T := patternTemplate C (fun j => (r j).1)
  let B := maskedBids T (rowBids 0 r) E
  let p := marginal (xi i) (small T) B 0
  let z := receipt (xi i) (small T) B 0 b
  have heq (a : ℝ) : complementMarginal (xi i) T (rowBids a r) E 0=p a :=
    complement_eq_marginal i C r E hE a
  have hf : (0:Fin (N+1)) ∈ T.support \ E :=
    Finset.mem_sdiff.mpr ⟨focal_mem C r,hE⟩
  have hB : ∀ k,0 ≤ B k := masked_nonnegative C r E hr
  have hp := marginal_bounds hξ hξ1 (small T) B 0 b
  have hz : 0 < z := receipt_pos hξ hξ1 (small T) B 0 hb
  have hremain (a : ℝ) (ha : 0 < a) : remainingDemand (xi i) B {0} a=
      EntryThresholdNull.demand (xi i) a (rivalDeletion E) r :=
    remaining_masked_eq i C r E ha 0
  have hfun : (fun a => complementMarginal (xi i) T (rowBids a r) E 0)=p := funext heq
  rw [hfun]
  change HasDerivAt p (if (0:Fin (N+1)) ∈ T.support \ E then
    derivative (xi i) (small T) B 0 b else 0) b
  rw [if_pos hf]
  by_cases hpz : p b=0
  · have hd : HasDerivAt p 0 b := by
      by_cases hw : ∃ j : Fin N,j.succ ∉ E ∧ (r j).1=0 ∧
          b<(r j).2 ∧ (1-xi i)*(r j).2≤ b
      · have hcle := zero_implies_capacity_le hξ hξ1 (small T) B 0 hb hpz
        have hne : remainingDemand (xi i) B {0} b ≠ (small T:ℝ) := by
          rw [hremain b hb]
          apply hthreshold (rivalDeletion E) (small T)
          obtain ⟨j,hj,ht,hb',hg⟩ := hw
          exact ⟨j,by simpa using hj,ht,hb',hg⟩
        exact zero_face_hasDerivAt hξ hξ1 (small T) B 0 hb
          (lt_of_le_of_ne hcle hne.symm)
      · exact zero_face_hasDerivAt_of_flat hξ hξ1 (small T) B 0 hb hpz
          (masked_fixed_faces i C r E hb hfacesb)
          (masked_flat_of_no_witness i C r E hb hw)
    simpa only [derivative,
      show marginal (xi i) (small T) B 0 b=0 from hpz,
      lt_self_iff_false,false_and,if_false] using hd
  · by_cases hpo : p b=1
    · have hd : HasDerivAt p 0 b := by
        by_cases hw : ∃ j : Fin N,j.succ ∉ E ∧ (r j).1=0 ∧
            (1-xi i)*b<(r j).2 ∧ (1-xi i)*(r j).2≤(1-xi i)*b
        · have hcap := full_implies_capacity_le hξ hξ1 (small T) B 0 hb hpo
          have hnonH := remaining_nonnegative hξ hκb B 0
          have hc1 : 1 ≤ small T := by exact_mod_cast (show (1:ℝ) ≤ (small T:ℝ) by linarith)
          have hcast : ((small T-1:ℕ):ℝ)=(small T:ℝ)-1 := by
            rw [Nat.cast_sub hc1,Nat.cast_one]
          have hne : remainingDemand (xi i) B {0} ((1-xi i)*b) ≠ (small T:ℝ)-1 := by
            rw [hremain _ hκb,← hcast]
            apply hthresholdκ (rivalDeletion E) (small T-1)
            obtain ⟨j,hj,ht,hb',hg⟩ := hw
            exact ⟨j,by simpa using hj,ht,hb',hg⟩
          apply full_face_hasDerivAt hξ hξ1 (small T) B 0 hb
          by_contra hn
          exact hne (by linarith)
        · exact full_face_hasDerivAt_of_flat hξ hξ1 (small T) B 0 hb hpo
            (masked_fixed_faces i C r E hκb hfacesκ)
            (masked_flat_of_no_witness i C r E hκb hw)
      simpa only [derivative,
        show marginal (xi i) (small T) B 0 b=1 from hpo,
        lt_self_iff_false,and_false,if_false] using hd
    · have hpi : p b ∈ Ioo (0:ℝ) 1 :=
        ⟨lt_of_le_of_ne hp.1 (Ne.symm hpz),lt_of_le_of_ne hp.2 hpo⟩
      have hstrip : z ∈ Ioo ((1-xi i)*b) b := by
        dsimp only [z,receipt]
        constructor
        · nlinarith [mul_pos (mul_pos hb hξ) (sub_pos.mpr hpi.2)]
        · nlinarith [mul_pos hb (mul_pos hξ hpi.1)]
      have he : exposure (xi i) z b+
          EntryThresholdNull.demand (xi i) z (rivalDeletion E) r=(small T:ℝ) := by
        have hh := actual_interior_equation hξ hξ1 (small T) B 0 hb hpi
        rw [hremain z hz] at hh
        have hexp : exposure (xi i) z b=p b := by
          exact exposure_at_receipt hξ hξ1 hb hpi
        rw [hexp]
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
        (fun k _ => hB k) hb hpi hfaces
      have hpi' : 0 < marginal (xi i) (small T) B 0 b ∧
          marginal (xi i) (small T) B 0 b < 1 := hpi
      rw [derivative,if_pos hpi']
      exact hd

theorem original_every_fixed_bid_derivatives (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G]
    (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0 ≤ p.2) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (C : ℕ) (E : Finset (Fin (N+1))),
        HasDerivAt (fun a => complementMarginal (xi i)
          (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0)
          (MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (r j).1))
            (rowBids 0 r) E 0 b) b ∧
        HasDerivAt (fun a => (complementMarginal (xi i)
          (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0)^2)
          (2*complementMarginal (xi i) (patternTemplate C (fun j => (r j).1))
            (rowBids b r) E 0*MaskedRootDerivative.slope (xi i)
              (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) E 0 b) b := by
  filter_upwards [original_all_removed_derivatives i G hnull hnon hb] with r hr C E
  have hd : HasDerivAt (fun a => complementMarginal (xi i)
      (patternTemplate C (fun j => (r j).1)) (rowBids a r) E 0)
      (MaskedRootDerivative.slope (xi i) (patternTemplate C (fun j => (r j).1))
        (rowBids 0 r) E 0 b) b := by
    by_cases he : (0:Fin (N+1)) ∈ E
    · have hf : (0:Fin (N+1)) ∉ (patternTemplate C (fun j => (r j).1)).support \ E :=
        fun h => (Finset.mem_sdiff.mp h).2 he
      simpa only [MaskedRootDerivative.complement_zero_absent _ _ _ _ _ hf,
        MaskedRootDerivative.slope,if_neg hf] using (hasDerivAt_const b (0:ℝ))
    · exact hr C E he
  refine ⟨hd,?_⟩
  convert! hd.pow 2 using 1
  ring

end FCAppendix.Affine.Uniform06.FixedPriceAllFaces
