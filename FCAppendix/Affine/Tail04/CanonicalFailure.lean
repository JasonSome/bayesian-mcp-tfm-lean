import FCAppendix.Affine.Tail04.UnusedFocalCountError
import FCAppendix.Affine.Tail04.SourceMenuIdentity

noncomputable section
namespace FCAppendix.Affine.Tail04.CanonicalFailure
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues MenuError SourceMenuIdentity SourceMenuPopulation SourceMomentRectangle SourceMenuError
open UnusedFocalCountError

def probabilityGap (ξ : ℝ) : ℝ := 2*γ ξ/(ξ*Central.B ξ)

lemma probabilityGap_pos {ξ : ℝ} (hξ : 0< ξ) : 0< probabilityGap ξ := by
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  unfold probabilityGap γ
  positivity

lemma probabilityGap_le_one {ξ : ℝ} (hξ : 0< ξ) : probabilityGap ξ≤1 := by
  have hB : 1≤ Central.B ξ := by unfold Central.B;linarith
  unfold probabilityGap γ
  apply (div_le_one (mul_pos hξ (by linarith))).mpr
  nlinarith

theorem canonical_probability_gap {ξ B lam b d : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (_hB : 0< B) (hb : b∈Icc (0:ℝ) B)
    (hd : d∈Icc (0:ℝ) 1) (hlam : (1-ξ)*B+d*ξ*B≤ lam) :
    canonicalProbability ξ lam b≤1-d := by
  have hnonneg : 0≤1-d := by linarith [hd.2]
  by_cases hb0 : b=0
  · simp only [canonicalProbability,hb0,mul_zero,div_zero,probabilityClip]
    norm_num
    exact hd.2
  have hbp : 0< b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
  have hk : 0≤1-ξ+d*ξ := by nlinarith [hd.1]
  have hbb:=mul_le_mul_of_nonneg_left hb.2 hk
  have hl : (1-ξ)*b+d*ξ*b≤ lam := by nlinarith
  have hh : (b-lam)/(ξ*b)≤1-d := (div_le_iff₀ (mul_pos hξ hbp)).mpr (by nlinarith)
  unfold canonicalProbability probabilityClip
  exact (min_le_right _ _).trans (max_le hnonneg hh)

theorem source_canonical_probability_gap {ξ lam b : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (hlam : (1-ξ)*Central.B ξ+2*γ ξ≤ lam) :
    canonicalProbability ξ lam b≤1-probabilityGap ξ := by
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  apply canonical_probability_gap hξ hξ1 hB hb
    ⟨(probabilityGap_pos hξ).le,probabilityGap_le_one hξ⟩
  convert! hlam using 1
  unfold probabilityGap
  field_simp [hξ.ne',hB.ne']

theorem canonical_failure {ξ lam b d : ℝ} (hd : 0≤ d)
    (hq : canonicalProbability ξ lam b≤1-d) :
    d^2≤1-(canonicalCount ξ lam b).success := by
  have hq0 := (canonicalProbability_mem ξ lam b).1
  have hq1 := (canonicalProbability_mem ξ lam b).2
  have he : (canonicalCount ξ lam b).success=
      1-(1-canonicalProbability ξ lam b)^2 := by
    rw [canonicalCount,CountLaw.success,twoCoinCountLaw_expect]
    norm_num [successIndicator]
    ring
  rw [he]
  have hs := pow_le_pow_left₀ hd
    (show d≤1-canonicalProbability ξ lam b by linarith) 2
  nlinarith

def leastFlag (P : ValueParameters) : ℝ := min (baseFlag P false) (baseFlag P true)

lemma leastFlag_pos (P : ValueParameters) : 0< leastFlag P :=
  lt_min (baseFlag_bounds P false).1 (baseFlag_bounds P true).1

lemma leastFlag_le (P : ValueParameters) (reg : Bool) : leastFlag P≤ baseFlag P reg := by
  cases reg
  · exact min_le_left _ _
  · exact min_le_right _ _

def movingCoefficient (P : ValueParameters) (ξ k : ℝ) : ℝ :=
  leastFlag P*k^2*(probabilityGap ξ)^2/(Central.B ξ-1)^2

lemma movingCoefficient_pos (P : ValueParameters) {ξ k : ℝ} (hξ : 0< ξ) (hk : 0< k) :
    0< movingCoefficient P ξ k := by
  have he:=leastFlag_pos P
  have hd:=probabilityGap_pos hξ
  have hB : 0< Central.B ξ-1 := by unfold Central.B;linarith
  unfold movingCoefficient
  positivity

theorem exposure_gap {ξ lam b : ℝ} (hξ : 0< ξ) (hξ1 : ξ≤1)
    (hb : b∈Icc (1:ℝ) (Central.B ξ)) (hlam : (1-ξ)*Central.B ξ+2*γ ξ≤ lam)
    (hlam1 : lam≤1) : exposure ξ lam b≤1-probabilityGap ξ := by
  have hb0 : 0< b := (by norm_num : (0:ℝ)<1).trans_le hb.1
  have hg := source_canonical_probability_gap hξ hξ1 ⟨by linarith [hb.1],hb.2⟩ hlam
  have hq:=exposure_bounds hξ hξ1 hb (by linarith [show 0≤ γ ξ by unfold γ;positivity]) hlam1
  rw [canonicalProbability_positive hξ.ne' hb0.ne',clippedMarginal] at hg
  change (1-lam/b)/ξ∈Icc (0:ℝ) 1 at hq
  simpa only [div_one,probabilityClip_eq hq,exposure] using hg

theorem active_regime_failure (P : ValueParameters) {ξ M W t k b : ℝ}
    (hξ : 0< ξ) (hξ1 : ξ≤1) (ht : 0< t) (hk : 0< k)
    (hb : b∈Icc (1:ℝ) (Central.B ξ-k/t)) (reg : Bool)
    (hlam : (1-ξ)*Central.B ξ+2*γ ξ≤ meanNumerator P ξ M reg/W)
    (hlam1 : meanNumerator P ξ M reg/W≤1) :
    movingCoefficient P ξ k/t^2≤1-(idealRegime P ξ M W b reg).success := by
  have hB : 0< Central.B ξ-1 := by unfold Central.B;linarith
  have hcap : b≤ Central.B ξ := by linarith [hb.2,div_pos hk ht]
  have hq:=exposure_bounds hξ hξ1 ⟨hb.1,hcap⟩
    (by linarith [show 0≤ γ ξ by unfold γ;positivity]) hlam1
  have hg:=exposure_gap hξ hξ1 ⟨hb.1,hcap⟩ hlam hlam1
  have hd:=probabilityGap_pos hξ
  have he:=baseFlag_bounds P reg
  have hmix : leastFlag P*(k/(t*(Central.B ξ-1)))^2≤ mixedProbability P ξ reg b := by
    have hs : k/(t*(Central.B ξ-1))≤(Central.B ξ-b)/(Central.B ξ-1) := by
      rw [←div_div]
      exact div_le_div_of_nonneg_right (by linarith [hb.2]) hB.le
    have hs0 : 0≤ k/(t*(Central.B ξ-1)) := by positivity
    have hs1 : 0≤(Central.B ξ-b)/(Central.B ξ-1) := div_nonneg (by linarith) hB.le
    have hs2 : (k/(t*(Central.B ξ-1)))^2≤((Central.B ξ-b)/(Central.B ξ-1))^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs2 (leastFlag_pos P).le).trans
      (mul_le_mul_of_nonneg_right (leastFlag_le P reg) (sq_nonneg _))
  have hfail : (probabilityGap ξ)^2≤(1-exposure ξ (meanNumerator P ξ M reg/W) b)^2 := by
    exact pow_le_pow_left₀ hd.le (by linarith) 2
  have hreal : 1-(idealRegime P ξ M W b reg).success=
      mixedProbability P ξ reg b*(1-exposure ξ (meanNumerator P ξ M reg/W) b)^2 := by
    rw [idealRegime_eq_activeLaw P hξ ⟨hb.1,hcap⟩ reg hq]
    unfold Counts.activeLaw CountLaw.success
    rw [FiniteLaw.expect_mixture,Counts.pairLaw_expect,FiniteLaw.expect_dirac]
    norm_num [successIndicator]
    ring
  rw [hreal]
  have hh:=mul_le_mul hmix hfail (sq_nonneg _) (mixedProbability_bounds P hξ ⟨hb.1,hcap⟩ reg).1
  convert! hh using 1
  unfold movingCoefficient
  field_simp [ht.ne',hB.ne']

end FCAppendix.Affine.Tail04.CanonicalFailure
