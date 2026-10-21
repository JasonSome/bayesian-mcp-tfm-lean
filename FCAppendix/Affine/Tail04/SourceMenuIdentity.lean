import FCAppendix.Affine.Tail04.SourceMenuError
import FCAppendix.Affine.Tail04.CountLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMenuIdentity
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open OriginalValues
open MenuError SourceMenuPopulation SourceMenuError Counts

def exposure (ξ lam b : ℝ) : ℝ := (1-lam/b)/ξ

def mixedProbability (P : ValueParameters) (ξ : ℝ) (reg : Bool) (b : ℝ) : ℝ :=
  baseFlag P reg*((Central.B ξ-b)/(Central.B ξ-1))^2

def served (P : ValueParameters) (ξ lamA lamR b : ℝ) : ℝ :=
  1-((1-P.theta)*mixedProbability P ξ false b*(1-exposure ξ lamA b)^2+
    P.theta*mixedProbability P ξ true b*(1-exposure ξ lamR b)^2)

def duplicates (P : ValueParameters) (ξ lamA lamR b : ℝ) : ℝ :=
  (1-P.theta)*mixedProbability P ξ false b*(exposure ξ lamA b)^2+
    P.theta*mixedProbability P ξ true b*(exposure ξ lamR b)^2

def payment (P : ValueParameters) (ξ lamA lamR b : ℝ) : ℝ :=
  b*(served P ξ lamA lamR b+(1-2*ξ)*duplicates P ξ lamA lamR b)

def menuUtility (P : ValueParameters) (ξ lamA lamR v b : ℝ) : ℝ :=
  v*served P ξ lamA lamR b-payment P ξ lamA lamR b

theorem exposure_bounds {ξ lam b B : ℝ} (hξ : 0< ξ) (hξ1 : ξ≤1)
    (hb : b∈Icc (1:ℝ) B) (hlam0 : (1-ξ)*B≤ lam) (hlam1 : lam≤1) :
    exposure ξ lam b∈Icc (0:ℝ) 1 := by
  have hb0 : 0< b := (by norm_num : (0:ℝ)<1).trans_le hb.1
  have hκ : 0≤1-ξ := by linarith
  have hlb : (1-ξ)*b≤ lam := (mul_le_mul_of_nonneg_left hb.2 hκ).trans hlam0
  have hupper : lam/b≤1 := (div_le_one hb0).mpr (hlam1.trans hb.1)
  have hlower : 1-ξ≤ lam/b := (le_div_iff₀ hb0).mpr hlb
  unfold exposure
  exact ⟨div_nonneg (by linarith) hξ.le,(div_le_one hξ).mpr (by linarith)⟩

theorem mixedProbability_bounds (P : ValueParameters) {ξ b : ℝ}
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ)) (reg : Bool) :
    mixedProbability P ξ reg b∈Icc (0:ℝ) 1 := by
  have he := baseFlag_bounds P reg
  have hB : 1< Central.B ξ := by unfold Central.B;linarith
  exact ⟨mixedFlagProbability_nonneg he.1.le,
    mixedFlagProbability_le_one he.1.le he.2.le hB hb⟩

theorem sourceFlag_eq_mixedProbability (P : ValueParameters) {ξ b : ℝ}
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ)) (reg : Bool) :
    (sourceProbability (baseFlag P reg) (Central.B ξ) b:ℝ)=mixedProbability P ξ reg b := by
  change probabilityClip (mixedProbability P ξ reg b)=_
  exact probabilityClip_eq (mixedProbability_bounds P hξ hb reg)

theorem clippedMarginal_eq_exposure {ξ b n W : ℝ}
    (hq : exposure ξ (n/W) b∈Icc (0:ℝ) 1) :
    clippedMarginal ξ b n W=exposure ξ (n/W) b :=
  probabilityClip_eq hq

theorem clippedCount_eq_pair {ξ b n W : ℝ}
    (hq : exposure ξ (n/W) b∈Icc (0:ℝ) 1) :
    clippedCount ξ b n n W=pairLaw (exposure ξ (n/W) b) (exposure ξ (n/W) b) hq hq := by
  apply FiniteLaw.ext
  intro k
  rw [←FiniteLaw.expect_singleton,←FiniteLaw.expect_singleton,
    clippedCount_expect,pairLaw_expect,clippedMarginal_eq_exposure hq]
  rfl

def idealRegime (P : ValueParameters) (ξ M W b : ℝ) (reg : Bool) : CountLaw 2 :=
  FiniteLaw.mixture (clippedCount ξ b (meanNumerator P ξ M reg) (meanNumerator P ξ M reg) W)
    (FiniteLaw.dirac 1) (sourceProbability (baseFlag P reg) (Central.B ξ) b)
    (sourceProbability (baseFlag P reg) (Central.B ξ) b).2.1
    (sourceProbability (baseFlag P reg) (Central.B ξ) b).2.2

def idealCount (P : ValueParameters) (ξ MA WA MR WR b : ℝ) : CountLaw 2 :=
  regimeLaw P.theta ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
    (idealRegime P ξ MA WA b false) (idealRegime P ξ MR WR b true)

theorem idealRegime_eq_activeLaw (P : ValueParameters) {ξ M W b : ℝ}
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ)) (reg : Bool)
    (hq : exposure ξ (meanNumerator P ξ M reg/W) b∈Icc (0:ℝ) 1) :
    idealRegime P ξ M W b reg=
      activeLaw (mixedProbability P ξ reg b) (exposure ξ (meanNumerator P ξ M reg/W) b)
        (exposure ξ (meanNumerator P ξ M reg/W) b)
        (mixedProbability_bounds P hξ hb reg) hq hq := by
  unfold idealRegime activeLaw
  simp only [clippedCount_eq_pair hq,sourceFlag_eq_mixedProbability P hξ hb reg]

theorem idealCount_eq_twoRegimeLaw (P : ValueParameters) {ξ MA WA MR WR b : ℝ}
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hqA : exposure ξ (meanNumerator P ξ MA false/WA) b∈Icc (0:ℝ) 1)
    (hqR : exposure ξ (meanNumerator P ξ MR true/WR) b∈Icc (0:ℝ) 1) :
    idealCount P ξ MA WA MR WR b=
      twoRegimeLaw P.theta (mixedProbability P ξ false b) (mixedProbability P ξ true b)
        (exposure ξ (meanNumerator P ξ MA false/WA) b) (exposure ξ (meanNumerator P ξ MR true/WR) b)
        ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
        (mixedProbability_bounds P hξ hb false) (mixedProbability_bounds P hξ hb true) hqA hqR := by
  unfold idealCount twoRegimeLaw
  rw [idealRegime_eq_activeLaw P hξ hb false hqA,idealRegime_eq_activeLaw P hξ hb true hqR]

theorem idealCount_statistics (P : ValueParameters) {ξ MA WA MR WR b : ℝ}
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hqA : exposure ξ (meanNumerator P ξ MA false/WA) b∈Icc (0:ℝ) 1)
    (hqR : exposure ξ (meanNumerator P ξ MR true/WR) b∈Icc (0:ℝ) 1) :
    let K := idealCount P ξ MA WA MR WR b
    let lamA := meanNumerator P ξ MA false/WA
    let lamR := meanNumerator P ξ MR true/WR
    K.success=served P ξ lamA lamR b ∧ K.duplicates=duplicates P ξ lamA lamR b ∧
      K.mass 0=1-served P ξ lamA lamR b ∧
      K.mass 1=served P ξ lamA lamR b-duplicates P ξ lamA lamR b ∧
      K.mass 2=duplicates P ξ lamA lamR b := by
  dsimp only
  have he := idealCount_eq_twoRegimeLaw P hξ hb hqA hqR
  have hs := twoRegimeLaw_statistics P.theta (mixedProbability P ξ false b) (mixedProbability P ξ true b)
    (exposure ξ (meanNumerator P ξ MA false/WA) b) (exposure ξ (meanNumerator P ξ MR true/WR) b)
    ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
    (mixedProbability_bounds P hξ hb false) (mixedProbability_bounds P hξ hb true) hqA hqR
  rw [←he] at hs
  have hm := count_masses (idealCount P ξ MA WA MR WR b)
  exact ⟨hs.1,hs.2.1,by rw [hm.1,hs.1]; rfl,
    by rw [hm.2.1,hs.1,hs.2.1]; rfl,by rw [hm.2.2,hs.2.1]; rfl⟩

theorem affineStatistic_expect (K : CountLaw 2) (η v b : ℝ) :
    K.expect (affineStatistic η v b)=v*K.success-b*(K.success+η*K.duplicates) := by
  have hs : K.success=K.mass 1+K.mass 2 := by
    norm_num [CountLaw.success,FiniteLaw.expect,Fin.sum_univ_succ,successIndicator]
  have hm := count_masses K
  norm_num [affineStatistic,FiniteLaw.expect,Fin.sum_univ_succ]
  rw [hs,←hm.2.2]
  ring

theorem idealCount_payoff (P : ValueParameters) {ξ MA WA MR WR b : ℝ} (v : ℝ)
    (hξ : 0< ξ) (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hqA : exposure ξ (meanNumerator P ξ MA false/WA) b∈Icc (0:ℝ) 1)
    (hqR : exposure ξ (meanNumerator P ξ MR true/WR) b∈Icc (0:ℝ) 1) :
    (idealCount P ξ MA WA MR WR b).expect (affineStatistic (1-2*ξ) v b)=
      menuUtility P ξ (meanNumerator P ξ MA false/WA) (meanNumerator P ξ MR true/WR) v b := by
  have hs := idealCount_statistics P hξ hb hqA hqR
  rw [affineStatistic_expect,hs.1,hs.2.1]
  rfl

end FCAppendix.Affine.Tail04.SourceMenuIdentity
