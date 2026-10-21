import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.CompactMenuChoice

noncomputable section
namespace FCAppendix.Affine.Tail04.ParametricMenuCount
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues SourceMenuIdentity MenuError Counts

variable (P : ValueParameters) (ξ : ℝ)

def localLaw (lam b : ℝ) (reg : Bool) : CountLaw 2 :=
  FiniteLaw.mixture (clippedCount ξ b lam lam 1) (FiniteLaw.dirac 1)
    (sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) b)
    (sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) b).2.1
    (sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) b).2.2

def law (lam : ℝ×ℝ) (b : ℝ) : CountLaw 2 :=
  regimeLaw P.theta ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
    (localLaw P ξ lam.1 b false) (localLaw P ξ lam.2 b true)

lemma clippedCount_ratio (b n w : ℝ) :
    clippedCount ξ b n n w=clippedCount ξ b (n/w) (n/w) 1 := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [clippedCount_expect,clippedMarginal,div_one]

theorem idealCount_eq (MA WA MR WR b : ℝ) :
    idealCount P ξ MA WA MR WR b=
      law P ξ (SourceMenuError.meanNumerator P ξ MA false/WA,
        SourceMenuError.meanNumerator P ξ MR true/WR) b := by
  unfold idealCount idealRegime law localLaw
  rw [clippedCount_ratio ξ b (SourceMenuError.meanNumerator P ξ MA false) WA,
    clippedCount_ratio ξ b (SourceMenuError.meanNumerator P ξ MR true) WR]

lemma expect_localLaw (lam b : ℝ) (reg : Bool) (f : Fin 3→ℝ) :
    (localLaw P ξ lam b reg).expect f=
      (sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) b:ℝ)*
        coinMoment (probabilityClip (exposure ξ lam b))
          (probabilityClip (exposure ξ lam b)) f+
      (1-(sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) b:ℝ))*f 1 := by
  simp only [localLaw,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac,
    clippedCount_expect,clippedMarginal,div_one,exposure]

lemma expect_law (lam : ℝ×ℝ) (b : ℝ) (f : Fin 3→ℝ) :
    (law P ξ lam b).expect f=
      (1-P.theta)*(localLaw P ξ lam.1 b false).expect f+
        P.theta*(localLaw P ξ lam.2 b true).expect f :=
  regimeLaw_expect _ _ _ _ _

attribute [local irreducible] localLaw law

lemma continuous_expect_localLaw (U : ℝ) (reg : Bool) (f : Fin 3→ℝ) :
    Continuous (fun z : ℝ×Icc (1:ℝ) U=>(localLaw P ξ z.1 z.2 reg).expect f) := by
  simp_rw [expect_localLaw]
  have hq : Continuous (fun z : ℝ×Icc (1:ℝ) U=>
      probabilityClip (exposure ξ z.1 z.2)) := by
    apply continuous_probabilityClip.comp
    unfold exposure
    exact (continuous_const.sub (continuous_fst.div continuous_snd.subtype_val
      (fun z=> by linarith [z.2.2.1]))).div_const ξ
  have he : Continuous (fun z : ℝ×Icc (1:ℝ) U=>
      (sourceProbability (SourceMenuPopulation.baseFlag P reg) (Central.B ξ) z.2:ℝ)) :=
    continuous_probabilityClip.comp
      ((continuous_mixedFlagProbability _ _).comp continuous_snd.subtype_val)
  unfold coinMoment
  fun_prop

lemma continuous_expect_law (U : ℝ) (f : Fin 3→ℝ) :
    Continuous (fun z : (ℝ×ℝ)×Icc (1:ℝ) U=>(law P ξ z.1 z.2).expect f) := by
  simp_rw [expect_law]
  exact (continuous_const.mul ((continuous_expect_localLaw P ξ U false f).comp
    (continuous_fst.fst.prodMk continuous_snd))).add
      (continuous_const.mul ((continuous_expect_localLaw P ξ U true f).comp
        (continuous_fst.snd.prodMk continuous_snd)))

lemma continuous_mass (U : ℝ) (r : Fin 3) :
    Continuous (fun z : (ℝ×ℝ)×Icc (1:ℝ) U=>(law P ξ z.1 z.2).mass r) := by
  simpa only [FiniteLaw.expect_singleton] using
    continuous_expect_law P ξ U (fun q : Fin 3=> if q=r then 1 else 0)

def massMap (U : ℝ) (r : Fin 3) (lam : ℝ×ℝ) : C(Icc (1:ℝ) U,ℝ) :=
  ⟨fun b=>(law P ξ lam b).mass r,
    (continuous_mass P ξ U r).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_massMap (U : ℝ) (r : Fin 3) : Continuous (massMap P ξ U r) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_mass P ξ U r)

def utilityMap (U : ℝ) (v : ℝ) (lam : ℝ×ℝ) : C(Icc (1:ℝ) U,ℝ) :=
  ⟨fun b=>menuUtility P ξ lam.1 lam.2 v b,
    (CompactMenuChoice.continuous_utility P ξ U).comp
      ((continuous_const : Continuous (fun _ : Icc (1:ℝ) U=>(lam,v))).prodMk continuous_id)⟩

lemma continuous_utilityMap (U v : ℝ) : Continuous (utilityMap P ξ U v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (CompactMenuChoice.continuous_utility P ξ U).comp
    ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)

theorem law_eq_twoRegime (hξ : 0< ξ) {lam : ℝ×ℝ} {b : ℝ}
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hA : exposure ξ lam.1 b∈Icc (0:ℝ) 1)
    (hR : exposure ξ lam.2 b∈Icc (0:ℝ) 1) :
    law P ξ lam b=twoRegimeLaw P.theta
      (mixedProbability P ξ false b) (mixedProbability P ξ true b)
      (exposure ξ lam.1 b) (exposure ξ lam.2 b)
      ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
      (mixedProbability_bounds P hξ hb false) (mixedProbability_bounds P hξ hb true) hA hR := by
  have hc (z : ℝ) (hz : exposure ξ z b∈Icc (0:ℝ) 1) :
      clippedCount ξ b z z 1=pairLaw (exposure ξ z b) (exposure ξ z b) hz hz := by
    simpa only [div_one] using (clippedCount_eq_pair (n:=z) (W:=1) (by simpa using hz))
  unfold law localLaw twoRegimeLaw activeLaw
  simp only [hc lam.1 hA,hc lam.2 hR,sourceFlag_eq_mixedProbability P hξ hb false,
    sourceFlag_eq_mixedProbability P hξ hb true]

theorem statistics (hξ : 0< ξ) {lam : ℝ×ℝ} {b : ℝ}
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hA : exposure ξ lam.1 b∈Icc (0:ℝ) 1)
    (hR : exposure ξ lam.2 b∈Icc (0:ℝ) 1) :
    (law P ξ lam b).success=served P ξ lam.1 lam.2 b ∧
      (law P ξ lam b).duplicates=duplicates P ξ lam.1 lam.2 b ∧
      (law P ξ lam b).mass 0=1-served P ξ lam.1 lam.2 b ∧
      (law P ξ lam b).mass 1=served P ξ lam.1 lam.2 b-duplicates P ξ lam.1 lam.2 b ∧
      (law P ξ lam b).mass 2=duplicates P ξ lam.1 lam.2 b := by
  have hs := twoRegimeLaw_statistics P.theta
    (mixedProbability P ξ false b) (mixedProbability P ξ true b)
    (exposure ξ lam.1 b) (exposure ξ lam.2 b)
    ⟨P.theta_pos.le,by linarith [P.theta_small]⟩
    (mixedProbability_bounds P hξ hb false) (mixedProbability_bounds P hξ hb true) hA hR
  rw [←law_eq_twoRegime P ξ hξ hb hA hR] at hs
  have hm := count_masses (law P ξ lam b)
  have hS : (law P ξ lam b).success=served P ξ lam.1 lam.2 b := hs.1
  have hD : (law P ξ lam b).duplicates=duplicates P ξ lam.1 lam.2 b := hs.2.1
  exact ⟨hS,hD,by rw [hm.1,hS],by rw [hm.2.1,hS,hD],
    by rw [hm.2.2,hD]⟩

end FCAppendix.Affine.Tail04.ParametricMenuCount
