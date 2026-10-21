import FCAppendix.Affine.Tail04.OrderedSourceTerminal

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceTerminalCounts
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity OrderedSourceOriginalCountFamily SourceTailOptimizer
open SourceAnalyticContract OrderedSourceTerminal Counts

variable {S : SourceAnalyticContract.Parameters} (Z : TailFiniteAndLimitOutput S)

abbrev law (v : ℝ) : CountLaw 2 := limitLaw S.P S.ξ S.ξ_pos Z.multipliers v

theorem exposure_bounds (b : Icc (1:ℝ) (Central.B S.ξ)) (reg : Bool) :
    SourceMenuIdentity.exposure S.ξ (if reg then Z.multipliers.2 else Z.multipliers.1) b∈Icc (0:ℝ) 1 := by
  let z:=if reg then Z.multipliers.2 else Z.multipliers.1
  have hz : (1-S.ξ)*Central.B S.ξ< z ∧ z<1-S.ξ/2 := by
    have h:=S.exposure_rectangle Z.multipliers Z.multipliers_mem
    cases reg
    · exact ⟨h.1,h.2.1⟩
    · exact ⟨h.2.2.1,h.2.2.2⟩
  have hb0 : 0<(b:ℝ) := lt_of_lt_of_le (by norm_num) b.2.1
  have hκ : 0<1-S.ξ := by linarith [S.ξ_half]
  have htop : z/(b:ℝ)<1 := (div_lt_one hb0).mpr (by linarith [b.2.1,S.ξ_pos])
  have hbottom : 1-S.ξ< z/(b:ℝ) := by
    apply (lt_div_iff₀ hb0).mpr
    exact (mul_le_mul_of_nonneg_left b.2.2 hκ.le).trans_lt hz.1
  change (1-z/(b:ℝ))/S.ξ∈Icc (0:ℝ) 1
  constructor
  · exact div_nonneg (by linarith) S.ξ_pos.le
  · apply (div_le_one S.ξ_pos).mpr
    linarith

def activeBid (v : ℝ) : Icc (1:ℝ) (Central.B S.ξ) :=
  if v∈S.P.bulkValues then ⟨1,le_rfl,by unfold Central.B;linarith [S.ξ_pos]⟩
  else beta S.P S.ξ S.ξ_pos Z.multipliers v

theorem activeBid_bulk (v : ℝ) (hv : v∈S.P.bulkValues) : (activeBid Z v:ℝ)=1 := by
  simp only [activeBid,if_pos hv,Subtype.coe_mk]

theorem activeBid_tail (v : ℝ) (hv : S.P.M≤ v) :
    activeBid Z v=beta S.P S.ξ S.ξ_pos Z.multipliers v := by
  have hn : v∉S.P.bulkValues := by
    intro h
    linarith [h.2,S.P.active_tail_gap]
  simp only [activeBid,if_neg hn]

theorem tail_response (v : ℝ) (hv : S.P.M≤ v) :
    (activeBid Z v:ℝ)∈Ioo (1:ℝ) (Central.B S.ξ) ∧
      v=ratio S.P S.ξ Z.multipliers (activeBid Z v) ∧
      ∀a : Icc (1:ℝ) (Central.B S.ξ),a≠activeBid Z v→
        menuUtility S.P S.ξ Z.multipliers.1 Z.multipliers.2 v a<
          menuUtility S.P S.ξ Z.multipliers.1 Z.multipliers.2 v (activeBid Z v) := by
  rw [activeBid_tail Z v hv]
  exact beta_spec S.P S.ξ S.ξ_pos (OrderedSourceAnalyticAdapter.Parameters.derivativeGeometry S)
    Z.multipliers Z.multipliers_mem v hv

def sourceSuccess (v : ℝ) : ℝ :=
  if v∈Icc (0:ℝ) S.P.d0 then 0
  else if v∈S.P.partialValues then 1-S.P.theta
  else served S.P S.ξ Z.multipliers.1 Z.multipliers.2 (activeBid Z v)

def sourceDuplicates (v : ℝ) : ℝ :=
  if v∈Icc (0:ℝ) S.P.d0 then 0
  else if v∈S.P.partialValues then 0
  else SourceMenuIdentity.duplicates S.P S.ξ Z.multipliers.1 Z.multipliers.2 (activeBid Z v)

theorem low_law (v : ℝ) (hv : v∈Icc (0:ℝ) S.P.d0) :
    law Z v=FiniteLaw.dirac 0 := by
  simp only [law,limitLaw,if_pos hv]

theorem partial_law (v : ℝ) (hv : v∈S.P.partialValues) :
    law Z v=singletonLaw (1-S.P.theta)
      ⟨by linarith [S.P.theta_small],by linarith [S.P.theta_pos]⟩ := by
  have hn : v∉Icc (0:ℝ) S.P.d0 := by
    intro h
    linarith [h.2,hv.1,S.P.low_partial_gap]
  simp only [law,limitLaw,if_neg hn,if_pos hv]

theorem active_law (v : ℝ) (hL : v∉Icc (0:ℝ) S.P.d0)
    (hP : v∉S.P.partialValues) :
    law Z v=ParametricMenuCount.law S.P S.ξ Z.multipliers (activeBid Z v) := by
  by_cases hB : v∈S.P.bulkValues
  · simp only [law,limitLaw,if_neg hL,if_neg hP,if_pos hB,activeBid,Subtype.coe_mk]
  · simp only [law,limitLaw,if_neg hL,if_neg hP,if_neg hB,activeBid]

theorem statistics (v : ℝ) :
    (law Z v).success=sourceSuccess Z v ∧
      (law Z v).duplicates=sourceDuplicates Z v ∧
      (law Z v).load=sourceSuccess Z v+sourceDuplicates Z v ∧
      (law Z v).mass 0=1-sourceSuccess Z v ∧
      (law Z v).mass 1=sourceSuccess Z v-sourceDuplicates Z v ∧
      (law Z v).mass 2=sourceDuplicates Z v := by
  have hs : (law Z v).success=sourceSuccess Z v ∧
      (law Z v).duplicates=sourceDuplicates Z v := by
    by_cases hL : v∈Icc (0:ℝ) S.P.d0
    · rw [low_law Z v hL]
      simp only [sourceSuccess,sourceDuplicates,if_pos hL]
      norm_num [CountLaw.success,CountLaw.duplicates,CountLaw.load,
        FiniteLaw.expect_dirac,successIndicator]
    · by_cases hP : v∈S.P.partialValues
      · rw [partial_law Z v hP]
        have hp:=singletonLaw_statistics (1-S.P.theta)
          ⟨by linarith [S.P.theta_small],by linarith [S.P.theta_pos]⟩
        simp only [sourceSuccess,sourceDuplicates,if_neg hL,if_pos hP]
        exact ⟨hp.1,hp.2.1⟩
      · rw [active_law Z v hL hP]
        have hp:=ParametricMenuCount.statistics S.P S.ξ S.ξ_pos (activeBid Z v).2
          (exposure_bounds Z (activeBid Z v) false) (exposure_bounds Z (activeBid Z v) true)
        simp only [sourceSuccess,sourceDuplicates,if_neg hL,if_neg hP]
        exact ⟨hp.1,hp.2.1⟩
  have hm:=count_masses (law Z v)
  refine ⟨hs.1,hs.2,?_,?_,?_,?_⟩
  · have hd : (law Z v).load-(law Z v).success=(law Z v).duplicates := rfl
    linarith [hs.1,hs.2]
  · exact hm.1.trans (congrArg (fun z : ℝ=>1-z) hs.1)
  · rw [hm.2.1,hs.1,hs.2]
  · exact hm.2.2.trans hs.2

theorem expect_formula (v : ℝ) (f : Fin 3→ℝ) :
    (law Z v).expect f=(1-sourceSuccess Z v)*f 0+
      (sourceSuccess Z v-sourceDuplicates Z v)*f 1+sourceDuplicates Z v*f 2 := by
  have h:=statistics Z v
  have he : (law Z v).expect f=(law Z v).mass 0*f 0+
      (law Z v).mass 1*f 1+(law Z v).mass 2*f 2 := by
    simp [FiniteLaw.expect,Fin.sum_univ_succ]; ring
  rw [he,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]

theorem count_tests_source (f : Fin 3→ℝ) :
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw (Z.game (Z.subsequence j))
      (Nat.succ_pos (Z.family.rivals (Z.subsequence j))) v).expect f ∂valueLaw S.P) atTop
      (𝓝 (∫v,(1-sourceSuccess Z v)*f 0+
        (sourceSuccess Z v-sourceDuplicates Z v)*f 1+sourceDuplicates Z v*f 2 ∂valueLaw S.P)) := by
  have he : (∫v,(law Z v).expect f ∂valueLaw S.P)=
      ∫v,(1-sourceSuccess Z v)*f 0+
        (sourceSuccess Z v-sourceDuplicates Z v)*f 1+sourceDuplicates Z v*f 2 ∂valueLaw S.P := by
    apply integral_congr_ae
    exact ae_of_all _ (fun v=> expect_formula Z v f)
  rw [←he]
  exact Z.count_tests f

theorem source_load :
    (∫v,sourceSuccess Z v+sourceDuplicates Z v ∂valueLaw S.P)=99/100 := by
  have h : (∫v,sourceSuccess Z v+sourceDuplicates Z v ∂valueLaw S.P)=
      ∫v,(law Z v).load ∂valueLaw S.P := by
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>(statistics Z v).2.2.1.symm)
  exact h.trans Z.limiting_load

end FCAppendix.Affine.Tail04.OrderedSourceTerminalCounts
