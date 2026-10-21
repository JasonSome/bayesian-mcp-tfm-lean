import FCAppendix.Affine.Uniform06.LiteralKernelDecomposition

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralLowDuplicate

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition
open LiteralPrefixStieltjes GuardPrefix SourceGuardGeometry
open PureRankCounts PureDuplicateIntervals PureDuplicateRare EqualCanonicalRegularity
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07

variable {N : ℕ}

theorem row_masked_empty (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) :
    maskedBids (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) ∅=rowBids b ω := by
  funext j
  simp only [maskedBids,Finset.sdiff_empty]
  split_ifs with hj
  · rfl
  · exact (rowBids_outside c b ω j hj).symm

theorem row_complement_eq_equal (ξ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival)
    (he : rowResidual c 0 ω=rowResidual c 1 ω) :
    complementMarginal ξ (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) ∅ 0=
      equalMarginal ξ c b ω := by
  unfold complementMarginal
  rw [row_masked_empty]
  have hsmall : small (patternTemplate c (fun j => (ω j).1))=rowResidual c 0 ω := by
    change min (rowResidual c 0 ω) (rowResidual c 1 ω)=rowResidual c 0 ω
    rw [← he,min_self]
  rw [hsmall]
  rfl

theorem literal_duplicate_eq_pureDuplicate {ι : Type*} [DecidableEq ι]
    (P : Finset ι × Finset ι) (j : ι) : duplicate j P=pureDuplicate P j := by
  simp only [duplicate_eq_indicator,pureDuplicate,Finset.mem_inter]

theorem raw_duplicate_monotone {κ : ℝ} (hκ : 0 < κ) (c : ℕ) (ω : Fin N → RowRival) :
    Monotone (fun b => rowPureDuplicate κ c b ω) := by
  have hh := (pure_first_duplicate_monotone hκ (patternTemplate c (fun j => (ω j).1))
    (rowBids 0 ω) 0).2
  simpa only [rowBids_update,literal_duplicate_eq_pureDuplicate,rowPureDuplicate,rowPureSelection] using hh

theorem row_low_duplicate_increment_le_split
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) (ω : Fin N → RowRival)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ B) :
    (rowLaw ξ κ c g margin y ω).expect (duplicate 0)-
      (rowLaw ξ κ c g margin x ω).expect (duplicate 0) ≤
      rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω+
        (equalDuplicate ξ c y ω-equalDuplicate ξ c x ω) := by
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have hf (b : ℝ) : (rowLaw ξ κ c g margin b ω).expect (duplicate 0)=equalDuplicate ξ c b ω := by
      have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
      simp only [rowLaw,continuationLaw,if_pos heT,empty_completion_duplicate hξ hξ1,
        row_complement_eq_equal ξ c b ω he,equalDuplicate,if_pos he]
    rw [hf x,hf y]
    have hp := raw_duplicate_monotone hκ c ω hxy
    linarith
  · have hf {b : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) :
        (rowLaw ξ κ c g margin b ω).expect (duplicate 0)=rowPureDuplicate κ c b ω := by
      have hh := (unequal_low_full_eq_pure hξ hξ1 hκ1
        {g with countMargin := margin (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
        hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
        hg.rejectionScale_pos hg.lower_pos (rowBids_outside c b ω) 0
        (by simpa only [rowBids,Fin.cons_zero] using hb)
        (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hB)
        (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hg.rejection) he).2
      simpa only [rowLaw,rowPureDuplicate,rowPureSelection,literal_duplicate_eq_pureDuplicate] using hh
    rw [hf hx (hxy.trans hy),hf (hx.trans hxy) hy]
    simp only [equalDuplicate,if_neg he,sub_self,add_zero]
    exact le_rfl

theorem row_low_duplicate_le_split
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B) (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) (ω : Fin N → RowRival)
    {b : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) :
    (rowLaw ξ κ c g margin b ω).expect (duplicate 0) ≤
      rowPureDuplicate κ c b ω+equalDuplicate ξ c b ω := by
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have hf : (rowLaw ξ κ c g margin b ω).expect (duplicate 0)=equalDuplicate ξ c b ω := by
      have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
      simp only [rowLaw,continuationLaw,if_pos heT,empty_completion_duplicate hξ hξ1,
        row_complement_eq_equal ξ c b ω he,equalDuplicate,if_pos he]
    rw [hf]
    linarith [(rowPureDuplicate_bounds κ c b ω).1]
  · have hh := (unequal_low_full_eq_pure hξ hξ1 hκ1
      {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.rejectionScale_pos hg.lower_pos (rowBids_outside c b ω) 0
      (by simpa only [rowBids,Fin.cons_zero] using hb)
      (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hB)
      (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hg.rejection) he).2
    simpa only [rowLaw,rowPureDuplicate,rowPureSelection,literal_duplicate_eq_pureDuplicate,
      equalDuplicate,if_neg he,add_zero] using hh.le

theorem actual_low_duplicate_increment_le_split
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B) (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ B) :
    actualDuplicate t ξ κ G c N g margin y-actualDuplicate t ξ κ G c N g margin x ≤
      expectedPureDuplicate (N := N) t 0 (1-t) κ G c y-
        expectedPureDuplicate (N := N) t 0 (1-t) κ G c x+
      (expectedEqualDuplicate (Measure.pi fun _ : Fin N => sourceRivalLaw t G) ξ c y-
        expectedEqualDuplicate (Measure.pi fun _ : Fin N => sourceRivalLaw t G) ξ c x) := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hxP := integrable_rowPureDuplicate κ c x P
  have hyP := integrable_rowPureDuplicate κ c y P
  have hiPD : Integrable (fun ω => rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω) P := by
    convert! hyP.sub hxP using 1
  have hxE := integrable_equalDuplicate hξ hξ1 c x P
  have hyE := integrable_equalDuplicate hξ hξ1 c y P
  have hiED : Integrable (fun ω => equalDuplicate ξ c y ω-equalDuplicate ξ c x ω) P := by
    convert! hyE.sub hxE using 1
  have hxA := integrable_row_duplicate hξ hξ1 κ c g margin x P
  have hyA := integrable_row_duplicate hξ hξ1 κ c g margin y P
  have hh := integral_mono_ae (hyA.sub hxA) ((hyP.sub hxP).add (hyE.sub hxE))
    (Eventually.of_forall fun ω => row_low_duplicate_increment_le_split hξ hξ1 hκ hκ1
      c g hg hB margin ω hx hxy hy)
  change (∫ ω, (rowLaw ξ κ c g margin y ω).expect (duplicate 0)-
    (rowLaw ξ κ c g margin x ω).expect (duplicate 0) ∂P) ≤
      (∫ ω, (rowPureDuplicate κ c y ω-rowPureDuplicate κ c x ω)+
        (equalDuplicate ξ c y ω-equalDuplicate ξ c x ω) ∂P) at hh
  rw [integral_sub hyA hxA,integral_add hiPD hiED,
    integral_sub hyP hxP,integral_sub hyE hxE] at hh
  exact hh

theorem actual_low_duplicate_le_split
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hκ1 : κ ≤ 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B) (hB : B ≤ g.multiplier-g.radius)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0 ≤ b) (hbB : b ≤ B) :
    actualDuplicate t ξ κ G c N g margin b ≤
      expectedPureDuplicate (N := N) t 0 (1-t) κ G c b+
        expectedEqualDuplicate (Measure.pi fun _ : Fin N => sourceRivalLaw t G) ξ c b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hP := integrable_rowPureDuplicate κ c b P
  have hE := integrable_equalDuplicate hξ hξ1 c b P
  have hA := integrable_row_duplicate hξ hξ1 κ c g margin b P
  have hh := integral_mono_ae hA (hP.add hE)
    (Eventually.of_forall fun ω => row_low_duplicate_le_split hξ hξ1 hκ1 c g hg hB margin ω hb hbB)
  change (∫ ω, (rowLaw ξ κ c g margin b ω).expect (duplicate 0) ∂P) ≤
    (∫ ω, rowPureDuplicate κ c b ω+equalDuplicate ξ c b ω ∂P) at hh
  rw [integral_add hP hE] at hh
  exact hh

def pureRare (m : ℕ) : ℝ := Real.exp (-(9/1000000:ℝ)*m)

def equalRare (i : Row) (m : ℕ) : ℝ :=
  Real.exp ((LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
    (m-1:ℕ)*((LowChernoff.thetaQ i:ℝ)*rho+LowChernoff.rankI0 i+LowChernoff.sourceGap i))

theorem source_actual_duplicate_level_and_interval (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    {m : ℕ} (hm : 4 ≤ m)
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (hBL : B ≤ g.multiplier-g.radius) (hBM : B ≤ RankCutoff.Mstar i)
    (hBhalf : B ≤ (501/1000:ℝ)*cutoff i)
    (margin : (Fin (m-1) → Fin 4) → ℝ) :
    (∀ b : ℝ, 0 < b → b ≤ B → sourceDuplicate i m G g margin b ≤ pureRare m+equalRare i m) ∧
    (∀ x y : ℝ, 0 < x → x < y → y ≤ B →
      sourceDuplicate i m G g margin y-sourceDuplicate i m G g margin x ≤
        (m-1:ℕ)*pureRare m*(cutoff i*(G.map Prod.snd).real (Ioc x y)+
          cutoff i*(G.map Prod.snd).real (Ioc (kappa i*x) (kappa i*y)))+
            (2/(xi i*x))*equalRare i m*(y-x)) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i ≤ 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hE := source_equal_duplicate_level_and_increment i G hvalue hfloor (show 2 ≤ m by omega)
  constructor
  · intro b hb hbB
    have hsplit := actual_low_duplicate_le_split (cutoff_mem i) (xi_pos i) hξ1 hκ1 Gb
      (capacity m) g hg hBL margin hb.le hbB
    have hP := source_pure_duplicate_exponential i G hvalue hfloor hm b hb (hbB.trans hBM)
    exact hsplit.trans (add_le_add hP (hE.1 b hb (hbB.trans hBhalf)))
  · intro x y hx hxy hyB
    have hsplit := actual_low_duplicate_increment_le_split (cutoff_mem i) (xi_pos i) hξ1 hκ hκ1 Gb
      (capacity m) g hg hBL margin hx.le hxy.le hyB
    have hP := source_pure_duplicate_stieltjes_interval i G hvalue hfloor hatom hm x y hx hxy (hyB.trans hBM)
    have hEE := hE.2 x y hx hxy.le (hyB.trans hBhalf)
    have hh := hsplit.trans (add_le_add hP hEE)
    dsimp only [pureRare,equalRare]
    convert! hh using 1
    ring

end FCAppendix.Affine.Uniform06.LiteralLowDuplicate
