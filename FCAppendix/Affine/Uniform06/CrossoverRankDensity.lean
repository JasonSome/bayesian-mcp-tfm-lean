import FCAppendix.Affine.Uniform06.CrossoverRankPreparation
import FCAppendix.Affine.Uniform06.SharpICAbsorption

noncomputable section
namespace FCAppendix.Affine.Uniform06.CrossoverRankDensity

open MeasureTheory Set Filter Topology
open Rank LiteralExperiment LiteralPrefixStieltjes LiteralKernelDecomposition
open LiteralPureComponents LiteralRankIC LowRankMeasures LiteralWeakRent LiteralLowDuplicate
open LiteralSuccessLower SourceRankRates PureRankCounts PureRankProbability PureDuplicateIntervals PureDuplicateRare
open EqualCanonicalRegularity CanonicalPrefixLipschitz CrossoverRankPreparation
open SharpICAbsorption ScaledMeasure
open FCAppendix.Affine.Uniform07

def pivotalCoefficient (i : Row) (m : ℕ) : ℝ := (m:ℝ)*Lm i m/80000
def rentCoefficient (i : Row) (m : ℕ) : ℝ := Lm i m/10
def duplicateCoefficient (m : ℕ) : ℝ := (m-1:ℕ)*pureRare m
def contraction (i : Row) (m : ℕ) : ℝ :=
  8*duplicateCoefficient m/(rentCoefficient i m*pivotalCoefficient i m)
def densityCoefficient (i : Row) (m : ℕ) (g : GuardData) (H : ℝ) : ℝ :=
  48*max 1 (canonicalConstant (xi i) g H)/
    (rentCoefficient i m*pivotalCoefficient i m)

theorem physical_coefficients (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (hrare : pureRare m < (Lm i m)^2/10000000) :
    0 < pivotalCoefficient i m ∧ 0 < rentCoefficient i m ∧
      0 ≤ duplicateCoefficient m ∧ 0 ≤ contraction i m ∧ contraction i m < 1 := by
  have hLm := (Lm_mem_Ioc i hm).1
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hNm : ((m-1:ℕ):ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hE0 : 0 ≤ duplicateCoefficient m := by unfold duplicateCoefficient pureRare; positivity
  have hsmall : 8*duplicateCoefficient m < rentCoefficient i m*pivotalCoefficient i m := by
    have hmul := mul_lt_mul_of_pos_left hrare hm0
    have hN := mul_le_mul_of_nonneg_right hNm (show 0 ≤ pureRare m by unfold pureRare; positivity)
    unfold duplicateCoefficient rentCoefficient pivotalCoefficient
    nlinarith [sq_pos_of_pos hLm]
  have hA : 0 < pivotalCoefficient i m := by unfold pivotalCoefficient; positivity
  have hr : 0 < rentCoefficient i m := by unfold rentCoefficient; positivity
  exact ⟨hA,hr,hE0,by unfold contraction; positivity,
    (div_lt_one (mul_pos hr hA)).mpr hsmall⟩

theorem unequal_duplicate_increment_le_pure {t κ x y : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hκ : 0 < κ) (hxy : x ≤ y)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) :
    expectedUnequalPureDuplicate N c κ t G y-expectedUnequalPureDuplicate N c κ t G x ≤
      expectedPureDuplicate (N := N) t 0 (1-t) κ G c y-
        expectedPureDuplicate (N := N) t 0 (1-t) κ G c x := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hx := integrable_rowUnequalPureDuplicate κ c x P
  have hy := integrable_rowUnequalPureDuplicate κ c y P
  have hpx := integrable_rowPureDuplicate κ c x P
  have hpy := integrable_rowPureDuplicate κ c y P
  have hi := integral_mono_ae (hy.sub hx) (hpy.sub hpx) (Eventually.of_forall fun ω => by
    simp only [Pi.sub_apply,rowUnequalPureDuplicate]
    split_ifs
    · simpa only [sub_self] using sub_nonneg.mpr (raw_duplicate_monotone hκ c ω hxy)
    · rfl)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub hy hx,integral_sub hpy hpx] at hi
  exact hi

theorem source_duplicate_interval (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {H : ℝ} (hg : PrefixConditions (xi i) g H)
    (hHM : H ≤ RankCutoff.Mstar i) (margin : (Fin (m-1) → Fin 4) → ℝ)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hyH : y ≤ H) :
    sourceDuplicate i m G g margin y-sourceDuplicate i m G g margin x ≤
      duplicateCoefficient m*(cutoff i*(G.map Prod.snd).real (Ioc x y)+
        cutoff i*(G.map Prod.snd).real (Ioc (kappa i*x) (kappa i*y)))+
      canonicalConstant (xi i) g H*(y-x)/x := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hraw := source_pure_duplicate_stieltjes_interval i G hvalue hfloor hatom hm
    x y hx hxy (hyH.trans hHM)
  have hmask := unequal_duplicate_increment_le_pure (cutoff_mem i) hκ hxy.le
    (G.map Prod.snd) (m-1) (capacity m)
  have hC := (source_canonical_increments i m G hfloor g hg margin hx hxy.le hyH).2
  have hdx := (source_both_decompositions i m G g hg margin ⟨hx.le,hxy.le.trans hyH⟩).2
  have hdy := (source_both_decompositions i m G g hg margin ⟨(hx.trans hxy).le,hyH⟩).2
  unfold sourcePureDuplicate at hdx hdy
  unfold duplicateCoefficient pureRare
  nlinarith

theorem finite_constant_density
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hatom : ∀ x : ℝ, μ {x}=0)
    (M ell cp s d : ℝ → ℝ) (η κ r A E L H δ : ℝ)
    (hM : Continuous M) (hell : Continuous ell) (hcp : Continuous cp)
    (hs : ContinuousOn s (Ioi 0)) (hd : ContinuousOn d (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ell (M b) < a → a < cp (M b) →
      payoff η (M b) a (s a) (d a) ≤ payoff η (M b) b (s b) (d b))
    (hfloor : ∀ᵐ b ∂μ, ell (M b) ≤ b)
    (hcap : ∀ v b : ℝ, b < v → b ≤ H → b < cp v)
    (hη : η ∈ Icc (0:ℝ) 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hr : 0 < r) (hA : 0 < A) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hsmall : 8*E < r*A) (hH : H ≤ 1) (hδ : 0 < δ)
    (hrent : ∀ b ∈ μ.support, b ∈ Ioc 0 H → r*b ≤ M b-b)
    (hlevel : ∀ b ∈ Ioc 0 H, s b+η*d b ≤ 2)
    (hfirst : ∀ x y : ℝ, 0 < x → x < y → y ≤ H → y-x ≤ δ →
      A*μ.real (Ioc x y) ≤ s y-s x)
    (hdup : ∀ x y : ℝ, 0 < x → x < y → y ≤ H →
      d y-d x ≤ E*(μ.real (Ioc x y)+μ.real (Ioc (κ*x) (κ*y)))+L*(y-x)/x) :
    μ.restrict (Ioc (0:ℝ) H) ≪ volume ∧
      ∀ lo : ℝ, 0 < lo → ∀ T : Set ℝ, MeasurableSet T → T ⊆ Icc lo H →
        μ.real T ≤ (48*max 1 L/(r*A))*(volume.real T/(1-(8*E/(r*A))*κ)+
          (∫ b in T, 1/b)/(1-8*E/(r*A))) := by
  let Q0 := max 1 L
  have hQ0 : 0 < Q0 := zero_lt_one.trans_le (le_max_left _ _)
  let P := Q0/A
  have hP : 0 < P := div_pos hQ0 hA
  have hPA : P*A=Q0 := by dsimp only [P]; field_simp [hA.ne']
  have hscaled : 8*P*E < r*Q0 := by
    calc
      8*P*E = P*(8*E) := by ring
      _ < P*(r*A) := mul_lt_mul_of_pos_left hsmall hP
      _ = r*(P*A) := by ring
      _ = r*Q0 := by rw [hPA]
  have hI := sharp_IC_weighted_Borel μ hatom M ell cp s d (fun _ => Q0) η κ r P 1 Q0 E L H δ
    hM hell hcp hs hd hIC hfloor hcap hη hκ hr hP le_rfl hQ0 hE hL hscaled
    (le_max_right _ _) hH hδ (fun _ _ => le_rfl)
    (by
      intro b hb hbi
      simpa only [one_div_one,min_eq_left (hbi.2.trans hH)] using hrent b hb hbi)
    (by
      intro b hb
      exact (hlevel b hb).trans (by dsimp [Q0]; linarith [le_max_left (1:ℝ) L]))
    (by
      intro x y hx hxy hy hs
      have he : (1/P)*Q0=A := by dsimp [P]; field_simp [hQ0.ne',hA.ne']
      rw [he]
      exact hfirst x y hx hxy hy hs) hdup
  have hBorel : ∀ lo : ℝ, 0 < lo → ∀ T : Set ℝ, MeasurableSet T → T ⊆ Icc lo H →
      μ.real T ≤ (48*max 1 L/(r*A))*(∫ b in T, rentWeight 1 b)+
        (8*E/(r*A))*μ.real (scaledSet κ T) := by
    intro lo hlo T hT hTI
    have hi := hI lo hlo T hT hTI
    convert! hi using 1
    dsimp only [P,Q0]
    field_simp [hA.ne',hr.ne',hQ0.ne']
  have hε : 0 ≤ 8*E/(r*A) := by positivity
  have hε1 : 8*E/(r*A) < 1 := (div_lt_one (mul_pos hr hA)).mpr hsmall
  have hC : 0 ≤ 48*max 1 L/(r*A) := by positivity
  have hi := sharp_IC_integrated_density μ hκ hκ1 hε hε1 hC zero_lt_one hBorel
  simpa only [one_mul] using hi

theorem eventually_source_crossover_rank_density (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
        (min p.1 (ReceiptGap.cap i))) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (H Z K err : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      0 < H → H < Z → Z ≤ K → Z < ReceiptGap.cap i → entry i < K →
      K ≤ entry i+cutoff i/400 → PrefixConditions (xi i) g K →
      extensionEnd i ≤ g.multiplier-g.radius →
      Z+err < ActiveGraphComponent.activeBid i K →
      (∀ᵐ p ∂G, p.1 ∈ Icc K (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ err) →
      (∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
          payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) →
      (bidMeasure i G).restrict (Ioc (0:ℝ) H) ≪ volume ∧
        ∀ lo : ℝ, 0 < lo → ∀ T : Set ℝ, MeasurableSet T → T ⊆ Icc lo H →
          (lowBidMeasure i G H).real T ≤ densityCoefficient i m g H*
            (volume.real T/(1-contraction i m*kappa i)+
              (∫ b in T, 1/b)/(1-contraction i m)) := by
  filter_upwards [eventually_source_rare_small i,source_actual_first_pivotal_interval i,
    eventually_ge_atTop (4:ℕ)] with m hrare hpiv hm
  intro G hG hvalue hmenu hatom g H Z K err margin hH hHZ hZK hZcap hK hKfloor hg hlow hgap hactive hIC
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let μ := lowBidMeasure i G H
  let M := sourceRank (cutoff i) Gb
  let s := S i m G g margin Z
  let d := D i m G g margin Z
  have hp := prepare_source i hm hrare.1 G hvalue hmenu hatom g hH hHZ hZK hK hKfloor
    hg hlow hgap hactive margin hIC
  have hgH := LowRankMeasures.PrefixConditions.mono hg (hHZ.le.trans hZK)
  have hgZ := LowRankMeasures.PrefixConditions.mono hg hZK
  have hKM : K < RankCutoff.Mstar i := by
    change K < (x i+1/200)*cutoff i
    have hKfloor' := hKfloor
    unfold entry at hKfloor'
    linarith [cutoff_pos i]
  have hHM : H ≤ RankCutoff.Mstar i := (hHZ.le.trans hZK).trans hKM.le
  have hH1 : H ≤ 1 := by
    have hh : RankCutoff.Mstar i < 1 := by
      have ht := cutoff_lt_one i
      have hx : 0 < x i+1/200 ∧ x i+1/200 < 1 := by cases i <;> norm_num [x,xQ]
      unfold RankCutoff.Mstar
      nlinarith [cutoff_pos i]
    exact hHM.trans hh.le
  have hf : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2 := hmenu.mono fun _ h => h.1
  have hn : ∀ᵐ p ∂G, 0 ≤ p.2 := by
    filter_upwards [hf] with p hp
    exact (show 0 ≤ LowChernoff.physicalFloor i p.1 by unfold LowChernoff.physicalFloor; positivity).trans hp
  obtain ⟨δ,hδ,hfirstSource⟩ := hpiv G inferInstance hn hatom g H margin hgH
    (fun b hb => (hp.rank_le b (hb.2.trans hHZ.le)).trans hKM.le)
  have hc := physical_coefficients i hm hrare.2
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hκ1 : kappa i ≤ 1 := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hagree {b : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
      sourceSuccess i m G g margin b=s b ∧ sourceDuplicate i m G g margin b=d b :=
    CrossoverRankPreparation.source_extensions_agree i m G g hgZ margin hb (hbH.trans hHZ.le)
  have hfirst : ∀ x y : ℝ, 0 < x → x < y → y ≤ H → y-x ≤ δ →
      pivotalCoefficient i m*μ.real (Ioc x y) ≤ s y-s x := by
    intro x y hx hxy hy hstep
    have hi := hfirstSource x y hx hxy hy hstep
    rw [(hagree (hx.trans hxy) hy).1,(hagree hx (hxy.le.trans hy)).1] at hi
    rw [lowBidMeasure_real_Ioc i G hx.le hy]
    have hQ := unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) Gb y (m-1) (capacity m)
    have hmass : 0 ≤ cutoff i*Gb.real (Ioc x y) :=
      mul_nonneg (cutoff_pos i).le measureReal_nonneg
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hQ (show 0 ≤ (m:ℝ)/80000 by positivity)) hmass
    have he : pivotalCoefficient i m=((m:ℝ)/80000)*Lm i m := by unfold pivotalCoefficient; ring
    rw [he]
    exact hh.trans hi
  have hdup : ∀ x y : ℝ, 0 < x → x < y → y ≤ H →
      d y-d x ≤ duplicateCoefficient m*(μ.real (Ioc x y)+
        μ.real (Ioc (kappa i*x) (kappa i*y)))+canonicalConstant (xi i) g H*(y-x)/x := by
    intro x y hx hxy hy
    have hi := source_duplicate_interval i hm G hvalue hf hatom g hgH hHM margin hx hxy hy
    rw [(hagree (hx.trans hxy) hy).2,(hagree hx (hxy.le.trans hy)).2] at hi
    have hky : kappa i*y ≤ H := (mul_le_of_le_one_left (hx.trans hxy).le hκ1).trans hy
    rw [lowBidMeasure_real_Ioc i G hx.le hy,
      lowBidMeasure_real_Ioc i G (mul_nonneg hκ.le hx.le) hky]
    exact hi
  have hlevel : ∀ b ∈ Ioc 0 H, s b+eta i*d b ≤ 2 := by
    intro b hb
    have hh := source_first_duplicate_bounds i m G g margin b
    rw [← (hagree hb.1 hb.2).1,← (hagree hb.1 hb.2).2]
    have heta : eta i ∈ Icc (0:ℝ) 1 := by cases i <;> norm_num [eta,etaQ]
    have hS := hh.1.2
    have hD := mul_le_mul_of_nonneg_left hh.2.2 heta.1
    nlinarith only [hS,hD,heta.2]
  have hsmall : 8*duplicateCoefficient m < rentCoefficient i m*pivotalCoefficient i m :=
    (div_lt_one (mul_pos hc.2.1 hc.1)).mp hc.2.2.2.2
  have hres := finite_constant_density μ (lowBidMeasure_atomless i G hatom H)
    M (LowChernoff.physicalFloor i) (cap i Z) s d (eta i) (kappa i)
    (rentCoefficient i m) (pivotalCoefficient i m) (duplicateCoefficient m)
    (canonicalConstant (xi i) g H) H δ hp.rank_continuous
    (LowChernoff.continuous_physicalFloor i) (by unfold cap; fun_prop)
    hp.kernel_continuous.1 hp.kernel_continuous.2 hp.rank_IC hp.floor_on_rank
    (fun v b hbv hbH => lt_min (lt_min hbv (hbH.trans_lt (hHZ.trans hZcap))) (hbH.trans_lt hHZ))
    (show eta i ∈ Icc (0:ℝ) 1 by cases i <;> norm_num [eta,etaQ]) hκ hκ1
    hc.2.1 hc.1 hc.2.2.1 (canonicalConstant_pos (xi_pos i) hH.le hgH).le hsmall hH1 hδ
    (fun b hb _ => hp.rent_on_support b hb) hlevel hfirst hdup
  refine ⟨?_,?_⟩
  · simpa only [μ,lowBidMeasure,Measure.restrict_restrict measurableSet_Ioc,inter_self] using hres.1
  · simpa only [densityCoefficient,contraction] using hres.2

end FCAppendix.Affine.Uniform06.CrossoverRankDensity
