import FCAppendix.Affine.Uniform06.SourceValueEnvelope
import FCAppendix.Affine.Uniform06.LowSuccessComparison

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowInactiveIdentity

open MeasureTheory Set Filter Topology LowBody
open Rank LiteralRankIC LiteralPrefixStieltjes LiteralExperiment
open LiteralKernelDecomposition LiteralLowDuplicate LiteralWeakRent LiteralSuccessLower
open LowSuccessComparison LowRankMeasures SourceRankRates PureRankCounts
open PureRankProbability PurePivotalSource EqualCanonicalRegularity SourceValueEnvelope
open FCAppendix.Affine.Uniform07

def rankRareFactor (i : Row) (m : ℕ) : ℝ :=
  Real.exp (-(6/1000000:ℝ)*(m:ℝ))+
    Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)

def lowInactiveError (i : Row) (m : ℕ) : ℝ :=
  80000/(m:ℝ)+4*cutoff i*rankRareFactor i m

theorem rankRareFactor_nonnegative (i : Row) (m : ℕ) : 0 ≤ rankRareFactor i m := by
  unfold rankRareFactor
  positivity

theorem lowInactiveError_tendsto_zero (i : Row) :
    Tendsto (lowInactiveError i) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun m : ℕ => (80000:ℝ)/(m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hP := tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 6/1000000) 0
  have hE := tendsto_exp_affine_nat (equalRelativeGap_pos i) (equalRateConstant i)
  have hR : Tendsto (rankRareFactor i) atTop (𝓝 0) := by
    convert! hP.add hE using 1
    · funext m
      dsimp only [rankRareFactor]
      congr 1
      ring
    · simp
  simpa only [lowInactiveError,mul_zero,add_zero] using! hdiv.add (hR.const_mul (4*cutoff i))

theorem eventually_rare_le_rank_factor (i : Row) :
    ∀ᶠ m : ℕ in atTop, 0 < Lm i m ∧
      pureRare m+equalRare i m ≤ rankRareFactor i m*Lm i m := by
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (2:ℕ)] with m hL hm
  have hL0 := (Real.exp_pos _).trans_le hL
  have hP : pureRare m ≤ Real.exp (-(6/1000000:ℝ)*(m:ℝ))*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hL
      (Real.exp_pos (-(6/1000000:ℝ)*(m:ℝ))).le
    convert! hh using 1
    unfold pureRare
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : equalRare i m ≤
      Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*Lm i m := by
    have hh := mul_le_mul_of_nonneg_left hL
      (Real.exp_pos (equalRateConstant i-(m:ℝ)*equalRelativeGap i)).le
    have he : Real.exp (equalRateConstant i-(m:ℝ)*equalRelativeGap i)*
        Real.exp (-(m:ℝ)*(3/1000000))=
          Real.exp (equalRateConstant i-(m:ℝ)*LowChernoff.sourceGap i) := by
      rw [← Real.exp_add]
      congr 1
      unfold equalRelativeGap
      ring
    rw [he] at hh
    exact (Real.exp_le_exp.mpr (source_equal_exponent_upper i (by omega))).trans hh
  refine ⟨hL0,?_⟩
  unfold rankRareFactor
  nlinarith

theorem source_low_canonical_first_le_equalRare (i : Row) {m : ℕ} (hm : 2 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (hBL : B ≤ g.multiplier-g.radius) (hBZ : B ≤ extensionEnd i)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B) :
    canonicalFirst i m G g margin b ≤ equalRare i m := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hs := actual_low_first_le_rank_and_equal_tail (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show 0 < extensionEnd i by unfold extensionEnd; exact mul_pos (by norm_num) (cutoff_pos i))
    (G.map Prod.snd) (capacity m) g hg hBL hBZ margin hb hbB
  have he := source_equal_tail_chernoff i G hvalue hfloor hm
  have hd := source_first_decomposition i m G g hg margin ⟨hb.le,hbB⟩
  change sourceSuccess i m G g margin b ≤
    expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b+_ at hs
  have hu := hs.trans (add_le_add le_rfl he)
  unfold canonicalFirst
  change sourceSuccess i m G g margin b ≤
    expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b+
      equalRare i m at hu
  nlinarith

theorem eventually_source_low_used_bid_error (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (K U : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      0 ≤ U → PrefixConditions (xi i) g K → extensionEnd i ≤ g.multiplier-g.radius →
      (∀ᵐ p ∂G, p ∈ usedSet i m G g margin U) →
      ∀ p ∈ usedSet i m G g margin U, p.1 < K → p.1 ≤ entry i → p.2 ≤ lowEnd i →
        0 ≤ p.1-p.2 ∧ p.1-p.2 ≤ lowInactiveError i m := by
  filter_upwards [eventually_source_low_success_comparable i,eventually_rare_le_rank_factor i,
    eventually_ge_atTop (4:ℕ)] with m hcomp hrare hm
  intro G hG hvalue hatom g K U margin hU hg hZL hcommon p hp hpK hpe hpH
  letI := hG
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hf : ∀ᵐ q ∂G, LowChernoff.physicalFloor i q.1 ≤ q.2 :=
    hcommon.mono fun _ hq => hq.2.2.1.1
  have hentryM : entry i < RankCutoff.Mstar i := by
    have ht := cutoff_pos i
    unfold entry RankCutoff.Mstar
    nlinarith
  have hpM := hpe.trans hentryM.le
  have hpbv : p.2 ≤ p.1 := hp.2.2.1.2.trans (min_le_left _ _)
  have hrent : 0 ≤ p.1-p.2 := sub_nonneg.mpr hpbv
  have hpbK : p.2 ≤ K := hpbv.trans hpK.le
  have hpbZ : p.2 ≤ extensionEnd i := hpH.trans (lowEnd_bounds i).2.1.le
  have hgp := LowRankMeasures.PrefixConditions.mono hg hpbK
  have hrank := source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin U hcommon p hp hpK
  let Q := pureRank (m-1) (capacity m) ((1+cutoff i)/2) p.1
  have hLQ : Lm i m ≤ Q := by
    have hh := unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i)
      (G.map Prod.snd) p.2 (m-1) (capacity m)
    rwa [hrank] at hh
  have hQ : 0 < Q := hrare.1.trans_le hLQ
  have hS := (hcomp G hG hvalue hf hatom g p.2 margin hgp
    (hpbZ.trans hZL) hpbZ p.2 hp.2.1 le_rfl (by rw [hrank]; exact hpM)).1
  rw [hrank] at hS
  change Q/2 ≤ sourceSuccess i m G g margin p.2 at hS
  have hD := (source_actual_duplicate_level_and_interval i G hvalue hf hatom hm g hgp
    (hpbZ.trans hZL) (hpbv.trans hpM) hpbZ margin).1 p.2 hp.2.1 le_rfl
  have hC := source_low_canonical_first_le_equalRare i (show 2 ≤ m by omega) G hvalue hf
    g hgp (hpbZ.trans hZL) hpbZ margin hp.2.1 le_rfl
  have hE := actual_envelope_on_usedSet i hm G hvalue hatom g hU hg margin hcommon
    p hp hpK hpe hpM
  change payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2)
    (sourceDuplicate i m G g margin p.2) ≤
      (40000/(m:ℝ))*Q+p.1*pureRare m+p.1*canonicalFirst i m G g margin p.2 at hE
  let R := pureRare m+equalRare i m
  have hR : 0 ≤ R := by dsimp [R,pureRare,equalRare]; positivity
  have hRbound : R ≤ rankRareFactor i m*Q :=
    hrare.2.trans (mul_le_mul_of_nonneg_left hLQ (rankRareFactor_nonnegative i m))
  have hη : eta i ∈ Icc (0:ℝ) 1 := by cases i <;> norm_num [eta,etaQ]
  have hηb : eta i*p.2 ≤ cutoff i := by
    have hh := mul_le_mul_of_nonneg_right hη.2 hp.2.1.le
    linarith [hp.1.2]
  have hcost := mul_le_mul_of_nonneg_left hD (mul_nonneg hη.1 hp.2.1.le)
  have hcostbound := mul_le_mul_of_nonneg_right hηb hR
  have hCbound := mul_le_mul_of_nonneg_left hC hp.1.1
  have hvR := mul_le_mul_of_nonneg_right hp.1.2 hR
  have hfirst := mul_le_mul_of_nonneg_left hS hrent
  have hRR := mul_le_mul_of_nonneg_left hRbound (show 0 ≤ 2*cutoff i by exact mul_nonneg (by norm_num) (cutoff_pos i).le)
  refine ⟨hrent,?_⟩
  apply (mul_le_mul_iff_left₀ hQ).mp
  have hcoef : (80000:ℝ)/(m:ℝ)=2*((40000:ℝ)/(m:ℝ)) := by ring
  dsimp only [lowInactiveError]
  rw [hcoef]
  dsimp only [payoff] at hE
  dsimp only [R] at hcostbound hvR hRR
  nlinarith

theorem eventually_source_low_common_conull_error (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (K : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g K → extensionEnd i ≤ g.multiplier-g.radius →
      (∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i))) →
      (∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1) (min p.1 (ReceiptGap.cap i)),
        payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
          payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2) (sourceDuplicate i m G g margin p.2)) →
      ∀ᵐ p ∂G, p.1 < K → p.1 ≤ entry i → p.2 ≤ lowEnd i →
        |p.2-p.1| ≤ lowInactiveError i m := by
  filter_upwards [eventually_source_low_used_bid_error i] with m hsource
  intro G hG hvalue hatom g K margin hg hZL hmenu hIC
  letI := hG
  have hc := usedSet_full i m G hvalue hatom g margin (ReceiptGap.cap i) hmenu hIC
  have hh := hsource G hG hvalue hatom g K (ReceiptGap.cap i) margin
    (ReceiptGap.cap_bounds i).1.le hg hZL hc
  filter_upwards [hc] with p hp hpK hpe hpH
  have he := hh p hp hpK hpe hpH
  rw [abs_of_nonpos (by linarith [he.1] : p.2-p.1 ≤ 0)]
  linarith [he.2]

end FCAppendix.Affine.Uniform06.LowInactiveIdentity
