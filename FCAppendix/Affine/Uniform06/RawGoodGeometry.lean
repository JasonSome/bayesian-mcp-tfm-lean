import FCAppendix.Affine.Uniform06.RawDeficitGeometry
import FCAppendix.Affine.Uniform06.LiteralCoarseMeasurable
import FCAppendix.Affine.Uniform06.TiltedGood

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawGoodGeometry

open MeasureTheory Set LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open Uniform07 LiteralExperiment LiteralCoarsePath RawMixedSource RawTiltedSource
open RawDeficitGeometry CanonicalCoarse ReciprocalSecantBounds

variable {N : ℕ}

def stripRivals (lo U : ℝ) (ω : Fin N → RowRival) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun j => ω j ∈ CostAmplification.activeStrip lo U)

def stripSet (lo U : ℝ) (ω : Fin N → RowRival) : Finset (Fin (N+1)) :=
  (stripRivals lo U ω).image Fin.succ

theorem stripSet_card (lo U : ℝ) (ω : Fin N → RowRival) :
    ((stripSet lo U ω).card : ℝ)=∑ j,TiltedGood.stripTest lo U (ω j) := by
  classical
  rw [stripSet,Finset.card_image_of_injective _ (Fin.succ_injective N)]
  simp [stripRivals,TiltedGood.stripTest,Set.indicator_apply]

theorem stripSet_bids {b lo U : ℝ} (hbl : b < lo) (ω : Fin N → RowRival) :
    ∀ k ∈ stripSet lo U ω,b < rowBids b ω k ∧ rowBids b ω k ≤ U := by
  classical
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
  have hr : ω j ∈ CostAmplification.activeStrip lo U := (Finset.mem_filter.mp (show j ∈ Finset.univ.filter (fun k => ω k ∈ CostAmplification.activeStrip lo U) from hj)).2
  simp only [rowBids,Fin.cons_succ,if_pos hr.1]
  exact ⟨hbl.trans hr.2.1,hr.2.2⟩

theorem scaled_empirical_error {N : ℕ} (hN : 0 < N) {a p ε : ℝ}
    (h : |a/(N:ℝ)-p| < ε) : |a-(N:ℝ)*p| < ε*(N:ℝ) := by
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have he : a/(N:ℝ)-p=(a-(N:ℝ)*p)/(N:ℝ) := by field_simp [hn.ne']
  rw [he,abs_div,abs_of_pos hn] at h
  exact (div_lt_iff₀ hn).mp h

theorem sum_tag_eq_count (k : Fin 4) (ω : Fin N → RowRival) :
    (∑ j,RivalGood.tag k (ω j))=(classCount k ω : ℝ) := by
  simp [RivalGood.tag,classCount]

theorem source_count_errors (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ lo U : ℝ) {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (ω : Fin N → RowRival)
    (hg : ω ∈ RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics lo U) N ε) :
    |(classCount 0 ω : ℝ)-(N:ℝ)*TiltedGood.lowerProbability i G b θ| < ε*(N:ℝ) ∧
    |(classCount 2 ω : ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ| < ε*(N:ℝ) ∧
    |(classCount 3 ω : ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ| < ε*(N:ℝ) ∧
    |((stripSet lo U ω).card : ℝ)-(N:ℝ)*
      (TiltedGood.law i G b θ).real (CostAmplification.activeStrip lo U)| < ε*(N:ℝ) := by
  letI := TiltedGood.law_probability i G hb θ
  have hpop := (TiltedGood.tilted_population_identities i G hb θ).1
  have hh (k : Fin 4) := scaled_empirical_error hN (hg k)
  refine ⟨?_,?_,?_,?_⟩
  · simpa [RivalGood.empirical,TiltedGood.statistics,sum_tag_eq_count,
      TiltedGood.lowerProbability] using hh 0
  · simpa [RivalGood.empirical,TiltedGood.statistics,sum_tag_eq_count,
      TiltedGood.upperProbability] using hh 1
  · simpa [RivalGood.empirical,TiltedGood.statistics,sum_tag_eq_count,hpop,
      TiltedGood.upperProbability] using hh 2
  · simpa [RivalGood.empirical,TiltedGood.statistics,← stripSet_card,
      TiltedGood.integral_stripTest] using hh 3

theorem source_good_geometry (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b : ℝ} (hb : 0 < b) (θ lo U : ℝ) {N c : ℕ} (hN : 0 < N)
    {ε q : ℝ} (_hε : 0 ≤ ε) (_hq : 0 < q)
    (hfloor : |(c:ℝ)-(N:ℝ)*rho| ≤ 1)
    (hpos : ε*(N:ℝ)+2 < (N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3 ≤ (N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hstrip : q ≤ (TiltedGood.law i G b θ).real (CostAmplification.activeStrip lo U))
    (hεq : 12*ε ≤ q) (hNq : 4 ≤ q*(N:ℝ))
    (ω : Fin N → RowRival) (hno : ∀ j,(ω j).1 ≠ 1)
    (hg : ω ∈ RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics lo U) N ε) :
    let T := patternTemplate c (fun j => (ω j).1)
    (T.residual₀=c-classCount 2 ω ∧ T.residual₁=c-classCount 3 ω) ∧
    balancedTemplateDeficit (xi i) T (rowBids b ω) 0=deficit i b c ω ∧
    imbalance T=(imbalanceSum ω).natAbs ∧
    q*(N:ℝ)/2 ≤ ((stripSet lo U ω).card : ℝ)-(imbalance T : ℝ)-1 := by
  dsimp only
  have hc1 : classCount 1 ω=0 := by simp [classCount,hno]
  have he := source_count_errors i G hb θ lo U hN ω hg
  have hlow : |((1+classCount 0 ω:ℕ):ℝ)-(N:ℝ)*TiltedGood.lowerProbability i G b θ| ≤
      ε*(N:ℝ)+1 := by
    have ht := abs_add_le ((classCount 0 ω : ℝ)-(N:ℝ)*TiltedGood.lowerProbability i G b θ) 1
    push_cast
    have heq : (1:ℝ)+classCount 0 ω-(N:ℝ)*TiltedGood.lowerProbability i G b θ=
      ((classCount 0 ω : ℝ)-(N:ℝ)*TiltedGood.lowerProbability i G b θ)+1 := by ring
    rw [heq]
    norm_num only [abs_one] at ht
    linarith [he.1]
  have hr0 := RivalGood.residual_of_counts hfloor hlow
    (he.2.1.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith : ε*(N:ℝ)+1+1 < (N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (by linarith : 2*(ε*(N:ℝ)+1)+1 ≤ (N:ℝ)*
      (TiltedGood.lowerProbability i G b θ-(rho-TiltedGood.upperProbability i G b θ)))
  have hr1 := RivalGood.residual_of_counts hfloor hlow
    (he.2.2.1.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith : ε*(N:ℝ)+1+1 < (N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (by linarith : 2*(ε*(N:ℝ)+1)+1 ≤ (N:ℝ)*
      (TiltedGood.lowerProbability i G b θ-(rho-TiltedGood.upperProbability i G b θ)))
  have hroom0 : c-classCount 1 ω-classCount 2 ω ≤ 1+classCount 0 ω := by
    simpa only [hc1,Nat.sub_zero] using (min_eq_right_iff.mp hr0.1)
  have hroom1 : c-classCount 1 ω-classCount 3 ω ≤ 1+classCount 0 ω := by
    simpa only [hc1,Nat.sub_zero] using (min_eq_right_iff.mp hr1.1)
  have hcap0 : classCount 1 ω+classCount 2 ω ≤ c := by simpa only [hc1,zero_add] using hr0.2.1.le
  have hcap1 : classCount 1 ω+classCount 3 ω ≤ c := by simpa only [hc1,zero_add] using hr1.2.1.le
  have hr := residuals_unclamped c ω hroom0 hroom1
  have hd := template_imbalance_eq_draws c ω hcap0 hcap1 hroom0 hroom1
  refine ⟨by simpa only [hc1,Nat.sub_zero] using hr,
    template_deficit_eq_raw i c hb ω hcap0 hcap1 hroom0 hroom1,
    hd.trans (draws_eq_natAbs ω),?_⟩
  have hdb : (draws ω:ℝ) ≤ 2*ε*(N:ℝ) := by
    rw [draws_eq_abs,sign_count]
    have ht := abs_sub
      ((classCount 2 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)
      ((classCount 3 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)
    have heq : (classCount 2 ω:ℝ)-classCount 3 ω=
      ((classCount 2 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ)-
      ((classCount 3 ω:ℝ)-(N:ℝ)*TiltedGood.upperProbability i G b θ) := by ring
    rw [heq]
    linarith [he.2.1,he.2.2.1]
  have hslower : q*(N:ℝ)-ε*(N:ℝ) ≤ ((stripSet lo U ω).card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hstrip (Nat.cast_nonneg N)
    linarith [(abs_lt.mp he.2.2.2).1]
  rw [hd]
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hεqn := mul_le_mul_of_nonneg_right hεq hn
  nlinarith

section WindowLower

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem equal_window_lower_from_strip {ξ lo U q : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo) (hU : 0 < U) (hq : 0 < q)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (S : Finset ι) (j : ι)
    (hequal : T.residual₀=T.residual₁)
    (_hjT : j ∈ T.support) (hlb : lo < B j)
    (hBU : ∀ k,B k ≤ U) (hout : ∀ k,k ∉ T.support → B k=0)
    (hguard : (1-ξ)*U ≤ lo)
    (hS : ∀ k ∈ S,B j < B k ∧ B k ≤ U)
    (hcount : q ≤ (S.card:ℝ)-1)
    (hW : balancedTemplateDeficit ξ T B j ∈ Icc (1:ℝ) 2)
    (hwindow : 2/((B j-lo)*q/(ξ*U)) < (B j-lo)/(ξ*B j)) :
    1/(1+B j*(Fintype.card ι:ℝ)/lo) ≤ numericMarginal ξ g T B j := by
  have hb : 0 < B j := hlo.trans hlb
  have hmask : maskedBids T B ∅=B := by
    funext k
    by_cases hk : k ∈ T.support
    · simp [maskedBids,hk]
    · simp [maskedBids,hk,hout k hk]
  have hd0 : imbalance T=0 := by simp [imbalance,small,hequal]
  have hD : (small T:ℝ)-remainingDemand ξ B {j} (B j) ∈ Icc (1:ℝ) 2 := by
    simpa only [balancedTemplateDeficit,hd0,Nat.cast_zero,zero_div,add_zero] using hW
  have hR0 := reciprocalSum_active_strip_lower B {j} S hb hU hS
  have hR : q/U ≤ reciprocalSum B {j} (B j) :=
    (div_le_div_of_nonneg_right (by simpa using hcount) hU.le).trans
      (by simpa using hR0)
  have hRp : 0 < reciprocalSum B {j} (B j) := (div_pos hq hU).trans_le hR
  have hA : 0 < (B j-lo)*q/(ξ*U) := by positivity
  have hg : (B j-lo)*q/(ξ*U) ≤ gain ξ lo (B j) (reciprocalSum B {j} (B j)) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hR (sub_pos.mpr hlb).le) hξ.le
    convert! hh using 1
    ring
  have hsmall : 2/gain ξ lo (B j) (reciprocalSum B {j} (B j)) < (B j-lo)/(ξ*B j) :=
    (div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2:ℝ)) hA hg).trans_lt hwindow
  have hh := actual_marginal_lower_on_window hξ hξ1 hlo (small T) B j hlb hBU hguard hRp
    (lt_of_lt_of_le (by norm_num : 0 < (1:ℝ)) hD.1) hD.2 hsmall
  rw [numericMarginal,if_pos hequal,complementMarginal,hmask]
  have hden : 0 < 1+B j*(Fintype.card ι:ℝ)/lo := by positivity
  exact (div_le_div_of_nonneg_right hD.1 hden.le).trans hh

end WindowLower
end FCAppendix.Affine.Uniform06.RawGoodGeometry
