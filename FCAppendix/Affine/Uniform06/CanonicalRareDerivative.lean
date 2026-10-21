import FCAppendix.Affine.Uniform06.EqualCanonicalExpected
import FCAppendix.Affine.Uniform06.SharpPureDerivative

noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalRareDerivative

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EqualCanonicalRegularity PureRankCounts

variable {N : ℕ}

theorem equal_duplicate_monotone_nonnegative {ξ x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (ω : Fin N → RowRival)
    (hω : ∀ j,0 ≤ (ω j).2) (hx : 0 ≤ x) (hxy : x ≤ y) :
    equalDuplicate ξ c x ω ≤ equalDuplicate ξ c y ω := by
  have hm := LowBody.positiveMarginal_update_mono hξ hξ1 (rowResidual c 0 ω)
    (rowBids x ω) 0 (fun j _ => rowBids_nonneg x ω hx (fun k _ => hω k) j) hx hxy
  have he (z : ℝ) : Function.update (rowBids x ω) 0 z=rowBids z ω := rowBids_update x z ω
  rw [he x,he y] at hm
  have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids x ω)
  have hq := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids y ω)
  unfold equalDuplicate equalMarginal
  split_ifs
  · nlinarith [hp.1 0,hq.1 0]
  · exact le_rfl

theorem expected_equal_duplicate_monotone_nonnegative {ξ x y : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P]
    (hP : ∀ᵐ ω ∂P,∀ j,0 ≤ (ω j).2) (hx : 0 ≤ x) (hxy : x ≤ y) :
    expectedEqualDuplicate P ξ c x ≤ expectedEqualDuplicate P ξ c y := by
  apply integral_mono_ae (integrable_equalDuplicate hξ hξ1 c x P)
    (integrable_equalDuplicate hξ hξ1 c y P)
  exact hP.mono fun ω hω => equal_duplicate_monotone_nonnegative hξ hξ1 c ω hω hx hxy

theorem derivative_upper_of_forward_increment {f : ℝ → ℝ} {b H A d : ℝ}
    (hd : HasDerivAt f d b) (hbH : b < H)
    (hi : ∀ y,b < y → y < H → f y-f b ≤ A*(y-b)) : d ≤ A := by
  have ht := hd.tendsto_slope.mono_left
    (nhdsWithin_mono b (show Ioi b ⊆ {b}ᶜ from fun _ h => ne_of_gt h))
  apply le_of_tendsto ht
  have hh : ∀ᶠ y in 𝓝[>] b,y < H := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbH)
  filter_upwards [self_mem_nhdsWithin,hh] with y hy hyH
  rw [slope_def_field]
  exact (div_le_iff₀ (sub_pos.mpr hy)).mpr (hi y hy hyH)

theorem source_equal_duplicate_derivative_ae (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G,LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 2 ≤ m) :
    let P := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) (G.map Prod.snd)
    let e := Real.exp ((LowChernoff.thetaQ i:ℝ)*(capacity m:ℝ)-
      (m-1:ℕ)*((LowChernoff.thetaQ i:ℝ)*rho+LowChernoff.rankI0 i+LowChernoff.sourceGap i))
    ∀ᵐ b ∂volume,b ∈ Ioo (0:ℝ) ((501/1000:ℝ)*cutoff i) →
      DifferentiableAt ℝ (expectedEqualDuplicate P (xi i) (capacity m)) b ∧
      0 ≤ deriv (expectedEqualDuplicate P (xi i) (capacity m)) b ∧
      deriv (expectedEqualDuplicate P (xi i) (capacity m)) b ≤ 2*e/(xi i*b) := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI := sourceRivalLaw_probability (cutoff_mem i) Gb
  let P := Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) Gb
  let f := expectedEqualDuplicate P (xi i) (capacity m)
  let F := fun b : ℝ => f (max 0 b)
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hnon : ∀ᵐ ω ∂P,∀ j,0 ≤ (ω j).2 :=
    iid_rows_ae_bid_nonnegative _ (rivalLaw_ae_bid_nonnegative (cutoff i) 0 (1-cutoff i) Gb
      (source_floor_bid_nonnegative i G hfloor))
  have hmono : Monotone F := by
    intro x y hxy
    exact expected_equal_duplicate_monotone_nonnegative (xi_pos i) hξ1 (capacity m)
      P hnon (le_max_left _ _) (max_le_max le_rfl hxy)
  have hinc := (source_equal_duplicate_level_and_increment i G hvalue hfloor hm).2
  filter_upwards [hmono.ae_differentiableAt] with b hd hb
  have heq : F=ᶠ[𝓝 b] f := by
    filter_upwards [Ioi_mem_nhds hb.1] with a ha
    dsimp only [F]
    rw [max_eq_right ha.le]
  have hdF := hd.hasDerivAt
  have hdf : HasDerivAt f (deriv F b) b := hdF.congr_of_eventuallyEq heq.symm
  have hnonneg := SharpPureDerivative.derivative_nonnegative_of_monotone hmono hdF
  have hupper := derivative_upper_of_forward_increment hdf hb.2 (by
    intro y hby hyH
    exact hinc b y hb.1 hby.le hyH.le)
  refine ⟨hdf.differentiableAt,?_,?_⟩
  · rw [hdf.deriv]
    exact hnonneg
  · rw [hdf.deriv]
    convert! hupper using 1
    ring

end FCAppendix.Affine.Uniform06.CanonicalRareDerivative
