import FCAppendix.Affine.Uniform06.PreciseRootGood
import FCAppendix.Affine.Uniform06.ClampedMomentBounds
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralBadCountTransfer

open MeasureTheory Set Filter LowBody
open scoped BigOperators Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open RawMomentPartition RawPathAdapter PreciseRootGood RareEmpiricalReplacement
open ClampedMomentBounds

def countMargins (i : Row) (G : Measure (ℝ × ℝ)) (N c : ℕ)
    (b θ ε : ℝ) : Prop :=
  |(c:ℝ)-(N:ℝ)*rho|≤1 ∧
    ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ) ∧
    2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ))

theorem original_literal_cell_replacement (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (N c : ℕ → ℕ) [∀ n,Nonempty (Fin (N n))]
    (hN : Tendsto N atTop atTop) (hNpos : ∀ n,0< N n)
    (b θ τ : ℕ → ℝ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (N n) → Fin 4) → ℝ)
    (hb : ∀ n,0< b n) (hbL : ∀ n,b n≤(g n).multiplier)
    (hτ : ∀ n,0≤τ n) (hc : ∀ n,(c n:ℝ)≤ N n)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    (hh : ∀ n,∀ᵐ x ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n),
      0≤ rawH (xi i) (b n) x)
    {ε : ℝ} (hε : 0<ε) (s U : ℝ)
    (hfinite : ∀ᶠ n in atTop,countMargins i (G n:Measure (ℝ × ℝ))
      (N n) (c n) (b n) (θ n) ε) (q j : ℕ) :
    Tendsto (fun n => (N n:ℝ)*∫ ω : Fin (N n) → RowRival,
      ((imbalanceSum ω).natAbs:ℝ)^j*
        |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
          cellSum i (c n) (g n) (cm n) (b n) (τ n) q ω|
        ∂Measure.pi (fun _ : Fin (N n) =>
          tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))) atTop (𝓝 0) := by
  let μ := fun n => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  letI : ∀ n,IsProbabilityMeasure (μ n) := fun n => tiltedSource_probability i _ (hb n) _
  let P := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let good := fun n => RivalGood.good (μ n) (TiltedGood.statistics s U) (N n) ε
  let F := fun n => fun ω : Fin (N n) → RowRival =>
    ((imbalanceSum ω).natAbs:ℝ)^j*
      |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
        cellSum i (c n) (g n) (cm n) (b n) (τ n) q ω|
  have hF (n : ℕ) : Measurable (F n) := by
    have hk : Measurable (fun ω : Fin (N n) → RowRival =>
        ((imbalanceSum ω).natAbs:ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z.natAbs:ℝ))).comp
        RawTiltedSource.measurable_imbalanceSum
    apply (hk.pow_const j).mul
      (((measurable_literalMoment i _ _ _ _ _ _).sub
        (measurable_cellSum i _ _ _ _ _ _)).abs)
  have hrow (n : ℕ) : ∀ᵐ ω ∂P n,
      (∀ k,0≤ rawH (xi i) (b n) (ω k)) ∧ (∀ k,(ω k).1≠1) := by
    have hn := (hh n).and (TiltedGood.tilted_no_active_tag i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    have hc' (k : Fin (N n)) :=
      (measurePreserving_eval (fun _ : Fin (N n) => μ n) k).quasiMeasurePreserving.ae hn
    filter_upwards [ae_all_iff.mpr hc'] with ω hω
    exact ⟨fun k => (hω k).1,fun k => (hω k).2⟩
  have hFb (n : ℕ) : ∀ᵐ ω ∂P n,0≤ F n ω ∧ F n ω≤2*(N n:ℝ)^(q+j) := by
    filter_upwards [hrow n] with ω hω
    have h1 := literalMoment_polynomial i (c n) (g n) (cm n) (hb n) (hbL n)
      (hτ n) q (hc n) (hg n).1 (hg n).2.1 (hg n).2.2 ω hω.1
    have h2 := cellSum_polynomial i (c n) (g n) (cm n) (hb n) (hτ n)
      q (hNpos n) (hc n) ω hω.1
    have hk : ((imbalanceSum ω).natAbs:ℝ)≤(N n:ℝ) := by
      exact_mod_cast (show (imbalanceSum ω).natAbs≤ N n by
        rw [← RawTiltedSource.draws_eq_natAbs]
        exact RawMixedSource.draws_le ω)
    have hj := pow_le_pow_left₀ (Nat.cast_nonneg (imbalanceSum ω).natAbs) hk j
    have hd : |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
        cellSum i (c n) (g n) (cm n) (b n) (τ n) q ω|≤2*(N n:ℝ)^q := by
      exact (abs_sub _ _).trans (by
        rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]
        linarith [h1.2,h2.2])
    refine ⟨by dsimp [F]; positivity,?_⟩
    have hh' := mul_le_mul hj hd (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) j)
    dsimp only [F]
    convert! hh' using 1
    rw [pow_add]
    ring
  have hbad : ∀ᶠ n in atTop,(P n).real (good n)ᶜ≤8*Real.exp (-(2*ε^2)*(N n:ℝ)) := by
    apply Eventually.of_forall
    intro n
    have h := TiltedGood.source_good_complement i (G n:Measure (ℝ × ℝ))
      (hb n) (θ n) s U (hNpos n) hε.le
    convert! h using 1
    ring
  have ht := rare_bad_event_replacement μ N hN F hF (fun n => (good n)ᶜ)
    (fun n => (RivalGood.measurable_good _ _ (TiltedGood.statistics_measurable s U) _ _).compl)
    (q+j) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤8)
    (by positivity : 0<2*ε^2) hFb hbad
  apply ht.congr'
  filter_upwards [hfinite] with n hn
  apply congrArg ((N n:ℝ)*·)
  apply integral_congr_ae
  filter_upwards [hrow n] with ω hω
  by_cases hgood : ω ∈ good n
  · have hv := source_valid_counts i (G n:Measure (ℝ × ℝ)) (hb n) (hNpos n)
      hn.1 hn.2.1 hn.2.2 ω hω.2 hgood
    have he := literalMoment_eq_cellSum i (c n) (g n) (cm n) (hb n) (hbL n)
      (τ n) q (hg n).1 (hg n).2.1 (hg n).2.2 ω hv
    simp only [indicator_of_notMem (show ω ∉ (good n)ᶜ from by
        simpa only [Set.mem_compl_iff,not_not] using hgood),F,he,
      sub_self,abs_zero,mul_zero]
  · exact indicator_of_mem (show ω ∈ (good n)ᶜ from hgood) _

end FCAppendix.Affine.Uniform06.LiteralBadCountTransfer
