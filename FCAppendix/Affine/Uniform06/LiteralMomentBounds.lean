import FCAppendix.Affine.Uniform06.RawTotalCellBounds
import FCAppendix.Affine.Uniform06.LiteralBadCountTransfer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralMomentBounds

open MeasureTheory Set Filter LowBody
open scoped BigOperators Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT RawMomentPartition LiteralBadCountTransfer ClampedMomentBounds
open RawTotalCellBounds

theorem finite_family_bounded_above {J : Type*} [Fintype J]
    (F : J → ℕ → ℝ) (L : J → ℝ)
    (hF : ∀ j,Tendsto (F j) atTop (𝓝 (L j))) :
    ∃ B>(0:ℝ),∀ᶠ n in atTop,∀ j,F j n≤ B := by
  let B := (∑ j, (|L j|+1))+1
  have hs : 0≤∑ j, (|L j|+1) := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨B,by dsimp [B]; linarith,?_⟩
  apply eventually_all.mpr
  intro j
  filter_upwards [(hF j).eventually (Iio_mem_nhds
    (show L j < |L j|+1 by linarith [le_abs_self (L j)]))] with n hn
  have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    show 0≤|L k|+1 by positivity) (Finset.mem_univ j)
  dsimp only [B]
  linarith

variable {N : ℕ} [Nonempty (Fin N)]

lemma integral_le_integral_add_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F H : Ω → ℝ) (hF : Integrable F μ) (hH : Integrable H μ) :
    (∫ ω,F ω ∂μ)≤(∫ ω,H ω ∂μ)+(∫ ω,|F ω-H ω| ∂μ) := by
  have hh : |∫ ω,F ω-H ω ∂μ|≤∫ ω,|F ω-H ω| ∂μ := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=fun ω => F ω-H ω) (μ:=μ)
  rw [integral_sub hF hH] at hh
  linarith [le_abs_self ((∫ ω,F ω ∂μ)-(∫ ω,H ω ∂μ))]

omit [Nonempty (Fin N)] in
lemma weighted_test_integrable (_i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (F : (Fin N → RowRival) → ℝ) (hF : Measurable F) (q j : ℕ)
    (hFb : ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => μ),F ω ∈ Icc (0:ℝ) ((N:ℝ)^q)) :
    Integrable (fun ω => ((imbalanceSum ω).natAbs:ℝ)^j*F ω)
      (Measure.pi (fun _ : Fin N => μ)) := by
  have hk : Measurable (fun ω : Fin N → RowRival => ((imbalanceSum ω).natAbs:ℝ)) :=
    (measurable_of_countable (fun z : ℤ => (z.natAbs:ℝ))).comp measurable_imbalanceSum
  apply Integrable.of_mem_Icc 0 ((N:ℝ)^(q+j)) ((hk.pow_const j).mul hF).aemeasurable
  filter_upwards [hFb] with ω hω
  have hkn : ((imbalanceSum ω).natAbs:ℝ)≤(N:ℝ) := by
    exact_mod_cast (show (imbalanceSum ω).natAbs≤ N by rw [← draws_eq_natAbs]; exact draws_le ω)
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hkn j
  refine ⟨mul_nonneg (pow_nonneg (Nat.cast_nonneg _) j) hω.1,?_⟩
  have hh := mul_le_mul hp hω.2 hω.1 (pow_nonneg (Nat.cast_nonneg _) j)
  simpa only [pow_add,Pi.mul_apply,mul_comm] using! hh

theorem original_bounded_moments (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ τ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hb : ∀ n,0< b n) (hbL : ∀ n,b n≤(g n).multiplier)
    (hc : ∀ n,(c n:ℝ)≤ A.N n)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    {t0 t1 η z ε : ℝ} (ht0 : 0< t0) (ht : ∀ n,t0≤τ n ∧ τ n≤ t1)
    (hη : 0<η) (hz : 0< z) (hε : 0<ε) (s U : ℝ)
    (hh : ∀ n,∀ᵐ x ∂A.law n,0≤ rawH (xi i) (b n) x ∧
      (0< rawWeight (xi i) (g n) x → η≤ rawH (xi i) (b n) x))
    (hwmean : Tendsto (fun n => ∫ x,rawWeight (xi i) (g n) x ∂A.law n) atTop (𝓝 z))
    (hfinite : ∀ᶠ n in atTop,countMargins i (G n:Measure (ℝ × ℝ))
      (A.N n) (c n) (b n) (θ n) ε) :
    ∃ B > (0:ℝ),∀ᶠ n in atTop,∀ q : Fin 3,
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)≤ B ∧
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        ((imbalanceSum ω).natAbs:ℝ)*literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)≤ B := by
  obtain ⟨B,hB,hbound⟩ := eventual_total_cell_bounds i A hgap b τ r c g cm hY hcenter
    hb hc ht0 ht hη hz hh hwmean
  have herror (q : Fin 3) (j : Fin 2) := original_literal_cell_replacement i G A.N c
    A.market (fun n => Nat.cast_pos.mp (A.N_pos n)) b θ τ g cm hb hbL
    (fun n => ht0.le.trans (ht n).1) hc hg
    (fun n => by rw [← hlaw]; exact (hh n).mono fun _ hx => hx.1)
    hε s U hfinite q.val j.val
  have herr : ∀ᶠ n in atTop,∀ q : Fin 3,∀ j : Fin 2,
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        ((imbalanceSum ω).natAbs:ℝ)^j.val*
          |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω-
            cellSum i (c n) (g n) (cm n) (b n) (τ n) q.val ω|
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)<1 := by
    apply eventually_all.mpr
    intro q
    apply eventually_all.mpr
    intro j
    simpa only [hlaw] using (herror q j).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨B+1,by linarith,?_⟩
  filter_upwards [hbound,herr] with n hn he q
  let P := Measure.pi (fun _ : Fin (A.N n) => A.law n)
  let F := literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val
  let H := cellSum i (c n) (g n) (cm n) (b n) (τ n) q.val
  have hrow : ∀ᵐ ω ∂P,∀ k,0≤ rawH (xi i) (b n) (ω k) := by
    exact ae_all_iff.mpr fun k => (measurePreserving_eval (fun _ : Fin (A.N n) => A.law n) k).quasiMeasurePreserving.ae ((hh n).mono fun _ hx => hx.1)
  have hFb : ∀ᵐ ω ∂P,F ω ∈ Icc (0:ℝ) ((A.N n:ℝ)^q.val) := hrow.mono fun ω hw =>
    literalMoment_polynomial i _ _ _ (hb n) (hbL n) (ht0.le.trans (ht n).1) _ (hc n)
      (hg n).1 (hg n).2.1 (hg n).2.2 ω hw
  have hHb : ∀ᵐ ω ∂P,H ω ∈ Icc (0:ℝ) ((A.N n:ℝ)^q.val) := hrow.mono fun ω hw =>
    cellSum_polynomial i _ _ _ (hb n) (ht0.le.trans (ht n).1) _
      (Nat.cast_pos.mp (A.N_pos n)) (hc n) ω hw
  have hj (j : Fin 2) : (A.N n:ℝ)*∫ ω,((imbalanceSum ω).natAbs:ℝ)^j.val*F ω ∂P≤ B+1 := by
    have hFi := weighted_test_integrable i (A.law n) F
      (measurable_literalMoment _ _ _ _ _ _ _) q.val j.val hFb
    have hHi := weighted_test_integrable i (A.law n) H
      (measurable_cellSum _ _ _ _ _ _ _) q.val j.val hHb
    have hh' := mul_le_mul_of_nonneg_left (integral_le_integral_add_abs P _ _ hFi hHi) (A.N_pos n).le
    have hab : (fun ω : Fin (A.N n) → RowRival =>
        |((imbalanceSum ω).natAbs:ℝ)^j.val*F ω-
          ((imbalanceSum ω).natAbs:ℝ)^j.val*H ω|)=
        fun ω => ((imbalanceSum ω).natAbs:ℝ)^j.val*|F ω-H ω| := by
      funext ω
      rw [← mul_sub,abs_mul,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg _) j.val)]
    rw [hab] at hh'
    have hx := he q j
    have hc' : (A.N n:ℝ)*∫ ω,((imbalanceSum ω).natAbs:ℝ)^j.val*H ω ∂P≤ B := by
      fin_cases j
      · simpa only [Fin.val_mk,pow_zero,one_mul] using (hn q).1
      · simpa only [Fin.val_mk,pow_one] using (hn q).2
    dsimp only [F,H,P] at *
    linarith
  exact ⟨by simpa only [Fin.val_zero,pow_zero,one_mul] using hj 0,
    by simpa only [Fin.val_one,pow_one] using hj 1⟩

end FCAppendix.Affine.Uniform06.LiteralMomentBounds
