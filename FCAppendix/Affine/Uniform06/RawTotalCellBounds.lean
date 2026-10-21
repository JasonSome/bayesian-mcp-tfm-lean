import FCAppendix.Affine.Uniform06.RawMomentPartition
import FCAppendix.Affine.Uniform06.ImbalanceWeightedMoment

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RawTotalCellBounds

open MeasureTheory Set Filter LowBody
open scoped BigOperators Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT FiniteSampledLaplace SampledCellDomination SampledSafeLimit
open RawMomentPartition GuardedSampledMoments RareEmpiricalReplacement LiteralGuardRare

lemma finite_geometric_le {Q : ℝ} (hQ0 : 0≤ Q) (hQ1 : Q<1) (N : ℕ) :
    (∑ k ∈ Finset.range N,Q^(k+1))≤ Q/(1-Q) := by
  have he : (1-Q)*(∑ k ∈ Finset.range N,Q^(k+1))=Q-Q^(N+1) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ,mul_add,ih,pow_succ,pow_succ]
      ring
  apply (le_div_iff₀ (sub_pos.mpr hQ1)).mpr
  rw [mul_comm,he]
  linarith [pow_nonneg hQ0 (N+1)]

variable {N : ℕ} [Nonempty (Fin N)]

theorem safeCell_le_unweighted (i : Row) (μ : Measure RowRival)
    [IsProbabilityMeasure μ] (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hθ : 0≤θ)
    (y : ℤ) (k q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N)
    (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r) :
    safeCell i μ N c g cm b θ y k q≤
      (N:ℝ)*∫ ω : Fin N → RowRival,
        safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g) integerSign
          (rawWeight_bounds (xi i) g) c θ y q k ω ∂Measure.pi (fun _ : Fin N => μ) := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let F : (Fin N → RowRival) → ℝ := safeRow (demand (xi i) b) (rawH (xi i) b) (rawWeight (xi i) g)
    integerSign (rawWeight_bounds (xi i) g) c θ y q k
  have hbF := (polynomial_sampled_ae μ hN
    (RawMixedSource.demand (xi i) b) (rawH (xi i) b)
    (rawWeight (xi i) g) integerSign (rawWeight_bounds (xi i) g)
    (hh.mono fun r hr => ⟨(demand_bounds (xi_pos i) hb r).1,hr⟩) hc hθ y q k).mono
      fun _ hx => hx.2
  have hFi : Integrable F P := Integrable.of_mem_Icc 0 ((N:ℝ)^q)
    (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
      (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _).aemeasurable hbF
  have hgi : Integrable (fun ω => rawGuard (xi i) g c cm b ω*F ω) P := by
    apply Integrable.of_mem_Icc 0 ((N:ℝ)^q)
      ((measurable_rawGuard (xi i) g c cm b).mul
        (measurable_safeRow (measurable_demand (xi i) b) (measurable_rawH (xi i) b)
          (measurable_rawWeight (xi i) g) measurable_integerSign _ _ _ _ _ _)).aemeasurable
    filter_upwards [hbF] with ω hω
    have ha := rawGuard_bounds (xi i) g c cm b ω
    exact ⟨mul_nonneg ha.1 hω.1,(mul_le_mul_of_nonneg_right ha.2 hω.1).trans
      (by simpa only [one_mul] using hω.2)⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  apply integral_mono_ae hgi hFi
  filter_upwards [hbF] with ω hω
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (rawGuard_bounds (xi i) g c cm b ω).2 hω.1

theorem finite_total_bound (i : Row) (μ : Measure RowRival) [IsProbabilityMeasure μ]
    (c : ℕ) (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) {b θ C C0 Q : ℝ}
    (hb : 0< b) (hθ : 0≤θ) (q : ℕ) (hN : 0< N) (hc : (c:ℝ)≤ N)
    (hh : ∀ᵐ r ∂μ,0≤ rawH (xi i) b r)
    (hC : 0≤ C) (hQ0 : 0≤ Q) (hQ1 : Q<1)
    (hzero : zeroCell i μ N c g b θ q≤ C0)
    (hcells : ∀ y k,safeCell i μ N c g cm b θ y k q≤ C*Q^k) :
    (N:ℝ)*∫ ω : Fin N → RowRival,cellSum i c g cm b θ q ω
      ∂Measure.pi (fun _ : Fin N => μ)≤ C0+2*C*Q/(1-Q) ∧
    (N:ℝ)*∫ ω : Fin N → RowRival,((imbalanceSum ω).natAbs:ℝ)*cellSum i c g cm b θ q ω
      ∂Measure.pi (fun _ : Fin N => μ)≤2*C*Q/(1-Q)^2 := by
  have hsum := normalized_integral_cellSum i μ c g cm hb hθ q hN hc hh
  have hfinite : (∑' k : ℕ,
      (safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
        safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q))=
      ∑ k ∈ Finset.range N,
        (safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
          safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q) := by
    apply tsum_eq_sum
    intro k hk
    have hz := safeCell_zero_outside i μ c g cm b θ q k
      (by simpa only [Finset.mem_range,not_lt] using hk)
    rw [hz.1,hz.2,zero_add]
  refine ⟨?_,ImbalanceWeightedMoment.integral_imbalance_cellSum_le i μ c g cm
    hb hθ q hN hc hh hQ0 hQ1 hC (fun k _ => ⟨hcells _ _,hcells _ _⟩)⟩
  rw [hsum,hfinite]
  have hs : (∑ k ∈ Finset.range N,
      (safeCell i μ N c g cm b θ ((k+1:ℕ):ℤ) (k+1) q+
        safeCell i μ N c g cm b θ (-((k+1:ℕ):ℤ)) (k+1) q))≤
      2*C*(∑ k ∈ Finset.range N,Q^(k+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := add_le_add (hcells ((k+1:ℕ):ℤ) (k+1)) (hcells (-((k+1:ℕ):ℤ)) (k+1))
    nlinarith
  have hg := mul_le_mul_of_nonneg_left (finite_geometric_le hQ0 hQ1 N)
    (show 0≤2*C by positivity)
  rw [← mul_div_assoc] at hg
  linarith

theorem eventual_total_cell_bounds (i : Row) (A : CenteredArray RowRival)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b τ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ)
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hb : ∀ n,0< b n) (hc : ∀ n,(c n:ℝ)≤ A.N n)
    {t0 t1 η z : ℝ} (ht0 : 0< t0) (ht : ∀ n,t0≤τ n ∧ τ n≤ t1)
    (hη : 0<η) (hz : 0< z)
    (hh : ∀ n,∀ᵐ x ∂A.law n,0≤ rawH (xi i) (b n) x ∧
      (0< rawWeight (xi i) (g n) x → η≤ rawH (xi i) (b n) x))
    (hwmean : Tendsto (fun n => ∫ x,rawWeight (xi i) (g n) x ∂A.law n) atTop (𝓝 z)) :
    ∃ B > (0:ℝ),∀ᶠ n in atTop,∀ q : Fin 3,
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        cellSum i (c n) (g n) (cm n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)≤ B ∧
      (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
        ((imbalanceSum ω).natAbs:ℝ)*cellSum i (c n) (g n) (cm n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)≤ B := by
  let X := fun n => demand (xi i) (b n)
  let H := fun n => rawH (xi i) (b n)
  let W := fun n => rawWeight (xi i) (g n)
  let Q := Real.exp (-t0*η)
  have hQ0 : 0< Q := Real.exp_pos _
  have hQ1 : Q<1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos ht0 hη])
  obtain ⟨C,hC,hcells⟩ := eventual_sampled_cell_bounds A hgap X H W r
    (fun n => (c n:ℝ)) τ (fun n => measurable_demand (xi i) (b n))
    (fun n => measurable_rawH (xi i) (b n)) (fun n => measurable_rawWeight (xi i) (g n))
    (fun n => rawWeight_bounds (xi i) (g n)) (fun n => demand_bounds (xi_pos i) (hb n))
    (fun n => (hh n).mono fun _ hx => hx.1) hcenter hc ht0 ht hη
    (fun n => (hh n).mono fun _ hx => hx.2)
  have hdiff (q : Fin 3) := fixed_safe_difference (fun n => A.law n) A.N
    (fun n => Nat.cast_pos.mp (A.N_pos n)) A.market X H W (fun n => A.Y n)
    (fun n => measurable_demand (xi i) (b n)) (fun n => measurable_rawH (xi i) (b n))
    (fun n => measurable_rawWeight (xi i) (g n)) A.measurable_Y
    (fun n => rawWeight_bounds (xi i) (g n))
    (fun n => (hh n).mono fun x hx => ⟨(demand_bounds (xi_pos i) (hb n) x).1,hx.1⟩)
    (fun n => (c n:ℝ)) τ hc (fun n => ht0.le.trans (ht n).1) 0 q.val 0 hz hwmean
  have hd : ∀ᶠ n in atTop,∀ q : Fin 3,
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → RowRival,
        sampledRow (X n) (H n) (W n) (A.Y n) (rawWeight_bounds (xi i) (g n))
          (c n) (τ n) 0 q.val 0 ω-
        safeRow (X n) (H n) (W n) (A.Y n) (rawWeight_bounds (xi i) (g n))
          (c n) (τ n) 0 q.val 0 ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))<1 := by
    exact eventually_all.mpr fun q => (hdiff q).eventually (Iio_mem_nhds (by norm_num))
  let B := 2*C+2+2*C*Q/(1-Q)+2*C*Q/(1-Q)^2
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  filter_upwards [hcells,hd] with n hn hdn q
  have hp := (hh n).mono fun _ hx => hx.1
  have hnc := Nat.cast_pos.mp (A.N_pos n)
  have hs (y : ℤ) (k : ℕ) : safeCell i (A.law n) (A.N n) (c n) (g n) (cm n)
      (b n) (τ n) y k q.val≤ C*Q^k := by
    exact (safeCell_le_unweighted i (A.law n) (c n) (g n) (cm n) (hb n)
      (ht0.le.trans (ht n).1) y k q.val hnc (hc n) hp).trans
      (by simpa only [X,H,W,hY,Q] using hn y k q)
  have hzero : zeroCell i (A.law n) (A.N n) (c n) (g n) (b n) (τ n) q.val≤ C+1 := by
    have hi := polynomial_sampled_ae (A.law n) hnc (X n) (H n) (W n) (A.Y n) (rawWeight_bounds (xi i) (g n))
      ((hh n).mono fun x hx => ⟨(demand_bounds (xi_pos i) (hb n) x).1,hx.1⟩)
      (hc n) (ht0.le.trans (ht n).1) 0 q.val 0
    have h1 : Integrable (sampledRow (X n) (H n) (W n) (A.Y n)
        (rawWeight_bounds (xi i) (g n)) (c n) (τ n) 0 q.val 0) _ :=
      Integrable.of_mem_Icc 0 _ (measurable_sampledRow (measurable_demand _ _)
        (measurable_rawH _ _) (measurable_rawWeight _ _) (A.measurable_Y n) _ _ _ _ _ _).aemeasurable
        (hi.mono fun _ hx => hx.1)
    have h2 : Integrable (safeRow (X n) (H n) (W n) (A.Y n)
        (rawWeight_bounds (xi i) (g n)) (c n) (τ n) 0 q.val 0) _ :=
      Integrable.of_mem_Icc 0 _ (measurable_safeRow (measurable_demand _ _)
        (measurable_rawH _ _) (measurable_rawWeight _ _) (A.measurable_Y n) _ _ _ _ _ _).aemeasurable
        (hi.mono fun _ hx => hx.2)
    have hz' := hdn q
    rw [integral_sub h1 h2] at hz'
    have hc0 := hn 0 0 q
    simp only [pow_zero,mul_one] at hc0
    change (A.N n:ℝ)*∫ ω,
      sampledRow (X n) (H n) (W n) integerSign _ _ _ _ _ _ ω ∂_≤ C+1
    simpa only [hY] using (show (A.N n:ℝ)*(∫ ω,
      sampledRow (X n) (H n) (W n) (A.Y n) _ _ _ _ _ _ ω ∂_)≤ C+1 by linarith)
  have ht' := finite_total_bound i (A.law n) (c n) (g n) (cm n) (hb n)
    (ht0.le.trans (ht n).1) q.val hnc (hc n) hp hC.le hQ0.le hQ1 hzero hs
  have htail0 : 0 ≤ 2*C*Q/(1-Q) := by positivity
  have htail1 : 0 ≤ 2*C*Q/(1-Q)^2 := by positivity
  dsimp only [B]
  constructor <;> nlinarith [ht'.1,ht'.2]

end FCAppendix.Affine.Uniform06.RawTotalCellBounds
