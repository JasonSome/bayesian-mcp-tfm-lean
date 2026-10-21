import FCAppendix.Affine.Uniform06.FiniteSampledLaplace
import FCAppendix.Affine.Uniform06.ExponentialCellBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.SampledCellDomination

open Set MeasureTheory Filter
open scoped Topology BigOperators
open FCAppendix.Affine.WeightedSampling
open FiniteSampledLaplace PathNumerator FiniteMarkedExchangeability
open WeightedIntervalLLT ExponentialCellBounds DeficitOrientation
open MixedIntervalLLT ExactUntilting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma tuple_sum_eq_selectedSum (h : ι → ℝ) (k : ℕ) (p : Path ι k) :
    (∑ j,h (tuple k p j))=selectedSum h k p := by
  induction k with
  | zero => simp [tuple,selectedSum]
  | succ k ih =>
    simp only [tuple,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,selectedSum,ih]

theorem supported_shift_lower (w : Weights ι) (h : ι → ℝ) {η : ℝ}
    (hh : ∀ j,0 < w.1 j → η ≤ h j) (k : ℕ)
    (hW : (k:ℝ) < totalWeight w) (p : Path ι k)
    (hp : 0 < (pathLaw w k ∅).mass p) :
    η*(k:ℝ) ≤ ∑ j,h (tuple k p j) := by
  have hW' : ((∅:Finset ι).card:ℝ)+k < totalWeight w := by simpa using hW
  have hcard := finalSet_card w k ∅ hW' p hp
  have hpos := finalSet_weight_pos w k ∅ hW' (by simp) p hp
  have hsum := selectedSum_eq_setSum w h k ∅ hW' p hp
  rw [tuple_sum_eq_selectedSum,hsum]
  simp only [Finset.sum_empty,sub_zero]
  calc
    _ = ∑ j ∈ finalSet k ∅ p,η := by
      simp only [Finset.sum_const,nsmul_eq_mul,hcard,Finset.card_empty,zero_add]
      ring
    _ ≤ _ := Finset.sum_le_sum fun j hj => hh j (hpos j hj)

section Cells
variable {Ω : Type*} [MeasurableSpace Ω]

def cellMajorant (X : Ω → ℝ) (Y : Ω → ℤ) (cap θ s : ℝ) (y : ℤ) (r : ℕ)
    {N : ℕ} (ω : Fin N → Ω) : ℝ :=
  if sumY Y ω=y then exponentialTest r θ s (cap-sumX X ω) else 0

def safeRow {N : ℕ} [Nonempty (Fin N)] (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ)
    (ω : Fin N → Ω) : ℝ :=
  if (k:ℝ) < totalWeight (rowWeights w hw ω) then
    sampledRow X h w Y hw cap θ y r k ω else 0

lemma measurable_safeRow {N : ℕ} [Nonempty (Fin N)] {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (hbw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ) :
    Measurable (safeRow X h w Y hbw cap θ y r k : (Fin N → Ω) → ℝ) := by
  unfold safeRow
  apply Measurable.ite _ (measurable_sampledRow hX hh hw hY hbw cap θ y r k) measurable_const
  apply measurableSet_lt measurable_const
  exact Finset.measurable_sum _ fun j _ => hw.comp (measurable_pi_apply j)

omit [MeasurableSpace Ω] in
lemma safeRow_nonneg {N : ℕ} [Nonempty (Fin N)] (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1) (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) :
    0 ≤ safeRow X h w Y hw cap θ y r k ω := by
  unfold safeRow
  split_ifs
  · exact expect_nonneg _ _ (fun p => tupleTest_nonneg X h Y cap θ y r ω (tuple k p))
  · rfl

omit [MeasurableSpace Ω] in
lemma tupleTest_le_majorant {N k : ℕ} (X h : Ω → ℝ) (Y : Ω → ℤ)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) (ω : Fin N → Ω) (v : Fin k → Fin N) {s : ℝ}
    (hs : s ≤ ∑ j,h (ω (v j))) :
    tupleTest X h Y cap θ y r ω v ≤ cellMajorant X Y cap θ s y r ω := by
  by_cases hY : sumY Y ω=y
  · simp only [cellMajorant,if_pos hY]
    unfold tupleTest
    split_ifs with hD
    · have hSW : s ≤ cap-sumX X ω := by linarith [hD.2]
      rw [exponentialTest,if_pos hSW]
      have hp := pow_le_pow_left₀ hD.2.le
        (sub_le_sub_left hs (cap-sumX X ω)) r
      simpa only [neg_mul, mul_comm] using mul_le_mul_of_nonneg_left hp
        (Real.exp_pos (-θ * (cap-sumX X ω))).le
    · exact exponentialTest_nonneg _ _ _ _
  · simp only [tupleTest,cellMajorant,hY,false_and,if_false,le_refl]

omit [MeasurableSpace Ω] in
theorem safeRow_le_cellMajorant {N : ℕ} [Nonempty (Fin N)]
    (X h w : Ω → ℝ) (Y : Ω → ℤ) (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r k : ℕ) (ω : Fin N → Ω) {η : ℝ}
    (hh : ∀ j,0 < w (ω j) → η ≤ h (ω j)) :
    safeRow X h w Y hw cap θ y r k ω ≤ cellMajorant X Y cap θ (η*k) y r ω := by
  unfold safeRow
  split_ifs with hW
  · apply expect_le_const
    intro p hp
    exact tupleTest_le_majorant X h Y cap θ y r ω (tuple k p)
      (supported_shift_lower (rowWeights w hw ω) (fun j => h (ω j)) hh k hW p hp)
  · unfold cellMajorant
    split_ifs
    · exact exponentialTest_nonneg _ _ _ _
    · rfl

lemma integral_cellMajorant_reflected (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (r cap : ℕ → ℝ)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (θ s : ℝ) (y : ℤ) (q n : ℕ) :
    (∫ ω : Fin (A.N n) → Ω,cellMajorant (U n) (A.Y n) (cap n) θ s y q ω
      ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))=
      ∫ w,exponentialTest q θ s w ∂MixedCellSmoothing.productCell
        (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
        (cap n-(A.N n:ℝ)*r n) 0 y := by
  rw [integral_productCell (A.law n) ((reflectX A).measurable_X n) (A.measurable_Y n)
    (A.N n) (cap n-(A.N n:ℝ)*r n) 0 y (measurable_exponentialTest q θ s)]
  apply integral_congr_ae
  filter_upwards [reflected_sum_eq_deficit A U r cap (fun _ => 0) hcenter n] with ω hω
  simp only [sub_zero] at hω
  simp only [MixedProductCharacteristic.continuousSum] at hω
  simp only [cellMajorant,zero_add,sumX,sumY,
    MixedProductCharacteristic.continuousSum,MixedProductCharacteristic.integerSum]
  rw [hω]
  split_ifs <;> simp

theorem eventual_sampled_cell_bounds (A : CenteredArray Ω)
    [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (U h w : ℕ → Ω → ℝ) (r cap θ : ℕ → ℝ)
    (hU : ∀ n,Measurable (U n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n)) (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hbU : ∀ n x,U n x ∈ Icc (0:ℝ) 1)
    (hpositive : ∀ n,∀ᵐ x ∂A.law n,0 ≤ h n x)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hcap : ∀ n,cap n ≤ (A.N n:ℝ))
    {lo hi η : ℝ} (hlo : 0 < lo) (hθ : ∀ n,lo ≤ θ n ∧ θ n ≤ hi) (hη : 0 < η)
    (hgapw : ∀ n,∀ᵐ x ∂A.law n,0 < w n x → η ≤ h n x) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n in atTop,∀ (y : ℤ) (k : ℕ) (q : Fin 3),
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → Ω,
        safeRow (U n) (h n) (w n) (A.Y n) (hbw n) (cap n) (θ n) y q.val k ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) ≤
        C*(Real.exp (-lo*η))^k := by
  obtain ⟨C0,hC0,he⟩ := eventual_all_cells_exponential_bounds (reflectX A)
    (reflectX_compactGap A hgap)
  let K := max (1/lo+1) (max (3/lo^2+2/lo) (10/lo^3+4/lo^2))
  have hK : 0 < K := lt_of_lt_of_le (by positivity : 0 < 1/lo+1) (le_max_left _ _)
  refine ⟨C0*K,mul_pos hC0 hK,?_⟩
  filter_upwards [he] with n hn
  intro y k q
  have ht : 0 < θ n := hlo.trans_le (hθ n).1
  have hηk : 0 ≤ η*(k:ℝ) := mul_nonneg hη.le (Nat.cast_nonneg _)
  let P := Measure.pi (fun _ : Fin (A.N n) => A.law n)
  have hrow : ∀ᵐ ω ∂P, (∀ j,0 ≤ h n (ω j)) ∧
      (∀ j,0 < w n (ω j) → η ≤ h n (ω j)) := by
    have hx (j : Fin (A.N n)) := (measurePreserving_eval
      (fun _ : Fin (A.N n) => A.law n) j).quasiMeasurePreserving.ae
        ((hpositive n).and (hgapw n))
    filter_upwards [ae_all_iff.mpr hx] with ω hω
    exact ⟨fun j => (hω j).1,fun j => (hω j).2⟩
  have hsi : Integrable (safeRow (U n) (h n) (w n) (A.Y n) (hbw n)
      (cap n) (θ n) y q.val k) P := by
    apply Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val)
      (measurable_safeRow (hU n) (hh n) (hw n) (A.measurable_Y n) (hbw n) _ _ _ _ _).aemeasurable
    filter_upwards [hrow] with ω hω
    refine ⟨safeRow_nonneg _ _ _ _ _ _ _ _ _ _ _,?_⟩
    unfold safeRow
    split_ifs
    · exact (row_polynomial_bounds (U n) (h n) (w n) (A.Y n) (hbw n)
        _ _ _ _ _ ω (Nat.cast_pos.mp (A.N_pos n)) (fun j => (hbU n (ω j)).1)
        hω.1 (hcap n) ht.le).1.2
    · positivity
  have hmi : Integrable (cellMajorant (U n) (A.Y n) (cap n) (θ n) (η*k) y q.val) P := by
    have hm : Measurable (cellMajorant (U n) (A.Y n) (cap n) (θ n) (η*k) y q.val :
        (Fin (A.N n) → Ω) → ℝ) := by
      have hx : Measurable (fun ω : Fin (A.N n) → Ω => cap n-sumX (U n) ω) :=
        measurable_const.sub (Finset.measurable_sum _ fun j _ =>
          (hU n).comp (measurable_pi_apply j))
      have hy : Measurable (fun ω : Fin (A.N n) → Ω => sumY (A.Y n) ω) :=
        Finset.measurable_sum _ fun j _ => (A.measurable_Y n).comp (measurable_pi_apply j)
      unfold cellMajorant
      exact Measurable.ite (measurableSet_eq_fun hy measurable_const)
        ((measurable_exponentialTest q.val (θ n) (η*k)).comp hx) measurable_const
    apply Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val) hm.aemeasurable
    apply ae_of_all
    intro ω
    unfold cellMajorant exponentialTest
    split_ifs with hy hs
    · have hx : 0 ≤ sumX (U n) ω := Finset.sum_nonneg (fun j _ => (hbU n (ω j)).1)
      have hD : 0 ≤ cap n-sumX (U n) ω-η*k := sub_nonneg.mpr hs
      have hDN : cap n-sumX (U n) ω-η*k ≤ (A.N n:ℝ) := by linarith [hcap n]
      have hW : 0 ≤ cap n-sumX (U n) ω := by linarith
      have hExp : Real.exp (-(θ n*(cap n-sumX (U n) ω))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht.le hW))
      exact ⟨mul_nonneg (pow_nonneg hD _) (Real.exp_pos _).le,
        (mul_le_mul_of_nonneg_left hExp (pow_nonneg hD _)).trans
          (by simpa only [mul_one] using pow_le_pow_left₀ hD hDN q.val)⟩
    · exact ⟨le_rfl,by positivity⟩
    · exact ⟨le_rfl,by positivity⟩
  have hle := integral_mono_ae hsi hmi (hrow.mono fun ω hω =>
    safeRow_le_cellMajorant (U n) (h n) (w n) (A.Y n) (hbw n) _ _ _ _ _ ω hω.2)
  rw [integral_cellMajorant_reflected A U r cap hcenter] at hle
  have hcells := hn (cap n-(A.N n:ℝ)*r n) 0 y (θ n) (η*k) ht
  have hpoly : (match q.val with
      | 0 => 1/θ n+1
      | 1 => 3/(θ n)^2+2/θ n
      | _ => 10/(θ n)^3+4/(θ n)^2) ≤ K := by
    have h1 : 1/θ n ≤ 1/lo := one_div_le_one_div_of_le hlo (hθ n).1
    have h2 : 1/(θ n)^2 ≤ 1/lo^2 := one_div_le_one_div_of_le (pow_pos hlo 2)
      (pow_le_pow_left₀ hlo.le (hθ n).1 2)
    have h3 : 1/(θ n)^3 ≤ 1/lo^3 := one_div_le_one_div_of_le (pow_pos hlo 3)
      (pow_le_pow_left₀ hlo.le (hθ n).1 3)
    have hb0 : 1/lo+1 ≤ K := le_max_left _ _
    have hb1 : 3/lo^2+2/lo ≤ K := (le_max_left _ _).trans (le_max_right _ _)
    have hb2 : 10/lo^3+4/lo^2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
    fin_cases q
    · change 1/θ n+1 ≤ K
      linarith
    · change 3/(θ n)^2+2/θ n ≤ K
      simp only [div_eq_mul_inv, one_mul] at h1 h2 hb1 ⊢
      linarith
    · change 10/(θ n)^3+4/(θ n)^2 ≤ K
      simp only [div_eq_mul_inv, one_mul] at h2 h3 hb2 ⊢
      linarith
  have heq : Real.exp (-(θ n*(η*k))) ≤ (Real.exp (-lo*η))^k := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hθ n).1 hηk]
  have hmain : (A.N n:ℝ)*(∫ ω,safeRow (U n) (h n) (w n) (A.Y n) (hbw n)
      (cap n) (θ n) y q.val k ω ∂P) ≤
        C0*Real.exp (-(θ n*(η*k)))*K := by
    have hq : (∫ w,exponentialTest q.val (θ n) (η*k) w
        ∂MixedCellSmoothing.productCell (A.law n) ((reflectX A).X n)
          (A.Y n) (A.N n) (cap n-(A.N n:ℝ)*r n) 0 y) ≤
        C0/(A.N n:ℝ)*Real.exp (-(θ n*(η*k)))*
          (match q.val with
            | 0 => 1/θ n+1
            | 1 => 3/(θ n)^2+2/θ n
            | _ => 10/(θ n)^3+4/(θ n)^2) := by
      fin_cases q
      · exact hcells.1
      · exact hcells.2.1
      · exact hcells.2.2
    have hh := mul_le_mul_of_nonneg_left (hle.trans hq) (A.N_pos n).le
    have he : (A.N n:ℝ)*(C0/(A.N n:ℝ)*Real.exp (-(θ n*(η*k)))*
        (match q.val with
          | 0 => 1/θ n+1
          | 1 => 3/(θ n)^2+2/θ n
          | _ => 10/(θ n)^3+4/(θ n)^2)) =
        C0*Real.exp (-(θ n*(η*k)))*
          (match q.val with
            | 0 => 1/θ n+1
            | 1 => 3/(θ n)^2+2/θ n
            | _ => 10/(θ n)^3+4/(θ n)^2) := by
      field_simp [(A.N_pos n).ne']
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg hC0.le (Real.exp_pos _).le))
  exact hmain.trans (by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heq hC0.le) hK.le
    convert! hh using 1
    ring)

end Cells
end FCAppendix.Affine.Uniform06.SampledCellDomination
