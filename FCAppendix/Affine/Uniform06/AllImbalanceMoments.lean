import FCAppendix.Affine.Uniform06.ExponentialCellBounds
import FCAppendix.Affine.Uniform06.ExactUntilting

noncomputable section
namespace FCAppendix.Affine.Uniform06.AllImbalanceMoments

open MeasureTheory Set Filter
open scoped BigOperators Topology
open MixedProductCharacteristic MixedCellSmoothing MixedIntervalLLT
open WeightedIntervalLLT ExponentialCellBounds ExactUntilting

lemma finite_geometric_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    (∑ k ∈ Finset.range M,q^k) ≤ 1/(1-q) := by
  have he : (1-q)*(∑ k ∈ Finset.range M,q^k)=1-q^M := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ,pow_succ]
      nlinarith
  apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
  nlinarith [pow_nonneg hq0 M]

lemma two_sign_domination (F : ℕ → ℝ) (hF : ∀ k,0 ≤ F k)
    (M : ℕ) (y : ℤ) (hy : y.natAbs ≤ M) :
    F y.natAbs ≤ ∑ k ∈ Finset.range (M+1),
      ((if y=(k : ℤ) then F k else 0)+(if y=-(k : ℤ) then F k else 0)) := by
  have hnonneg (k : ℕ) : 0 ≤
      ((if y=(k : ℤ) then F k else 0)+(if y=-(k : ℤ) then F k else 0)) := by
    split_ifs <;> linarith [hF k]
  have hmem : y.natAbs ∈ Finset.range (M+1) := Finset.mem_range.mpr (by omega)
  calc
    F y.natAbs ≤
        ((if y=(y.natAbs : ℤ) then F y.natAbs else 0)+
          (if y=-(y.natAbs : ℤ) then F y.natAbs else 0)) := by
      cases y with
      | ofNat k => simp [Int.natAbs]; split_ifs <;> linarith [hF k]
      | negSucc k =>
        have he : Int.negSucc k=-((k+1 : ℕ) : ℤ) := by omega
        simp only [Int.natAbs]
        rw [he]
        simp only [ite_true]
        split_ifs <;> linarith [hF (k+1)]
    _ ≤ _ := Finset.single_le_sum (fun k _ => hnonneg k) hmem

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_natAbs_real : Measurable (fun y : ℤ => (y.natAbs : ℝ)) :=
  measurable_of_countable _

lemma measurable_variable_exponentialTest {W : Ω → ℝ} {Y : Ω → ℤ}
    (hW : Measurable W) (hY : Measurable Y) (k : ℕ) (θ a : ℝ) :
    Measurable (fun ω => exponentialTest k θ (a*(Y ω).natAbs) (W ω)) := by
  have hs := (measurable_natAbs_real.comp hY).const_mul a
  unfold exponentialTest
  exact Measurable.ite (measurableSet_le hs hW)
    (((hW.sub hs).pow_const k).mul (show Measurable (fun ω => Real.exp (-(θ*W ω))) by fun_prop)) measurable_const

lemma integrable_variable_exponentialTest (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} {Y : Ω → ℤ} (hW : Measurable W) (hY : Measurable Y)
    {B θ a : ℝ} (hB : 0 ≤ B) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hbound : ∀ᵐ ω ∂μ,|W ω| ≤ B) (k : ℕ) :
    Integrable (fun ω => exponentialTest k θ (a*(Y ω).natAbs) (W ω)) μ := by
  apply Integrable.of_bound (measurable_variable_exponentialTest hW hY k θ a).aestronglyMeasurable
    (B^k*Real.exp (θ*B))
  filter_upwards [hbound] with ω hω
  rw [Real.norm_of_nonneg (exponentialTest_nonneg _ _ _ _)]
  unfold exponentialTest
  split_ifs with hs
  · have hs0 : 0 ≤ a*((Y ω).natAbs : ℝ) := mul_nonneg ha (Nat.cast_nonneg _)
    have hx : 0 ≤ W ω-a*((Y ω).natAbs : ℝ) := sub_nonneg.mpr hs
    have hxB : W ω-a*((Y ω).natAbs : ℝ) ≤ B := by
      linarith [(abs_le.mp hω).2]
    apply mul_le_mul (pow_le_pow_left₀ hx hxB k) _
      (Real.exp_pos _).le (pow_nonneg hB k)
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hω).1 hθ
    nlinarith
  · positivity

theorem all_imbalance_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} {Y : Ω → ℤ} (hW : Measurable W) (hY : Measurable Y)
    {B θ a C : ℝ} (hB : 0 ≤ B) (hθ : 0 < θ) (ha : 0 < a) (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂μ,|W ω| ≤ B) (M : ℕ)
    (hYbound : ∀ᵐ ω ∂μ,(Y ω).natAbs ≤ M) (k : ℕ)
    (hcell : ∀ n : ℕ, ∀ y : ℤ,
      (∫ ω,exponentialTest k θ (a*n) (W ω)*
        (if Y ω=y then (1 : ℝ) else 0) ∂μ) ≤ C*(Real.exp (-θ*a))^n) :
    (∫ ω,exponentialTest k θ (a*(Y ω).natAbs) (W ω) ∂μ) ≤
      2*C/(1-Real.exp (-θ*a)) := by
  classical
  let F : ℕ → Ω → ℝ := fun n ω => exponentialTest k θ (a*n) (W ω)
  let H : ℕ → Ω → ℝ := fun n ω =>
    F n ω*(if Y ω=(n : ℤ) then 1 else 0)+
      F n ω*(if Y ω=-(n : ℤ) then 1 else 0)
  have hFi (n : ℕ) : Integrable (F n) μ := by
    simpa [F] using
      integrable_variable_exponentialTest μ hW
        (show Measurable (fun _ : Ω => (n : ℤ)) from measurable_const)
        hB hθ.le ha.le hbound k
  have hHi (n : ℕ) : Integrable (H n) μ := by
    have hp := (hFi n).indicator
      (show MeasurableSet {ω | Y ω=(n : ℤ)} from measurableSet_eq_fun hY measurable_const)
    have hn := (hFi n).indicator
      (show MeasurableSet {ω | Y ω=-(n : ℤ)} from measurableSet_eq_fun hY measurable_const)
    convert! hp.add hn using 1
    funext ω
    simp only [H,Pi.add_apply]
    split_ifs <;> simp_all
  have hsum_i (L : ℕ) : Integrable (fun ω => ∑ n ∈ Finset.range L,H n ω) μ := by
    induction L with
    | zero => simp
    | succ L ih =>
      convert! ih.add (hHi L) using 1
      funext ω
      simp only [Finset.sum_range_succ,Pi.add_apply]
  have hsum_integral (L : ℕ) :
      (∫ ω,∑ n ∈ Finset.range L,H n ω ∂μ)=∑ n ∈ Finset.range L,∫ ω,H n ω ∂μ := by
    induction L with
    | zero => simp
    | succ L ih =>
      simp_rw [Finset.sum_range_succ]
      rw [integral_add (hsum_i L) (hHi L),ih]
  have hmain := integrable_variable_exponentialTest μ hW hY hB hθ.le ha.le hbound k
  calc
    _ ≤ ∫ ω,∑ n ∈ Finset.range (M+1),H n ω ∂μ := by
      apply integral_mono_ae hmain (hsum_i (M+1))
      filter_upwards [hYbound] with ω hω
      have hh := two_sign_domination (fun n => F n ω)
        (fun n => exponentialTest_nonneg _ _ _ _) M (Y ω) hω
      simpa only [F,H,ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero] using hh
    _ = ∑ n ∈ Finset.range (M+1),∫ ω,H n ω ∂μ := hsum_integral (M+1)
    _ ≤ ∑ n ∈ Finset.range (M+1),2*C*(Real.exp (-θ*a))^n := by
      apply Finset.sum_le_sum
      intro n hn
      dsimp [H]
      have hp : Integrable (fun ω => F n ω*(if Y ω=(n : ℤ) then (1 : ℝ) else 0)) μ := by
        convert! (hFi n).indicator (measurableSet_eq_fun hY
          (measurable_const : Measurable (fun _ : Ω => (n:ℤ)))) using 1
        funext ω
        by_cases hh : Y ω=(n : ℤ) <;> simp [hh]
      have hm : Integrable (fun ω => F n ω*(if Y ω=-(n : ℤ) then (1 : ℝ) else 0)) μ := by
        convert! (hFi n).indicator (measurableSet_eq_fun hY
          (measurable_const : Measurable (fun _ : Ω => -(n:ℤ)))) using 1
        funext ω
        by_cases hh : Y ω=-(n : ℤ) <;> simp [hh]
      rw [integral_add hp hm]
      have hplus := hcell n (n : ℤ)
      have hminus := hcell n (-(n : ℤ))
      dsimp [F] at *
      linarith
    _ = 2*C*(∑ n ∈ Finset.range (M+1),(Real.exp (-θ*a))^n) := by
      rw [Finset.mul_sum]
    _ ≤ 2*C/(1-Real.exp (-θ*a)) := by
      have hq : Real.exp (-θ*a) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
      have hg := finite_geometric_sum_le (Real.exp_pos (-θ*a)).le hq (M+1)
      have hh := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2*C)
      simpa only [div_eq_mul_inv,mul_one,one_mul,mul_assoc] using hh

lemma product_coordinate_bounds (A : CenteredArray Ω) (n : ℕ) (c : ℝ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
      |c+continuousSum (A.X n) (A.N n) ω| ≤ |c|+(A.N n : ℝ) ∧
        (integerSum (A.Y n) (A.N n) ω).natAbs ≤ A.N n := by
  have hc (j : Fin (A.N n)) :=
    (measurePreserving_eval (fun _ : Fin (A.N n) => A.law n) j).quasiMeasurePreserving.ae
      (A.bounded n)
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  have hX : |continuousSum (A.X n) (A.N n) ω| ≤ (A.N n : ℝ) := by
    unfold continuousSum
    calc
      _ ≤ ∑ j,|A.X n (ω j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (A.N n),(1 : ℝ) := Finset.sum_le_sum (fun j _ => (hω j).1)
      _ = _ := by simp
  have hY : |((integerSum (A.Y n) (A.N n) ω : ℤ) : ℝ)| ≤ (A.N n : ℝ) := by
    simp only [integerSum,Int.cast_sum]
    calc
      _ ≤ ∑ j,|((A.Y n (ω j) : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin (A.N n),(1 : ℝ) := Finset.sum_le_sum (fun j _ => (hω j).2)
      _ = _ := by simp
  refine ⟨(abs_add_le _ _).trans (add_le_add le_rfl hX),?_⟩
  have hl : -(A.N n : ℤ) ≤ integerSum (A.Y n) (A.N n) ω := by
    exact_mod_cast (abs_le.mp hY).1
  have hu : integerSum (A.Y n) (A.N n) ω ≤ (A.N n : ℤ) := by
    exact_mod_cast (abs_le.mp hY).2
  have hcast : ((integerSum (A.Y n) (A.N n) ω).natAbs : ℤ) ≤ (A.N n : ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mpr ⟨hl,hu⟩
  exact_mod_cast hcast

theorem eventual_all_imbalance_moments (A : CenteredArray Ω) (hgap : A.CompactGap) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ c θ a : ℝ, 0 < θ → 0 < a →
      (∫ ω,exponentialTest 1 θ
        (a*(integerSum (A.Y n) (A.N n) ω).natAbs)
        (c+continuousSum (A.X n) (A.N n) ω)
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) ≤
        (2*C/(A.N n : ℝ))*(3/θ^2+2/θ)/(1-Real.exp (-θ*a)) ∧
      (∫ ω,exponentialTest 2 θ
        (a*(integerSum (A.Y n) (A.N n) ω).natAbs)
        (c+continuousSum (A.X n) (A.N n) ω)
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) ≤
        (2*C/(A.N n : ℝ))*(10/θ^3+4/θ^2)/(1-Real.exp (-θ*a)) := by
  obtain ⟨C,hC,he⟩ := eventual_all_cells_exponential_bounds A hgap
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with n hn
  intro c θ a hθ ha
  let μ := Measure.pi (fun _ : Fin (A.N n) => A.law n)
  let W := fun ω => c+continuousSum (A.X n) (A.N n) ω
  let Y := integerSum (A.Y n) (A.N n)
  have hW : Measurable W := measurable_const.add (measurable_continuousSum (A.measurable_X n) _)
  have hY : Measurable Y := measurable_integerSum (A.measurable_Y n) _
  have hb := product_coordinate_bounds A n c
  have hc (k : ℕ) (y : ℤ) :
      (∫ ω,exponentialTest 1 θ (a*k) (W ω)*(if Y ω=y then (1 : ℝ) else 0) ∂μ) ≤
        (C/(A.N n : ℝ)*(3/θ^2+2/θ))*(Real.exp (-θ*a))^k ∧
      (∫ ω,exponentialTest 2 θ (a*k) (W ω)*(if Y ω=y then (1 : ℝ) else 0) ∂μ) ≤
        (C/(A.N n : ℝ)*(10/θ^3+4/θ^2))*(Real.exp (-θ*a))^k := by
    have hh := hn c 0 y θ (a*k) hθ
    have hp : Real.exp (-(θ*(a*(k : ℝ))))=(Real.exp (-θ*a))^k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [integral_productCell _ (A.measurable_X n) (A.measurable_Y n) _ c 0 y
      (measurable_exponentialTest 1 θ (a*k)),
      integral_productCell _ (A.measurable_X n) (A.measurable_Y n) _ c 0 y
      (measurable_exponentialTest 2 θ (a*k))] at hh
    simp only [zero_add,hp] at hh
    constructor
    · simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.2.1
    · simpa only [mul_assoc,mul_comm,mul_left_comm] using hh.2.2
  have hfirst := all_imbalance_bound μ hW hY (by positivity) hθ ha
    (show 0 ≤ C/(A.N n : ℝ)*(3/θ^2+2/θ) by positivity)
    (hb.mono fun _ h => h.1) (A.N n) (hb.mono fun _ h => h.2) 1
    (fun k y => (hc k y).1)
  have hsecond := all_imbalance_bound μ hW hY (by positivity) hθ ha
    (show 0 ≤ C/(A.N n : ℝ)*(10/θ^3+4/θ^2) by positivity)
    (hb.mono fun _ h => h.1) (A.N n) (hb.mono fun _ h => h.2) 2
    (fun k y => (hc k y).2)
  constructor
  · convert! hfirst using 1
    ring
  · convert! hsecond using 1
    ring

end FCAppendix.Affine.Uniform06.AllImbalanceMoments
