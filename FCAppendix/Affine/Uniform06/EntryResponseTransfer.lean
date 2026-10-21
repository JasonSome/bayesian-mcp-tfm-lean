import FCAppendix.Affine.Uniform06.EntryRandomReciprocal
import FCAppendix.Affine.Uniform06.EntryCentralReplacement

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryResponseTransfer

open MeasureTheory ProbabilityTheory Set Filter Topology
open EntryCentralReplacement EntryCentralPassage
open scoped BigOperators

def coefficient (N : ℕ) (b c k : ℝ) : ℝ := 1/(1/(N:ℝ)+b*max c k)

lemma clamp_error {c k κ : ℝ} (hc : c ≤ κ) : |max c k-κ| ≤ |k-κ| := by
  by_cases hk : c ≤ k
  · rw [max_eq_right hk]
  · rw [max_eq_left (le_of_not_ge hk),abs_of_nonpos (sub_nonpos.mpr hc),
      abs_of_nonpos (sub_nonpos.mpr ((le_of_not_ge hk).trans hc))]
    linarith

lemma coefficient_bounds {N : ℕ} {b c k lo : ℝ}
    (hlo : 0 < lo) (hb : lo ≤ b) (hc : 0 < c) :
    coefficient N b c k ∈ Ioc (0:ℝ) (1/(lo*c)) := by
  have hprod : lo*c ≤ b*max c k := mul_le_mul hb (le_max_left _ _) hc.le
    (hlo.trans_le hb).le
  have hden : lo*c ≤ 1/(N:ℝ)+b*max c k := by
    linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) N)]
  exact ⟨one_div_pos.mpr ((mul_pos hlo hc).trans_le hden),
    one_div_le_one_div_of_le (mul_pos hlo hc) hden⟩

lemma coefficient_error {N : ℕ} {b c k lo lam κ : ℝ}
    (hlo : 0 < lo) (hb : lo ≤ b) (hc : 0 < c)
    (hLam : 0 < lam) (hκ : 0 < κ) (hcκ : c ≤ κ) :
    |coefficient N b c k-1/(lam*κ)| ≤
      (1/(N:ℝ)+|b-lam| *κ+|b| *|k-κ|)/((lo*c)*(lam*κ)) := by
  let d := 1/(N:ℝ)+b*max c k
  have hb0 := hlo.trans_le hb
  have hdlo : lo*c ≤ d := by
    have hh := mul_le_mul hb (le_max_left c k) hc.le hb0.le
    dsimp [d]
    linarith [one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) N)]
  have hd : 0 < d := (mul_pos hlo hc).trans_le hdlo
  have hLamκ := mul_pos hLam hκ
  have he : |coefficient N b c k-1/(lam*κ)|=|d-lam*κ| /(d*(lam*κ)) := by
    unfold coefficient
    change |1/d-1/(lam*κ)|= _
    rw [div_sub_div _ _ hd.ne' hLamκ.ne',abs_div,abs_of_pos (mul_pos hd hLamκ),abs_sub_comm]
    simp only [one_mul,mul_one]
  have hdiff : |d-lam*κ| ≤ 1/(N:ℝ)+|b-lam| *κ+|b| *|k-κ| := by
    have hid : d-lam*κ=1/(N:ℝ)+(b-lam)*κ+b*(max c k-κ) := by dsimp[d]; ring
    rw [hid]
    calc
      _ ≤ |1/(N:ℝ)+(b-lam)*κ|+|b*(max c k-κ)| := abs_add_le _ _
      _ ≤ |1/(N:ℝ)|+|(b-lam)*κ|+|b*(max c k-κ)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 1/(N:ℝ)+|b-lam| *κ+|b| *|k-κ| := by
        rw [abs_of_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg (α := ℝ) N)),abs_mul,
          abs_of_pos hκ,abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (clamp_error hcκ) (abs_nonneg b))
  rw [he]
  exact (div_le_div_of_nonneg_right hdiff (mul_pos hd hLamκ).le).trans
    (div_le_div_of_nonneg_left (by positivity) (mul_pos (mul_pos hlo hc) hLamκ)
      (mul_le_mul_of_nonneg_right hdlo hLamκ.le))

section Arrays
variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
  (P : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]

theorem coefficient_L1 (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (b : ℕ → ℝ) {lo lam c κ : ℝ} (hlo : 0 < lo) (hLam : 0 < lam)
    (hblo : ∀ m, lo ≤ b m) (hb : Tendsto b atTop (𝓝 lam))
    (hc : 0 < c) (hκ : 0 < κ) (hcκ : c ≤ κ)
    (K : (m : ℕ) → Ω m → ℝ) (hKm : ∀ m, Measurable (K m))
    (hKi : ∀ m, Integrable (fun x => |K m x-κ|) (P m))
    (hK : Tendsto (fun m => ∫ x, |K m x-κ| ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, |coefficient (N m) (b m) c (K m x)-1/(lam*κ)| ∂P m)
      atTop (𝓝 0) := by
  have hm (m) : Measurable (fun x => coefficient (N m) (b m) c (K m x)) := by
    unfold coefficient
    fun_prop
  have hI m : Integrable (fun x => |coefficient (N m) (b m) c (K m x)-1/(lam*κ)|) (P m) := by
    apply Integrable.of_bound ((hm m).sub_const _).abs.aestronglyMeasurable
      (1/(lo*c)+|1/(lam*κ)|)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have hcoef := coefficient_bounds (N := N m) (k := K m x) hlo (hblo m) hc
      exact (abs_sub _ _).trans (add_le_add (by simpa only [abs_of_pos hcoef.1] using hcoef.2) le_rfl)
  have hNr : Tendsto (fun m => (N m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hi : Tendsto (fun m => 1/(N m:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using! tendsto_inv_atTop_zero.comp hNr
  have he := ((hi.add (((hb.sub_const lam).abs).mul_const κ)).add
    (hb.abs.mul hK)).div_const ((lo*c)*(lam*κ))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun m => ?_)
    (by simpa using he)
  have hR : Integrable (fun x => (1/(N m:ℝ)+|b m-lam| *κ+|b m| *|K m x-κ|)/
      ((lo*c)*(lam*κ))) (P m) :=
    ((integrable_const _).add ((hKi m).const_mul _)).div_const _
  have hh := integral_mono (hI m) hR
    (fun x => coefficient_error hlo (hblo m) hc hLam hκ hcκ)
  rw [integral_div,integral_add (integrable_const _) ((hKi m).const_mul _),
    integral_const,probReal_univ,one_smul,integral_const_mul] at hh
  simpa only [one_div] using! hh

theorem dependent_coefficient_L2
    (Z e : (m : ℕ) → Ω m → ℝ) (hZm : ∀ m, Measurable (Z m))
    (hem : ∀ m, Measurable (e m)) (L : ℕ → ℝ)
    (hZb : ∀ m x, |Z m x| ≤ L m) {C M : ℝ}
    (hC : 0 ≤ C) (heb : ∀ m x, |e m x| ≤ C)
    (hM : 0 ≤ M) (hZ4 : ∀ᶠ m in atTop, (∫ x, (Z m x)^4 ∂P m) ≤ M)
    (he : Tendsto (fun m => ∫ x, |e m x| ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, (Z m x*e m x)^2 ∂P m) atTop (𝓝 0) := by
  have he4 := EntryEmpiricalRatio.bounded_error_fourth_tendsto P e hem hC
    (fun m => Eventually.of_forall (heb m)) he
  apply tendsto_zero_of_parameter_bound _ (fun _ => 0)
    (fun m => (∫ x, (e m x)^4 ∂P m)/4) hM
    (fun _ => integral_nonneg fun _ => sq_nonneg _) tendsto_const_nhds
    (by simpa using he4.div_const 4)
  intro δ hδ
  filter_upwards [hZ4] with m hm
  have hh := integral_dependent_product (P m) (hZm m) (hem m) (hZb m) (heb m) hδ
  simp only [mul_pow] at hh ⊢
  calc
    _ ≤ δ*(∫ x, (Z m x)^4 ∂P m)+(∫ x, (e m x)^4 ∂P m)/(4*δ) := hh
    _ ≤ 0+δ*M+((∫ x, (e m x)^4 ∂P m)/4)/δ := by
      have hd := mul_le_mul_of_nonneg_left hm hδ.le
      have heq : (∫ x, (e m x)^4 ∂P m)/(4*δ)=((∫ x, (e m x)^4 ∂P m)/4)/δ := by ring
      rw [heq]
      linarith

lemma square_difference_bound (x y δ : ℝ) (hδ : 0 < δ) :
    |x^2-y^2| ≤ (x-y)^2+δ*y^2+(x-y)^2/δ := by
  have hcross : 2*|x-y| *|y| ≤ δ*y^2+(x-y)^2/δ := by
    have hh := sq_nonneg (δ*|y|-|x-y|)
    have hy := sq_abs y
    have he := sq_abs (x-y)
    have hmul : (2*|x-y| *|y|)*δ ≤ (δ*y^2+(x-y)^2/δ)*δ := by
      have heq : (δ*y^2+(x-y)^2/δ)*δ=δ^2*y^2+(x-y)^2 := by
        field_simp [hδ.ne']
      rw [heq]
      nlinarith
    exact (mul_le_mul_iff_left₀ hδ).mp hmul
  have he : x^2-y^2=(x-y)^2+2*(x-y)*y := by ring
  rw [he]
  have hh := abs_add_le ((x-y)^2) (2*(x-y)*y)
  rw [abs_of_nonneg (sq_nonneg (x-y)),abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hh
  linarith

theorem moments_of_L2
    (X Y : (m : ℕ) → Ω m → ℝ)
    (hX : ∀ m, MemLp (X m) 2 (P m)) (hY : ∀ m, MemLp (Y m) 2 (P m))
    {a b : ℝ} (ha : Tendsto (fun m => ∫ x, Y m x ∂P m) atTop (𝓝 a))
    (hb : Tendsto (fun m => ∫ x, (Y m x)^2 ∂P m) atTop (𝓝 b))
    (herr : Tendsto (fun m => ∫ x, (X m x-Y m x)^2 ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, X m x ∂P m) atTop (𝓝 a) ∧
    Tendsto (fun m => ∫ x, (X m x)^2 ∂P m) atTop (𝓝 b) := by
  have heI m := (hX m).sub (hY m)
  have he1 := L1_tendsto_of_L2 P _ heI herr
  have hfirst : Tendsto (fun m => |(∫ x, X m x ∂P m)-(∫ x, Y m x ∂P m)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun m => ?_) he1
    rw [← integral_sub ((hX m).integrable (by norm_num)) ((hY m).integrable (by norm_num))]
    exact abs_integral_le_integral_abs
  have hM : 0 ≤ |b|+1 := by positivity
  have hbound : ∀ᶠ m in atTop, (∫ x, (Y m x)^2 ∂P m) ≤ |b|+1 :=
    (hb.eventually_lt_const (by linarith [le_abs_self b])).mono fun _ h => h.le
  have hsnd : Tendsto (fun m => ∫ x, |(X m x)^2-(Y m x)^2| ∂P m) atTop (𝓝 0) := by
    apply tendsto_zero_of_parameter_bound _ _ _ hM
      (fun _ => integral_nonneg fun _ => abs_nonneg _) herr herr
    intro δ hδ
    filter_upwards [hbound] with m hm
    have hFi := ((hX m).integrable_sq.sub (hY m).integrable_sq).abs
    have hRi := ((heI m).integrable_sq.add ((hY m).integrable_sq.const_mul δ)).add
      ((heI m).integrable_sq.div_const δ)
    have hh := integral_mono hFi hRi (fun x => square_difference_bound (X m x) (Y m x) δ hδ)
    simp only [Pi.add_apply,Pi.sub_apply] at hh
    have hsum : Integrable (fun x => (X m x-Y m x)^2+δ*(Y m x)^2) (P m) :=
      (heI m).integrable_sq.add ((hY m).integrable_sq.const_mul δ)
    have htail : Integrable (fun x => (X m x-Y m x)^2/δ) (P m) := (heI m).integrable_sq.div_const δ
    have hsq : Integrable (fun x => (X m x-Y m x)^2) (P m) := (heI m).integrable_sq
    rw [integral_add hsum htail,integral_add hsq ((hY m).integrable_sq.const_mul δ),
      integral_const_mul,integral_div] at hh
    exact hh.trans (by linarith [mul_le_mul_of_nonneg_left hm hδ.le])
  have hsecond : Tendsto (fun m => |(∫ x, (X m x)^2 ∂P m)-(∫ x, (Y m x)^2 ∂P m)|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) (fun m => ?_) hsnd
    rw [← integral_sub (hX m).integrable_sq (hY m).integrable_sq]
    exact abs_integral_le_integral_abs
  exact ⟨EntryRawGoodMoments.tendsto_of_abs_sub_tendsto ha hfirst,
    EntryRawGoodMoments.tendsto_of_abs_sub_tendsto hb hsecond⟩

end Arrays
end FCAppendix.Affine.Uniform06.EntryResponseTransfer
