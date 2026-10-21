import FCAppendix.Affine.Uniform06.EntryActiveMoments
import FCAppendix.Probability.EmpiricalMean

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryEmpiricalRatio
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Probability
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def empirical (f : Ω → ℝ) (N : ℕ) (r : Fin N → Ω) : ℝ :=
  (∑ i, f (r i))/(N : ℝ)

lemma measurable_empirical {f : Ω → ℝ} (hf : Measurable f) (N : ℕ) :
    Measurable (empirical f N) :=
  (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))).div_const _

omit [MeasurableSpace Ω] in
lemma abs_empirical_le {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ ω, |f ω| ≤ A) (N : ℕ) (r : Fin N → Ω) :
    |empirical f N r| ≤ A := by
  by_cases hN : N=0
  · subst N
    simp [empirical,hA]
  · have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [empirical,abs_div,abs_of_pos hNp]
    apply (div_le_iff₀ hNp).mpr
    calc
      |∑ i, f (r i)| ≤ ∑ i, |f (r i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, A := Finset.sum_le_sum fun i _ => hf (r i)
      _ = A*(N : ℝ) := by simp [mul_comm]

lemma abs_empirical_le_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (hf : ∀ᵐ ω ∂μ, |f ω| ≤ A) (N : ℕ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => μ), |empirical f N r| ≤ A := by
  have hcoord (i : Fin N) :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hf
  filter_upwards [ae_all_iff.mpr hcoord] with r hr
  by_cases hN : N=0
  · subst N
    simp [empirical,hA]
  · have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [empirical,abs_div,abs_of_pos hNp]
    apply (div_le_iff₀ hNp).mpr
    calc
      |∑ i, f (r i)| ≤ ∑ i, |f (r i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, A := Finset.sum_le_sum fun i _ => hr i
      _ = A*(N : ℝ) := by simp [mul_comm]

lemma integrable_empirical (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ A) (N : ℕ) :
    Integrable (empirical f N) (Measure.pi (fun _ : Fin N => μ)) :=
  Integrable.of_bound (measurable_empirical hf N).aestronglyMeasurable A
    ((abs_empirical_le_ae μ hA hb N).mono fun _ h => by simpa only [Real.norm_eq_abs] using h)

theorem empirical_L1_tendsto (μ : ℕ → Measure Ω) [∀ m, IsProbabilityMeasure (μ m)]
    (f : ℕ → Ω → ℝ) (hf : ∀ m, Measurable (f m)) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ m, ∀ᵐ ω ∂μ m, |f m ω| ≤ A) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {a : ℝ} (ha : Tendsto (fun m => ∫ ω, f m ω ∂μ m) atTop (𝓝 a)) :
    Tendsto (fun m => ∫ r, |empirical (f m) (N m) r-a|
      ∂Measure.pi (fun _ : Fin (N m) => μ m)) atTop (𝓝 0) := by
  have hdev := iid_empiricalMean_L1_tendsto_zero μ f (fun m => (hf m).aestronglyMeasurable)
    A hA hb N hN
  have hrhs : Tendsto (fun m => (∫ r,
      |empirical (f m) (N m) r-(∫ ω, f m ω ∂μ m)|
        ∂Measure.pi (fun _ : Fin (N m) => μ m))+|((∫ ω, f m ω ∂μ m)-a)|)
      atTop (𝓝 0) := by
    simpa [empirical] using hdev.add ((ha.sub_const a).abs)
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) ?_ hrhs
  intro m
  have hI := integrable_empirical (μ m) (hf m) hA (hb m) (N m)
  have hbnd := integral_mono ((hI.sub (integrable_const a)).abs)
    (((hI.sub (integrable_const _)).abs).add (integrable_const _)) (fun r =>
      abs_sub_le (empirical (f m) (N m) r) (∫ ω, f m ω ∂μ m) a)
  have hsplit := integral_add ((hI.sub (integrable_const (∫ ω, f m ω ∂μ m))).abs)
    (integrable_const |(∫ ω, f m ω ∂μ m)-a|)
  simp only [Pi.add_apply,Pi.sub_apply] at hbnd hsplit
  rw [hsplit,integral_const,probReal_univ,one_smul] at hbnd
  exact hbnd

def guardedRatio (c : ℝ) (w g : Ω → ℝ) (N : ℕ) (r : Fin N → Ω) : ℝ :=
  empirical g N r/max c (empirical w N r)

lemma measurable_guardedRatio (c : ℝ) {w g : Ω → ℝ}
    (hw : Measurable w) (hg : Measurable g) (N : ℕ) :
    Measurable (guardedRatio c w g N) :=
  (measurable_empirical hg N).div (measurable_const.max (measurable_empirical hw N))

lemma ratio_error_bound {c d a u v : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    |u/max c v-a/d| ≤ |u-a| /c+|a| *|v-d| /(c*d) := by
  let q := max c v
  have hq : 0 < q := hc.trans_le (le_max_left _ _)
  have hd : 0 < d := hc.trans_le hcd
  have hmax : |q-d| ≤ |v-d| := by
    have hh := abs_max_sub_max_le_abs v d c
    simpa only [q,max_comm c v,max_eq_left hcd] using hh
  have he : u/q-a/d=(u-a)/q+a*(d-q)/(q*d) := by
    field_simp [hq.ne',hd.ne']
    ring
  calc
    _ ≤ |u-a| /q+|a| *|q-d| /(q*d) := by
      rw [he]
      apply (abs_add_le _ _).trans_eq
      rw [abs_div,abs_div,abs_mul,abs_sub_comm d q,abs_of_pos hq,
        abs_of_pos (mul_pos hq hd)]
    _ ≤ |u-a| /c+|a| *|v-d| /(c*d) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (abs_nonneg _) hc (le_max_left _ _)
      · apply (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmax (abs_nonneg a)) (mul_pos hq hd).le).trans
        exact div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_pos hc hd) (mul_le_mul_of_nonneg_right (le_max_left _ _) hd.le)

omit [MeasurableSpace Ω] in

theorem guardedRatio_eq_weightedMean {c : ℝ} {w h : Ω → ℝ} {N : ℕ}
    (hN : 0 < N) (r : Fin N → Ω) (hguard : c*(N : ℝ) ≤ ∑ i, w (r i)) :
    guardedRatio c w (fun ω => w ω*h ω) N r=
      (∑ i, w (r i)*h (r i))/(∑ i, w (r i)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : c ≤ empirical w N r := (le_div_iff₀ hNr).mpr hguard
  rw [guardedRatio,max_eq_right hc,empirical,empirical]
  by_cases hs : (∑ i, w (r i))=0
  · simp [hs]
  · field_simp [hNr.ne',hs]

theorem guardedRatio_L1_tendsto (μ : ℕ → Measure Ω) [∀ m, IsProbabilityMeasure (μ m)]
    (w g : ℕ → Ω → ℝ) (hw : ∀ m, Measurable (w m)) (hg : ∀ m, Measurable (g m))
    {W G : ℝ} (hW : 0 ≤ W) (hG : 0 ≤ G)
    (hwb : ∀ m, ∀ᵐ ω ∂μ m, |w m ω| ≤ W)
    (hgb : ∀ m, ∀ᵐ ω ∂μ m, |g m ω| ≤ G)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) {c d a : ℝ}
    (hc : 0 < c) (hcd : c ≤ d)
    (hwlim : Tendsto (fun m => ∫ ω, w m ω ∂μ m) atTop (𝓝 d))
    (hglim : Tendsto (fun m => ∫ ω, g m ω ∂μ m) atTop (𝓝 a)) :
    Tendsto (fun m => ∫ r, |guardedRatio c (w m) (g m) (N m) r-a/d|
      ∂Measure.pi (fun _ : Fin (N m) => μ m)) atTop (𝓝 0) := by
  have hwL := empirical_L1_tendsto μ w hw hW hwb N hN hwlim
  have hgL := empirical_L1_tendsto μ g hg hG hgb N hN hglim
  have hrhs : Tendsto (fun m =>
      (∫ r, |empirical (g m) (N m) r-a| ∂Measure.pi (fun _ : Fin (N m) => μ m))/c+
      |a| /(c*d)*(∫ r, |empirical (w m) (N m) r-d| ∂Measure.pi (fun _ : Fin (N m) => μ m)))
      atTop (𝓝 0) := by simpa using (hgL.div_const c).add (hwL.const_mul (|a| /(c*d)))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) ?_ hrhs
  intro m
  have hgi := integrable_empirical (μ m) (hg m) hG (hgb m) (N m)
  have hwi := integrable_empirical (μ m) (hw m) hW (hwb m) (N m)
  have hri : Integrable (guardedRatio c (w m) (g m) (N m))
      (Measure.pi (fun _ : Fin (N m) => μ m)) := by
    apply Integrable.of_bound (measurable_guardedRatio c (hw m) (hg m) (N m)).aestronglyMeasurable (G/c)
    filter_upwards [abs_empirical_le_ae (μ m) hG (hgb m) (N m)] with r hr
    rw [Real.norm_eq_abs,guardedRatio,abs_div,abs_of_pos (hc.trans_le (le_max_left _ _))]
    exact (div_le_div_of_nonneg_right hr (hc.trans_le (le_max_left _ _)).le).trans
      (div_le_div_of_nonneg_left hG hc (le_max_left _ _))
  have hi1 := ((hgi.sub (integrable_const a)).abs).div_const c
  have hi2 := ((hwi.sub (integrable_const d)).abs).const_mul (|a| /(c*d))
  have hpoint (r : Fin (N m) → Ω) :
      |guardedRatio c (w m) (g m) (N m) r-a/d| ≤
        |empirical (g m) (N m) r-a|/c+|a|/(c*d)*|empirical (w m) (N m) r-d| := by
    have hh := FCAppendix.Affine.Uniform06.EntryEmpiricalRatio.ratio_error_bound
      (c := c) (d := d) (a := a) (u := empirical (g m) (N m) r)
      (v := empirical (w m) (N m) r) hc hcd
    convert! hh using 1
    ring
  have hbnd := integral_mono ((hri.sub (integrable_const (a/d))).abs) (hi1.add hi2) hpoint
  have hsplit := integral_add hi1 hi2
  simp only [Pi.add_apply,Pi.sub_apply] at hbnd hsplit
  rw [hsplit] at hbnd
  simpa only [integral_div,integral_const_mul] using hbnd

theorem bounded_error_fourth_tendsto
    {Ξ : ℕ → Type*} [∀ m, MeasurableSpace (Ξ m)]
    (P : (m : ℕ) → Measure (Ξ m)) [∀ m, IsProbabilityMeasure (P m)]
    (e : (m : ℕ) → Ξ m → ℝ) (he : ∀ m, Measurable (e m)) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ m, ∀ᵐ ω ∂P m, |e m ω| ≤ C)
    (hL : Tendsto (fun m => ∫ ω, |e m ω| ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, (e m ω)^4 ∂P m) atTop (𝓝 0) := by
  have hi1 m : Integrable (fun ω => |e m ω|) (P m) :=
    Integrable.of_bound (he m).abs.aestronglyMeasurable C
      ((hb m).mono fun _ h => by simpa only [Real.norm_eq_abs,abs_abs] using h)
  have hi4 m : Integrable (fun ω => (e m ω)^4) (P m) := by
    apply Integrable.of_bound ((he m).pow_const 4).aestronglyMeasurable (C^4)
    filter_upwards [hb m] with ω hω
    rw [Real.norm_eq_abs,abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 4
  apply squeeze_zero (fun _ => integral_nonneg fun _ => by positivity) ?_
    (by simpa using hL.const_mul (C^3))
  intro m
  rw [← integral_const_mul]
  apply integral_mono_ae (hi4 m) ((hi1 m).const_mul _)
  filter_upwards [hb m] with ω hω
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hω 3) (abs_nonneg (e m ω))
  have he4 : |e m ω|^4=(e m ω)^4 := by
    rw [show (4 : ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
  nlinarith [he4]

end FCAppendix.Affine.Uniform06.EntryEmpiricalRatio
