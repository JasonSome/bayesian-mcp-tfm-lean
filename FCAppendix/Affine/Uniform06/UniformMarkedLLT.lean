import FCAppendix.Affine.Uniform06.MixedIntervalLLT
import FCAppendix.Affine.Uniform06.MarkedRows

noncomputable section
namespace FCAppendix.Affine.Uniform06.UniformMarkedLLT

open MeasureTheory Filter Set
open scoped Topology
open MixedIntervalLLT MixedProductCharacteristic MixedCellSmoothing IntervalRecovery

theorem eventually_uniform_of_all_sequences {α : Type*}
    (P : ℕ → α → Prop) (F : ℕ → α → ℝ) (L : ℝ)
    (a₀ : ℕ → α) (ha₀ : ∀ n, P n (a₀ n))
    (hlim : ∀ a : ℕ → α, (∀ n, P n (a n)) →
      Tendsto (fun n => F n (a n)) atTop (𝓝 L)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ a, P n a → |F n a-L| < ε := by
  classical
  intro ε hε
  let bad : ℕ → Prop := fun n => ∃ a, P n a ∧ ¬ |F n a-L| < ε
  let a : ℕ → α := fun n => if h : bad n then h.choose else a₀ n
  have ha : ∀ n, P n (a n) := by
    intro n
    by_cases h : bad n
    · simpa only [a,dif_pos h] using h.choose_spec.1
    · simpa only [a,dif_neg h] using ha₀ n
  have he : ∀ᶠ n in atTop, |F n (a n)-L| < ε := by
    have hh := (Metric.tendsto_nhds.mp (hlim a ha)) ε hε
    simpa only [Real.dist_eq] using hh
  filter_upwards [he] with n hn
  intro b hb
  by_contra hbad
  have h : bad n := ⟨b,hb,hbad⟩
  have hh : ¬ |F n (a n)-L| < ε := by
    simpa only [a,dif_pos h] using h.choose_spec.2
  exact hh hn

lemma bounded_multiplier_tendsto_zero {d c : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hd : Tendsto d atTop (𝓝 0)) (hc : ∀ n, |c n| ≤ C) :
    Tendsto (fun n => d n*c n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC1 : 0 < C+1 := by linarith
  have he := (Metric.tendsto_nhds.mp hd) (ε/(C+1)) (div_pos hε hC1)
  filter_upwards [he] with n hn
  simp only [Real.dist_eq,sub_zero] at hn ⊢
  calc
    |d n*c n| = |d n| *|c n| := abs_mul _ _
    _ ≤ |d n| *(C+1) :=
      mul_le_mul_of_nonneg_left ((hc n).trans (by linarith)) (abs_nonneg _)
    _ < ε/(C+1)*(C+1) := mul_lt_mul_of_pos_right hn hC1
    _ = ε := div_mul_cancel₀ _ hC1.ne'

variable {Ω : Type*} [MeasurableSpace Ω]

theorem interval_limit_uniform_in_bounded_shifts (A : CenteredArray Ω)
    (hgap : A.CompactGap) {C J a b : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) (hab : a ≤ b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ c : ℝ, |c| ≤ C → ∀ y : ℤ, |(y : ℝ)| ≤ J →
        |(A.N n : ℝ) * intervalMass
          (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c 0 y) a b -
            (b-a)*density A.vX A.vY| < ε := by
  have hlim : ∀ p : ℕ → ℝ × ℤ,
      (∀ n, |(p n).1| ≤ C ∧ |((p n).2 : ℝ)| ≤ J) →
      Tendsto (fun n => (A.N n : ℝ)*intervalMass
        (productCell (A.law n) (A.X n) (A.Y n) (A.N n) (p n).1 0 (p n).2) a b)
          atTop (𝓝 ((b-a)*density A.vX A.vY)) := by
    intro p hp
    have hc : Tendsto (fun n => A.d n*(p n).1) atTop (𝓝 0) :=
      bounded_multiplier_tendsto_zero hC A.d_zero (fun n => (hp n).1)
    have hy : Tendsto (fun n => A.d n*((0 : ℤ)-(p n).2 : ℤ)) atTop (𝓝 0) := by
      apply bounded_multiplier_tendsto_zero hJ A.d_zero
      intro n
      simpa only [zero_sub,Int.cast_neg,abs_neg] using (hp n).2
    convert! tendsto_scaled_interval A hgap (fun n => (p n).1) (fun _ => 0)
      (fun n => (p n).2) hc hy hab using 1
    funext n
    rw [intervalMass_eq_measure]
    rfl
  have hu := eventually_uniform_of_all_sequences
    (fun (_ : ℕ) (p : ℝ × ℤ) => |p.1| ≤ C ∧ |(p.2 : ℝ)| ≤ J)
    (fun n (p : ℝ × ℤ) => (A.N n : ℝ)*intervalMass
      (productCell (A.law n) (A.X n) (A.Y n) (A.N n) p.1 0 p.2) a b)
    ((b-a)*density A.vX A.vY) (fun _ => (0,0))
    (fun _ => by simp only [abs_zero,Int.cast_zero]; exact ⟨hC,hJ⟩) hlim
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro c hc y hy
  exact hn (c,y) ⟨hc,hy⟩

theorem relative_interval_uniform_in_bounded_shifts (A : CenteredArray Ω)
    (hgap : A.CompactGap) {C J a b : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) (hab : a < b) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ c : ℝ, |c| ≤ C → ∀ y : ℤ, |(y : ℝ)| ≤ J →
        |intervalMass
          (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c 0 y) a b /
            ((b-a)*density A.vX A.vY/(A.N n : ℝ))-1| < ε := by
  intro ε hε
  have hL : 0 < (b-a)*density A.vX A.vY :=
    mul_pos (sub_pos.mpr hab) (density_pos A.vX_pos A.vY_pos)
  filter_upwards [interval_limit_uniform_in_bounded_shifts A hgap hC hJ hab.le
    (ε*((b-a)*density A.vX A.vY)) (mul_pos hε hL)] with n hn
  intro c hc y hy
  have he := hn c hc y hy
  have hN := A.N_pos n
  have hid₀ (v L N : ℝ) (hL : L ≠ 0) (hN : N ≠ 0) :
      v/(L/N)-1=(N*v-L)/L := by
    field_simp [hL,hN]
  have hid (v : ℝ) :
      v/((b-a)*density A.vX A.vY/(A.N n : ℝ))-1 =
        ((A.N n : ℝ)*v-(b-a)*density A.vX A.vY)/((b-a)*density A.vX A.vY) := by
    exact hid₀ v _ _ hL.ne' hN.ne'
  rw [hid,abs_div,abs_of_pos hL]
  exact (div_lt_iff₀ hL).mpr he

theorem full_row_scale_after_fixed_prefix (A : CenteredArray Ω)
    (hgap : A.CompactGap) (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n*c n) atTop (𝓝 0))
    (hy : Tendsto (fun n => A.d n*((j n-y n : ℤ) : ℝ)) atTop (𝓝 0))
    (r : ℕ) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => ((A.N n+r : ℕ) : ℝ)*intervalMass (A.cell c j y n) a b)
      atTop (𝓝 ((b-a)*density A.vX A.vY)) := by
  have hN : Tendsto (fun n => (A.N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp A.market
  have hinv : Tendsto (fun n => (A.N n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hN
  have hratio : Tendsto (fun n => 1+(r : ℝ)/(A.N n : ℝ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      tendsto_const_nhds.add (hinv.const_mul (r : ℝ))
  have hh := hratio.mul (tendsto_scaled_interval A hgap c j y hc hy hab)
  simp_rw [intervalMass_eq_measure]
  convert! hh using 1
  · funext n
    push_cast
    field_simp [(A.N_pos n).ne']
  · ring

end FCAppendix.Affine.Uniform06.UniformMarkedLLT
