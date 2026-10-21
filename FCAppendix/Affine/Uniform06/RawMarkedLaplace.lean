import FCAppendix.Affine.Uniform06.FiniteMarkedExchangeability
import FCAppendix.Affine.Uniform06.RawTiltedSource

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawMarkedLaplace

open MeasureTheory Set LowBody
open scoped BigOperators
open Uniform07 RawMixedSource RawTiltedSource LiteralExperiment
open FiniteMarkedExchangeability

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_markedFunctional {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ} (f : Fin k → Fin N) :
    Measurable (fun ω : Fin N → Ω => markedFunctional X h w Y cap θ y r ω
      (fun j => ω (f j))) := by
  have hx : Measurable (fun ω : Fin N → Ω => sumX X ω) :=
    Finset.measurable_sum Finset.univ (fun j _ => hX.comp (measurable_pi_apply j))
  have hy : Measurable (fun ω : Fin N → Ω => sumY Y ω) :=
    Finset.measurable_sum Finset.univ (fun j _ => hY.comp (measurable_pi_apply j))
  have hs : Measurable (fun ω : Fin N → Ω => ∑ j : Fin k, h (ω (f j))) :=
    Finset.measurable_sum Finset.univ
    (fun j _ => hh.comp (measurable_pi_apply (f j)))
  have hp : Measurable (fun ω : Fin N → Ω => ∏ j : Fin k, w (ω (f j))) :=
    Finset.measurable_prod Finset.univ
    (fun j _ => hw.comp (measurable_pi_apply (f j)))
  have hD : Measurable (fun ω : Fin N → Ω => cap-sumX X ω-∑ j : Fin k, h (ω (f j))) :=
    (measurable_const.sub hx).sub hs
  unfold markedFunctional sumX sumY
  exact hp.mul (Measurable.ite ((measurableSet_eq_fun hy measurable_const).inter
    (measurableSet_lt measurable_const hD))
    (((measurable_const.sub hx).const_mul (-θ)).exp.mul (hD.pow_const r)) measurable_const)

omit [MeasurableSpace Ω] in
lemma markedFunctional_bound {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : ∀ x,X x ∈ Icc (0:ℝ) 1) (hh : ∀ x,|h x| ≤ 1)
    (hw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ}
    (ω : Fin N → Ω) (marks : Fin k → Ω) :
    |markedFunctional X h w Y cap θ y r ω marks| ≤
      Real.exp (|θ| *(|cap|+(N:ℝ)))*(|cap|+(N:ℝ)+(k:ℝ))^r := by
  classical
  have hx0 : 0 ≤ sumX X ω := Finset.sum_nonneg (fun j _ => (hX (ω j)).1)
  have hx1 : sumX X ω ≤ (N:ℝ) := by
    simpa [sumX] using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => (hX (ω j)).2)
  have hh1 : |sumX h marks| ≤ (k:ℝ) := by
    calc
      _ ≤ ∑ j,|h (marks j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin k,(1:ℝ) := Finset.sum_le_sum (fun j _ => hh (marks j))
      _ = _ := by simp
  have hW : |cap-sumX X ω| ≤ |cap|+(N:ℝ) := by
    exact (abs_sub _ _).trans (add_le_add le_rfl (by simpa only [abs_of_nonneg hx0] using hx1))
  have hD : |cap-sumX X ω-sumX h marks| ≤ |cap|+(N:ℝ)+(k:ℝ) :=
    (abs_sub _ _).trans (add_le_add hW hh1)
  have hp0 : 0 ≤ ∏ j,w (marks j) := Finset.prod_nonneg (fun j _ => (hw (marks j)).1)
  have hp1 : (∏ j,w (marks j)) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (hw (marks j)).1) (fun j _ => (hw (marks j)).2)
  have he : Real.exp (-θ*(cap-sumX X ω)) ≤ Real.exp (|θ| *(|cap|+(N:ℝ))) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |-θ*(cap-sumX X ω)| := le_abs_self _
      _ = |θ| *|cap-sumX X ω| := by rw [abs_mul,abs_neg]
      _ ≤ _ := mul_le_mul_of_nonneg_left hW (abs_nonneg _)
  unfold markedFunctional
  split_ifs with hc
  · rw [abs_mul,abs_of_nonneg hp0,abs_mul,abs_of_pos (Real.exp_pos _),abs_pow]
    have hp := pow_le_pow_left₀ (abs_nonneg _) hD r
    have hmain := mul_le_mul he hp (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le
    exact (mul_le_mul_of_nonneg_left hmain hp0).trans
      (by simpa using mul_le_mul_of_nonneg_right hp1 (by positivity :
        0 ≤ Real.exp (|θ| *(|cap|+(N:ℝ)))*(|cap|+(N:ℝ)+(k:ℝ))^r))
  · simp only [mul_zero,abs_zero]
    positivity

theorem integrable_markedFunctional (μ : Measure Ω) [IsFiniteMeasure μ]
    {X h w : Ω → ℝ} {Y : Ω → ℤ}
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (hXb : ∀ x,X x ∈ Icc (0:ℝ) 1) (hhb : ∀ x,|h x| ≤ 1)
    (hwb : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ} (f : Fin k → Fin N) :
    Integrable (fun ω : Fin N → Ω => markedFunctional X h w Y cap θ y r ω
      (fun j => ω (f j))) (Measure.pi (fun _ : Fin N => μ)) := by
  apply Integrable.of_bound (measurable_markedFunctional hX hh hw hY cap θ y r f).aestronglyMeasurable
    (Real.exp (|θ| *(|cap|+(N:ℝ)))*(|cap|+(N:ℝ)+(k:ℝ))^r)
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using markedFunctional_bound hXb hhb hwb cap θ y r ω
      (fun j => ω (f j))

def rawWeight (ξ : ℝ) (g : GuardData) (r : RowRival) : ℝ :=
  if r.1=0 then FiniteGuards.eligibility ξ g.multiplier g.requiredDemand r.2 else 0

def rawH (ξ b : ℝ) (r : RowRival) : ℝ := 1/2-RawMixedSource.demand ξ b r

theorem rawWeight_bounds (ξ : ℝ) (g : GuardData) (r : RowRival) :
    rawWeight ξ g r ∈ Icc (0:ℝ) 1 := by
  unfold rawWeight
  split_ifs
  · exact FiniteGuards.eligibility_bounds _ _ _ _
  · norm_num

theorem measurable_rawWeight (ξ : ℝ) (g : GuardData) : Measurable (rawWeight ξ g) := by
  unfold rawWeight
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · unfold FiniteGuards.eligibility FiniteGuards.clip01 FCAppendix.Affine.ClippedResidual.exposure
    fun_prop
  · exact measurable_const

theorem measurable_rawH (ξ b : ℝ) : Measurable (rawH ξ b) :=
  measurable_const.sub (measurable_demand ξ b)

theorem raw_support (ξ b : ℝ) (g : GuardData) (r : RowRival)
    (hw : rawWeight ξ g r ≠ 0) :
    RawMixedSource.demand ξ b r+rawH ξ b r=1/2 ∧ RawTiltedSource.integerSign r=0 := by
  have htag : r.1=0 := by
    by_contra hn
    exact hw (by simp [rawWeight,hn])
  constructor
  · unfold rawH
    ring
  · simp [RawTiltedSource.integerSign,htag]

theorem actual_tilted_distinct_laplace (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b)
    (θ cap : ℝ) (g : GuardData) (y : ℤ) (r k N : ℕ) :
    (∫ ω : Fin (k+N) → RowRival,∑ f : Fin k ↪ Fin (k+N),
      markedFunctional (RawMixedSource.demand (xi i) b) (rawH (xi i) b)
        (rawWeight (xi i) g) RawTiltedSource.integerSign cap θ y r ω
          (fun j => ω (f j))
      ∂Measure.pi (fun _ : Fin (k+N) => tiltedSource i G b θ))=
      ((k+N).descFactorial k:ℝ)*
        (∫ x,rawWeight (xi i) g x*Real.exp (-θ*rawH (xi i) b x)
          ∂tiltedSource i G b θ)^k*
        ∫ row : Fin N → RowRival,
          laplace (RawMixedSource.demand (xi i) b) RawTiltedSource.integerSign
            (cap-(k:ℝ)/2) θ y r row
          ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ) := by
  letI := tiltedSource_probability i G hb θ
  apply literal_distinct_laplace_identity _ _ _ _ _ (raw_support (xi i) b g) cap θ y r k N
  intro f
  apply integrable_markedFunctional _ (measurable_demand _ _) (measurable_rawH _ _)
    (measurable_rawWeight _ _) measurable_integerSign
    (fun x => demand_bounds (xi_pos i) hb x) _ (rawWeight_bounds _ _) cap θ y r f
  intro x
  have hx := demand_bounds (xi_pos i) hb x
  unfold rawH
  rw [abs_le]
  constructor <;> linarith [hx.1,hx.2]

end FCAppendix.Affine.Uniform06.RawMarkedLaplace
