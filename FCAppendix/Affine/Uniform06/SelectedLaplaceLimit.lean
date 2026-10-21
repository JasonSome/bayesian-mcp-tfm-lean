import FCAppendix.Affine.Uniform06.StrictLaplaceLLT
import FCAppendix.Affine.Uniform06.PathNumerator

noncomputable section
namespace FCAppendix.Affine.Uniform06.SelectedLaplaceLimit

open MeasureTheory Set Filter
open scoped Topology BigOperators
open MixedIntervalLLT FiniteMarkedExchangeability RawMarkedLaplace
open ArrayRecount StrictLaplaceLLT

variable {Ω : Type*} [MeasurableSpace Ω]

def numeratorMoment (μ : Measure Ω) (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (N : ℕ) (cap θ : ℝ) (y : ℤ) (r k : ℕ) : ℝ :=
  (∫ ω : Fin N → Ω,∑ f : Fin k ↪ Fin N,
    markedFunctional X h w Y cap θ y r ω (fun j => ω (f j))
      ∂Measure.pi (fun _ : Fin N => μ))/(N:ℝ)^k

theorem numeratorMoment_factorization (μ : Measure Ω) [IsFiniteMeasure μ]
    (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hX : Measurable X) (hh : Measurable h) (hw : Measurable w) (hY : Measurable Y)
    (hbX : ∀ x,X x ∈ Icc (0:ℝ) 1) (hbh : ∀ x,|h x| ≤ 1)
    (hbw : ∀ x,w x ∈ Icc (0:ℝ) 1)
    (hbal : ∀ x,w x ≠ 0 → X x+h x=1/2 ∧ Y x=0)
    (cap θ : ℝ) (y : ℤ) (r k N : ℕ) :
    numeratorMoment μ X h w Y (k+N) cap θ y r k=
      (((k+N).descFactorial k:ℝ)/(k+N:ℝ)^k)*
        (∫ x,w x*Real.exp (-θ*h x) ∂μ)^k*
        ∫ ω : Fin N → Ω,laplace X Y (cap-(k:ℝ)/2) θ y r ω
          ∂Measure.pi (fun _ : Fin N => μ) := by
  rw [numeratorMoment,literal_distinct_laplace_identity μ X h w Y hbal cap θ y r k N
    (fun f => integrable_markedFunctional μ hX hh hw hY hbX hbh hbw cap θ y r f)]
  rw [Nat.cast_add]
  ring

theorem distinct_numerator_moments (A : CenteredArray Ω) (hgap : A.CompactGap)
    (U h w : ℕ → Ω → ℝ) (r cap θn : ℕ → ℝ)
    (hU : ∀ n,Measurable (U n)) (hh : ∀ n,Measurable (h n))
    (hw : ∀ n,Measurable (w n))
    (hbU : ∀ n x,U n x ∈ Icc (0:ℝ) 1)
    (hbh : ∀ n x,|h n x| ≤ 1) (hbw : ∀ n x,w n x ∈ Icc (0:ℝ) 1)
    (hbal : ∀ n x,w n x ≠ 0 → U n x+h n x=1/2 ∧ A.Y n x=0)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hmatch : ∀ᶠ n in atTop,cap n=(A.N n:ℝ)*r n)
    (k : ℕ) (y : ℤ) {θ lo hi a : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n,lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ)
    (hmean : Tendsto (fun n => ∫ x,w n x*Real.exp (-θn n*h n x) ∂A.law n)
      atTop (𝓝 a)) :
    Tendsto (fun n => (A.N n:ℝ)*numeratorMoment (A.law n) (U n) (h n) (w n)
      (A.Y n) (A.N n) (cap n) (θn n) y 0 k)
        atTop (𝓝 (a^k*(density A.vX A.vY/θ))) ∧
    Tendsto (fun n => (A.N n:ℝ)*numeratorMoment (A.law n) (U n) (h n) (w n)
      (A.Y n) (A.N n) (cap n) (θn n) y 1 k)
        atTop (𝓝 (a^k*(density A.vX A.vY/θ^2))) ∧
    Tendsto (fun n => (A.N n:ℝ)*numeratorMoment (A.law n) (U n) (h n) (w n)
      (A.Y n) (A.N n) (cap n) (θn n) y 2 k)
        atTop (𝓝 (a^k*(density A.vX A.vY*(2/θ^3)))) := by
  have hm := deleted_laplace_moments A hgap U hU r cap θn hr hcenter hmatch k y
    hlo hbracket hθn hθ
  have hf := (descFactorial_ratio A.N A.market k).mul (hmean.pow k)
  have he (q : ℕ) : ∀ᶠ n in atTop,
      (A.N n:ℝ)*numeratorMoment (A.law n) (U n) (h n) (w n) (A.Y n)
        (A.N n) (cap n) (θn n) y q k=
      (((A.N n).descFactorial k:ℝ)/(A.N n:ℝ)^k)*
        (∫ x,w n x*Real.exp (-θn n*h n x) ∂A.law n)^k*
        ((A.N n:ℝ)*∫ ω : Fin (remaining A k n) → Ω,
          laplace (U n) (A.Y n) (cap n-(k:ℝ)/2) (θn n) y q ω
            ∂Measure.pi (fun _ : Fin (remaining A k n) => A.law n)) := by
    filter_upwards [remaining_eventually A k] with n hn
    have hfactor := numeratorMoment_factorization (A.law n) (U n) (h n) (w n) (A.Y n)
      (hU n) (hh n) (hw n) (A.measurable_Y n) (hbU n) (hbh n) (hbw n) (hbal n)
      (cap n) (θn n) y q k (remaining A k n)
    rw [hn] at hfactor
    have hcast : (k:ℝ)+(remaining A k n:ℝ)=(A.N n:ℝ) := by exact_mod_cast hn
    rw [hcast] at hfactor
    rw [hfactor]
    ring
  refine ⟨?_,?_,?_⟩
  · simpa only [one_mul] using (hf.mul hm.1).congr' (Filter.EventuallyEq.symm (he 0))
  · simpa only [one_mul] using (hf.mul hm.2.1).congr' (Filter.EventuallyEq.symm (he 1))
  · simpa only [one_mul] using (hf.mul hm.2.2).congr' (Filter.EventuallyEq.symm (he 2))

end FCAppendix.Affine.Uniform06.SelectedLaplaceLimit
