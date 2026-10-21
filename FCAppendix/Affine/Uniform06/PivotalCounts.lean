import FCAppendix.Affine.Uniform06.PureRankCounts
import FCAppendix.Affine.Uniform06.BinomialPivotal

noncomputable section
namespace FCAppendix.Affine.Uniform06.PivotalCounts

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem boundary_bad_relative
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E B : Set Ω) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hEB : Disjoint E B) (s : Finset ι) (r c : ℕ) (hc : 0 < c)
    {θ : ℝ} (hθ : 0 ≤ θ) (hE1 : μ.real E < 1) :
    (Measure.pi fun _ : ι => μ).real
      {ω | PiBinomial.count E s ω=r ∧ PiBinomial.count B s ω< c} ≤
      Real.exp (θ*(c-1:ℕ)-(s.card-r:ℕ)*
        (μ.real B/(1-μ.real E))*(1-Real.exp (-θ)))*
          PiBinomial.pmf s.card (μ.real E) r := by
  let P := Measure.pi fun _ : ι => μ
  let Ψ : (ι → Ω) → ℝ := fun ω =>
    if PiBinomial.count E s ω=r then Real.exp (-θ*PiBinomial.count B s ω) else 0
  let A : Set (ι → Ω) :=
    {ω | PiBinomial.count E s ω=r ∧ PiBinomial.count B s ω< c}
  have hAm : MeasurableSet A :=
    ((PiBinomial.measurable_count E hE s) (measurableSet_singleton r)).inter
      ((PiBinomial.measurable_count B hB s) (measurableSet_Iio (a := c)))
  have hΨm : Measurable Ψ :=
    Measurable.ite ((PiBinomial.measurable_count E hE s) (measurableSet_singleton r))
      (measurable_const.mul
        ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (PiBinomial.measurable_count B hB s))).exp measurable_const
  have hΨbounds (ω : ι → Ω) : 0 ≤ Ψ ω ∧ Ψ ω ≤ 1 := by
    dsimp only [Ψ]
    split_ifs
    · refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
      have hmul : 0 ≤ θ*(PiBinomial.count B s ω:ℝ) := by positivity
      linarith
    · simp
  have hΨi : Integrable Ψ P :=
    Integrable.of_bound (C := 1) hΨm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hΨbounds ω).1]
        exact (hΨbounds ω).2)
  have hp : ∀ ω, A.indicator (fun _ => (1:ℝ)) ω ≤
      Real.exp (θ*(c-1:ℕ))*Ψ ω := by
    intro ω
    by_cases ha : ω ∈ A
    · rw [indicator_of_mem ha]
      have hcnt : (PiBinomial.count B s ω:ℝ) ≤ (c-1:ℕ) := by
        have hless : PiBinomial.count B s ω < c := ha.2
        exact_mod_cast (show PiBinomial.count B s ω ≤ c-1 by omega)
      dsimp only [Ψ]
      rw [if_pos ha.1,← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    · rw [indicator_of_notMem ha]
      positivity
  have hint : P.real A ≤ Real.exp (θ*(c-1:ℕ))*
      PiBinomial.tiltMass s.card (μ.real E)
        (μ.real (Eᶜ\B)+μ.real B*Real.exp (-θ)) r := by
    rw [← integral_indicator_one hAm]
    have hh := integral_mono ((integrable_const (1:ℝ)).indicator hAm)
      (hΨi.const_mul _) hp
    rw [integral_const_mul,
      show ∫ ω, Ψ ω ∂P=PiBinomial.tiltMass s.card (μ.real E)
        (μ.real (Eᶜ\B)+μ.real B*Real.exp (-θ)) r from
          PiBinomial.integral_tilt_count μ E B hE hB hEB θ hθ s r] at hh
    exact hh
  let q := 1-μ.real B/(1-μ.real E)*(1-Real.exp (-θ))
  have hden : 0 < 1-μ.real E := sub_pos.mpr hE1
  have hBsub : B ⊆ Eᶜ := fun x hx hxE => Set.disjoint_left.mp hEB hxE hx
  have hβ : μ.real B ≤ 1-μ.real E := by
    have hh := measureReal_mono (μ := μ) hBsub
    rwa [probReal_compl_eq_one_sub hE] at hh
  have he0 : 0 ≤ 1-Real.exp (-θ) := by
    have hh := Real.exp_le_one_iff.mpr (show -θ ≤ 0 by linarith)
    linarith
  have he1 : 1-Real.exp (-θ) ≤ 1 := by linarith [Real.exp_pos (-θ)]
  have hq0 : 0 ≤ q := by
    have hratio : μ.real B/(1-μ.real E) ≤ 1 := (div_le_one hden).mpr hβ
    have hh := mul_le_one₀ hratio he0 he1
    dsimp only [q]
    linarith
  have hz : μ.real (Eᶜ\B)+μ.real B*Real.exp (-θ)=(1-μ.real E)*q := by
    rw [measureReal_sdiff hBsub hB,probReal_compl_eq_one_sub hE]
    dsimp only [q]
    field_simp [hden.ne']
    ring
  have hqexp : q ≤ Real.exp (-(μ.real B/(1-μ.real E)*(1-Real.exp (-θ)))) := by
    have hh := Real.add_one_le_exp (-(μ.real B/(1-μ.real E)*(1-Real.exp (-θ))))
    dsimp only [q]
    linarith
  have hpower := pow_le_pow_left₀ hq0 hqexp (s.card-r)
  rw [← Real.exp_nat_mul] at hpower
  have hmass : 0 ≤ PiBinomial.pmf s.card (μ.real E) r :=
    BinomialPivotal.pmf_nonneg s.card r ⟨measureReal_nonneg,hE1.le⟩
  apply hint.trans
  rw [hz,PiBinomial.tiltMass,mul_pow]
  have hfactor := mul_le_mul_of_nonneg_left hpower
    (mul_nonneg (Real.exp_pos (θ*(c-1:ℕ))).le hmass)
  dsimp only [PiBinomial.pmf] at hfactor ⊢
  convert! hfactor using 1
  · ring
  · rw [show θ*(c-1:ℕ)-(s.card-r:ℕ)*
        (μ.real B/(1-μ.real E))*(1-Real.exp (-θ)) =
        θ*(c-1:ℕ)+(s.card-r:ℕ)*
          -(μ.real B/(1-μ.real E)*(1-Real.exp (-θ))) by ring,
      Real.exp_add]
    ring

theorem boundary_good_relative
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E B : Set Ω) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hEB : Disjoint E B) (s : Finset ι) (r c : ℕ) (hc : 0 < c)
    {θ : ℝ} (hθ : 0 ≤ θ) (hE1 : μ.real E < 1) :
    (1-Real.exp (θ*(c-1:ℕ)-(s.card-r:ℕ)*
      (μ.real B/(1-μ.real E))*(1-Real.exp (-θ))))*
        PiBinomial.pmf s.card (μ.real E) r ≤
      (Measure.pi fun _ : ι => μ).real
        {ω | PiBinomial.count E s ω=r ∧ c ≤ PiBinomial.count B s ω} := by
  let P := Measure.pi fun _ : ι => μ
  let A : Set (ι → Ω) := {ω | PiBinomial.count E s ω=r}
  let C : Set (ι → Ω) := {ω | PiBinomial.count B s ω< c}
  have hC : MeasurableSet C :=
    (PiBinomial.measurable_count B hB s) (measurableSet_Iio (a := c))
  have hparts := measureReal_inter_add_sdiff (μ := P) (s := A) hC
  have hA : P.real A=PiBinomial.pmf s.card (μ.real E) r :=
    PiBinomial.measureReal_count_eq μ E hE s r
  have hbad := boundary_bad_relative μ E B hE hB hEB s r c hc hθ hE1
  have he : A\C={ω | PiBinomial.count E s ω=r ∧ c ≤ PiBinomial.count B s ω} := by
    ext ω
    simp only [A,C,Set.mem_sdiff,mem_setOf_eq,not_lt]
  change P.real (A∩C) ≤ _ at hbad
  rw [hA,he] at hparts
  nlinarith

end FCAppendix.Affine.Uniform06.PivotalCounts
