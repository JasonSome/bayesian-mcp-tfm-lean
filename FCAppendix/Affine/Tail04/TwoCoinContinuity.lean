import FCAppendix.Affine.Tail04.TypicalCountLaws

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory

lemma twoCoinCountLaw_mass_formula (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (r : Fin 3) :
    (twoCoinCountLaw p q hp0 hp1 hq0 hq1).mass r =
      (1-p)*(1-q)*(if 0=r then 1 else 0)+
        (p*(1-q)+(1-p)*q)*(if 1=r then 1 else 0)+p*q*(if 2=r then 1 else 0) := by
  classical
  rw [←FiniteLaw.expect_singleton, twoCoinCountLaw_expect]

theorem continuousAt_twoCoinCountLaw_mass {X : Type*} [TopologicalSpace X]
    (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1) {x : X}
    (hp : ContinuousAt p x) (hq : ContinuousAt q x) (r : Fin 3) :
    ContinuousAt (fun y => (twoCoinCountLaw (p y) (q y) (hp0 y) (hp1 y) (hq0 y) (hq1 y)).mass r) x := by
  simp_rw [twoCoinCountLaw_mass_formula]
  exact ((((continuousAt_const.sub hp).mul (continuousAt_const.sub hq)).mul continuousAt_const).add
    (((hp.mul (continuousAt_const.sub hq)).add ((continuousAt_const.sub hp).mul hq)).mul
      continuousAt_const)).add ((hp.mul hq).mul continuousAt_const)

theorem continuous_twoCoinCountLaw_mass {X : Type*} [TopologicalSpace X]
    (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1)
    (hp : Continuous p) (hq : Continuous q) (r : Fin 3) :
    Continuous (fun y => (twoCoinCountLaw (p y) (q y) (hp0 y) (hp1 y) (hq0 y) (hq1 y)).mass r) :=
  continuous_iff_continuousAt.mpr (fun _ =>
    continuousAt_twoCoinCountLaw_mass p q hp0 hp1 hq0 hq1 hp.continuousAt hq.continuousAt r)

theorem measurable_twoCoinCountLaw_mass {X : Type*} [MeasurableSpace X]
    (p q : X → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∀ x, q x ≤ 1)
    (hp : Measurable p) (hq : Measurable q) (r : Fin 3) :
    Measurable (fun y => (twoCoinCountLaw (p y) (q y) (hp0 y) (hp1 y) (hq0 y) (hq1 y)).mass r) := by
  simp_rw [twoCoinCountLaw_mass_formula]
  exact ((((measurable_const.sub hp).mul (measurable_const.sub hq)).mul measurable_const).add
    (((hp.mul (measurable_const.sub hq)).add ((measurable_const.sub hp).mul hq)).mul
      measurable_const)).add ((hp.mul hq).mul measurable_const)

end FCAppendix.Affine.Tail04
