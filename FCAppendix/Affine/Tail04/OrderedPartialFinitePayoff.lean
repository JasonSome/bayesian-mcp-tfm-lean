import FCAppendix.Affine.Tail04.OrderedNativePartialDeviation
import FCAppendix.Game.JointMeasurability

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedPartialFinitePayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy OrderedNativePartialDeviation

variable {m c : ℕ} (D : Data m c) (Γ : FiniteGame m 2 c Seed)

def partialAction (b : Icc D.E.R D.E.Rp) (k : Fin 3) : JointAction 2 :=
  RawRoutes.action b ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1) k

lemma measurable_partialAction (k : Fin 3) : Measurable (fun b => partialAction D b k) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun b : Icc D.E.R D.E.Rp => ((b:ℝ),k.val))
      inferInstance≤_
  exact Measurable.comap_le (measurable_subtype_coe.prodMk measurable_const)

def pay (i : Fin m) (v : ℝ) (b : Icc D.E.R D.E.Rp) (k : Fin 3) : ℝ :=
  (problem Γ i).payoff v (partialAction D b k)

lemma measurable_pay (i : Fin m) (v : ℝ) (k : Fin 3) :
    Measurable (fun b => pay D Γ i v b k) := by
  change Measurable ((fun p : ℝ×JointAction 2 => (problem Γ i).payoff p.1 p.2) ∘
    (fun b : Icc D.E.R D.E.Rp => (v,partialAction D b k)))
  exact (Bayes.measurable_payoff Γ i).comp
    (measurable_const.prodMk (measurable_partialAction D k))

variable (hpolicy : ∀ j,Γ.policy j=OrderedNativePolicy.policy D j)
  (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1)
  (hA : Γ.A=Schedule.affine 2 η hη0 hη1) (hg : Γ.g=0)

include hη0 hη1 hA hg in
lemma singleton_payoff (i : Fin m) (v : ℝ) (b : Icc D.E.R D.E.Rp) :
    pay D Γ i v b 1=(v-(b:ℝ))*((problem Γ i).outcome (partialAction D b 1)).success := by
  unfold pay
  rw [LowBody.native_affine_zero_fee_payoff Γ hη0 hη1 hA hg]
  have hd : ((problem Γ i).outcome (partialAction D b 1)).duplicates=0 :=
    (RawRoutes.singleton_statistics Γ i b
      ((D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1)).2
  rw [hd]
  simp only [partialAction,RawRoutes.action,mul_zero,sub_zero]

include hpolicy η hη0 hη1 hA hg in
theorem singleton_error (i : Fin m) (v : ℝ) (b : Icc D.E.R D.E.Rp) :
    |pay D Γ i v b 1-(v-(b:ℝ))*serviceProb D Γ i|≤
      |v-(b:ℝ)| * badMass D Γ i := by
  rw [singleton_payoff D Γ η hη0 hη1 hA hg]
  rw [←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_left
    (success_error D Γ hpolicy i b 1 (by decide)) (abs_nonneg _)

include hpolicy η hη0 hη1 hA hg in
theorem lower_price_gain (i : Fin m) (v : ℝ)
    (a b : Icc D.E.R D.E.Rp) :
    ((b:ℝ)-(a:ℝ))*serviceProb D Γ i-
      (|v-(a:ℝ)|+|v-(b:ℝ)|)*badMass D Γ i≤
        pay D Γ i v a 1-pay D Γ i v b 1 := by
  have ha := (abs_le.mp (singleton_error D Γ hpolicy η hη0 hη1 hA hg i v a)).1
  have hb := (abs_le.mp (singleton_error D Γ hpolicy η hη0 hη1 hA hg i v b)).2
  nlinarith only [ha,hb]

lemma abs_sub_partial_le {v V : ℝ} (hv : |v|≤ V) (b : Icc D.E.R D.E.Rp) :
    |v-(b:ℝ)|≤ V+1 := by
  have hb0 : 0≤(b:ℝ) := (D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hb0];linarith [b.2.2,D.E.Rp_lt_one])

include hpolicy η hη0 hη1 hA hg in
theorem uniform_lower_price_gain (i : Fin m) (v V q0 ε κ : ℝ)
    (hv : |v|≤ V) (_hq0 : 0≤ q0) (hq : q0≤ serviceProb D Γ i)
    (hε : badMass D Γ i≤ ε) (hκ : 0≤ κ)
    (a b : Icc D.E.R D.E.Rp) (hab : κ≤(b:ℝ)-(a:ℝ)) :
    κ*q0-2*(V+1)*ε≤ pay D Γ i v a 1-pay D Γ i v b 1 := by
  have hqa : 0≤ serviceProb D Γ i := (serviceProb_bounds D Γ i).1
  have hp : κ*q0≤((b:ℝ)-(a:ℝ))*serviceProb D Γ i :=
    (mul_le_mul_of_nonneg_left hq hκ).trans (mul_le_mul_of_nonneg_right hab hqa)
  have ha := abs_sub_partial_le D hv a
  have hb := abs_sub_partial_le D hv b
  have hsum : |v-(a:ℝ)|+|v-(b:ℝ)|≤2*(V+1) := by linarith
  have hV : 0≤2*(V+1) := by linarith [abs_nonneg v]
  have he := mul_le_mul hsum hε (badMass_nonneg D Γ i) hV
  have hh := lower_price_gain D Γ hpolicy η hη0 hη1 hA hg i v a b
  linarith

include hpolicy hη0 hη1 hA hg in
theorem uniform_broadcast_penalty (i : Fin m) (v V q0 ε : ℝ)
    (hv : |v|≤ V) (_hq0 : 0≤ q0) (hq : q0≤ serviceProb D Γ i)
    (hε : badMass D Γ i≤ ε) (b : Icc D.E.R D.E.Rp) :
    pay D Γ i v b 2-pay D Γ i v b 1≤
      -η*D.E.R*q0+(2*(V+1)+η)*ε := by
  have hb0 : 0≤(b:ℝ) := (D.E.d_nonneg.trans D.E.d_lt_R.le).trans b.2.1
  have hR0 : 0≤ D.E.R := D.E.d_nonneg.trans D.E.d_lt_R.le
  have hq0' := (serviceProb_bounds D Γ i).1
  have hpay : η*D.E.R*q0≤ η*(b:ℝ)*serviceProb D Γ i :=
    (mul_le_mul_of_nonneg_left hq (mul_nonneg hη0 hR0)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left b.2.1 hη0) hq0')
  have hc : 2*|v-(b:ℝ)|+η*(b:ℝ)≤2*(V+1)+η := by
    have hvb := abs_sub_partial_le D hv b
    have heb : η*(b:ℝ)≤ η := by nlinarith [D.E.Rp_lt_one,b.2.2]
    linarith
  have hC : 0≤2*(V+1)+η := by linarith [abs_nonneg v]
  have herr := mul_le_mul hc hε (badMass_nonneg D Γ i) hC
  have hh := broadcast_minus_singleton_le D Γ hpolicy η hη0 hη1 hA hg i b v
  change pay D Γ i v b 2-pay D Γ i v b 1≤_ at hh
  linarith

include hpolicy η hη0 hη1 hA hg in
theorem uniform_singleton_positive_margin (i : Fin m) (v V v0 q0 ε : ℝ)
    (hv : |v|≤ V) (hvv : v0≤ v) (hv0 : D.E.Rp≤ v0)
    (_hq0 : 0≤ q0) (hq : q0≤ serviceProb D Γ i)
    (hε : badMass D Γ i≤ ε) (b : Icc D.E.R D.E.Rp) :
    (v0-D.E.Rp)*q0-(V+1)*ε≤ pay D Γ i v b 1 := by
  have hs := (abs_le.mp (singleton_error D Γ hpolicy η hη0 hη1 hA hg i v b)).1
  have hq0' := (serviceProb_bounds D Γ i).1
  have hm : (v0-D.E.Rp)*q0≤(v-(b:ℝ))*serviceProb D Γ i :=
    (mul_le_mul_of_nonneg_left hq (by linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith [b.2.2]) hq0')
  have he := mul_le_mul (abs_sub_partial_le D hv b) hε
    (badMass_nonneg D Γ i) (by linarith [abs_nonneg v] : 0≤ V+1)
  nlinarith only [hs,hm,he]

include η hη0 hη1 hA hg in
lemma singleton_abs_bound (i : Fin m) (v : ℝ) (b : Icc D.E.R D.E.Rp) :
    |pay D Γ i v b 1|≤|v|+1 := by
  rw [singleton_payoff D Γ η hη0 hη1 hA hg,abs_mul,
    abs_of_nonneg ((problem Γ i).outcome (partialAction D b 1)).success_nonneg]
  have hs := ((problem Γ i).outcome (partialAction D b 1)).success_le_one
  have hv := abs_sub_partial_le D (le_refl |v|) b
  exact (mul_le_mul_of_nonneg_right hv
    ((problem Γ i).outcome (partialAction D b 1)).success_nonneg).trans
      (by nlinarith [abs_nonneg v])

include η hη0 hη1 hA hg in
lemma integrable_singleton {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (i : Fin m) (v : ℝ)
    (b : Ω→ Icc D.E.R D.E.Rp) (hb : Measurable b) :
    Integrable (fun x => pay D Γ i v (b x) 1) μ :=
  Integrable.of_bound ((measurable_pay D Γ i v 1).comp hb).aestronglyMeasurable (|v|+1)
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact singleton_abs_bound D Γ η hη0 hη1 hA hg i v (b x)))

include hpolicy η hη0 hη1 hA hg in
theorem integral_lower_price_gain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (i : Fin m) (v V q0 ε κ : ℝ)
    (hv : |v|≤ V) (hq0 : 0≤ q0) (hq : q0≤ serviceProb D Γ i)
    (hε : badMass D Γ i≤ ε) (hκ : 0≤ κ)
    (a b : Ω→ Icc D.E.R D.E.Rp) (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ x,κ≤(b x:ℝ)-(a x:ℝ)) :
    κ*q0-2*(V+1)*ε≤
      (∫ x,pay D Γ i v (a x) 1 ∂μ)-(∫ x,pay D Γ i v (b x) 1 ∂μ) := by
  have hai := integrable_singleton D Γ η hη0 hη1 hA hg μ i v a ha
  have hbi := integrable_singleton D Γ η hη0 hη1 hA hg μ i v b hb
  rw [←integral_sub hai hbi]
  simpa only [integral_const,probReal_univ,one_smul] using!
    integral_mono_ae (integrable_const (κ*q0-2*(V+1)*ε)) (hai.sub hbi)
      (ae_of_all _ (fun x => uniform_lower_price_gain D Γ hpolicy η hη0 hη1 hA hg
        i v V q0 ε κ hv hq0 hq hε hκ (a x) (b x) (hab x)))

end FCAppendix.Affine.Tail04.OrderedPartialFinitePayoff
