import FCAppendix.Affine.Tail04.EqualPrivateFiniteLoss

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualNoisyFiniteLoss
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualNoisyUtilities EqualPrivateFiniteLoss
open scoped BigOperators

variable {N H c : ℕ} {R Rp U eps ξ eta : ℝ}

private lemma mass_integrable (heps : 0≤ eps) (hξ : 0< ξ)
    (p : Input N H R Rp U) (i : Fin N) (r : Fin 3) :
    Integrable (fun z => (rawCount (c:=c) heps ξ p z i).mass r)
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  apply Integrable.of_bound
    ((measurable_rawCount_mass heps hξ p i r).aestronglyMeasurable) 1
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (AtypicalActiveNoisy.mass_bounds _ r).1]
    exact (AtypicalActiveNoisy.mass_bounds _ r).2)

private lemma payment_integrable (heps : 0≤ eps) (hξ : 0< ξ)
    (p : Input N H R Rp U) (i : Fin N) (r : Fin 3) :
    Integrable (fun z => (1+eps*(z i:ℝ))*(rawCount (c:=c) heps ξ p z i).mass r)
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  have hm := measurable_rawCount_mass (c:=c) heps hξ p i r
  apply Integrable.of_bound
    (((by fun_prop : Measurable (fun z : Fin N → unitInterval => 1+eps*(z i:ℝ))).mul hm).aestronglyMeasurable) (1+eps)
  exact ae_of_all _ (fun z => by
    have h0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps (z i).2.1]
    have h1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
    have hb := AtypicalActiveNoisy.mass_bounds (rawCount (c:=c) heps ξ p z i) r
    change ‖(1+eps*(z i:ℝ))*(rawCount (c:=c) heps ξ p z i).mass r‖≤1+eps
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 hb.1)]
    exact (mul_le_of_le_one_right h0 hb.2).trans h1)

private lemma rawUtility_formula (heps : 0≤ eps) (he0 : 0≤ eta) (he1 : eta≤1)
    (p : Input N H R Rp U) (i : Fin N) (v : ℝ) (z : Fin N → unitInterval) :
    affineCountUtility (rawCount (c:=c) heps ξ p z i)
        v (physicalReal heps p.1 z i) eta he0 he1 =
      ∑ r : Fin 3,(v*successIndicator r.val*(rawCount (c:=c) heps ξ p z i).mass r-
        (p.1 i:ℝ)*((Schedule.affine 2 eta he0 he1).charge r.val)*
          ((1+eps*(z i:ℝ))*(rawCount (c:=c) heps ξ p z i).mass r)) := by
  unfold affineCountUtility CountLaw.utility FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro r _
  dsimp [userPayoff,physicalReal,physical,CompactSourceBidLaws.noisyBid,Hybrid.activeNoisyRealBid]
  ring

theorem integrable_rawUtility (heps : 0≤ eps) (hξ : 0< ξ)
    (he0 : 0≤ eta) (he1 : eta≤1)
    (p : Input N H R Rp U) (i : Fin N) (v : ℝ) :
    Integrable (fun z => affineCountUtility (rawCount (c:=c) heps ξ p z i)
      v (physicalReal heps p.1 z i) eta he0 he1)
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  simp_rw [rawUtility_formula]
  exact integrable_finsetSum _ (fun r _ =>
    ((mass_integrable (c:=c) heps hξ p i r).const_mul _).sub
      ((payment_integrable (c:=c) heps hξ p i r).const_mul _))

theorem activeUtility_eq_integral (heps : 0≤ eps) (hξ : 0< ξ)
    (he0 : 0≤ eta) (he1 : eta≤1)
    (p : Input N H R Rp U) (i : Fin N) (v : ℝ) :
    activeUtility (c:=c) heps ξ eta he0 he1 i (v,p)=
      ∫ z,affineCountUtility (rawCount (c:=c) heps ξ p z i)
        v (physicalReal heps p.1 z i) eta he0 he1
          ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)) := by
  simp_rw [rawUtility_formula]
  erw [integral_finsetSum _ (fun r _ =>
    ((mass_integrable (c:=c) heps hξ p i r).const_mul _).sub
      ((payment_integrable (c:=c) heps hξ p i r).const_mul _))]
  unfold activeUtility mass paymentMass
  apply Finset.sum_congr rfl
  intro r _
  simp only [Pi.sub_apply]
  erw [integral_sub ((mass_integrable (c:=c) heps hξ p i r).const_mul _)
      ((payment_integrable (c:=c) heps hξ p i r).const_mul _),
    integral_const_mul,integral_const_mul]

theorem activeUtility_finite_loss (heps : 0≤ eps) (hξ : 0< ξ) (hξ1 : ξ≤1)
    (he0 : 0≤ eta) (he1 : eta≤1)
    (μ : ProbabilityMeasure (Signal H R Rp))
    (b d : Fin N → Icc (1:ℝ) U) (i : Fin N) (hother : ∀ j,j≠i → d j=b j)
    (v : ℝ) (hv : 0≤ v) (hy : (b i:ℝ)≤(d i:ℝ)) :
    activeUtility (c:=c) heps ξ eta he0 he1 i (v,(b,μ))-
      activeUtility (c:=c) heps ξ eta he0 he1 i (v,(d,μ))≤
      ((2*v+2*(U*(1+eps)))/ξ+2)*(1+eps)*((d i:ℝ)-(b i:ℝ)) := by
  rw [activeUtility_eq_integral heps hξ,activeUtility_eq_integral heps hξ,
    ← integral_sub (integrable_rawUtility heps hξ he0 he1 (b,μ) i v)
      (integrable_rawUtility heps hξ he0 he1 (d,μ) i v)]
  have hh := integral_mono
    ((integrable_rawUtility heps hξ he0 he1 (b,μ) i v).sub
      (integrable_rawUtility heps hξ he0 he1 (d,μ) i v))
    (integrable_const (((2*v+2*(U*(1+eps)))/ξ+2)*(1+eps)*((d i:ℝ)-(b i:ℝ))))
    (physical_countUtility_finite_loss (c:=c) heps hξ hξ1 he0 he1 μ b d i hother v hv hy)
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,Pi.sub_apply] at hh
  convert! hh using 1

end FCAppendix.Affine.Tail04.EqualNoisyFiniteLoss
