import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalU19
import FCAppendix.Affine.Uniform07Finishing.Crossover.Boundary
import FCAppendix.Affine.Uniform07Finishing.Native.CommonBoundary

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem ac_abs_increment {f : ℝ→ℝ} {a b K : ℝ}
    (hab : a≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hder : ∀ᵐ z ∂volume.restrict (Icc a b), |deriv f z|≤ K) :
    |f b-f a|≤ K*(b-a) := by
  have hlo := ac_increment_lower hab hf (hder.mono fun _ hz => (abs_le.mp hz).1)
  have hhi := ac_increment_upper hab hf (hder.mono fun _ hz => (abs_le.mp hz).2)
  exact abs_le.mpr ⟨by linarith,hhi⟩

theorem pure_gap_correction_lipschitz
    {s d : ℝ→ℝ} {eta w x y e q m : ℝ}
    (heta : eta∈Icc (0:ℝ) 1) (hx0 : 0≤ x) (hxy : x< y)
    (hyw : y≤ w) (hw1 : w≤ 1) (hq : 0≤ q) (hm : 1≤ m) (he : 0≤ e)
    (hS : AbsolutelyContinuousOnInterval s x y)
    (hD : AbsolutelyContinuousOnInterval d x y)
    (hbudget : ∀ᵐ z ∂volume, z∈Ioo x y →
      HasDerivAt s (deriv s z) z ∧ HasDerivAt d (deriv d z) z ∧
      |s z|≤ e*q/m ∧ |d z|≤ e*q/m ∧
      |deriv s z|≤ e*q ∧ |deriv d z|≤ e*q) :
    ∀ z∈Ioo x y,
      |((w-z)*s z-eta*z*d z)-((w-y)*s y-eta*y*d y)|≤ 4*e*q*(y-z) := by
  let r : ℝ→ℝ := fun z => (w-z)*s z-eta*z*d z
  have hRent : AbsolutelyContinuousOnInterval (fun z : ℝ => w-z) x y :=
    (show ContDiffOn ℝ 1 (fun z : ℝ => w-z) (uIcc x y) by fun_prop).absolutelyContinuousOnInterval
  have hCost : AbsolutelyContinuousOnInterval (fun z : ℝ => eta*z) x y :=
    (show ContDiffOn ℝ 1 (fun z : ℝ => eta*z) (uIcc x y) by fun_prop).absolutelyContinuousOnInterval
  have hR : AbsolutelyContinuousOnInterval r x y :=
    (hRent.fun_mul hS).fun_sub (hCost.fun_mul hD)
  have hder : ∀ᵐ z ∂volume, z∈Ioo x y → |deriv r z|≤ 4*e*q := by
    filter_upwards [hbudget] with z hz hzxy
    rcases hz hzxy with ⟨hs,hd,hsv,hdv,hsd,hdd⟩
    have hz0 : 0≤ z := hx0.trans hzxy.1.le
    have hz1 : z≤ 1 := hzxy.2.le.trans (hyw.trans hw1)
    have hdelta : w-z∈Icc (0:ℝ) 1 := by
      constructor <;> linarith [hzxy.2]
    have hB := signed_residual_bound_with_flow heta ⟨hz0,hz1⟩ hdelta hq
      (show (0:ℝ)≤ 0 by norm_num) hm he hsv hdv
      (by simpa using hsd) (by simpa using hdd)
    have hdr : HasDerivAt r
        (-s z+(w-z)*deriv s z-eta*d z-eta*z*deriv d z) z := by
      convert! ((((hasDerivAt_id z).const_sub w).mul hs).sub
        (((hasDerivAt_id z).const_mul eta).mul hd)) using 1
      simp only [id_eq]
      ring
    rw [hdr.deriv]
    have heq : -s z+(w-z)*deriv s z-eta*d z-eta*z*deriv d z =
        -(s z+eta*d z+eta*z*deriv d z-(w-z)*deriv s z) := by ring
    rw [heq,abs_neg]
    simpa using hB
  intro z hz
  have hu : uIcc z y ⊆ uIcc x y := by
    rw [uIcc_of_le hz.2.le,uIcc_of_le hxy.le]
    exact fun u hu => ⟨hz.1.le.trans hu.1,hu.2⟩
  have haey : ∀ᵐ u ∂(volume : Measure ℝ), u≠y :=
    measure_eq_zero_iff_ae_notMem.mp (measure_singleton y)
  have hdzy : ∀ᵐ u ∂volume.restrict (Icc z y), |deriv r u|≤ 4*e*q := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hder,haey] with u hu hne huy
    exact hu ⟨hz.1.trans_le huy.1,lt_of_le_of_ne huy.2 hne⟩
  have hi := ac_abs_increment hz.2.le (hR.mono hu) hdzy
  simpa only [r,abs_sub_comm] using hi

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

@[simp] theorem sourceLowerBroadcastAction_eq_two (U : ℝ) (b : Icc (0:ℝ) U) :
    sourceLowerBroadcastAction U b=two b.1 := by
  simp [sourceLowerBroadcastAction,two,action,max_eq_left b.2.1]

def gapCorrection (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (eta t w b : ℝ) : ℝ :=
  (w-b)*successError Γ i B t b-eta*b*duplicateError Γ i B b

theorem actual_gap_payoff (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) {eta t w p b : ℝ}
    (heta0 : 0≤ eta) (heta1 : eta≤ 1)
    (hA : Γ.A=Schedule.affine 2 eta heta0 heta1) (hg : Γ.g=0)
    (hb : 0≤ b) (hp : pureRank m c t (rank Γ t b)=p) :
    (problem Γ i).payoff w (two b)=
      gapPayoff eta w p (canonicalMarginal Γ i B) (canonicalDuplicate Γ i B) b+
        gapCorrection Γ i B eta t w b := by
  rw [LowBody.native_affine_zero_fee_payoff Γ heta0 heta1 hA hg]
  simp only [two_bid hb]
  change (w-b)*success Γ i b-eta*b*duplicate Γ i b=_
  unfold gapPayoff gapCorrection successError duplicateError comparisonMarginal
  rw [hp]
  ring

theorem actual_gap_reset (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) {eta t U x : ℝ} (y : Icc (0:ℝ) U)
    (heta : eta∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 eta heta.1 heta.2) (hg : Γ.g=0)
    [NullSingletonClass (lowerBidMeasure Γ t)]
    (hx0 : 0≤ x) (hxy : x<(y:ℝ))
    (hgap : ∀ z∈Ioo x (y:ℝ), z∉(lowerBidMeasure Γ t).support)
    (π : Measure (ℝ × Icc (0:ℝ) U))
    (hpay : ∀ j : Fin m, ContinuousAt (fun z : ℝ × Icc (0:ℝ) U =>
      (problem Γ j).payoff z.1 (sourceLowerBroadcastAction U z.2)) (rank Γ t y.1,y))
    (hM : Continuous (fun b : Icc (0:ℝ) U => rank Γ t b.1))
    (J : Set (Icc (0:ℝ) U)) (hJ : IsOpen J)
    (hrank : ∀ᵐ z ∂π, z.2∈J → z.1=rank Γ t z.2.1)
    (hIC : ∀ᵐ z ∂π, ∀ j : Fin m, ∀ b' : Icc (0:ℝ) U,
      (problem Γ j).payoff z.1 (sourceLowerBroadcastAction U b')≤
        (problem Γ j).payoff z.1 (sourceLowerBroadcastAction U z.2))
    (hy : y∈(π.map Prod.snd).support) (hyJ : y∈J)
    {c' d' den e : ℝ}
    (hC : HasDerivAt (canonicalMarginal Γ i B) c' y.1)
    (hD : HasDerivAt (canonicalDuplicate Γ i B) d' y.1)
    (hgapDen : 0<2*c'-d') (hden : 2*c'-d'≤ den)
    (hN : 0≤ barrierNumerator eta y.1 (comparisonMarginal Γ i B t y.1)
      (canonicalDuplicate Γ i B y.1) d'-4*e*comparisonMarginal Γ i B t y.1)
    (hcorrection : ∀ z∈Ioo x y.1,
      |gapCorrection Γ i B eta t (rank Γ t y.1) z-
        gapCorrection Γ i B eta t (rank Γ t y.1) y.1|≤
          4*e*comparisonMarginal Γ i B t y.1*(y.1-z)) :
    barrierNumerator eta y.1 (comparisonMarginal Γ i B t y.1)
        (canonicalDuplicate Γ i B y.1) d'/den-
      (4*e*comparisonMarginal Γ i B t y.1)/den≤ rank Γ t y.1-y.1 := by
  have hr := rank_constant_on_unused_gap Γ t hxy.le hgap
  have hcommon := actual_common_boundary_broadcast_IC_local_at Γ U π
    (fun b : Icc (0:ℝ) U => rank Γ t b.1) hM J hJ hrank hIC hy hyJ hpay
  have hopt : ∀ z∈Ioo x y.1,
      gapPayoff eta (rank Γ t y.1) (pureRank m c t (rank Γ t y.1))
        (canonicalMarginal Γ i B) (canonicalDuplicate Γ i B) z+
          gapCorrection Γ i B eta t (rank Γ t y.1) z≤
      gapPayoff eta (rank Γ t y.1) (pureRank m c t (rank Γ t y.1))
        (canonicalMarginal Γ i B) (canonicalDuplicate Γ i B) y.1+
          gapCorrection Γ i B eta t (rank Γ t y.1) y.1 := by
    intro z hz
    let z' : Icc (0:ℝ) U := ⟨z,⟨hx0.trans hz.1.le,hz.2.le.trans y.2.2⟩⟩
    have h := hcommon i z'
    simp only [sourceLowerBroadcastAction_eq_two] at h
    rw [actual_gap_payoff Γ i B heta.1 heta.2 hA hg y.2.1 rfl,
      actual_gap_payoff Γ i B heta.1 heta.2 hA hg z'.2.1
        (congrArg (pureRank m c t) (hr z ⟨hz.1.le,hz.2.le⟩))] at h
    exact h
  simpa only [comparisonMarginal] using
    right_gap_reset_of_common_type_optimality hxy hC hD hgapDen hden
      (by simpa only [comparisonMarginal] using hN) hopt hcorrection

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
