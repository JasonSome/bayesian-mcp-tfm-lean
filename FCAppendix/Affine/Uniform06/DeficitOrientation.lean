import FCAppendix.Affine.Uniform06.UniformMarkedLLT
import FCAppendix.Affine.Uniform06.CenteredSourceGap

noncomputable section
namespace FCAppendix.Affine.Uniform06.DeficitOrientation

open MeasureTheory Filter Set
open scoped Topology BigOperators
open MixedIntervalLLT MixedProductCharacteristic MixedCellSmoothing
open MixedSpectralLimit BoundedMixedGaussian CharacteristicExpansion

variable {Ω : Type*} [MeasurableSpace Ω]

def reflectX (A : CenteredArray Ω) : CenteredArray Ω where
  law := A.law
  probability := A.probability
  X := fun n ω => -A.X n ω
  Y := A.Y
  N := A.N
  d := A.d
  measurable_X := fun n => (A.measurable_X n).neg
  measurable_Y := A.measurable_Y
  bounded := fun n => (A.bounded n).mono fun ω hω => by simpa only [abs_neg] using hω
  mean_X := by intro n; rw [integral_neg,A.mean_X,neg_zero]
  mean_Y := A.mean_Y
  covariance := by intro n; simp_rw [neg_mul,integral_neg,A.covariance,neg_zero]
  d_nonneg := A.d_nonneg
  d_zero := A.d_zero
  scale := A.scale
  market := A.market
  vX := A.vX
  vY := A.vY
  lowerVariance := A.lowerVariance
  lowerVariance_pos := A.lowerVariance_pos
  variance_X_lower := by intro n; simpa only [neg_sq] using A.variance_X_lower n
  variance_Y_lower := A.variance_Y_lower
  variance_X_limit := by simpa only [neg_sq] using A.variance_X_limit
  variance_Y_limit := A.variance_Y_limit

lemma reflect_frequency_mem {T : ℝ} {q : ℝ × ℝ} (hq : q ∈ bandExterior T) :
    (-q.1,q.2) ∈ bandExterior T := by
  refine ⟨⟨⟨?_,?_⟩,hq.1.2⟩,?_⟩
  · linarith [hq.1.1.2]
  · linarith [hq.1.1.1]
  · intro h
    apply hq.2
    change 1*(|-q.1|+|q.2|) ≤ 1/4 at h
    change 1*(|q.1|+|q.2|) ≤ 1/4
    simpa only [abs_neg] using h

theorem reflectX_compactGap (A : CenteredArray Ω) (hgap : A.CompactGap) :
    (reflectX A).CompactGap := by
  intro T hT
  obtain ⟨r,hr0,hr1,he⟩ := hgap T hT
  refine ⟨r,hr0,hr1,?_⟩
  filter_upwards [he] with n hn
  intro q hq
  have hh := hn (-q.1,q.2) (reflect_frequency_mem hq)
  have hid : projection ((reflectX A).X n) ((reflectX A).realY n) q =
      projection (A.X n) (A.realY n) (-q.1,q.2) := by
    funext ω
    dsimp [projection,reflectX,CenteredArray.realY]
    ring
  change ‖rowCharacteristic (A.law n)
    (projection ((reflectX A).X n) ((reflectX A).realY n) q)‖ ≤ r
  rw [hid]
  exact hh

lemma productCell_real_event (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {Y : Ω → ℤ} (hX : Measurable X) (_hY : Measurable Y)
    (N : ℕ) (c : ℝ) (j y : ℤ) (a b : ℝ) :
    (productCell μ X Y N c j y).real (Icc a b) =
      (Measure.pi (fun _ : Fin N => μ)).real
        {ω | c+continuousSum X N ω ∈ Icc a b ∧ j+integerSum Y N ω=y} := by
  have hsum : Measurable (fun ω : Fin N → Ω => c+continuousSum X N ω) :=
    measurable_const.add (measurable_continuousSum hX N)
  simp only [productCell,measureReal_def]
  rw [Measure.map_apply hsum measurableSet_Icc,
    Measure.restrict_apply (hsum measurableSet_Icc)]
  congr 1

theorem reflected_sum_eq_deficit (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (r cap marks : ℕ → ℝ)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n) (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
      (cap n-marks n-(A.N n : ℝ)*r n) +
        continuousSum ((reflectX A).X n) (A.N n) ω =
          cap n-marks n-continuousSum (U n) (A.N n) ω := by
  have hc (j : Fin (A.N n)) :=
    (measurePreserving_eval (fun _ : Fin (A.N n) => A.law n) j).quasiMeasurePreserving.ae
      (hcenter n)
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  change cap n-marks n-(A.N n : ℝ)*r n + (∑ j, -A.X n (ω j)) =
    cap n-marks n-(∑ j,U n (ω j))
  simp_rw [hω]
  simp only [neg_sub,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

theorem reflected_cell_eq_original_deficit (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (r cap marks : ℕ → ℝ)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n)
    (n : ℕ) (j y : ℤ) (a b : ℝ) :
    (productCell (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
      (cap n-marks n-(A.N n : ℝ)*r n) j y).real (Icc a b) =
      (Measure.pi (fun _ : Fin (A.N n) => A.law n)).real
        {ω | cap n-marks n-continuousSum (U n) (A.N n) ω ∈ Icc a b ∧
          j+integerSum (A.Y n) (A.N n) ω=y} := by
  rw [productCell_real_event (A.law n) (show Measurable ((reflectX A).X n) from
    (A.measurable_X n).neg) (A.measurable_Y n)]
  have hset :
      {ω : Fin (A.N n) → Ω |
        cap n-marks n-(A.N n : ℝ)*r n+
          continuousSum ((reflectX A).X n) (A.N n) ω ∈ Icc a b ∧
          j+integerSum (A.Y n) (A.N n) ω=y} =ᵐ[Measure.pi (fun _ : Fin (A.N n) => A.law n)]
      {ω | cap n-marks n-continuousSum (U n) (A.N n) ω ∈ Icc a b ∧
        j+integerSum (A.Y n) (A.N n) ω=y} := by
    filter_upwards [reflected_sum_eq_deficit A U r cap marks hcenter n] with ω hω
    apply propext
    change (_ ∈ Icc a b ∧ _) ↔ (_ ∈ Icc a b ∧ _)
    rw [hω]
  simpa only [measureReal_def] using congrArg ENNReal.toReal (measure_congr hset)

theorem relative_deficit_interval (A : CenteredArray Ω) (hgap : A.CompactGap)
    (U : ℕ → Ω → ℝ) (r cap marks : ℕ → ℝ) (j y : ℕ → ℤ)
    (hcenter : ∀ n, ∀ᵐ ω ∂A.law n, A.X n ω=U n ω-r n)
    (hshift : Tendsto (fun n => A.d n*(cap n-marks n-(A.N n : ℝ)*r n)) atTop (𝓝 0))
    (hy : Tendsto (fun n => A.d n*((j n-y n : ℤ) : ℝ)) atTop (𝓝 0))
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun n =>
      (Measure.pi (fun _ : Fin (A.N n) => A.law n)).real
        {ω | cap n-marks n-continuousSum (U n) (A.N n) ω ∈ Icc a b ∧
          j n+integerSum (A.Y n) (A.N n) ω=y n} /
      ((b-a)*density A.vX A.vY/(A.N n : ℝ))) atTop (𝓝 1) := by
  have hh := tendsto_relative_interval (reflectX A) (reflectX_compactGap A hgap)
    (fun n => cap n-marks n-(A.N n : ℝ)*r n) j y hshift hy hab
  have he (n : ℕ) := reflected_cell_eq_original_deficit A U r cap marks hcenter n
    (j n) (y n) a b
  change Tendsto (fun n =>
    (productCell (A.law n) ((reflectX A).X n) (A.Y n) (A.N n)
      (cap n-marks n-(A.N n:ℝ)*r n) (j n) (y n)).real (Icc a b) /
      ((b-a)*density A.vX A.vY/(A.N n:ℝ))) atTop (𝓝 1) at hh
  simp_rw [he] at hh
  exact hh

end FCAppendix.Affine.Uniform06.DeficitOrientation
