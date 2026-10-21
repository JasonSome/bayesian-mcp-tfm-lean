import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Regularity
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06U19

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Physical

theorem source_band_subset_rate (row : Uniform07.Row) :
    Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)⊆OptimizedPhysicalRate.band row := by
  intro b hb
  have hz : Uniform07.sourceZhi row< Uniform07.x row := by
    cases row <;> norm_num [Uniform07.sourceZhi,Uniform07.x,Uniform07.xQ]
  have ht:=mul_lt_mul_of_pos_right hz (Uniform07.cutoff_pos row)
  exact ⟨hb.1,hb.2.trans_lt ht⟩

theorem actual_source_rate_derivative (row : Uniform07.Row) {b : ℝ}
    (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
    HasDerivWithinAt (negativePhysicalSourceRate row) (OptimizedPhysicalRate.A row b)
      (Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) b := by
  have hh:=(OptimizedPhysicalRate.canonicalRate_hasDerivWithinAt_physical row
    (source_band_subset_rate row hb)).neg
  have hfun : (-(fun a => Uniform07.canonicalRate row (a/Uniform07.cutoff row)))=
      negativePhysicalSourceRate row := rfl
  rw [hfun,neg_neg] at hh
  exact hh.mono (source_band_subset_rate row)

structure SourceRateConstants (row : Uniform07.Row) where
  Amin : ℝ
  Amax : ℝ
  Amin_pos : 0< Amin
  bounds : ∀b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row),
    OptimizedPhysicalRate.A row b∈Icc Amin Amax

theorem exists_source_rate_constants (row : Uniform07.Row) : Nonempty (SourceRateConstants row) := by
  have hI : (Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)).Nonempty:=
    ⟨sourceCrossoverStart row,le_rfl,(source_crossover_end_gt_start row).le⟩
  have hC := (OptimizedPhysicalRate.continuousOn_A row).mono (source_band_subset_rate row)
  obtain ⟨lo,hlo,hmin⟩:=isCompact_Icc.exists_isMinOn hI hC
  obtain ⟨hi,hhi,hmax⟩:=isCompact_Icc.exists_isMaxOn hI hC
  exact ⟨⟨OptimizedPhysicalRate.A row lo,OptimizedPhysicalRate.A row hi,
    OptimizedPhysicalRate.A_pos row (source_band_subset_rate row hlo),
    fun b hb=>⟨hmin hb,hmax hb⟩⟩⟩

def sourceRateConstants (row : Uniform07.Row) : SourceRateConstants row:=
  Classical.choice (exists_source_rate_constants row)

theorem sourceRateConstants_Amax_pos (row : Uniform07.Row) : 0<(sourceRateConstants row).Amax :=
  (sourceRateConstants row).Amin_pos.trans_le
    (((sourceRateConstants row).bounds _ ⟨le_rfl,(source_crossover_end_gt_start row).le⟩).1.trans
      ((sourceRateConstants row).bounds _ ⟨le_rfl,(source_crossover_end_gt_start row).le⟩).2)

def readyKernelFields (row : Uniform07.Row) :
    SourcePreciseFamily.KernelFields (Received05.G row) (Received05.g row) (Received05.cm row) row :=
  received06KernelFields (Received05.G row)
    (fun _ E=>E.1.law.multiplier) (fun _ E=>E.1.law.rejectionRoot)
    (fun _ E=>E.1.cluster.market_two_le) row

def u19Test (row : Uniform07.Row) (m n : ℕ) : Prop :=
  ∀E : Received05.ReadyLaw row m,∀b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row),
    SourcePreciseFamily.RelativeBounds row m (Received05.G row m E)
      (Received05.g row m E) (Received05.cm row m E) b (1/((n:ℝ)+2))

theorem eventually_u19Test (row : Uniform07.Row) (n : ℕ) : ∀ᶠm in atTop,u19Test row m n := by
  have hd : 0< Uniform07.x row-Uniform07.sourceZhi row := by
    cases row <;> norm_num [Uniform07.x,Uniform07.xQ,Uniform07.sourceZhi]
  have hdmax : Uniform07.x row-Uniform07.sourceZhi row≤ Uniform07.x row-1/2 := by
    cases row <;> norm_num [Uniform07.x,Uniform07.xQ,Uniform07.sourceZhi]
  have hh:=SourcePreciseFamily.uniform_u19
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.atoms row)
    (Received05.roots row).literal (Received05.roots row).rejection (readyKernelFields row)
    hd hdmax (1/((n:ℝ)+2)) (by positivity)
  simpa only [u19Test,sourceCrossoverStart,sourceCrossoverEnd,sub_sub_cancel] using hh

def u19Index (row : Uniform07.Row) (m : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (u19Test row m) m

theorem u19Index_tendsto (row : Uniform07.Row) : Tendsto (u19Index row) atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n,eventually_u19Test row n] with m hm hh
  exact Nat.le_findGreatest hm hh

def u19Tolerance (row : Uniform07.Row) (m : ℕ) : ℝ:=1/((u19Index row m:ℝ)+2)

theorem u19Tolerance_mem (row : Uniform07.Row) (m : ℕ) :
    u19Tolerance row m∈Ioo (0:ℝ) 1 := by
  unfold u19Tolerance
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).mpr
    have hh : (0:ℝ)≤ u19Index row m:=Nat.cast_nonneg _
    linarith

theorem u19Tolerance_tendsto (row : Uniform07.Row) : Tendsto (u19Tolerance row) atTop (𝓝 0) := by
  have hi : Tendsto (fun m => (u19Index row m:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (u19Index_tendsto row)
  have hi' : Tendsto (fun m => (u19Index row m:ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun m => by linarith) hi
  change Tendsto (fun m => 1/((u19Index row m:ℝ)+2)) atTop (𝓝 0)
  simpa only [one_div,Function.comp_def] using
    tendsto_inv_atTop_zero.comp hi'

theorem eventually_u19Tolerance (row : Uniform07.Row) :
    ∀ᶠm in atTop,∀E : Received05.ReadyLaw row m,
      ∀b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row),
        SourcePreciseFamily.RelativeBounds row m (Received05.G row m E)
          (Received05.g row m E) (Received05.cm row m E) b (u19Tolerance row m) := by
  classical
  filter_upwards [eventually_u19Test row 0] with m hm
  exact Nat.findGreatest_spec (Nat.zero_le m) hm

def receivedU19Error (row : Uniform07.Row) (m : ℕ) : ℝ :=
  u19Error (Uniform07.xi row) (sourceCrossoverStart row) (sourceRateConstants row).Amax
    (u19Tolerance row m)

theorem receivedU19Error_nonnegative (row : Uniform07.Row) (m : ℕ) : 0≤ receivedU19Error row m :=
  u19Error_nonnegative (Uniform07.xi_pos row) (source_crossover_geometry row).1
    (sourceRateConstants_Amax_pos row).le (u19Tolerance_mem row m).1.le

theorem receivedU19Error_tendsto (row : Uniform07.Row) :
    Tendsto (receivedU19Error row) atTop (𝓝 0) := u19Error_tendsto (u19Tolerance_tendsto row)

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
