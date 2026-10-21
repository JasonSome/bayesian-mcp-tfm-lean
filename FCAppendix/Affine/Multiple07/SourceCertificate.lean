import FCAppendix.Affine.Multiple07.SourceRateCertificate
import FCAppendix.Affine.Multiple07.SourceMeasureLifts
import FCAppendix.Affine.Multiple07.SourceMaxima

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Set Filter Topology

structure SourceC5Certificate (r : Partition) : Prop where
  masses : 0 < (3 / 200 : ℝ) ∧ 0 < activeMass r ∧ 0 < upperMass r ∧
    (3 / 200 : ℝ) + activeMass r + upperMass r = 1
  coefficient : 0 < xi ∧ xi < 1 / 2 ∧ eta = 1 - 2 * xi
  rank : upperMass r / 2 < rho ∧ rho < activeMass r + upperMass r / 2
  exposure_fraction : activeFraction r ∈ Ioo (0 : ℝ) 1
  low_support : ∀ᵐ v ∂bandLaw .low, v ∈ Icc (0 : ℝ) lowCeiling
  active_support : ∀ᵐ v ∂activeValueLaw r, v ∈ Icc (activeLower r) (activeUpper r)
  upper_support : ∀ᵐ v ∂upperValueLaw r, v ∈ Icc (upperLower r) (2301 / 2000 : ℝ)
  original_law : sourceValueLaw =
    ENNReal.ofReal (3 / 200 : ℝ) • bandLaw .low +
      ENNReal.ofReal (activeMass r) • activeValueLaw r +
      ENNReal.ofReal (upperMass r) • upperValueLaw r
  low_compact_map : sourceLowValueLaw.map
    (fun v : LowBody.LowValue lowCeiling => (v : ℝ)) = bandLaw .low
  active_compact_map : (sourceActiveValueLaw r).map
    (fun v : Hybrid.ActiveValue (activeLower r) (activeUpper r) => (v : ℝ)) = activeValueLaw r
  upper_compact_map : (sourceUpperValueLaw r).map
    (fun v : Icc (upperLower r) (2301 / 2000 : ℝ) => (v : ℝ)) = upperValueLaw r
  low_positive : ∀ᵐ (v : LowBody.LowValue lowCeiling) ∂sourceLowValueLaw, 0 < (v : ℝ)
  multiplier_interior : 0 < multiplier r ∧ multiplier r < activeLower r
  optimizer : ∀ v ∈ Icc (activeLower r) (activeUpper r),
    exposure r v ∈ Ioo (0 : ℝ) 1 ∧
      (∀ q : ℝ,
        (∀ q' ∈ Icc (0 : ℝ) 1,
          Hybrid.two xi 0 v (multiplier r) q' ≤ Hybrid.two xi 0 v (multiplier r) q) ↔
            q = exposure r v)
  clearing : (∫ v, exposure r v ∂activeValueLaw r) = activeFraction r
  receipt_inward : 0 < bidLower r ∧ bidLower r < bidUpper r ∧
    kappa * bidUpper r < meanReceipt r * bidLower r ∧
    meanReceipt r * bidLower r < meanReceipt r * bidUpper r ∧
    meanReceipt r * bidUpper r < bidLower r ∧
    lowCeiling < kappa * bidLower r ∧
    bidLower r < sourceInwardScale r * activeLower r ∧
    sourceInwardScale r * activeLower r < sourceInwardScale r * activeUpper r ∧
    sourceInwardScale r * activeUpper r < bidUpper r ∧
    bidUpper r < activeLower r ∧ bidUpper r < upperFloor r ∧
    0 < upperFloor r ∧ upperFloor r < upperLower r
  one_maximum : ∀ v : ℝ, ∃ q ∈ Icc (0 : ℝ) 1, ∀ q' ∈ Icc (0 : ℝ) 1,
    Hybrid.one xi 0 v (multiplier r) q' ≤ Hybrid.one xi 0 v (multiplier r) q
  active_menus : ∀ v ∈ Icc (activeLower r) (activeUpper r),
    (∀ q ∈ Icc (0 : ℝ) 1,
      Hybrid.one xi 0 v (multiplier r) q <
        Hybrid.two xi 0 v (multiplier r) (exposure r v)) ∧
    v - upperFloor r < Hybrid.two xi 0 v (multiplier r) (exposure r v) ∧
    Hybrid.two xi 0 v (multiplier r) (exposure r v) = Hybrid.outsideTwo v (multiplier r)
  upper_menus : ∀ v : ℝ, upperLower r ≤ v →
    Hybrid.outsideTwo v (multiplier r) < v - upperFloor r ∧
    (∀ q ∈ Icc (0 : ℝ) 1, Hybrid.one xi 0 v (multiplier r) q < v - upperFloor r) ∧
    (∀ q ∈ Icc (0 : ℝ) 1, Hybrid.two xi 0 v (multiplier r) q < v - upperFloor r)
  active_maxima : ∀ v ∈ Icc (activeLower r) (activeUpper r),
    sourceOneMaximum r v < sourceTwoMaximum r v ∧
      v - upperFloor r < sourceTwoMaximum r v ∧
      sourceTwoMaximum r v = Hybrid.outsideTwo v (multiplier r)
  upper_maxima : ∀ v : ℝ, upperLower r ≤ v →
    sourceTwoMaximum r v < v - upperFloor r ∧
      sourceOneMaximum r v < v - upperFloor r ∧
      Hybrid.outsideTwo v (multiplier r) < v - upperFloor r
  rate_margin : rateMargin r <
    LowBody.jointRate (3 / 200) (activeMass r) (upperMass r) rho -
      2 * Ample.binaryKL rho (1 - upperMass r / 2)
  capacity_floor : ∀ M, marketCapacity M = Nat.floor (rho * (M : ℝ))
  capacity_density : Tendsto (fun M : ℕ => (marketCapacity M : ℝ) / (M : ℝ)) atTop (𝓝 rho)

theorem source_c5_certificate (r : Partition) : SourceC5Certificate r where
  masses := by cases r <;> norm_num [activeMass, upperMass]
  coefficient := by norm_num [xi, eta]
  rank := by cases r <;> norm_num [activeMass, upperMass, rho]
  exposure_fraction := activeFraction_mem r
  low_support := by
    simpa only [bandLower, bandUpper, lowCeiling] using bandLaw_support Band.low
  active_support := activeValueLaw_support r
  upper_support := upperValueLaw_support r
  original_law := sourceValueLaw_decomposition r
  low_compact_map := sourceLowValueLaw_map_val
  active_compact_map := sourceActiveValueLaw_map_val r
  upper_compact_map := sourceUpperValueLaw_map_val r
  low_positive := sourceLowValueLaw_positive
  multiplier_interior := multiplier_bounds r
  optimizer := by
    intro v hv
    exact ⟨exposure_bounds_of_lower r hv.1, fun _ => source_two_zero_argmax_iff r hv.1⟩
  clearing := active_exposure_integral r
  receipt_inward := literal_receipt_inward_guards r
  one_maximum := source_one_maximum_attained r
  active_menus := fun _ hv => literal_active_menu_guards r hv
  upper_menus := fun _ hv => literal_upper_menu_guards r hv
  active_maxima := fun _ hv => literal_active_maximum_guards r hv
  upper_maxima := fun _ hv => literal_upper_maximum_guards r hv
  rate_margin := source_joint_rate_margin r
  capacity_floor := marketCapacity_floor
  capacity_density := marketCapacity_density

end FCAppendix.Affine.Multiple07
