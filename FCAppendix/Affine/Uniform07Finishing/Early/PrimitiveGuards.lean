import FCAppendix.Affine.Uniform07Finishing.Early.Scalar
import FCAppendix.Affine.Uniform07Finishing.Early.LowTransform

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set

structure UniformFinitePrimitiveGuards (i : Row) : Prop where
  cutoff_gt_delta : delta < cutoff i
  cutoff_bounds : 0 < cutoff i ∧ cutoff i < 1
  floor_ramp_bounds : ∀ v : ℝ, 0 ≤ v → v ≤ cutoff i →
    0 ≤ lowerFloor i v ∧ lowerFloor i v ≤ v ∧ lowerFloor i v ≤ floorMaximum i
  full_floor : ∀ v : ℝ, categoryCutoff i ≤ v →
    lowerFloor i v = chi*(v-smallValue i)
  full_floor_tail : ∀ v : ℝ, fullFloorStart i ≤ v →
    categoryCutoff i ≤ v ∧ (54/100 : ℝ)*cutoff i ≤ lowerFloor i v
  cap_formula : bidCap i = entry i*cutoff i /
    (kappa i*cutoff i+xi i*entry i) + cutoff i/200
  floor_cap_scalars :
    0 < chi ∧ (1/2 : ℝ) < chi ∧ chi < 1/(1+eta i) ∧
    floorMaximum i < entry i ∧
    kappa i*bidCap i < chi*(categoryCutoff i-smallValue i) ∧
    chi*cutoff i < bidCap i ∧
    kappa i*bidCap i < (54/100 : ℝ)*cutoff i ∧
    0 < bidCap i ∧ bidCap i < limitingFloor i ∧
    0 < limitingFloor i ∧ limitingFloor i < cutoff i ∧
    limitingFloor i < entry i/kappa i
  product_route : 1/(1+Real.sqrt (x i))^2 < xi i
  root_demand_positive : 0 < demandRatio i
  root_demand_upper : demandRatio i <
    (Row.casesOn i (342385/10^7 : ℝ) (503276/10^7 : ℝ))
  floor_demand_value :
    (Row.casesOn i (543982/10^7 : ℝ) (597053/10^7 : ℝ)) <
      floorDemand i
  floor_demand_strict : demandRatio i < floorDemand i
  floor_demand_literal : floorDemand i =
    (cutoff i-fullFloorStart i-((54/100 : ℝ)*cutoff i/chi)*
      Real.log ((cutoff i-smallValue i)/(fullFloorStart i-smallValue i))) /
      (xi i*cutoff i)
  root_bounds : kappa i*bidCap i < (54/100 : ℝ)*cutoff i ∧
    (54/100 : ℝ)*cutoff i < (1-xi i*demandRatio i)*bidCap i ∧
    (1-xi i*demandRatio i)*bidCap i < bidCap i
  sampling_margin : 0 < samplingMargin i ∧
    ∀ Λ : ℝ, (54/100 : ℝ)*cutoff i < Λ →
      max (kappa i*bidCap i) ((52/100 : ℝ)*cutoff i) < Λ-samplingMargin i ∧
      ∀ b : ℝ, 0 < b → demandRatio i/4 < clip01 ((1-Λ/b)/xi i) →
        Λ+3*samplingMargin i < b
  seed_guards : (21239/10^5 : ℝ) < seedTailMass i ∧
    (20227/10^5 : ℝ) < seedDemandLower i ∧
    3*demandRatio i < seedDemandLower i ∧
    (Row.casesOn i (145/1000 : ℝ) (193/1000 : ℝ)) <
      activeSeedDemandLower i ∧ 3*demandRatio i < activeSeedDemandLower i
  seed_tail_pointwise : ∀ b : ℝ, (54/100 : ℝ)*cutoff i ≤ b →
    (20/21 : ℝ) ≤ seedPsi i ((52/100 : ℝ)*cutoff i) b
  entropy_margins : (atomMarginQ i : ℝ) < atomRateJ i-atomRateI0 i-atomRateI1 i ∧
    2*atomRateI0 i < atomRateJ i
  low_transform_literal :
    lowTransform i = (1-cutoff i)*Real.exp (-(lowThetaQ i : ℝ)/2)+cutoff i*
      ((lowStartQ i : ℝ)+∫ y in (lowStartQ i : ℝ)..1,
        Real.exp (-(lowThetaQ i : ℝ)*
          ((1-(501/1000 : ℝ)/((69/100 : ℝ)*(y-1/200)))/xi i)))
  low_transform_margins : 0 < lowTransform i ∧
    (lowMarginQ i : ℝ) < lowCanonicalRate i-atomRateI0 i
  upper_interface : delta < cutoff i ∧ 0 < bidCap i ∧
    bidCap i < limitingFloor i ∧ limitingFloor i < cutoff i ∧
    (1-entry i/limitingFloor i)/xi i < 1

theorem primitive_guards (i : Row) : UniformFinitePrimitiveGuards i where
  cutoff_gt_delta := delta_lt_cutoff i
  cutoff_bounds := ⟨cutoff_pos i, cutoff_lt_one i⟩
  floor_ramp_bounds := fun v hv hvt =>
    ⟨lowerFloor_nonneg i v, lowerFloor_le_value i hv, lowerFloor_le_maximum i hvt⟩
  full_floor := fun _ hv => full_floor_formula i hv
  full_floor_tail := fun _ hv => full_floor_tail i hv
  cap_formula := cap_literal_product_formula i
  floor_cap_scalars := scalar_floor_cap_guards i
  product_route := product_route_guard i
  root_demand_positive := demandRatio_pos i
  root_demand_upper := by cases i <;> exact demandRatio_upper _
  floor_demand_value := by
    cases i
    · exact (floor_demand_guards .first).1
    · exact (floor_demand_guards .second).1
  floor_demand_strict := (floor_demand_guards i).2
  floor_demand_literal := floor_demand_source_formula i
  root_bounds := root_scalar_guards i
  sampling_margin := sampling_margin_guards i
  seed_guards := by cases i <;> exact seed_scalar_guards _
  seed_tail_pointwise := fun _ hb => seedPsi_tail_lower i hb
  entropy_margins := atom_entropy_guards i
  low_transform_literal := low_transform_source_integral i
  low_transform_margins := low_canonical_transform_guards i
  upper_interface := upper_floor_interface i

end FCAppendix.Affine.Uniform07Finishing.Early

namespace FCAppendix.Affine.Uniform07

theorem uniform_finite_primitive_guards (i : Row) :
    Uniform07Finishing.Early.UniformFinitePrimitiveGuards i :=
  Uniform07Finishing.Early.primitive_guards i

end FCAppendix.Affine.Uniform07
