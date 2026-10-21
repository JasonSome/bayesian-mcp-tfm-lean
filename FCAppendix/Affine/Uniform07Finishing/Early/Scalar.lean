import FCAppendix.Affine.Uniform07Finishing.Early.LogData
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set Filter Topology

theorem delta_lt_cutoff (i : Row) : delta < cutoff i := by
  apply Box.lower_real (earlyCutoffBox_ok i)
  cases i <;> norm_num [earlyCutoffBox, delta]

theorem demandRatio_pos (i : Row) : 0 < demandRatio i :=
  div_pos (sub_pos.mpr (delta_lt_cutoff i)) (mul_pos (by norm_num) (cutoff_pos i))

def demandRatioBox (i : Row) : Box := Box.div
  (Box.sub (earlyCutoffBox i) (Box.point (1/1000)))
  (Box.scale 2 (earlyCutoffBox i))

theorem demandRatioBox_ok (i : Row) : (demandRatioBox i).Holds (demandRatio i) := by
  have h := Box.div_ok
    (b := Box.scale 2 (earlyCutoffBox i))
    (by cases i <;> norm_num [earlyCutoffBox, Box.scale, Box.mul, Box.point])
    (Box.sub_ok (earlyCutoffBox_ok i) (Box.point_ok (1/1000)))
    (Box.scale_ok 2 (earlyCutoffBox_ok i))
  simpa [demandRatioBox, demandRatio, delta] using h

theorem demandRatio_upper (i : Row) :
    demandRatio i < (match i with
      | .first => (342385/10^7 : ℝ) | .second => (503276/10^7 : ℝ)) := by
  apply Box.upper_real (demandRatioBox_ok i)
  cases i <;> norm_num [demandRatioBox, earlyCutoffBox,
    Box.div, Box.inv, Box.mul, Box.scale, Box.sub, Box.add, Box.neg, Box.point]

theorem demandRatio_lt_one (i : Row) : demandRatio i < 1 := by
  have h := demandRatio_upper i
  cases i <;> norm_num at h <;> linarith

theorem demandRatio_lt_one_eighth (i : Row) : demandRatio i < (1/8 : ℝ) := by
  have h := demandRatio_upper i
  cases i <;> norm_num at h <;> linarith

theorem cap_literal_product_formula (i : Row) :
    bidCap i = entry i * cutoff i /
      (kappa i * cutoff i + xi i * entry i) + cutoff i / 200 := by
  have ht := (cutoff_pos i).ne'
  have hd : kappa i + xi i * x i ≠ 0 := by
    cases i <;> norm_num [kappa, kappaQ, xi, xiQ, x, xQ, etaQ]
  have hd' : kappa i * cutoff i + xi i * entry i ≠ 0 := by
    rw [show kappa i * cutoff i + xi i * entry i =
      (kappa i+xi i*x i)*cutoff i by unfold entry; ring]
    exact mul_ne_zero hd ht
  unfold bidCap capRatioQ entry
  push_cast
  change (x i/(kappa i+xi i*x i)+(1/200 : ℝ))*cutoff i =
    (x i*cutoff i)*cutoff i/(kappa i*cutoff i+xi i*(x i*cutoff i))+cutoff i/200
  field_simp [ht, hd, hd']

theorem scalar_floor_cap_guards (i : Row) :
    0 < chi ∧ (1/2 : ℝ) < chi ∧ chi < 1/(1+eta i) ∧
    floorMaximum i < entry i ∧
    kappa i * bidCap i < chi * (categoryCutoff i - smallValue i) ∧
    chi * cutoff i < bidCap i ∧
    kappa i * bidCap i < (54/100 : ℝ) * cutoff i ∧
    0 < bidCap i ∧ bidCap i < limitingFloor i ∧
    0 < limitingFloor i ∧ limitingFloor i < cutoff i ∧
    limitingFloor i < entry i / kappa i := by
  have ht := cutoff_pos i
  rw [floor_simplify i ht.ne']
  cases i <;>
    norm_num [chi, floorMaximum, smallValue, entry, categoryCutoff, bidCap,
      capRatioQ, eta, etaQ, xi, xiQ, kappa, kappaQ, x, xQ] at * <;>
    (repeat' constructor) <;> nlinarith

theorem kappa_limitingFloor_lt_root_lower (i : Row) :
    kappa i * limitingFloor i < (27/50 : ℝ) * cutoff i := by
  have ht := cutoff_pos i
  rw [floor_simplify i ht.ne']
  cases i <;> norm_num [kappa, kappaQ, xiQ, etaQ, x, xQ] at * <;> nlinarith

theorem root_lower_gap_pos (i : Row) :
    0 < (27/50 : ℝ) * cutoff i - kappa i * limitingFloor i :=
  sub_pos.mpr (kappa_limitingFloor_lt_root_lower i)

theorem kappa_limitingFloor_add_samplingMargin_lt_root_lower (i : Row) :
    kappa i * limitingFloor i + samplingMargin i <
      (27/50 : ℝ) * cutoff i := by
  have ht := cutoff_pos i
  have hr := demandRatio_lt_one_eighth i
  have hξ := xi_pos i
  have hb : samplingMargin i <
      (54/100 : ℝ) * cutoff i * xi i / 128 := by
    have hh := mul_lt_mul_of_pos_left hr
      (show 0 < (54/100 : ℝ) * cutoff i * xi i from by positivity)
    dsimp only [samplingMargin]
    nlinarith
  rw [floor_simplify i ht.ne']
  cases i <;> norm_num [kappa, kappaQ, xi, xiQ, etaQ, x, xQ] at * <;> nlinarith

theorem upper_floor_interface (i : Row) :
    delta < cutoff i ∧ 0 < bidCap i ∧
    bidCap i < limitingFloor i ∧ limitingFloor i < cutoff i ∧
    (1 - entry i / limitingFloor i) / xi i < 1 := by
  have ht := cutoff_pos i
  have hscalar := scalar_floor_cap_guards i
  refine ⟨delta_lt_cutoff i, hscalar.2.2.2.2.2.2.2.1,
    hscalar.2.2.2.2.2.2.2.2.1, hscalar.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  rw [floor_simplify i ht.ne']
  have hid : entry i / (cutoff i * (2*x i-x i^2)) =
      x i / (2*x i-x i^2) := by
    unfold entry
    cases i <;> norm_num [x, xQ] <;> field_simp [ht.ne'] <;> ring
  rw [hid]
  cases i <;> norm_num [x, xQ, xi, xiQ, etaQ]

theorem product_route_guard (i : Row) :
    1/(1 + Real.sqrt (x i))^2 < xi i := by
  have hx : 0 < x i := by cases i <;> norm_num [x, xQ]
  have hs : 0 ≤ Real.sqrt (x i) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hx.le
  have hl : (4/5 : ℝ) < Real.sqrt (x i) := by
    cases i <;> norm_num [x, xQ] at * <;> nlinarith
  rw [div_lt_iff₀ (by positivity : 0 < (1 + Real.sqrt (x i))^2)]
  have hsquare := sq_nonneg (Real.sqrt (x i)-4/5)
  cases i <;> norm_num [xi, xiQ, etaQ] at * <;> nlinarith

theorem clip01_mem (u : ℝ) : clip01 u ∈ Icc 0 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem lowerFloor_nonneg (i : Row) (v : ℝ) : 0 ≤ lowerFloor i v := by
  unfold lowerFloor
  exact mul_nonneg (mul_nonneg (by norm_num [chi]) (le_max_right _ _))
    (clip01_mem _).1

theorem lowerFloor_le_maximum (i : Row) {v : ℝ}
    (hv : v ≤ cutoff i) : lowerFloor i v ≤ floorMaximum i := by
  have ht := cutoff_pos i
  have hsmall : 0 ≤ cutoff i - smallValue i := by dsimp [smallValue]; linarith
  have hmax : max (v - smallValue i) 0 ≤ cutoff i - smallValue i :=
    max_le (sub_le_sub_right hv _) hsmall
  have hχ : 0 ≤ chi := by norm_num [chi]
  calc
    _ ≤ chi * max (v - smallValue i) 0 := by
      apply mul_le_of_le_one_right
      · exact mul_nonneg hχ (le_max_right _ _)
      · exact (clip01_mem _).2
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hχ

theorem lowerFloor_le_value (i : Row) {v : ℝ} (hv : 0 ≤ v) : lowerFloor i v ≤ v := by
  have ht := cutoff_pos i
  have hs : 0 ≤ smallValue i := by dsimp [smallValue]; positivity
  have hmax : max (v-smallValue i) 0 ≤ v := max_le (by linarith) hv
  calc
    _ ≤ chi * max (v-smallValue i) 0 := by
      apply mul_le_of_le_one_right
      · unfold chi; positivity
      · exact (clip01_mem _).2
    _ ≤ chi * v := mul_le_mul_of_nonneg_left hmax (by norm_num [chi])
    _ ≤ v := by dsimp [chi]; nlinarith

theorem fullFloorStartQ_value (i : Row) : fullFloorStartQ i = 3623/4600 := by
  cases i <;> norm_num [fullFloorStartQ, xQ]

theorem full_floor_formula (i : Row) {v : ℝ} (hv : categoryCutoff i ≤ v) :
    lowerFloor i v = chi * (v-smallValue i) := by
  have ht := cutoff_pos i
  have hd : 0 < categoryCutoff i - floorStart i := by
    dsimp [categoryCutoff, floorStart]; linarith
  have hvs : smallValue i ≤ v := by
    have hx : 0 ≤ entry i := by
      dsimp [entry]
      exact mul_nonneg (by cases i <;> norm_num [x, xQ]) ht.le
    dsimp [categoryCutoff, smallValue] at *
    linarith
  have hr : 1 ≤ (v-floorStart i)/(categoryCutoff i-floorStart i) := by
    rw [le_div_iff₀ hd]; linarith
  simp [lowerFloor, clip01, max_eq_left (sub_nonneg.mpr hvs), min_eq_left hr]

theorem full_floor_tail (i : Row) {v : ℝ} (hv : fullFloorStart i ≤ v) :
    categoryCutoff i ≤ v ∧ (54/100 : ℝ)*cutoff i ≤ lowerFloor i v := by
  have ht := cutoff_pos i
  have hc : categoryCutoff i ≤ fullFloorStart i := by
    dsimp [categoryCutoff, fullFloorStart, entry]
    rw [fullFloorStartQ_value]
    cases i <;> norm_num [x, xQ] <;> nlinarith
  have hcat := hc.trans hv
  refine ⟨hcat, ?_⟩
  rw [full_floor_formula i hcat]
  dsimp [fullFloorStart] at hv
  rw [fullFloorStartQ_value] at hv
  dsimp [chi, smallValue]
  nlinarith

def floorDemandBox (i : Row) : Box := Box.scale (1/xiQ i)
  (Box.sub (Box.point (1-3623/4600)) (Box.scale (54/69) floorLog.box))

theorem floorDemandBox_ok (i : Row) : (floorDemandBox i).Holds (floorDemand i) := by
  have h := Box.scale_ok (1/xiQ i)
    (Box.sub_ok (Box.point_ok (1-3623/4600)) (Box.scale_ok (54/69) floorLog.correct))
  convert h using 1
  · rfl
  · rw [floorDemand, fullFloorStartQ_value]
    norm_num [xi]
    ring

theorem floor_demand_source_formula (i : Row) :
    floorDemand i =
      (cutoff i - fullFloorStart i - ((54/100 : ℝ)*cutoff i/chi) *
        Real.log ((cutoff i-smallValue i)/(fullFloorStart i-smallValue i))) /
      (xi i*cutoff i) := by
  have ht := (cutoff_pos i).ne'
  have hx := (xi_pos i).ne'
  have hratio : (cutoff i-smallValue i)/(fullFloorStart i-smallValue i) =
      (199/200 : ℝ)/((fullFloorStartQ i : ℝ)-1/200) := by
    rw [fullFloorStartQ_value]
    dsimp [smallValue, fullFloorStart]
    rw [fullFloorStartQ_value]
    field_simp [ht]
    ring
  rw [hratio]
  unfold floorDemand fullFloorStart chi
  field_simp [ht, hx]

theorem floor_demand_shifted_integral (i : Row) :
    floorDemand i = (1/xi i) *
      ∫ y in (54/69 : ℝ)..(199/200 : ℝ), (1-(54/69 : ℝ)/y) := by
  have h := integral_moment (1 : ℝ) (54/69 : ℝ) 1
    (l := (54/69 : ℝ)) (h := (199/200 : ℝ)) (by norm_num) (by norm_num)
  simp only [pow_one] at h
  rw [h]
  unfold floorDemand
  rw [fullFloorStartQ_value]
  have hlog : Real.log ((199/200 : ℝ)/(54/69 : ℝ)) =
      Real.log (199/200 : ℝ)-Real.log (54/69 : ℝ) := by
    exact Real.log_div (by norm_num) (by norm_num)
  norm_num at hlog
  norm_num [moment, invMoment, Finset.sum_range_succ]
  rw [hlog]
  ring

theorem floor_demand_guards (i : Row) :
    (match i with | .first => (543982/10^7 : ℝ) | .second => (597053/10^7 : ℝ)) < floorDemand i ∧
    demandRatio i < floorDemand i := by
  have hb : (match i with | .first => (543982/10^7 : ℝ) | .second => (597053/10^7 : ℝ)) < floorDemand i := by
    apply Box.lower_real (floorDemandBox_ok i)
    cases i <;> norm_num [floorDemandBox, floorLog, LogCertificate.box,
      xiQ, etaQ, Box.scale, Box.mul, Box.point, Box.sub, Box.add, Box.neg]
  refine ⟨hb, ?_⟩
  have hr := demandRatio_upper i
  cases i <;> norm_num at hb hr <;> linarith

theorem root_scalar_guards (i : Row) :
    kappa i * bidCap i < (54/100 : ℝ) * cutoff i ∧
    (54/100 : ℝ) * cutoff i < (1-xi i*demandRatio i)*bidCap i ∧
    (1-xi i*demandRatio i)*bidCap i < bidCap i := by
  have ht := cutoff_pos i
  have hr0 := demandRatio_pos i
  have hr1 := demandRatio_upper i
  have hξ := xi_pos i
  have hU : 0 < bidCap i := by
    dsimp [bidCap]; cases i <;> norm_num [capRatioQ, xQ, kappaQ, xiQ, etaQ] <;> positivity
  constructor
  · dsimp [bidCap]
    cases i <;> norm_num [capRatioQ, kappa, kappaQ, xQ, xiQ, etaQ] <;> nlinarith
  constructor
  · cases i <;> norm_num [bidCap, capRatioQ, kappaQ, xQ, xi, xiQ, etaQ] at * <;>
      nlinarith [mul_lt_mul_of_pos_right hr1 ht]
  · nlinarith [mul_pos hξ hr0, mul_pos (mul_pos hξ hr0) hU]

theorem seed_scalar_guards (i : Row) :
    (21239/10^5 : ℝ) < seedTailMass i ∧
    (20227/10^5 : ℝ) < seedDemandLower i ∧
    3*demandRatio i < seedDemandLower i ∧
    (match i with | .first => (145/1000 : ℝ) | .second => (193/1000 : ℝ)) < activeSeedDemandLower i ∧
    3*demandRatio i < activeSeedDemandLower i := by
  have hr := demandRatio_upper i
  cases i <;> norm_num [seedTailMass, seedDemandLower, fullFloorStartQ, xQ,
    activeSeedDemandLower, normalizedProductBid, activeSeedStartQ, activeSeedLevelQ,
    x, xi, kappa, xiQ, kappaQ, etaQ] at * <;> repeat' constructor <;> linarith

theorem seedPsi_tail_lower (i : Row) {b : ℝ}
    (hb : (54/100 : ℝ)*cutoff i ≤ b) :
    (20/21 : ℝ) ≤ seedPsi i ((52/100 : ℝ)*cutoff i) b := by
  have ht := cutoff_pos i
  have hbp : 0 ≤ b-(52/100 : ℝ)*cutoff i := by nlinarith
  unfold seedPsi
  rw [max_eq_left hbp]
  have hd : 0 < cutoff i/1000+(b-(52/100 : ℝ)*cutoff i) := by nlinarith
  rw [le_div_iff₀ hd]
  nlinarith

theorem sampling_margin_guards (i : Row) :
    0 < samplingMargin i ∧
    ∀ (Λ : ℝ), (54/100 : ℝ)*cutoff i < Λ →
      max (kappa i*bidCap i) ((52/100 : ℝ)*cutoff i) < Λ-samplingMargin i ∧
      ∀ b : ℝ, 0 < b → demandRatio i/4 <
        clip01 ((1-Λ/b)/xi i) → Λ+3*samplingMargin i < b := by
  have ht := cutoff_pos i
  have hξ := xi_pos i
  have hr0 := demandRatio_pos i
  have hr1 := demandRatio_upper i
  have ha : 0 < samplingMargin i := by unfold samplingMargin; positivity
  refine ⟨ha, ?_⟩
  intro Λ hΛ
  have hΛ0 : 0 < Λ := lt_trans (by positivity) hΛ
  have hsmall : samplingMargin i < (1/100 : ℝ)*cutoff i := by
    unfold samplingMargin
    cases i <;> norm_num [xi, xiQ, etaQ] at * <;>
      nlinarith [mul_lt_mul_of_pos_right hr1 ht]
  have hk : kappa i*bidCap i < (53/100 : ℝ)*cutoff i := by
    unfold bidCap
    cases i <;> norm_num [capRatioQ, kappa, kappaQ, xQ, xiQ, etaQ] <;> nlinarith
  refine ⟨max_lt (by linarith) (by linarith), ?_⟩
  intro b hb hp
  have hclip : demandRatio i/4 < (1-Λ/b)/xi i := by
    by_contra h
    have hle : clip01 ((1-Λ/b)/xi i) ≤ demandRatio i/4 := by
      apply max_le (by positivity)
      exact (min_le_right _ _).trans (le_of_not_gt h)
    linarith
  have hmul := (lt_div_iff₀ hξ).mp hclip
  have hrent : b*(xi i*demandRatio i/4) < b-Λ := by
    calc
      _ = (demandRatio i/4*xi i)*b := by ring
      _ < (1-Λ/b)*b := mul_lt_mul_of_pos_right hmul hb
      _ = b-Λ := by field_simp [hb.ne']
  have hbΛ : Λ < b := by
    have hproduct : 0 < b*(xi i*demandRatio i/4) := by positivity
    linarith
  have hscale : 0 < xi i*demandRatio i/4 := by positivity
  have hlow := mul_lt_mul_of_pos_right (hΛ.trans hbΛ) hscale
  unfold samplingMargin
  nlinarith [hrent, hlow]

theorem capacity_floor (m : ℕ) :
    capacity m = Nat.floor ((4995/10000 : ℝ)*(m : ℝ)) := by
  have hr : (999*m)%2000 < 2000 := Nat.mod_lt _ (by norm_num)
  have he : (999*m)%2000 + 2000*((999*m)/2000) = 999*m := Nat.mod_add_div _ _
  have hrR : (((999*m)%2000 : ℕ) : ℝ) < 2000 := by exact_mod_cast hr
  have heR : (((999*m)%2000 : ℕ) : ℝ) +
      2000*(((999*m)/2000 : ℕ) : ℝ) = 999*(m : ℝ) := by exact_mod_cast he
  have hn : (0 : ℝ) ≤ (((999*m)%2000 : ℕ) : ℝ) := Nat.cast_nonneg _
  symm
  apply (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ (4995/10000 : ℝ)*(m : ℝ))).2
  unfold capacity
  constructor <;> nlinarith

theorem capacity_floor_rho (m : ℕ) :
    capacity m = Nat.floor (rho*(m : ℝ)) := by
  simpa only [rho, show (4995/10000 : ℝ) = 999/2000 by norm_num]
    using capacity_floor m

theorem capacity_density_limit :
    Tendsto (fun m : ℕ => (capacity m : ℝ)/(m : ℝ)) atTop (𝓝 rho) := by
  simpa only [Function.comp_def, ← capacity_floor_rho] using
    (tendsto_nat_floor_mul_div_atTop (show 0 ≤ rho by norm_num [rho])).comp
      tendsto_natCast_atTop_atTop

theorem capacity_tendsto : Tendsto capacity atTop atTop := by
  simpa only [Function.comp_def, ← capacity_floor_rho] using
    tendsto_nat_floor_mul_atTop rho (show 0 < rho by norm_num [rho])

end FCAppendix.Affine.Uniform07Finishing.Early
