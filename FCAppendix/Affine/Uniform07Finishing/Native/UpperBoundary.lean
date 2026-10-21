import FCAppendix.Affine.Uniform07.ParameterCertificate
import FCAppendix.Affine.Uniform07.SourceLaw
import FCAppendix.Affine.Hybrid.UpperFiniteError
import FCAppendix.Affine.Hybrid.UpperNativeAttainment
import FCAppendix.Affine.Uniform07Finishing.Native.VisibleBids

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open Existence.RankEnvelope

def upperValueMeasure (i : Uniform07.Row) : Measure ℝ :=
  volume.restrict (Icc (Uniform07.cutoff i) 1)

instance upperValueMeasure_finite (i : Uniform07.Row) :
    IsFiniteMeasure (upperValueMeasure i) := by
  unfold upperValueMeasure
  infer_instance

instance upperValueMeasure_atomless (i : Uniform07.Row) :
    NullSingletonClass (upperValueMeasure i) := by
  unfold upperValueMeasure
  infer_instance

def source_upper_rank (i : Uniform07.Row) (m : ℕ) (v : ℝ) : ℝ :=
  rank (upperValueMeasure i) (m - 1) (Uniform07.capacity m) 2 v

theorem upperValueMeasure_mass (i : Uniform07.Row) :
    (upperValueMeasure i).real univ = 1 - Uniform07.cutoff i := by
  rw [upperValueMeasure, measureReal_restrict_apply MeasurableSet.univ, univ_inter]
  change (volume (Icc (Uniform07.cutoff i) (1 : ℝ))).toReal = _
  rw [Real.volume_Icc, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (Uniform07.cutoff_lt_one i).le)]

theorem upperValueMeasure_mass_le_one (i : Uniform07.Row) :
    (upperValueMeasure i).real univ ≤ 1 := by
  rw [upperValueMeasure_mass]
  linarith [Uniform07.cutoff_pos i]

theorem uniform_upper_contactTail (i : Uniform07.Row) {v : ℝ}
    (hv : v ∈ Icc (Uniform07.cutoff i) 1) :
    contactTail (upperValueMeasure i) 2 v = (1 - v) / 2 := by
  unfold contactTail upperValueMeasure
  rw [measureReal_restrict_apply measurableSet_Ioi]
  have hs : Ioi v ∩ Icc (Uniform07.cutoff i) 1 = Ioc v 1 := by
    ext y
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hv.1.trans h.1.le, h.2⟩⟩
  rw [hs, Real.volume_real_Ioc_of_le hv.2]
  norm_num

theorem source_upper_rank_eq_binomial (i : Uniform07.Row) (m : ℕ) {v : ℝ}
    (hv : v ∈ Icc (Uniform07.cutoff i) 1) :
    source_upper_rank i m v =
      (IndependentCounts.binomial (m - 1) ((1 - v) / 2)
        (by linarith [hv.2])
        (by linarith [hv.1, Uniform07.cutoff_pos i])).prob
          (fun k => k.val < Uniform07.capacity m) := by
  rw [source_upper_rank, rank, uniform_upper_contactTail i hv]
  exact rankSuccess_eq_prob _ _ ⟨by linarith [hv.2],
    by linarith [hv.1, Uniform07.cutoff_pos i]⟩

theorem source_upper_rank_eq_source_event (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) {v : ℝ}
    (hv : v ∈ Icc (Uniform07.cutoff i) 1) :
    source_upper_rank i m v =
      (IndependentCounts.binomial (m - 1) ((1 - v) / 2)
        (by linarith [hv.2])
        (by linarith [hv.1, Uniform07.cutoff_pos i])).prob
          (fun k => k.val ≤ Uniform07.capacity m - 1) := by
  rw [source_upper_rank_eq_binomial i m hv]
  congr 1
  funext k
  apply propext
  omega

theorem source_upper_rank_pos (i : Uniform07.Row) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) (v : ℝ) :
    0 < source_upper_rank i m v :=
  rank_pos (upperValueMeasure i) _ _ hc (by norm_num)
    (upperValueMeasure_mass_le_one i) v

theorem source_upper_rank_bounds (i : Uniform07.Row) (m : ℕ) (v : ℝ) :
    source_upper_rank i m v ∈ Icc (0 : ℝ) 1 :=
  rank_bounds (upperValueMeasure i) _ _ (by norm_num)
    (upperValueMeasure_mass_le_one i) v

theorem uniform_upper_subcritical (i : Uniform07.Row) :
    contactTail (upperValueMeasure i) 2 (Uniform07.cutoff i) < Uniform07.rho := by
  rw [uniform_upper_contactTail i ⟨le_rfl, (Uniform07.cutoff_lt_one i).le⟩]
  have ht : (1 / 1000 : ℝ) < Uniform07.cutoff i := by
    cases i
    · linarith [Uniform07.cutoff_first_enclosure.1]
    · linarith [Uniform07.cutoff_second_enclosure.1]
  norm_num [Uniform07.rho]
  linarith

def endogenousUpperFloor (i : Uniform07.Row) (u : ℕ → ℝ) (m : ℕ) : ℝ :=
  Uniform07.cutoff i - u m / source_upper_rank i m (Uniform07.cutoff i)

theorem limiting_floor_boundary_identity (i : Uniform07.Row) :
    Uniform07.cutoff i -
      (Uniform07.cutoff i - Uniform07.entry i)^2 / Uniform07.cutoff i =
        Uniform07.limitingFloor i := by
  have ht := (Uniform07.cutoff_pos i).ne'
  unfold Uniform07.limitingFloor
  field_simp
  ring

theorem endogenous_matching (i : Uniform07.Row) (u : ℕ → ℝ) (m : ℕ)
    (hc : 1 ≤ Uniform07.capacity m) :
    utility (source_upper_rank i m) (Uniform07.cutoff i)
      (endogenousUpperFloor i u m) (Uniform07.cutoff i) = u m := by
  rw [utility_at_floor, endogenousUpperFloor, sub_sub_cancel,
    div_mul_cancel₀ _ (source_upper_rank_pos i m hc _).ne']

theorem endogenous_floor_tendsto (i : Uniform07.Row) (u : ℕ → ℝ)
    (hU : Tendsto u atTop
      (𝓝 ((Uniform07.cutoff i - Uniform07.entry i)^2 / Uniform07.cutoff i)))
    (hq : Tendsto (fun m => source_upper_rank i m (Uniform07.cutoff i))
      atTop (𝓝 1)) :
    Tendsto (endogenousUpperFloor i u) atTop (𝓝 (Uniform07.limitingFloor i)) := by
  have h := (tendsto_const_nhds (x := Uniform07.cutoff i)).sub
    (hU.div hq (by norm_num : (1 : ℝ) ≠ 0))
  convert! h using 1; simp only [div_one, limiting_floor_boundary_identity]

theorem eventually_hidden_guard_moving_floor {E δ R : ℕ → ℝ} {η Rlim : ℝ}
    (hE : Tendsto E atTop (𝓝 0)) (hδ : Tendsto δ atTop (𝓝 0))
    (hR : Tendsto R atTop (𝓝 Rlim)) (hη : 0 < η) (hRlim : 0 < Rlim) :
    ∀ᶠ m in atTop, E m < η * R m * (1 - 2 * δ m) := by
  have h : Tendsto (fun m => η * R m * (1 - 2 * δ m) - E m)
      atTop (𝓝 (η * Rlim)) := by
    simpa only [mul_zero, sub_zero, mul_one] using
      ((hR.const_mul η).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (hδ.const_mul 2))).sub hE
  filter_upwards [h.eventually (eventually_gt_nhds (mul_pos hη hRlim))] with m hm
  linarith

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_payoff_value_increment (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) (v t : ℝ) :
    (problem Γ i).payoff v a = (problem Γ i).payoff t a +
      (v - t) * ((problem Γ i).outcome a).success := by
  change ((problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G =
    ((problem Γ i).outcome a).utility t a.bid Γ.g Γ.A Γ.G + _
  rw [CountLaw.utility_eq, CountLaw.utility_eq]
  ring

theorem upper_beats_actual_lower_above (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) {q : ℝ → ℝ} (hq : Monotone q)
    {t R s v : ℝ} (hs : s < q t) (hv : t < v)
    (hS : ((problem Γ i).outcome a).success ≤ s)
    (ht : (problem Γ i).payoff t a ≤ utility q t R t) :
    (problem Γ i).payoff v a < utility q t R v := by
  apply upper_beats_lower_above hq hs hv
  rw [actual_payoff_value_increment Γ i a v t]
  exact add_le_add ht (mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hv.le))

theorem actual_lower_beats_floor_below (Γ : FiniteGame m n c Seed)
    (i : Fin m) (a : JointAction n) {q : ℝ → ℝ} {t R s v : ℝ}
    (hs : s < q t) (hv : v < t)
    (hS : ((problem Γ i).outcome a).success ≤ s)
    (ht : (problem Γ i).payoff t a = utility q t R t) :
    (v - R) * q t < (problem Γ i).payoff v a := by
  apply lower_beats_floor_below hs hv
  rw [actual_payoff_value_increment Γ i a v t, ht]
  exact add_le_add le_rfl (mul_le_mul_of_nonpos_left hS (sub_nonpos.mpr hv.le))

theorem actual_success_cap_of_joint_bounds (P : CountLaw 2)
    {p pmax e : ℝ} (_hp : 0 ≤ p) (hpm : p ≤ pmax) (hpmax : pmax < 1)
    (hL : P.load ≤ 2 * p) (hD : p^2 - e ≤ P.duplicates)
    (he : e ≤ (1 - pmax)^2 / 2) :
    P.success ≤ 1 - (1 - pmax)^2 / 2 ∧
      1 - (1 - pmax)^2 / 2 < 1 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hpm)
    (show 0 ≤ 2 - p - pmax by linarith)
  have hd : P.duplicates = P.load - P.success := rfl
  have hsq : 0 < (1 - pmax)^2 := sq_pos_of_pos (sub_pos.mpr hpmax)
  constructor <;> nlinarith

theorem native_hidden_upper_below_boundary (Γ : FiniteGame m 2 c Seed)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hg : Γ.g = 0)
    {q : ℝ → ℝ} (hq1 : ∀ x, q x ≤ 1) {t R δ v : ℝ}
    (hR : 0 < R) (hRt : R < t) (hRv : R ≤ v) (hvt : v ≤ t)
    (hguard : error q t R < η * R * (1 - 2 * δ))
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount = 2) (hb : R ≤ a.bid)
    (hmean : 1 - δ ≤ meanAcceptProb Γ i a.bid) :
    (problem Γ i).payoff v a < (v - R) * q t := by
  let P := (problem Γ i).outcome a
  have hD : 1 - 2 * δ ≤ P.duplicates :=
    Hybrid.native_broadcast_duplicates_lower Γ i a hk δ hmean
  have hE := error_nonneg hRt.le hq1
  have hδ : 0 ≤ 1 - 2 * δ := by
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hη0 hR.le) (le_of_not_ge hn)
    linarith
  have hcost := mul_le_mul_of_nonneg_left hD
    (mul_nonneg hη0 (hR.le.trans hb))
  have hfloor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hη0) hδ
  have hS : (v - a.bid) * P.success ≤ v - R := by
    by_cases hvb : a.bid ≤ v
    · have h := mul_le_mul_of_nonneg_left P.success_le_one (sub_nonneg.mpr hvb)
      nlinarith
    · have h := mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_not_ge hvb)) P.success_nonneg
      linarith
  have hEf : (t - R) * (1 - q t) ≤ error q t R := by
    unfold error
    exact le_add_of_nonneg_right (integral_nonneg fun x => sub_nonneg.mpr (hq1 x))
  have hEv := mul_le_mul_of_nonneg_right (sub_le_sub_right hvt R)
    (sub_nonneg.mpr (hq1 t))
  change P.utility v a.bid Γ.g Γ.A Γ.G < _
  rw [hA, hg, affine_zero_base_utility]
  nlinarith

theorem native_hidden_upper_below_floor (Γ : FiniteGame m 2 c Seed)
    {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1) (hg : Γ.g = 0)
    {q : ℝ → ℝ} (hq1 : ∀ x, q x ≤ 1) {t R δ v : ℝ}
    (hR : 0 < R) (hRt : R < t) (hvR : v ≤ R)
    (hguard : error q t R < η * R * (1 - 2 * δ))
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount = 2) (hb : R ≤ a.bid)
    (hmean : 1 - δ ≤ meanAcceptProb Γ i a.bid) :
    (problem Γ i).payoff v a < 0 := by
  let P := (problem Γ i).outcome a
  have hD : 1 - 2 * δ ≤ P.duplicates :=
    Hybrid.native_broadcast_duplicates_lower Γ i a hk δ hmean
  have hE := error_nonneg hRt.le hq1
  have hδ : 0 ≤ 1 - 2 * δ := by
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hη0 hR.le) (le_of_not_ge hn)
    linarith
  have hcost := mul_le_mul_of_nonneg_left hD
    (mul_nonneg hη0 (hR.le.trans hb))
  have hfloor := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hη0) hδ
  have hS := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr (hvR.trans hb)) P.success_nonneg
  change P.utility v a.bid Γ.g Γ.A Γ.G < _
  rw [hA, hg, affine_zero_base_utility]
  nlinarith

end FCAppendix.Affine.Uniform07Finishing
