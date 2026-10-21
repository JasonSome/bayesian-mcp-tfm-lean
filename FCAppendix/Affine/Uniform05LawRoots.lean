import FCAppendix.Affine.Uniform05Rows
import FCAppendix.Affine.Uniform05Roots

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

abbrev Bid (i : Row) := Icc (0 : ℝ) (cap i)

instance bidCompactSpace (i : Row) : CompactSpace (Bid i) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

lemma cap_pos (i : Row) : 0 < cap i := by
  rw [cap_eq_ratio]
  exact mul_pos (capRatio_pos i) (t_pos i)

instance bidNonempty (i : Row) : Nonempty (Bid i) :=
  ⟨⟨0, le_rfl, (cap_pos i).le⟩⟩

def rejectionScale (i : Row) : ℝ := t i/1000

def rejectionExposure (d₀ z b : ℝ) : ℝ :=
  max 0 (b-z)/(d₀+max 0 (b-z))

lemma rejectionScale_pos (i : Row) : 0 < rejectionScale i := by
  have ht := t_pos i
  unfold rejectionScale
  positivity

lemma rejectionExposure_nonneg {d₀ z b : ℝ} (hd : 0 < d₀) :
    0 ≤ rejectionExposure d₀ z b := by
  unfold rejectionExposure
  exact div_nonneg (le_max_left _ _) (by positivity)

lemma rejectionExposure_le_one {d₀ z b : ℝ} (hd : 0 < d₀) :
    rejectionExposure d₀ z b ≤ 1 := by
  unfold rejectionExposure
  apply (div_le_iff₀ (by positivity : 0 < d₀+max 0 (b-z))).2
  linarith

lemma rejectionExposure_zero {d₀ z b : ℝ} (hb : b ≤ z) :
    rejectionExposure d₀ z b = 0 := by
  simp [rejectionExposure, max_eq_left (sub_nonpos.mpr hb)]

lemma continuous_rejectionExposure {d₀ : ℝ} (hd : 0 < d₀) :
    Continuous (fun p : ℝ × ℝ => rejectionExposure d₀ p.1 p.2) := by
  unfold rejectionExposure
  apply (continuous_const.max (continuous_snd.sub continuous_fst)).div
    (continuous_const.add (continuous_const.max (continuous_snd.sub continuous_fst)))
  intro p
  exact ne_of_gt (by positivity : 0 < d₀+max 0 (p.2-p.1))

lemma rejectionExposure_monotone_bid {d₀ z : ℝ} (hd : 0 < d₀) :
    Monotone (rejectionExposure d₀ z) := by
  intro a b hab
  have hposA : 0 < d₀+max 0 (a-z) := by positivity
  have hposB : 0 < d₀+max 0 (b-z) := by positivity
  have hm : max 0 (a-z) ≤ max 0 (b-z) := max_le_max_left _ (by linarith)
  unfold rejectionExposure
  apply (div_le_div_iff₀ hposA hposB).2
  nlinarith

lemma exposure_eq_min_of_above {ξ z b : ℝ}
    (hξ : 0 < ξ) (hz : 0 < z) (hb : z < b) :
    exposure ξ z b = min 1 ((1-z/b)/ξ) := by
  have hb0 : 0 < b := hz.trans hb
  rw [exposure, max_eq_left hb.le, max_eq_right (sub_nonneg.mpr hb.le)]
  congr 1
  field_simp [hξ.ne',hb0.ne']

lemma exposure_monotone_bid {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z) :
    Monotone (exposure ξ z) := by
  intro a b hab
  by_cases ha : a ≤ z
  · rw [exposure_zero ha]
    exact exposure_nonneg hξ hz
  · have hza : z < a := lt_of_not_ge ha
    have hzb := hza.trans_le hab
    rw [exposure_eq_min_of_above hξ hz hza,
      exposure_eq_min_of_above hξ hz hzb]
    apply min_le_min_left
    apply div_le_div_of_nonneg_right _ hξ.le
    have hr := div_le_div_of_nonneg_left hz.le (hz.trans hza) hab
    linarith

lemma exposure_z_interval_bound {ξ U lo a b v : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (hguard : (1-ξ)*U ≤ lo) (hvU : v ≤ U)
    (ha : lo ≤ a) (hab : a ≤ b) :
    0 ≤ exposure ξ a v-exposure ξ b v ∧
      exposure ξ a v-exposure ξ b v ≤ (b-a)/(ξ*lo) := by
  have hapos : 0 < a := hlo.trans_le ha
  have hbpos : 0 < b := hapos.trans_le hab
  have hκ : 0 ≤ 1-ξ := by linarith
  have hga : (1-ξ)*v ≤ a :=
    (mul_le_mul_of_nonneg_left hvU hκ).trans (hguard.trans ha)
  by_cases hva : v ≤ a
  · rw [exposure_zero hva, exposure_zero (hva.trans hab)]
    constructor
    · simp
    · simp only [sub_self]
      positivity
  · have hav : a < v := lt_of_not_ge hva
    have hvpos : 0 < v := hapos.trans hav
    rw [exposure_of_between hξ hapos hav hga]
    by_cases hvb : v ≤ b
    · rw [exposure_zero hvb, sub_zero]
      have he : (1-a/v)/ξ = (v-a)/(ξ*v) := by
        field_simp [hξ.ne',hvpos.ne']
      rw [he]
      refine ⟨by positivity, ?_⟩
      calc
        (v-a)/(ξ*v) ≤ (b-a)/(ξ*v) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        _ ≤ (b-a)/(ξ*lo) :=
          div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (mul_pos hξ hlo)
            (mul_le_mul_of_nonneg_left (ha.trans hav.le) hξ.le)
    · have hbv : b < v := lt_of_not_ge hvb
      rw [exposure_of_between hξ hbpos hbv (hga.trans hab)]
      have he : (1-a/v)/ξ-(1-b/v)/ξ = (b-a)/(ξ*v) := by
        field_simp [hξ.ne',hvpos.ne']
        ring
      rw [he]
      refine ⟨by positivity, ?_⟩
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab) (mul_pos hξ hlo)
        (mul_le_mul_of_nonneg_left (ha.trans hav.le) hξ.le)

lemma exposure_abs_sub_z {ξ U lo a b v : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hlo : 0 < lo)
    (hguard : (1-ξ)*U ≤ lo) (hvU : v ≤ U) (ha : lo ≤ a) (hb : lo ≤ b) :
    |exposure ξ a v-exposure ξ b v| ≤ |a-b| /(ξ*lo) := by
  rcases le_total a b with hab | hba
  · have h := exposure_z_interval_bound hξ hξ1 hlo hguard hvU ha hab
    rw [abs_of_nonneg h.1, abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using h.2
  · have h := exposure_z_interval_bound hξ hξ1 hlo hguard hvU hb hba
    rw [abs_sub_comm, abs_sub_comm a b,
      abs_of_nonneg h.1, abs_of_nonpos (sub_nonpos.mpr hba)]
    simpa only [neg_sub] using h.2

lemma rejectionExposure_z_interval_bound {d₀ a b v : ℝ}
    (hd : 0 < d₀) (hab : a ≤ b) :
    0 ≤ rejectionExposure d₀ a v-rejectionExposure d₀ b v ∧
      rejectionExposure d₀ a v-rejectionExposure d₀ b v ≤ (b-a)/d₀ := by
  let x := max 0 (v-a)
  let y := max 0 (v-b)
  have hx0 : 0 ≤ x := le_max_left _ _
  have hy0 : 0 ≤ y := le_max_left _ _
  have hyx : y ≤ x := max_le_max_left _ (by linarith)
  have hxy : x-y ≤ b-a := by
    dsimp [x,y]
    by_cases hva : v ≤ a
    · rw [max_eq_left (sub_nonpos.mpr hva),
        max_eq_left (sub_nonpos.mpr (hva.trans hab))]
      linarith
    · rw [max_eq_right (by linarith : 0 ≤ v-a)]
      have hm : v-b ≤ max 0 (v-b) := le_max_right _ _
      linarith
  have hdenA : 0 < d₀+x := by linarith
  have hdenB : 0 < d₀+y := by linarith
  have he : rejectionExposure d₀ a v-rejectionExposure d₀ b v =
      d₀*(x-y)/((d₀+x)*(d₀+y)) := by
    change x/(d₀+x)-y/(d₀+y) = _
    field_simp [hdenA.ne',hdenB.ne']
    ring
  rw [he]
  refine ⟨by positivity, ?_⟩
  apply (div_le_div_iff₀ (mul_pos hdenA hdenB) hd).2
  have hden : d₀^2 ≤ (d₀+x)*(d₀+y) := by nlinarith [mul_nonneg hx0 hy0]
  have hm := mul_le_mul_of_nonneg_left hden (sub_nonneg.mpr hab)
  have hn := mul_le_mul_of_nonneg_left hxy (sq_nonneg d₀)
  nlinarith

lemma rejectionExposure_abs_sub_z {d₀ a b v : ℝ} (hd : 0 < d₀) :
    |rejectionExposure d₀ a v-rejectionExposure d₀ b v| ≤ |a-b| /d₀ := by
  rcases le_total a b with hab | hba
  · have h := rejectionExposure_z_interval_bound (v := v) hd hab
    rw [abs_of_nonneg h.1, abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using h.2
  · have h := rejectionExposure_z_interval_bound (v := v) hd hba
    rw [abs_sub_comm, abs_sub_comm a b,
      abs_of_nonneg h.1, abs_of_nonpos (sub_nonpos.mpr hba)]
    simpa only [neg_sub] using h.2

lemma rejectionExposure_drop {d₀ U a b v : ℝ}
    (hd : 0 < d₀) (hU : 0 ≤ U) (ha : 0 ≤ a) (hab : a ≤ b) (hv : v ≤ U) :
    (d₀/(d₀+U)^2)*(b-a)*rejectionExposure d₀ b v ≤
      rejectionExposure d₀ a v-rejectionExposure d₀ b v := by
  by_cases hvb : v ≤ b
  · rw [rejectionExposure_zero hvb, mul_zero, sub_zero]
    exact rejectionExposure_nonneg hd
  · have hbv : b < v := lt_of_not_ge hvb
    have hav : a < v := hab.trans_lt hbv
    have hda : 0 < d₀+(v-a) := by linarith
    have hdb : 0 < d₀+(v-b) := by linarith
    have hdU : 0 < d₀+U := by linarith
    have he : rejectionExposure d₀ a v-rejectionExposure d₀ b v =
        d₀*(b-a)/((d₀+(v-a))*(d₀+(v-b))) := by
      rw [rejectionExposure, rejectionExposure,
        max_eq_right (sub_nonneg.mpr hav.le), max_eq_right (sub_nonneg.mpr hbv.le)]
      field_simp [hda.ne',hdb.ne']
      ring
    have hden : (d₀+(v-a))*(d₀+(v-b)) ≤ (d₀+U)^2 := by
      have h₁ : d₀+(v-a) ≤ d₀+U := by linarith
      have h₂ : d₀+(v-b) ≤ d₀+U := by linarith
      simpa [sq] using mul_le_mul h₁ h₂ hdb.le hdU.le
    calc
      (d₀/(d₀+U)^2)*(b-a)*rejectionExposure d₀ b v
          ≤ (d₀/(d₀+U)^2)*(b-a) := by
        exact (mul_le_mul_of_nonneg_left (rejectionExposure_le_one hd) (by positivity)).trans_eq
          (mul_one _)
      _ = d₀*(b-a)/(d₀+U)^2 := by ring
      _ ≤ d₀*(b-a)/((d₀+(v-a))*(d₀+(v-b))) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hda hdb) hden
      _ = _ := he.symm

section ProbabilityBounds
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_of_unit_bounds (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [] with x
  simpa [Real.norm_eq_abs, abs_of_nonneg (h0 x)] using h1 x

lemma abs_integral_sub_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    {C : ℝ} (h : ∀ x, |f x-g x| ≤ C) :
    |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)| ≤ C := by
  rw [← integral_sub hf hg]
  calc
    |∫ x, f x-g x ∂μ| = ‖∫ x, f x-g x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f x-g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, C ∂μ := integral_mono (hf.sub hg).norm (integrable_const _) (by
      intro x
      simpa [Real.norm_eq_abs] using h x)
    _ = C := by simp

end ProbabilityBounds

def lawDemand (i : Row) (G : ProbabilityMeasure (Bid i)) (z : ℝ) : ℝ :=
  ∫ b, exposure (xi i) z (b : ℝ) ∂(G : Measure (Bid i))

def lawRejection (i : Row) (G : ProbabilityMeasure (Bid i)) (z : ℝ) : ℝ :=
  ∫ b, rejectionExposure (rejectionScale i) z (b : ℝ) ∂(G : Measure (Bid i))

lemma integrable_lawDemand (i : Row) (G : ProbabilityMeasure (Bid i))
    {z : ℝ} (hz : 0 < z) :
    Integrable (fun b : Bid i => exposure (xi i) z (b : ℝ)) (G : Measure (Bid i)) := by
  apply integrable_of_unit_bounds
  · exact ((continuous_exposure (xi_range i).1 hz).comp continuous_subtype_val).measurable
  · exact fun _ => exposure_nonneg (xi_range i).1 hz
  · exact fun _ => exposure_le_one _ _ _

lemma integrable_lawRejection (i : Row) (G : ProbabilityMeasure (Bid i)) (z : ℝ) :
    Integrable (fun b : Bid i => rejectionExposure (rejectionScale i) z (b : ℝ))
      (G : Measure (Bid i)) := by
  apply integrable_of_unit_bounds
  · exact ((continuous_rejectionExposure (rejectionScale_pos i)).comp
      (continuous_const.prodMk continuous_subtype_val)).measurable
  · exact fun _ => rejectionExposure_nonneg (rejectionScale_pos i)
  · exact fun _ => rejectionExposure_le_one (rejectionScale_pos i)

lemma lawDemand_drop (i : Row) (G : ProbabilityMeasure (Bid i))
    {lo a b : ℝ} (hlo : 0 < lo) (hguard : kappa i*cap i ≤ lo)
    (ha : lo ≤ a) (hab : a ≤ b) :
    (b-a)/(xi i*cap i)*lawDemand i G b ≤ lawDemand i G a-lawDemand i G b := by
  have hapos := hlo.trans_le ha
  have hbpos := hapos.trans_le hab
  unfold lawDemand
  rw [← integral_const_mul, ← integral_sub
    (integrable_lawDemand i G hapos) (integrable_lawDemand i G hbpos)]
  apply integral_mono
    ((integrable_lawDemand i G hbpos).const_mul _)
    ((integrable_lawDemand i G hapos).sub (integrable_lawDemand i G hbpos))
  intro v
  exact exposure_drop (xi_range i).1 (xi_range i).2 (cap_pos i) hapos
    (by simpa [kappa] using hguard.trans ha) hab v.2.2

lemma lawRejection_drop (i : Row) (G : ProbabilityMeasure (Bid i))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (rejectionScale i/(rejectionScale i+cap i)^2)*(b-a)*lawRejection i G b ≤
      lawRejection i G a-lawRejection i G b := by
  unfold lawRejection
  rw [← integral_const_mul, ← integral_sub
    (integrable_lawRejection i G a) (integrable_lawRejection i G b)]
  apply integral_mono
    ((integrable_lawRejection i G b).const_mul _)
    ((integrable_lawRejection i G a).sub (integrable_lawRejection i G b))
  intro v
  exact rejectionExposure_drop (rejectionScale_pos i) (cap_pos i).le ha hab v.2.2

lemma lawDemand_nonneg (i : Row) (G : ProbabilityMeasure (Bid i))
    {z : ℝ} (hz : 0 < z) : 0 ≤ lawDemand i G z :=
  integral_nonneg (fun _ => exposure_nonneg (xi_range i).1 hz)

lemma lawRejection_nonneg (i : Row) (G : ProbabilityMeasure (Bid i)) (z : ℝ) :
    0 ≤ lawRejection i G z :=
  integral_nonneg (fun _ => rejectionExposure_nonneg (rejectionScale_pos i))

lemma lawDemand_at_cap (i : Row) (G : ProbabilityMeasure (Bid i)) :
    lawDemand i G (cap i) = 0 := by
  unfold lawDemand
  have hz : (fun b : Bid i => exposure (xi i) (cap i) (b : ℝ)) = fun _ => 0 := by
    funext b
    exact exposure_zero b.2.2
  rw [hz]
  simp

lemma lawRejection_at_cap (i : Row) (G : ProbabilityMeasure (Bid i)) :
    lawRejection i G (cap i) = 0 := by
  unfold lawRejection
  have hz : (fun b : Bid i => rejectionExposure (rejectionScale i) (cap i) (b : ℝ)) =
      fun _ => 0 := by
    funext b
    exact rejectionExposure_zero b.2.2
  rw [hz]
  simp

lemma lawDemand_abs_sub (i : Row) (G : ProbabilityMeasure (Bid i))
    {lo a b : ℝ} (hlo : 0 < lo) (hguard : kappa i*cap i ≤ lo)
    (ha : lo ≤ a) (hb : lo ≤ b) :
    |lawDemand i G a-lawDemand i G b| ≤ |a-b| /(xi i*lo) := by
  apply abs_integral_sub_le _
    (integrable_lawDemand i G (hlo.trans_le ha))
    (integrable_lawDemand i G (hlo.trans_le hb))
  intro v
  exact exposure_abs_sub_z (xi_range i).1 (xi_range i).2 hlo
    (by simpa [kappa] using hguard) v.2.2 ha hb

lemma lawRejection_abs_sub (i : Row) (G : ProbabilityMeasure (Bid i)) (a b : ℝ) :
    |lawRejection i G a-lawRejection i G b| ≤ |a-b| /rejectionScale i := by
  apply abs_integral_sub_le _ (integrable_lawRejection i G a) (integrable_lawRejection i G b)
  intro v
  exact rejectionExposure_abs_sub_z (rejectionScale_pos i)

lemma continuousOn_lawDemand (i : Row) (G : ProbabilityMeasure (Bid i))
    {lo hi : ℝ} (hlo : 0 < lo) (hguard : kappa i*cap i ≤ lo) :
    ContinuousOn (lawDemand i G) (Icc lo hi) := by
  rw [continuousOn_iff_continuous_restrict]
  have hξ := (xi_range i).1
  let K : NNReal := ⟨1/(xi i*lo), by positivity⟩
  have hlip : LipschitzWith K (fun z : Icc lo hi => lawDemand i G z) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have hK : (K : ℝ) = 1/(xi i*lo) := rfl
    rw [hK, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      lawDemand_abs_sub i G hlo hguard a.2.1 b.2.1
  exact hlip.continuous

lemma continuous_lawRejection (i : Row) (G : ProbabilityMeasure (Bid i)) :
    Continuous (lawRejection i G) := by
  let K : NNReal := ⟨1/rejectionScale i, (one_div_pos.mpr (rejectionScale_pos i)).le⟩
  have hlip : LipschitzWith K (lawRejection i G) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    have hK : (K : ℝ) = 1/rejectionScale i := rfl
    rw [hK, Real.dist_eq, Real.dist_eq]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using lawRejection_abs_sub i G a b
  exact hlip.continuous

lemma continuous_lawDemand_in_law (i : Row) {z : ℝ} (hz : 0 < z) :
    Continuous (fun G : ProbabilityMeasure (Bid i) => lawDemand i G z) := by
  let f : C(Bid i, ℝ) := ⟨fun b => exposure (xi i) z (b : ℝ),
    (continuous_exposure (xi_range i).1 hz).comp continuous_subtype_val⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

lemma continuous_lawRejection_in_law (i : Row) (z : ℝ) :
    Continuous (fun G : ProbabilityMeasure (Bid i) => lawRejection i G z) := by
  let f : C(Bid i, ℝ) := ⟨fun b => rejectionExposure (rejectionScale i) z (b : ℝ),
    (continuous_rejectionExposure (rejectionScale_pos i)).comp
      (continuous_const.prodMk continuous_subtype_val)⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

abbrev RootDomain (i : Row) :=
  {G : ProbabilityMeasure (Bid i) //
    requiredDemand i < lawDemand i G ((54 : ℝ)/100*t i) ∧
    3*requiredDemand i < lawRejection i G ((52 : ℝ)/100*t i)}

lemma demandLo_pos (i : Row) : 0 < (54 : ℝ)/100*t i := by
  have ht := t_pos i
  positivity

lemma demandLo_lt_cap (i : Row) : (54 : ℝ)/100*t i < cap i := by
  have h := chi_t_lt_cap i
  have ht := t_pos i
  norm_num [chi] at h
  nlinarith

lemma demandLo_receipt (i : Row) : kappa i*cap i < (54 : ℝ)/100*t i := by
  have h := numerical_root_receipt_gap i
  have ht := t_pos i
  nlinarith

lemma rejectionLo_pos (i : Row) : 0 < (52 : ℝ)/100*t i := by
  have ht := t_pos i
  positivity

lemma rejectionLo_lt_cap (i : Row) : (52 : ℝ)/100*t i < cap i := by
  have ht := t_pos i
  have h := demandLo_lt_cap i
  nlinarith

theorem exists_unique_lawMultiplier (i : Row) (G : RootDomain i) :
    ∃! z : ℝ, z ∈ Icc ((54 : ℝ)/100*t i) (cap i) ∧
      lawDemand i G.1 z = requiredDemand i := by
  have hc := continuousOn_lawDemand i G.1 (hi := cap i)
    (demandLo_pos i) (demandLo_receipt i).le
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' (demandLo_lt_cap i).le hc
    (show requiredDemand i ∈ Icc (lawDemand i G.1 (cap i))
      (lawDemand i G.1 ((54 : ℝ)/100*t i)) by
      rw [lawDemand_at_cap]
      exact ⟨(requiredDemand_range i).1.le,G.2.1.le⟩)
  refine ⟨z,⟨hz,hroot⟩,?_⟩
  intro z' hz'
  apply le_antisymm
  · by_contra h
    have hzz' : z < z' := lt_of_not_ge h
    have hh := lawDemand_drop i G.1 (demandLo_pos i) (demandLo_receipt i).le
      hz.1 hzz'.le
    rw [hroot,hz'.2] at hh
    have hp : 0 < (z'-z)/(xi i*cap i)*requiredDemand i := by
      have := (xi_range i).1
      have := cap_pos i
      have := (requiredDemand_range i).1
      positivity
    linarith
  · by_contra h
    have hz'z : z' < z := lt_of_not_ge h
    have hh := lawDemand_drop i G.1 (demandLo_pos i) (demandLo_receipt i).le
      hz'.1.1 hz'z.le
    rw [hroot,hz'.2] at hh
    have hp : 0 < (z-z')/(xi i*cap i)*requiredDemand i := by
      have := (xi_range i).1
      have := cap_pos i
      have := (requiredDemand_range i).1
      positivity
    linarith

theorem exists_unique_rejectionRoot (i : Row) (G : RootDomain i) :
    ∃! z : ℝ, z ∈ Icc ((52 : ℝ)/100*t i) (cap i) ∧
      lawRejection i G.1 z = 3*requiredDemand i := by
  have hr : 0 < 3*requiredDemand i := by have := (requiredDemand_range i).1; positivity
  obtain ⟨z,hz,hroot⟩ := intermediate_value_Icc' (rejectionLo_lt_cap i).le
    (continuous_lawRejection i G.1).continuousOn
    (show 3*requiredDemand i ∈ Icc (lawRejection i G.1 (cap i))
      (lawRejection i G.1 ((52 : ℝ)/100*t i)) by
      rw [lawRejection_at_cap]
      exact ⟨hr.le,G.2.2.le⟩)
  have hk : 0 < rejectionScale i/(rejectionScale i+cap i)^2 := by
    have := rejectionScale_pos i
    have := cap_pos i
    positivity
  refine ⟨z,⟨hz,hroot⟩,?_⟩
  intro z' hz'
  apply le_antisymm
  · by_contra h
    have hzz' : z < z' := lt_of_not_ge h
    have hh := lawRejection_drop i G.1 ((rejectionLo_pos i).le.trans hz.1) hzz'.le
    rw [hroot,hz'.2] at hh
    have hp := mul_pos (mul_pos hk (sub_pos.mpr hzz')) hr
    linarith
  · by_contra h
    have hz'z : z' < z := lt_of_not_ge h
    have hh := lawRejection_drop i G.1 ((rejectionLo_pos i).le.trans hz'.1.1) hz'z.le
    rw [hroot,hz'.2] at hh
    have hp := mul_pos (mul_pos hk (sub_pos.mpr hz'z)) hr
    linarith

def lawMultiplier (i : Row) (G : RootDomain i) : ℝ :=
  Classical.choose (exists_unique_lawMultiplier i G)

def lawRejectionRoot (i : Row) (G : RootDomain i) : ℝ :=
  Classical.choose (exists_unique_rejectionRoot i G)

lemma lawMultiplier_spec (i : Row) (G : RootDomain i) :
    lawMultiplier i G ∈ Icc ((54 : ℝ)/100*t i) (cap i) ∧
      lawDemand i G.1 (lawMultiplier i G) = requiredDemand i :=
  (Classical.choose_spec (exists_unique_lawMultiplier i G)).1

lemma lawRejectionRoot_spec (i : Row) (G : RootDomain i) :
    lawRejectionRoot i G ∈ Icc ((52 : ℝ)/100*t i) (cap i) ∧
      lawRejection i G.1 (lawRejectionRoot i G) = 3*requiredDemand i :=
  (Classical.choose_spec (exists_unique_rejectionRoot i G)).1

lemma lawMultiplier_strict_bounds (i : Row) (G : RootDomain i) :
    (54 : ℝ)/100*t i < lawMultiplier i G ∧ lawMultiplier i G < cap i := by
  have h := lawMultiplier_spec i G
  constructor
  · by_contra hn
    have he : lawMultiplier i G = (54 : ℝ)/100*t i :=
      le_antisymm (le_of_not_gt hn) h.1.1
    have heq := h.2
    rw [he] at heq
    linarith [G.2.1]
  · by_contra hn
    have he : lawMultiplier i G = cap i :=
      le_antisymm h.1.2 (le_of_not_gt hn)
    have heq := h.2
    rw [he,lawDemand_at_cap] at heq
    linarith [(requiredDemand_range i).1]

lemma lawRejectionRoot_strict_bounds (i : Row) (G : RootDomain i) :
    (52 : ℝ)/100*t i < lawRejectionRoot i G ∧ lawRejectionRoot i G < cap i := by
  have h := lawRejectionRoot_spec i G
  constructor
  · by_contra hn
    have he : lawRejectionRoot i G = (52 : ℝ)/100*t i :=
      le_antisymm (le_of_not_gt hn) h.1.1
    have heq := h.2
    rw [he] at heq
    linarith [G.2.2]
  · by_contra hn
    have he : lawRejectionRoot i G = cap i :=
      le_antisymm h.1.2 (le_of_not_gt hn)
    have heq := h.2
    rw [he,lawRejection_at_cap] at heq
    linarith [(requiredDemand_range i).1]

lemma lawMultiplier_upper (i : Row) (G : RootDomain i) :
    lawMultiplier i G ≤ (1-xi i*requiredDemand i)*cap i := by
  let z := lawMultiplier i G
  have hz : 0 < z := (demandLo_pos i).trans (lawMultiplier_strict_bounds i G).1
  have hzU : z < cap i := (lawMultiplier_strict_bounds i G).2
  have hguard : (1-xi i)*cap i ≤ z := by
    simpa [kappa,z] using (demandLo_receipt i).le.trans (lawMultiplier_spec i G).1.1
  have hpoint : ∀ b : Bid i, exposure (xi i) z b ≤ exposure (xi i) z (cap i) :=
    fun b => exposure_monotone_bid (xi_range i).1 hz b.2.2
  have hint := integral_mono (integrable_lawDemand i G.1 hz)
    (integrable_const (exposure (xi i) z (cap i))) hpoint
  change lawDemand i G.1 z ≤ _ at hint
  have hzroot : lawDemand i G.1 z = requiredDemand i := (lawMultiplier_spec i G).2
  rw [hzroot] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  rw [exposure_of_between (xi_range i).1 hz hzU hguard] at hint
  have hξ := (xi_range i).1
  have hU := cap_pos i
  have hmul := (le_div_iff₀ hξ).mp hint
  have hmul' := (div_le_iff₀ hU).mp (show z/cap i ≤ 1-requiredDemand i*xi i by linarith)
  dsimp [z] at *
  nlinarith

lemma lawMultiplier_receipt_guard (i : Row) (G : RootDomain i) :
    kappa i*cap i < lawMultiplier i G :=
  (demandLo_receipt i).trans (lawMultiplier_strict_bounds i G).1

theorem continuous_lawMultiplier (i : Row) : Continuous (lawMultiplier i) := by
  apply root_continuous (F := fun G : RootDomain i => lawDemand i G.1)
    (root := lawMultiplier i)
    (lo := (54 : ℝ)/100*t i) (hi := cap i)
    (k := 1/(xi i*cap i)) (r := requiredDemand i)
  · have := (xi_range i).1
    have := cap_pos i
    positivity
  · exact (requiredDemand_range i).1
  · exact lawMultiplier_spec i
  · intro G a b ha hb hab
    convert! lawDemand_drop i G.1 (demandLo_pos i) (demandLo_receipt i).le ha.1 hab using 1; ring
  · intro z hz
    exact (continuous_lawDemand_in_law i ((demandLo_pos i).trans_le hz.1)).comp continuous_subtype_val

theorem continuous_lawRejectionRoot (i : Row) : Continuous (lawRejectionRoot i) := by
  apply root_continuous (F := fun G : RootDomain i => lawRejection i G.1)
    (root := lawRejectionRoot i)
    (lo := (52 : ℝ)/100*t i) (hi := cap i)
    (k := rejectionScale i/(rejectionScale i+cap i)^2) (r := 3*requiredDemand i)
  · have := rejectionScale_pos i
    have := cap_pos i
    positivity
  · have := (requiredDemand_range i).1
    positivity
  · exact lawRejectionRoot_spec i
  · intro G a b ha hb hab
    exact lawRejection_drop i G.1 ((rejectionLo_pos i).le.trans ha.1) hab
  · intro z _
    exact (continuous_lawRejection_in_law i z).comp continuous_subtype_val

theorem lawMultiplier_distance_bound (i : Row) (G H : RootDomain i)
    (hnear : requiredDemand i/2 ≤ lawDemand i G.1 (lawMultiplier i H)) :
    |lawMultiplier i G-lawMultiplier i H| ≤
      2*|lawDemand i G.1 (lawMultiplier i H)-requiredDemand i| /
        ((1/(xi i*cap i))*requiredDemand i) := by
  apply root_distance_bound
    (F := fun K : RootDomain i => lawDemand i K.1) (root := lawMultiplier i)
    (lo := (54 : ℝ)/100*t i) (hi := cap i)
    (k := 1/(xi i*cap i)) (r := requiredDemand i)
  · have := (xi_range i).1
    have := cap_pos i
    positivity
  · exact (requiredDemand_range i).1
  · exact lawMultiplier_spec i
  · intro K a b ha hb hab
    convert! lawDemand_drop i K.1 (demandLo_pos i) (demandLo_receipt i).le
      ha.1 hab using 1; ring
  · exact hnear

theorem lawRejectionRoot_distance_bound (i : Row) (G H : RootDomain i)
    (hnear : (3*requiredDemand i)/2 ≤ lawRejection i G.1 (lawRejectionRoot i H)) :
    |lawRejectionRoot i G-lawRejectionRoot i H| ≤
      2*|lawRejection i G.1 (lawRejectionRoot i H)-3*requiredDemand i| /
        ((rejectionScale i/(rejectionScale i+cap i)^2)*(3*requiredDemand i)) := by
  apply root_distance_bound
    (F := fun K : RootDomain i => lawRejection i K.1) (root := lawRejectionRoot i)
    (lo := (52 : ℝ)/100*t i) (hi := cap i)
    (k := rejectionScale i/(rejectionScale i+cap i)^2) (r := 3*requiredDemand i)
  · have := rejectionScale_pos i
    have := cap_pos i
    positivity
  · have := (requiredDemand_range i).1
    positivity
  · exact lawRejectionRoot_spec i
  · intro K a b ha hb hab
    exact lawRejection_drop i K.1 ((rejectionLo_pos i).le.trans ha.1) hab
  · exact hnear

lemma exposure_antitone_threshold {ξ v a b : ℝ}
    (hξ : 0 < ξ) (ha : 0 < a) (hab : a ≤ b) :
    exposure ξ b v ≤ exposure ξ a v := by
  by_cases hvb : v ≤ b
  · rw [exposure_zero hvb]
    exact exposure_nonneg hξ ha
  · have hbv : b < v := lt_of_not_ge hvb
    have hav := hab.trans_lt hbv
    have hv0 := ha.trans hav
    rw [exposure_eq_min_of_above hξ (ha.trans_le hab) hbv,
      exposure_eq_min_of_above hξ ha hav]
    apply min_le_min_left
    apply div_le_div_of_nonneg_right _ hξ.le
    have hd := div_le_div_of_nonneg_right hab hv0.le
    linarith

lemma lawDemand_antitone_positive (i : Row) (G : ProbabilityMeasure (Bid i))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : lawDemand i G b ≤ lawDemand i G a := by
  apply integral_mono (integrable_lawDemand i G (ha.trans_le hab))
    (integrable_lawDemand i G ha)
  intro v
  exact exposure_antitone_threshold (xi_range i).1 ha hab

lemma lawRejection_antitone (i : Row) (G : ProbabilityMeasure (Bid i)) :
    Antitone (lawRejection i G) := by
  intro a b hab
  apply integral_mono (integrable_lawRejection i G b) (integrable_lawRejection i G a)
  intro v
  have h := (rejectionExposure_z_interval_bound (v := (v : ℝ)) (rejectionScale_pos i) hab).1
  linarith

theorem lawMultiplier_unique (i : Row) (G : RootDomain i) {z : ℝ}
    (hz : 0 < z) (heq : lawDemand i G.1 z = requiredDemand i) :
    z = lawMultiplier i G := by
  have hlo : (54 : ℝ)/100*t i ≤ z := by
    by_contra hn
    have hlt : z < (54 : ℝ)/100*t i := lt_of_not_ge hn
    have hh := lawDemand_antitone_positive i G.1 hz hlt.le
    rw [heq] at hh
    linarith [G.2.1]
  have hhi : z ≤ cap i := by
    by_contra hn
    have hlt : cap i < z := lt_of_not_ge hn
    have hh := lawDemand_antitone_positive i G.1 (cap_pos i) hlt.le
    rw [heq,lawDemand_at_cap] at hh
    linarith [(requiredDemand_range i).1]
  exact (Classical.choose_spec (exists_unique_lawMultiplier i G)).2 z ⟨⟨hlo,hhi⟩,heq⟩

theorem lawRejectionRoot_unique (i : Row) (G : RootDomain i) {z : ℝ}
    (heq : lawRejection i G.1 z = 3*requiredDemand i) :
    z = lawRejectionRoot i G := by
  have hlo : (52 : ℝ)/100*t i ≤ z := by
    by_contra hn
    have hlt : z < (52 : ℝ)/100*t i := lt_of_not_ge hn
    have hh := lawRejection_antitone i G.1 hlt.le
    rw [heq] at hh
    linarith [G.2.2]
  have hhi : z ≤ cap i := by
    by_contra hn
    have hlt : cap i < z := lt_of_not_ge hn
    have hh := lawRejection_antitone i G.1 hlt.le
    rw [heq,lawRejection_at_cap] at hh
    linarith [(requiredDemand_range i).1]
  exact (Classical.choose_spec (exists_unique_rejectionRoot i G)).2 z ⟨⟨hlo,hhi⟩,heq⟩

end FCAppendix.Affine.Uniform05
