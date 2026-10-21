import FCAppendix.Finite.EnvelopeIntegral
import FCAppendix.Ample.RankMeasureTools

noncomputable section
namespace FCAppendix.Existence.RankEnvelope
open MeasureTheory Set Filter Topology
open scoped Interval

def utility (q : ℝ → ℝ) (t R v : ℝ) : ℝ :=
  (t-R)*q t + ∫ x in t..v, q x

def bid (q : ℝ → ℝ) (t R v : ℝ) : ℝ := v-utility q t R v/q v

theorem utility_at_floor (q : ℝ → ℝ) (t R : ℝ) : utility q t R t = (t-R)*q t := by
  simp [utility]

theorem bid_at_floor (q : ℝ → ℝ) (t R : ℝ) (hq : q t ≠ 0) : bid q t R t = R := by
  rw [bid,utility_at_floor,mul_div_cancel_right₀ _ hq]
  ring

theorem utility_increment {q : ℝ → ℝ} (hq : Monotone q) (t R x v : ℝ) :
    utility q t R v-utility q t R x = ∫ z in x..v, q z := by
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hq.intervalIntegrable (μ:=volume) (a:=t) (b:=x)) (hq.intervalIntegrable (μ:=volume) (a:=x) (b:=v))
  dsimp only [utility]
  linarith

theorem integral_bounds {q : ℝ → ℝ} (hq : Monotone q) {x v : ℝ} (hxv : x ≤ v) :
    (v-x)*q x ≤ ∫ z in x..v, q z ∧ (∫ z in x..v, q z) ≤ (v-x)*q v := by
  constructor
  · have hi := intervalIntegral.integral_mono_on hxv intervalIntegrable_const
      (hq.intervalIntegrable (μ:=volume) (a:=x) (b:=v)) (fun z hz => hq hz.1)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hi
  · have hi := intervalIntegral.integral_mono_on hxv
      (hq.intervalIntegrable (μ:=volume) (a:=x) (b:=v)) intervalIntegrable_const (fun z hz => hq hz.2)
    simpa only [intervalIntegral.integral_const,smul_eq_mul] using hi

theorem supporting_line {q : ℝ → ℝ} (hq : Monotone q) (t R x v : ℝ) :
    utility q t R x+(v-x)*q x ≤ utility q t R v := by
  rcases le_total x v with hxv | hvx
  · have hb := (integral_bounds hq hxv).1
    rw [← utility_increment hq t R x v] at hb
    linarith
  · have hb := (integral_bounds hq hvx).2
    rw [← utility_increment hq t R v x] at hb
    nlinarith

theorem report_payoff {q : ℝ → ℝ} (t R x v : ℝ) (hx : q x ≠ 0) :
    (v-bid q t R x)*q x = utility q t R x+(v-x)*q x := by
  dsimp [bid]
  field_simp
  ring

theorem one_route_IC {q : ℝ → ℝ} (hq : Monotone q) (t R x v : ℝ) (hx : q x ≠ 0) :
    (v-bid q t R x)*q x ≤ utility q t R v := by
  rw [report_payoff t R x v hx]
  exact supporting_line hq t R x v

theorem utility_nonneg {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ}
    (hRt : R ≤ t) (hqt : 0 ≤ q t) (htv : t ≤ v) : 0 ≤ utility q t R v := by
  have hb := (integral_bounds hq htv).1
  have hp := mul_nonneg (sub_nonneg.mpr hRt) hqt
  have hp' := mul_nonneg (sub_nonneg.mpr htv) hqt
  dsimp only [utility]
  linarith

theorem utility_pos {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ}
    (hRt : R < t) (hqt : 0 < q t) (htv : t ≤ v) : 0 < utility q t R v := by
  have hb := (integral_bounds hq htv).1
  have hp := mul_pos (sub_pos.mpr hRt) hqt
  have hp' := mul_nonneg (sub_nonneg.mpr htv) hqt.le
  dsimp only [utility]
  linarith

theorem floor_le_bid {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ}
    (hRt : R ≤ t) (hqt : 0 < q t) (htv : t ≤ v) : R ≤ bid q t R v := by
  have hqv : 0 < q v := hqt.trans_le (hq htv)
  have hb := (integral_bounds hq htv).2
  have hm := mul_le_mul_of_nonneg_left (hq htv) (sub_nonneg.mpr hRt)
  have hU : utility q t R v ≤ (v-R)*q v := by dsimp [utility]; nlinarith
  dsimp only [bid]
  have hd := (div_le_iff₀ hqv).mpr hU
  linarith

theorem bid_le_value {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ}
    (hRt : R ≤ t) (hqt : 0 < q t) (htv : t ≤ v) : bid q t R v ≤ v := by
  have hU := utility_nonneg hq hRt hqt.le htv
  have hd := div_nonneg hU (hqt.trans_le (hq htv)).le
  dsimp only [bid]
  linarith

theorem bid_increase_bound {q : ℝ → ℝ} (hq : Monotone q) {t R x v : ℝ}
    (_hRt : R ≤ t) (hqt : 0 < q t) (htx : t ≤ x) (hxv : x ≤ v) :
    utility q t R x*(q v-q x)/(q x*q v) ≤ bid q t R v-bid q t R x := by
  have hqx : 0 < q x := hqt.trans_le (hq htx)
  have hqv : 0 < q v := hqx.trans_le (hq hxv)
  have hb := (integral_bounds hq hxv).2
  have hi := utility_increment hq t R x v
  rw [div_le_iff₀ (mul_pos hqx hqv)]
  dsimp only [bid]
  field_simp
  nlinarith [mul_nonneg hqx.le (sub_nonneg.mpr hb)]

theorem bid_monotoneOn {q : ℝ → ℝ} (hq : Monotone q) {t R : ℝ}
    (hRt : R ≤ t) (hqt : 0 < q t) : MonotoneOn (bid q t R) (Ici t) := by
  intro x hx v _hv hxv
  have hb := bid_increase_bound hq hRt hqt hx hxv
  have hU := utility_nonneg hq hRt hqt.le hx
  have hp := div_nonneg (mul_nonneg hU (sub_nonneg.mpr (hq hxv)))
    (mul_nonneg (hqt.trans_le (hq hx)).le (hqt.trans_le (hq (hx.trans hxv))).le)
  linarith

theorem bid_lt_of_rank_lt {q : ℝ → ℝ} (hq : Monotone q) {t R x v : ℝ}
    (hRt : R < t) (hqt : 0 < q t) (htx : t ≤ x) (hxv : x ≤ v)
    (hqstrict : q x < q v) : bid q t R x < bid q t R v := by
  have hU := utility_pos hq hRt hqt htx
  have hp := div_pos (mul_pos hU (sub_pos.mpr hqstrict))
    (mul_pos (hqt.trans_le (hq htx)) (hqt.trans_le (hq (htx.trans hxv))))
  have hb := bid_increase_bound hq hRt.le hqt htx hxv
  linarith

theorem continuous_bid {q : ℝ → ℝ} (hq : Continuous q) (hpos : ∀ x, q x ≠ 0)
    (t R : ℝ) : Continuous (bid q t R) := by
  have hU : Continuous (utility q t R) :=
    continuous_const.add (intervalIntegral.continuous_primitive (μ:=volume)
      (fun a b => hq.intervalIntegrable a b) t)
  exact continuous_id.sub (hU.div hq hpos)

theorem upper_beats_lower_above {q : ℝ → ℝ} (hq : Monotone q) {t R s v L : ℝ}
    (hs : s < q t) (htv : t < v)
    (hL : L ≤ utility q t R t+(v-t)*s) : L < utility q t R v := by
  have hU := supporting_line hq t R t v
  have hp := mul_pos (sub_pos.mpr htv) (sub_pos.mpr hs)
  nlinarith

theorem lower_beats_floor_below {q : ℝ → ℝ} {t R s v L : ℝ}
    (hs : s < q t) (hvt : v < t)
    (hL : utility q t R t+(v-t)*s ≤ L) :
    (v-R)*q t < L := by
  rw [utility_at_floor] at hL
  have hp := mul_pos (sub_pos.mpr hvt) (sub_pos.mpr hs)
  nlinarith

def deficitTo (q : ℝ → ℝ) (t R v : ℝ) : ℝ :=
  (t-R)*(1-q t) + ∫ x in t..v, (1-q x)

def error (q : ℝ → ℝ) (t R : ℝ) : ℝ :=
  (t-R)*(1-q t) + ∫ x in Ioi t, (1-q x)

theorem utility_deficit_identity {q : ℝ → ℝ} (hq : Monotone q) (t R v : ℝ) :
    utility q t R v = v-R-deficitTo q t R v := by
  dsimp only [utility,deficitTo]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (hq.intervalIntegrable (μ:=volume) (a:=t) (b:=v)),intervalIntegral.integral_const]
  simp only [smul_eq_mul,mul_one]
  ring

theorem deficitTo_le_error {q : ℝ → ℝ} {t R v : ℝ} (htv : t ≤ v)
    (hq1 : ∀ x, q x ≤ 1) (hint : IntegrableOn (fun x => 1-q x) (Ioi t)) :
    deficitTo q t R v ≤ error q t R := by
  dsimp only [deficitTo,error]
  apply add_le_add le_rfl
  rw [intervalIntegral.integral_of_le htv]
  exact setIntegral_mono_set hint (Eventually.of_forall fun x => sub_nonneg.mpr (hq1 x))
    (Eventually.of_forall fun _ hx => hx.1)

theorem error_nonneg {q : ℝ → ℝ} {t R : ℝ} (hRt : R ≤ t) (hq1 : ∀ x, q x ≤ 1) :
    0 ≤ error q t R := by
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hRt) (sub_nonneg.mpr (hq1 t)))
    (integral_nonneg fun x => sub_nonneg.mpr (hq1 x))

theorem utility_error_bound {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ} (htv : t ≤ v)
    (hq1 : ∀ x, q x ≤ 1) (hint : IntegrableOn (fun x => 1-q x) (Ioi t)) :
    v-R-error q t R ≤ utility q t R v := by
  rw [utility_deficit_identity hq]
  linarith [deficitTo_le_error (R:=R) htv hq1 hint]

theorem bid_error_bound {q : ℝ → ℝ} (hq : Monotone q) {t R v : ℝ}
    (hRt : R ≤ t) (hqt : 0 < q t) (htv : t ≤ v) (hq1 : ∀ x, q x ≤ 1)
    (hint : IntegrableOn (fun x => 1-q x) (Ioi t)) :
    R ≤ bid q t R v ∧ bid q t R v ≤ R+error q t R/q t := by
  refine ⟨floor_le_bid hq hRt hqt htv,?_⟩
  have hqv := hqt.trans_le (hq htv)
  have hE := error_nonneg hRt hq1
  have hU := utility_error_bound hq (R:=R) htv hq1 hint
  have hnum : (v-R)*q v-utility q t R v ≤ error q t R := by
    have hm := mul_le_mul_of_nonneg_left (hq1 v) (sub_nonneg.mpr (hRt.trans htv))
    nlinarith
  have hd := div_le_div_of_nonneg_right hnum hqv.le
  have he : bid q t R v-R=((v-R)*q v-utility q t R v)/q v := by
    dsimp only [bid]
    field_simp
    ring
  have hdiv := div_le_div_of_nonneg_left hE hqt (hq htv)
  rw [← he] at hd
  linarith

theorem atomless_bid_of_rank_strict {q : ℝ → ℝ} (hq : Monotone q) (hcont : Continuous q)
    (hpos : ∀ x, 0 < q x) {t R : ℝ} (hRt : R < t)
    (mu : Measure ℝ) [IsFiniteMeasure mu] [NullSingletonClass mu]
    (hsupport : ∀ᵐ x ∂mu, t ≤ x)
    (hstrict : ∀ x v, t ≤ x → x<v → mu (Ioc x v) ≠ 0 → q x<q v) :
    NullSingletonClass (mu.map (bid q t R)) := by
  have hb := continuous_bid hcont (fun x => (hpos x).ne') t R
  constructor
  intro z
  rw [Measure.map_apply hb.measurable (measurableSet_singleton z)]
  have hzero : mu (Ici t ∩ {x | bid q t R x=z})=0 := by
    apply Ample.RankMeasureTools.closed_set_null_of_interval_null mu (fun x => measure_singleton x)
      (isClosed_Ici.inter (isClosed_eq hb continuous_const))
    intro x hx v hv hxv
    by_cases he : x=v
    · rw [he,Ioc_self,measure_empty]
    · by_contra hmass
      have hqstrict := hstrict x v hx.1 (lt_of_le_of_ne hxv he) hmass
      have hbstrict := bid_lt_of_rank_lt hq hRt (hpos t) hx.1 hxv hqstrict
      rw [hx.2,hv.2] at hbstrict
      exact lt_irrefl _ hbstrict
  apply le_antisymm _ bot_le
  calc
    _ ≤ mu (Ici t ∩ {x | bid q t R x=z}) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with x hx hz
      exact ⟨hx,hz⟩
    _ = 0 := hzero

end FCAppendix.Existence.RankEnvelope
