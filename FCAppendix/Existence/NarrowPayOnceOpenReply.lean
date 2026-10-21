import FCAppendix.Existence.NarrowPayOnceScoreC1
import Mathlib.Topology.Order.ProjIcc

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)

abbrev extensionJetRate (_U : FiniteScoreControl n R c w0 kappa eps delta) : ℝ :=
  scoreTypeJetBound n (kappa/2) (2*w0)

def extensionWidth : ℝ := min (kappa/(16*(U.extensionJetRate+1)))
  (kappa*eps/(16*(U.typeRate+1)))

abbrev openValueBand := Ioo (w0-delta-U.extensionWidth) (w0+delta+U.extensionWidth)

def clampedValue (w : ℝ) : U.valueBand :=
  projIcc (w0-delta) (w0+delta) (by linarith [U.delta_nonneg]) w

theorem extensionWidth_pos : 0<U.extensionWidth := by
  have hk:=U.kappa_pos
  have he:=U.eps_pos
  have hw:=U.w_pos
  have hJ : 0≤U.extensionJetRate := by dsimp [extensionJetRate,scoreTypeJetBound,secondJetBound,firstJetBound]; positivity
  have hT := U.typeRate_nonneg
  unfold extensionWidth
  positivity

theorem clampedValue_distance (w : U.openValueBand) : |(w:ℝ)-U.clampedValue w|<U.extensionWidth := by
  change |(w:ℝ)-max (w0-delta) (min (w0+delta) w)|<U.extensionWidth
  rcases le_total (w:ℝ) (w0-delta) with h | h
  · rw [min_eq_right (by linarith [U.delta_nonneg]),max_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [w.property.1]
  · rcases le_total (w:ℝ) (w0+delta) with h' | h'
    · rw [min_eq_right h',max_eq_right h,sub_self,abs_zero]
      exact U.extensionWidth_pos
    · rw [min_eq_left h',max_eq_right (by linarith [U.delta_nonneg]),abs_of_nonneg (sub_nonneg.mpr h')]
      linarith [w.property.2]

theorem extension_jet_small : U.extensionJetRate*U.extensionWidth≤kappa/16 := by
  have hk:=U.kappa_pos
  have hw:=U.w_pos
  have hJ : 0≤U.extensionJetRate := by dsimp [extensionJetRate,scoreTypeJetBound,secondJetBound,firstJetBound]; positivity
  have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(U.extensionJetRate+1))).mp
    (min_le_left (kappa/(16*(U.extensionJetRate+1))) (kappa*eps/(16*(U.typeRate+1))))
  change U.extensionWidth*(16*(U.extensionJetRate+1))≤kappa at hh
  nlinarith [U.extensionWidth_pos]

theorem extension_type_small : U.typeRate*U.extensionWidth≤kappa*eps/16 := by
  have hT:=U.typeRate_nonneg
  have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(U.typeRate+1))).mp
    (min_le_right (kappa/(16*(U.extensionJetRate+1))) (kappa*eps/(16*(U.typeRate+1))))
  change U.extensionWidth*(16*(U.typeRate+1))≤kappa*eps at hh
  nlinarith [U.extensionWidth_pos]

theorem derivative_open_types (w : U.openValueBand)
    (b : Fin (R+1)→ℝ) (hb : b∈bidBox (U.B-eps) (U.B+eps)) :
    ‖fderiv ℝ (profileScore n c w) b-
      fderiv ℝ (profileScore n c w0) (fun _=>U.B)‖≤kappa/3 := by
  have hR : 0<R := by have:=U.c_pos; have:=U.c_le; omega
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hcreal : (1:ℝ)≤c := by exact_mod_cast U.c_pos
  have hcRreal : (c:ℝ)≤R := by exact_mod_cast U.c_le
  have hBw := (referenceBid_pos_lt U.n_ge hRreal hcreal hcRreal U.w_pos).2
  change U.B<w0 at hBw
  have hupper : U.B+eps≤2*w0 := by linarith [U.eps_small,U.bid_floor,U.w_pos]
  have hmon := scoreTypeJetBound_mono n (half_pos U.kappa_pos) U.lower_floor
    (by linarith [U.lower_pos,U.eps_pos] : 0≤U.B+eps) hupper
  have hty := norm_fderiv_profileScore_type_sub_le U.n_ge (by have:=U.c_le; omega) U.lower_pos b hb
    (U.interior b hb) w (U.clampedValue w)
  have htbound : ‖fderiv ℝ (profileScore n c w) b-
      fderiv ℝ (profileScore n c (U.clampedValue w)) b‖≤kappa/16 :=
    hty.trans ((mul_le_mul hmon (U.clampedValue_distance w).le (abs_nonneg _) (by
      have hk:=U.kappa_pos; have hw:=U.w_pos
      dsimp [extensionJetRate,scoreTypeJetBound,secondJetBound,firstJetBound]; positivity)).trans U.extension_jet_small)
  have hbase := U.derivative (U.clampedValue w) (U.value_mem (U.clampedValue w)) b hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add htbound hbase).trans (by linarith [U.kappa_pos]))

variable (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem expected_boundary_margin (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (v : U.valueBand) :
    kappa*eps/4≤finiteExpectedScore (R:=R) n c nu beta v (U.B-eps) ∧
      finiteExpectedScore (R:=R) n c nu beta v (U.B+eps)≤ -(kappa*eps/4) := by
  have hz : U.B∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  have hlo : U.B-eps∈Icc (U.B-eps) (U.B+eps) := ⟨le_rfl,by linarith [U.eps_pos]⟩
  have hhi : U.B+eps∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],le_rfl⟩
  have hleft := U.expected_decrease nu beta hbeta hb v (U.B-eps) U.B hlo hz (by linarith [U.eps_pos])
  have hright := U.expected_decrease nu beta hbeta hb v U.B (U.B+eps) hz hhi (by linarith [U.eps_pos])
  have hcenter := abs_le.mp (U.expected_center_bound nu beta hbeta hb v)
  have hgap := mul_le_mul_of_nonneg_right U.contraction_gap U.eps_pos.le
  have hsmall := U.type_small
  constructor <;> nlinarith

theorem expected_open_inward (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (v : U.openValueBand) :
    0<finiteExpectedScore (R:=R) n c nu beta v (U.B-eps) ∧
      finiteExpectedScore (R:=R) n c nu beta v (U.B+eps)<0 := by
  have hlo : U.B-eps∈Icc (U.B-eps) (U.B+eps) := ⟨le_rfl,by linarith [U.eps_pos]⟩
  have hhi : U.B+eps∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],le_rfl⟩
  have hm := U.expected_boundary_margin nu beta hbeta hb (U.clampedValue v)
  have hl := (U.expected_type_bound nu beta hbeta hb v (U.clampedValue v) (U.B-eps) hlo).trans
    ((mul_le_mul_of_nonneg_left (U.clampedValue_distance v).le U.typeRate_nonneg).trans U.extension_type_small)
  have hr := (U.expected_type_bound nu beta hbeta hb v (U.clampedValue v) (U.B+eps) hhi).trans
    ((mul_le_mul_of_nonneg_left (U.clampedValue_distance v).le U.typeRate_nonneg).trans U.extension_type_small)
  have hll:=abs_le.mp hl
  have hrr:=abs_le.mp hr
  have hke:=mul_pos U.kappa_pos U.eps_pos
  constructor <;> nlinarith

theorem expected_open_decrease (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (v : U.openValueBand)
    (x y : ℝ) (hx : x∈Icc (U.B-eps) (U.B+eps))
    (hy : y∈Icc (U.B-eps) (U.B+eps)) (hxy : x≤y) :
    (U.A-kappa/3)*(y-x)≤finiteExpectedScore (R:=R) n c nu beta v x-
      finiteExpectedScore (R:=R) n c nu beta v y := by
  have hh := integral_mono (μ:=Measure.pi (fun _ : Fin R=>nu)) (integrable_const ((U.A-kappa/3)*(y-x)))
    ((U.row_integrable nu beta hbeta hb v x hx).sub (U.row_integrable nu beta hbeta hb v y hy))
    (fun omega=>rowScore_decrease U.n_ge U.c_pos U.c_le U.w_pos U.eps_lt_bid U.interior
      (U.derivative_open_types v) beta hb x y hx hy hxy omega)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (U.row_integrable nu beta hbeta hb v x hx)
    (U.row_integrable nu beta hbeta hb v y hy)] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,finiteExpectedScore] using hh

def openScoreData (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) :
    Exclusive.Existence.ScoreData Unit U.openValueBand (U.B-eps) (U.B+eps) (U.A-kappa/3) where
  score _ v z := finiteExpectedScore (R:=R) n c nu beta v z
  band_nonempty := by linarith [U.eps_pos]
  curvature_pos := by linarith [U.curvature_floor,U.kappa_pos]
  continuous_bid _ v := U.expected_bid_continuous nu beta hbeta hb v
  inward_left _ v := (U.expected_open_inward nu beta hbeta hb v).1
  inward_right _ v := (U.expected_open_inward nu beta hbeta hb v).2
  decrease _ v x hx y hy hxy := U.expected_open_decrease nu beta hbeta hb v x y hx hy hxy

end FiniteScoreControl
end FCAppendix.Existence.NarrowPayOnce
