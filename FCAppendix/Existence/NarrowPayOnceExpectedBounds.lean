import FCAppendix.Existence.NarrowPayOnceRowBounds
import FCAppendix.Exclusive.CompactBestResponse

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology MeasureTheory
open PayOnce PayOnce.OwnImpact CommonList
open scoped BigOperators

structure FiniteScoreControl (n R c : ℕ) (w0 kappa eps delta : ℝ) : Prop where
  n_ge : 2≤n
  c_pos : 1≤c
  c_le : c≤R
  w_pos : 0<w0
  kappa_pos : 0<kappa
  eps_pos : 0<eps
  delta_nonneg : 0≤delta
  bid_floor : kappa≤referenceBid n R c w0
  eps_small : eps≤kappa/4
  curvature_floor : kappa≤referenceCurvature n R (density R c) w0 (referenceBid n R c w0)
  gap_floor : kappa≤referenceCurvature n R (density R c) w0 (referenceBid n R c w0)-
    |referenceCurvature n R (density R c) w0 (referenceBid n R c w0)-
      referenceCommonSensitivity n R (density R c) w0 (referenceBid n R c w0)|
  interior : ∀b∈bidBox (ι:=Fin (R+1)) (referenceBid n R c w0-eps) (referenceBid n R c w0+eps),
    ∀i,kernelMarginal n c b i∈Ioo (0:ℝ) 1
  derivative : ∀w,|w-w0|≤delta → ∀b∈bidBox (ι:=Fin (R+1))
    (referenceBid n R c w0-eps) (referenceBid n R c w0+eps),
    ‖fderiv ℝ (profileScore n c w) b-
      fderiv ℝ (profileScore n c w0) (fun _=>referenceBid n R c w0)‖≤kappa/4
  type_small : (n:ℝ)*firstJetBound n (kappa/2)*delta≤kappa*eps/4

namespace FiniteScoreControl
variable {n R c : ℕ} {w0 kappa eps delta : ℝ}
  (U : FiniteScoreControl n R c w0 kappa eps delta)

abbrev B (_U : FiniteScoreControl n R c w0 kappa eps delta) : ℝ := referenceBid n R c w0
abbrev A : ℝ := referenceCurvature n R (density R c) w0 U.B
abbrev E : ℝ := referenceCommonSensitivity n R (density R c) w0 U.B
abbrev own : ℝ := U.A-kappa/4
abbrev rival : ℝ := |U.A-U.E|+kappa/4
abbrev typeRate (_U : FiniteScoreControl n R c w0 kappa eps delta) : ℝ := (n:ℝ)*firstJetBound n (kappa/2)
abbrev valueBand (_U : FiniteScoreControl n R c w0 kappa eps delta) := Icc (w0-delta) (w0+delta)
abbrev strategyBand := Exclusive.Existence.bidBand U.valueBand (U.B-eps) (U.B+eps)

theorem eps_lt_bid : eps<U.B := by linarith [U.bid_floor,U.eps_small,U.kappa_pos]
theorem lower_pos : 0<U.B-eps := sub_pos.mpr U.eps_lt_bid
theorem lower_floor : kappa/2≤U.B-eps := by linarith [U.bid_floor,U.eps_small,U.kappa_pos]
theorem own_pos : 0<U.own := by dsimp [own]; linarith [U.curvature_floor,U.kappa_pos]
theorem rival_nonneg : 0≤U.rival := by have hk:=U.kappa_pos; dsimp [rival]; positivity
theorem contraction_gap : kappa/2≤U.own-U.rival := by
  dsimp [own,rival]
  linarith [U.gap_floor]
theorem typeRate_nonneg : 0≤U.typeRate := by have hk:=U.kappa_pos; dsimp [typeRate,firstJetBound]; positivity

theorem value_mem (v : U.valueBand) : |(v:ℝ)-w0|≤delta :=
  abs_le.mpr ⟨by linarith [v.property.1],by linarith [v.property.2]⟩

theorem row_box {V : Type*} (beta : V→ℝ)
    (hbeta : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) (omega : Fin R→V) :
    rowBids beta z omega∈bidBox (U.B-eps) (U.B+eps) := by
  intro i
  exact Fin.cases hz (fun j=>hbeta (omega j)) i

theorem row_type_bound {V : Type*} (beta : V→ℝ)
    (hbeta : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (w v z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) (omega : Fin R→V) :
    |finiteRowScore n c beta w z omega-finiteRowScore n c beta v z omega|≤U.typeRate*|w-v| := by
  have hbox := U.row_box beta hbeta z hz omega
  have hpos := fun v=>U.lower_pos.trans_le (hbeta v).1
  rw [finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta w z omega
      (U.lower_pos.trans_le hz.1) hpos (U.interior _ hbox),
    finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta v z omega
      (U.lower_pos.trans_le hz.1) hpos (U.interior _ hbox)]
  exact (profileScore_type_bound U.n_ge (by have:=U.c_le; omega) U.lower_pos _ hbox
    (U.interior _ hbox) w v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (firstJetBound_mono n (half_pos U.kappa_pos) U.lower_floor)
        (Nat.cast_nonneg n)) (abs_nonneg _))

section Expected
variable (nu : Measure U.valueBand) [IsProbabilityMeasure nu]

theorem row_integrable (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hband : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (w z : ℝ)
    (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    Integrable (finiteRowScore (R:=R) n c beta w z) (Measure.pi (fun _=>nu)) :=
  (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,continuous_finiteRowScore U.n_ge beta hbeta
    (fun v=>U.lower_pos.trans_le (hband v).1) w z (U.lower_pos.trans_le hz.1)⟩).integrable _

theorem expected_decrease (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hband : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (v : U.valueBand) (x y : ℝ) (hx : x∈Icc (U.B-eps) (U.B+eps))
    (hy : y∈Icc (U.B-eps) (U.B+eps)) (hxy : x≤y) :
    U.own*(y-x)≤finiteExpectedScore (R:=R) n c nu beta v x-
      finiteExpectedScore (R:=R) n c nu beta v y := by
  have hh := integral_mono (μ:=Measure.pi (fun _ : Fin R=>nu)) (integrable_const (U.own*(y-x)))
    ((U.row_integrable nu beta hbeta hband v x hx).sub (U.row_integrable nu beta hbeta hband v y hy))
    (fun omega=>rowScore_decrease U.n_ge U.c_pos U.c_le U.w_pos U.eps_lt_bid U.interior
      (U.derivative v (U.value_mem v)) beta hband x y hx hy hxy omega)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (U.row_integrable nu beta hbeta hband v x hx)
    (U.row_integrable nu beta hbeta hband v y hy)] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,finiteExpectedScore] using hh

theorem expected_type_bound (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hband : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (w v z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    |finiteExpectedScore (R:=R) n c nu beta w z-finiteExpectedScore (R:=R) n c nu beta v z|≤
      U.typeRate*|w-v| := by
  rw [finiteExpectedScore,finiteExpectedScore,← integral_sub
    (U.row_integrable nu beta hbeta hband w z hz) (U.row_integrable nu beta hbeta hband v z hz)]
  have hh := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin R=>nu))
    (f:=fun omega=>finiteRowScore n c beta w z omega-finiteRowScore n c beta v z omega)
    (C:=U.typeRate*|w-v|)
    (ae_of_all _ (fun omega=>by simpa only [Real.norm_eq_abs] using U.row_type_bound beta hband w v z hz omega))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem expected_rival_bound (beta gamma : U.valueBand→ℝ)
    (hbeta : Continuous beta) (hgamma : Continuous gamma)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps))
    (hg : ∀v,gamma v∈Icc (U.B-eps) (U.B+eps))
    (D : ℝ) (hD : 0≤D) (hbg : ∀v,|beta v-gamma v|≤D)
    (v : U.valueBand) (z : ℝ) (hz : z∈Icc (U.B-eps) (U.B+eps)) :
    |finiteExpectedScore (R:=R) n c nu beta v z-finiteExpectedScore (R:=R) n c nu gamma v z|≤U.rival*D := by
  have hrows (omega : Fin R→U.valueBand) :
      |finiteRowScore n c beta v z omega-finiteRowScore n c gamma v z omega|≤U.rival*D := by
    rw [finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) beta v z omega
        (U.lower_pos.trans_le hz.1) (fun v=>U.lower_pos.trans_le (hb v).1) (U.interior _ (U.row_box beta hb z hz omega)),
      finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) gamma v z omega
        (U.lower_pos.trans_le hz.1) (fun v=>U.lower_pos.trans_le (hg v).1) (U.interior _ (U.row_box gamma hg z hz omega))]
    apply profileScore_rival_bound U.n_ge U.c_pos U.c_le U.w_pos hD (by have hk:=U.kappa_pos; positivity)
      U.eps_lt_bid U.interior (U.derivative v (U.value_mem v))
      (rowBids gamma z omega) (rowBids beta z omega)
      (U.row_box gamma hg z hz omega) (U.row_box beta hb z hz omega) rfl
    intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · simpa only [rowBids,Fin.cons_zero,sub_self,abs_zero] using hD
    · simpa only [rowBids,Fin.cons_succ] using hbg (omega j)
  rw [finiteExpectedScore,finiteExpectedScore,← integral_sub
    (U.row_integrable nu beta hbeta hb v z hz) (U.row_integrable nu gamma hgamma hg v z hz)]
  have hh := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin R=>nu))
    (f:=fun omega=>finiteRowScore n c beta v z omega-finiteRowScore n c gamma v z omega)
    (C:=U.rival*D)
    (ae_of_all _ (fun omega=>by simpa only [Real.norm_eq_abs] using hrows omega))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

omit [IsProbabilityMeasure nu] in
theorem expected_constant_zero :
    finiteExpectedScore (R:=R) n c nu (fun _=>U.B) w0 U.B=0 := by
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro omega
  have hconst : rowBids (fun _ : U.valueBand=>U.B) U.B omega=(fun _=>U.B) := by
    ext i; refine Fin.cases rfl (fun _=>rfl) i
  have hz : U.B∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  rw [finiteRowScore_eq_profileScore U.n_ge (by have:=U.c_le; omega) _ w0 U.B omega
    (U.lower_pos.trans_le hz.1) (fun _=>U.lower_pos.trans_le hz.1)
    (U.interior _ (U.row_box _ (fun _=>hz) U.B hz omega)),hconst]
  exact (source_reference_linearization U.n_ge U.c_pos U.c_le U.w_pos (fun _=>0)).1

theorem expected_center_bound (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (v : U.valueBand) :
    |finiteExpectedScore (R:=R) n c nu beta v U.B|≤U.rival*eps+U.typeRate*delta := by
  have hz : U.B∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  have hpar := U.expected_rival_bound nu beta (fun _=>U.B) hbeta continuous_const hb
    (fun _=>hz) eps U.eps_pos.le (fun v=>abs_le.mpr ⟨by linarith [(hb v).1],by linarith [(hb v).2]⟩) v U.B hz
  have htype := (U.expected_type_bound nu (fun _=>U.B) continuous_const (fun _=>hz) v w0 U.B hz).trans
    (mul_le_mul_of_nonneg_left (U.value_mem v) U.typeRate_nonneg)
  rw [U.expected_constant_zero nu,sub_zero] at htype
  calc
    _=|(finiteExpectedScore (R:=R) n c nu beta v U.B-
      finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B)+
      finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B| := by congr 1; ring
    _≤|finiteExpectedScore (R:=R) n c nu beta v U.B-
      finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B|+
      |finiteExpectedScore (R:=R) n c nu (fun _=>U.B) v U.B| := abs_add_le _ _
    _≤_ := add_le_add hpar htype

theorem expected_inward (beta : U.valueBand→ℝ) (hbeta : Continuous beta)
    (hb : ∀v,beta v∈Icc (U.B-eps) (U.B+eps)) (v : U.valueBand) :
    0<finiteExpectedScore (R:=R) n c nu beta v (U.B-eps) ∧
      finiteExpectedScore (R:=R) n c nu beta v (U.B+eps)<0 := by
  have hz : U.B∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],by linarith [U.eps_pos]⟩
  have hlo : U.B-eps∈Icc (U.B-eps) (U.B+eps) := ⟨le_rfl,by linarith [U.eps_pos]⟩
  have hhi : U.B+eps∈Icc (U.B-eps) (U.B+eps) := ⟨by linarith [U.eps_pos],le_rfl⟩
  have hleft := U.expected_decrease nu beta hbeta hb v (U.B-eps) U.B hlo hz (by linarith [U.eps_pos])
  have hright := U.expected_decrease nu beta hbeta hb v U.B (U.B+eps) hz hhi (by linarith [U.eps_pos])
  have hcenter := abs_le.mp (U.expected_center_bound nu beta hbeta hb v)
  have hgap := mul_le_mul_of_nonneg_right U.contraction_gap U.eps_pos.le
  have hsmall := U.type_small
  have hkep := mul_pos U.kappa_pos U.eps_pos
  constructor <;> nlinarith

end Expected
end FiniteScoreControl

theorem exists_uniform_finiteScoreControl {n : ℕ} (hn : 2≤n) {w0 lo hi : ℝ}
    (hw0 : 0<w0) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa eps deltaStar : ℝ, 0<kappa ∧ 0<eps ∧ 0<deltaStar ∧ deltaStar≤w0/2 ∧
      ∀R c : ℕ, 1≤c → c≤R → density R c∈Icc lo hi →
      ∀delta∈Icc (0:ℝ) deltaStar, FiniteScoreControl n R c w0 kappa eps delta := by
  obtain ⟨kappa,eps,delta0,hk,he,hd,hek,he1,hdw,hall⟩ :=
    exists_uniform_score_neighborhood hn hw0 hlo hlohi hhi
  let T := (n:ℝ)*firstJetBound n (kappa/2)
  let deltaStar := min delta0 (kappa*eps/(16*(T+1)))
  have hT : 0≤T := by dsimp [T,firstJetBound]; positivity
  have hds : 0<deltaStar := lt_min hd (by positivity)
  have hds0 : deltaStar≤delta0 := min_le_left _ _
  have hsmall : T*deltaStar≤kappa*eps/16 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<16*(T+1))).mp
      (min_le_right delta0 (kappa*eps/(16*(T+1))))
    change deltaStar*(16*(T+1))≤kappa*eps at hh
    nlinarith
  refine ⟨kappa,eps,deltaStar,hk,he,hds,hds0.trans hdw,?_⟩
  intro R c hc hcR hrho delta hdelta
  obtain ⟨hB,hBw,hA,hgap,hint,hderiv⟩ := hall R c hc hcR hrho
  refine ⟨hn,hc,hcR,hw0,hk,he,hdelta.1,hB,hek,hA,hgap,?_,?_,?_⟩
  · intro b hb
    apply hint b
    intro i
    exact abs_le.mpr ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩
  · intro w hw b hb
    apply hderiv w (hw.trans (hdelta.2.trans hds0)) b
    intro i
    exact abs_le.mpr ⟨by linarith [(hb i).1],by linarith [(hb i).2]⟩
  · have hh := (mul_le_mul_of_nonneg_left hdelta.2 hT).trans hsmall
    change T*delta≤kappa*eps/4
    nlinarith [mul_pos hk he]

end FCAppendix.Existence.NarrowPayOnce
