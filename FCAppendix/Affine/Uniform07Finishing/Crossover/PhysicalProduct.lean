import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalAllActions
import FCAppendix.Affine.Uniform07Finishing.Early.Scalar
import FCAppendix.Affine.ClippedResidualRoots
import FCAppendix.Affine.Hybrid.Menu

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem clipped_singleton_product_upper
    {xi lam v b : ℝ} (hxi : 0< xi) (hlam : 0< lam)
    (_hb : 0≤ b) (hbv : b≤ v) :
    (v-b)*ClippedResidual.exposure xi lam b≤(v-lam)^2/(4*xi*lam) := by
  by_cases hbl : b≤ lam
  · rw [ClippedResidual.exposure_zero hbl,mul_zero]
    positivity
  have hlb : lam< b := lt_of_not_ge hbl
  have hb0 : 0< b := hlam.trans hlb
  have hp : ClippedResidual.exposure xi lam b≤(b-lam)/(xi*b) := by
    unfold ClippedResidual.exposure
    rw [max_eq_right (sub_nonneg.mpr hlb.le),max_eq_left hlb.le]
    exact min_le_right _ _
  have hn : 0≤(v-b)*(b-lam) := mul_nonneg (sub_nonneg.mpr hbv) (sub_nonneg.mpr hlb.le)
  have hfirst := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hbv)
  have hden := div_le_div_of_nonneg_left hn (mul_pos hxi hlam)
    (mul_le_mul_of_nonneg_left hlb.le hxi.le)
  have hquad : 4*((v-b)*(b-lam))≤(v-lam)^2 := by
    nlinarith [sq_nonneg (v+lam-2*b)]
  have hlast := div_le_div_of_nonneg_right hquad
    (show (0:ℝ)≤4*xi*lam from by positivity)
  calc
    (v-b)*ClippedResidual.exposure xi lam b≤((v-b)*(b-lam))/(xi*b) := by
      simpa only [mul_div_assoc] using hfirst
    _≤((v-b)*(b-lam))/(xi*lam) := hden
    _ = (4*((v-b)*(b-lam)))/(4*xi*lam) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _≤(v-lam)^2/(4*xi*lam) := hlast

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def sourceProductMarginal (row : Uniform07.Row) (b : ℝ) : ℝ :=
  ClippedResidual.exposure (Uniform07.xi row) (Uniform07.entry row) b

def sourceActiveBid (row : Uniform07.Row) (v : ℝ) : ℝ :=
  Uniform07.entry row*v/(Uniform07.kappa row*v+Uniform07.xi row*Uniform07.entry row)

def sourceActiveUtility (row : Uniform07.Row) (v : ℝ) : ℝ :=
  (v-Uniform07.entry row)^2/v

def sourceSingletonFraction (row : Uniform07.Row) : ℝ :=
  1/(4*Uniform07.xi row*Uniform07.x row)

lemma source_entry_positive (row : Uniform07.Row) : 0< Uniform07.entry row := by
  unfold Uniform07.entry
  exact mul_pos (by cases row <;> norm_num [Uniform07.x,Uniform07.xQ]) (Uniform07.cutoff_pos row)

lemma source_kappa_positive (row : Uniform07.Row) : 0< Uniform07.kappa row := by
  cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]

lemma source_kappa_add_xi (row : Uniform07.Row) : Uniform07.kappa row+Uniform07.xi row=1 := by
  cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]

lemma source_fraction_mem (row : Uniform07.Row) : sourceSingletonFraction row∈Ioo (0:ℝ) 1 := by
  cases row <;> norm_num [sourceSingletonFraction,Uniform07.xi,Uniform07.xiQ,
    Uniform07.etaQ,Uniform07.x,Uniform07.xQ]

lemma source_entry_lt_cap (row : Uniform07.Row) : Uniform07.entry row< Early.bidCap row := by
  have ht := Uniform07.cutoff_pos row
  cases row <;> norm_num [Uniform07.entry,Uniform07.x,Uniform07.xQ,Early.bidCap,
    Early.capRatioQ,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ] at * <;> linarith

lemma sourceProductMarginal_nonneg (row : Uniform07.Row) (b : ℝ) : 0≤ sourceProductMarginal row b :=
  ClippedResidual.exposure_nonneg (Uniform07.xi_pos row) (source_entry_positive row)

lemma sourceProductMarginal_le_one (row : Uniform07.Row) (b : ℝ) : sourceProductMarginal row b≤ 1 :=
  ClippedResidual.exposure_le_one _ _ _

lemma sourceProductMarginal_continuous (row : Uniform07.Row) : Continuous (sourceProductMarginal row) :=
  ClippedResidual.continuous_exposure (Uniform07.xi_pos row) (source_entry_positive row)

theorem source_active_bid_spec (row : Uniform07.Row) {v : ℝ}
    (hv : Uniform07.entry row< v) (hvt : v≤ Uniform07.cutoff row) :
    Uniform07.entry row< sourceActiveBid row v ∧ sourceActiveBid row v< v ∧
    sourceActiveBid row v< Early.bidCap row ∧
    sourceProductMarginal row (sourceActiveBid row v)=1-Uniform07.entry row/v ∧
    utilityTwo (Uniform07.eta row) v (sourceActiveBid row v)
      (sourceProductMarginal row (sourceActiveBid row v))
      ((sourceProductMarginal row (sourceActiveBid row v))^2)=sourceActiveUtility row v := by
  have hl := source_entry_positive row
  have hxi := Uniform07.xi_pos row
  have hk := source_kappa_positive row
  have hsum := source_kappa_add_xi row
  have hkEq : Uniform07.kappa row=1-Uniform07.xi row := by linarith
  have hv0 : 0< v := hl.trans hv
  have ht := Uniform07.cutoff_pos row
  have hd : 0< Uniform07.kappa row*v+Uniform07.xi row*Uniform07.entry row := by positivity
  have hdt : 0< Uniform07.kappa row*Uniform07.cutoff row+Uniform07.xi row*Uniform07.entry row := by positivity
  have hbl : Uniform07.entry row< sourceActiveBid row v := by
    dsimp [sourceActiveBid]
    apply (lt_div_iff₀ hd).2
    have h := mul_pos (mul_pos hxi hl) (sub_pos.mpr hv)
    rw [hkEq]
    nlinarith
  have hbv : sourceActiveBid row v< v := by
    dsimp [sourceActiveBid]
    apply (div_lt_iff₀ hd).2
    have h := mul_pos (mul_pos hk hv0) (sub_pos.mpr hv)
    rw [hkEq] at h ⊢
    nlinarith
  have hclip : (1-Uniform07.xi row)*sourceActiveBid row v≤ Uniform07.entry row := by
    have hid : 1-Uniform07.xi row=Uniform07.kappa row := by linarith
    rw [hid]
    dsimp [sourceActiveBid]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hxi.le (sq_nonneg (Uniform07.entry row))]
  have hmono : sourceActiveBid row v≤ sourceActiveBid row (Uniform07.cutoff row) := by
    dsimp [sourceActiveBid]
    apply (div_le_div_iff₀ hd hdt).2
    have h := mul_nonneg (mul_nonneg hxi.le (sq_nonneg (Uniform07.entry row))) (sub_nonneg.mpr hvt)
    nlinarith
  have hcap : sourceActiveBid row v< Early.bidCap row := by
    rw [Early.cap_literal_product_formula]
    change sourceActiveBid row v< sourceActiveBid row (Uniform07.cutoff row)+Uniform07.cutoff row/200
    linarith
  have hp : sourceProductMarginal row (sourceActiveBid row v)=1-Uniform07.entry row/v := by
    rw [sourceProductMarginal,ClippedResidual.exposure_of_between hxi hl hbl hclip]
    dsimp [sourceActiveBid]
    rw [hkEq]
    have hd' : (1-Uniform07.xi row)*v+Uniform07.xi row*Uniform07.entry row≠0 := by
      simpa only [← hkEq] using hd.ne'
    field_simp [hxi.ne',hl.ne',hv0.ne',hd']
    ring
  refine ⟨hbl,hbv,hcap,hp,?_⟩
  rw [hp]
  have heta : Uniform07.eta row=1-2*Uniform07.xi row := by
    linarith [Uniform07.xi_identity row]
  rw [heta]
  unfold utilityTwo sourceActiveBid sourceActiveUtility
  rw [hkEq]
  have hd' : (1-Uniform07.xi row)*v+Uniform07.xi row*Uniform07.entry row≠0 := by
    simpa only [← hkEq] using hd.ne'
  have hd'' : v-v*Uniform07.xi row+Uniform07.entry row*Uniform07.xi row≠0 := by
    convert hd' using 1
    ring
  field_simp [hv0.ne',hd']
  ring_nf
  linear_combination (-2*Uniform07.entry row*(v-Uniform07.entry row))*
    (mul_inv_cancel₀ hd'')

theorem source_product_singleton_fraction (row : Uniform07.Row) {v b : ℝ}
    (hv : 0< v) (hvt : v≤ Uniform07.cutoff row) (hb : 0≤ b) (hbv : b≤ v) :
    utilityOne v b (sourceProductMarginal row b)≤
      sourceSingletonFraction row*sourceActiveUtility row v := by
  have hx : 0< Uniform07.x row := by cases row <;> norm_num [Uniform07.x,Uniform07.xQ]
  have hxi := Uniform07.xi_pos row
  have hlam := source_entry_positive row
  have hxl : Uniform07.x row*v≤ Uniform07.entry row := by
    exact mul_le_mul_of_nonneg_left hvt hx.le
  have hfirst := clipped_singleton_product_upper hxi hlam hb hbv
  have hden : 4*Uniform07.xi row*(Uniform07.x row*v)≤ 4*Uniform07.xi row*Uniform07.entry row :=
    mul_le_mul_of_nonneg_left hxl (by positivity)
  have hlast := div_le_div_of_nonneg_left (sq_nonneg (v-Uniform07.entry row))
    (by positivity : 0<4*Uniform07.xi row*(Uniform07.x row*v)) hden
  calc
    utilityOne v b (sourceProductMarginal row b)≤
      (v-Uniform07.entry row)^2/(4*Uniform07.xi row*Uniform07.entry row) := hfirst
    _≤(v-Uniform07.entry row)^2/(4*Uniform07.xi row*(Uniform07.x row*v)) := hlast
    _=sourceSingletonFraction row*sourceActiveUtility row v := by
      unfold sourceSingletonFraction sourceActiveUtility
      ring

structure ProductKernels05 (row : Uniform07.Row) (Γ : FiniteGame m 2 c Seed)
    (i : Fin m) (R error : ℝ) where
  marginal : ∀ b∈Ico (0:ℝ) R, |q Γ i b-sourceProductMarginal row b|≤ error
  duplicate : ∀ b∈Ico (0:ℝ) R, |Physical.duplicate Γ i b-(sourceProductMarginal row b)^2|≤ error

lemma actual_one_product_error {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed}
    {i : Fin m} {R error v : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error) (hg : Γ.g=0) (hv : v∈Icc (0:ℝ) (Uniform07.cutoff row))
    (a : JointAction 2) (ha : a.routeCount=1) (hab : a.bid< R) (hav : a.bid≤ v) :
    (problem Γ i).payoff v a≤ utilityOne v a.bid (sourceProductMarginal row a.bid)+Uniform07.cutoff row*error := by
  rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg]
  have h := (abs_le.mp (E.marginal a.bid ⟨a.bid_nonneg,hab⟩)).2
  have hs := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hav)
  have hc := mul_le_mul_of_nonneg_right
    (show v-a.bid≤ Uniform07.cutoff row by linarith [hv.2,a.bid_nonneg]) he
  simp only [sub_zero]
  change utilityOne v a.bid (q Γ i a.bid)≤ _
  unfold utilityOne
  nlinarith

lemma actual_two_product_error {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed}
    {i : Fin m} {R error v b : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) (hv : v∈Icc (0:ℝ) (Uniform07.cutoff row))
    (hb : b∈Icc (0:ℝ) v) (hbR : b< R) :
    utilityTwo (Uniform07.eta row) v b (sourceProductMarginal row b)
      ((sourceProductMarginal row b)^2)-3*Uniform07.cutoff row*error≤
        (problem Γ i).payoff v (two b) := by
  have hq := (abs_le.mp (E.marginal b ⟨hb.1,hbR⟩)).1
  have hd := (abs_le.mp (E.duplicate b ⟨hb.1,hbR⟩)).2
  have heta := source_eta_mem row
  have heta0 := heta.1
  have hdelta0 : 0≤ v-b := sub_nonneg.mpr hb.2
  have hb0 := hb.1
  have hc : 0≤(v-b)+Uniform07.eta row*b ∧
      (v-b)+Uniform07.eta row*b≤ Uniform07.cutoff row := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr heta.2) hb.1,hv.2]
  have hqscale := mul_le_mul_of_nonneg_left hq (by positivity : 0≤ 2*(v-b))
  have hdscale := mul_le_mul_of_nonneg_left hd hc.1
  have hqerror := mul_le_mul_of_nonneg_right
    (show 2*(v-b)≤ 2*Uniform07.cutoff row by linarith [hv.2,hb.1]) he
  have hderror := mul_le_mul_of_nonneg_right hc.2 he
  rw [two_payoff Γ heta.1 heta.2 hA hg i v hb.1]
  unfold utilityTwo
  nlinarith

theorem actual_active_singleton_uniform_gap
    {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
    {R error v vmin : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error) (hR : Early.bidCap row< R)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) (hvmin : Uniform07.entry row< vmin)
    (hv : v∈Icc vmin (Uniform07.cutoff row))
    (a : JointAction 2) (ha : a.routeCount=1) (hab : a.bid< R) (hav : a.bid≤ v) :
    (1-sourceSingletonFraction row)*(vmin-Uniform07.entry row)^2/Uniform07.cutoff row-
        4*Uniform07.cutoff row*error≤
      (problem Γ i).payoff v (two (sourceActiveBid row v))-(problem Γ i).payoff v a := by
  have hl := source_entry_positive row
  have hv0 : 0< v := hl.trans (hvmin.trans_le hv.1)
  have hs := source_active_bid_spec row (hvmin.trans_le hv.1) hv.2
  have h1 := actual_one_product_error E he hg ⟨hv0.le,hv.2⟩ a ha hab hav
  have h2 := actual_two_product_error E he hA hg ⟨hv0.le,hv.2⟩
    ⟨(hl.trans hs.1).le,hs.2.1.le⟩ (hs.2.2.1.trans hR)
  rw [hs.2.2.2.2] at h2
  have hfrac := source_product_singleton_fraction row hv0 hv.2 a.bid_nonneg hav
  have hquad : (vmin-Uniform07.entry row)^2≤(v-Uniform07.entry row)^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hv.1)
      (show 0≤ v+vmin-2*Uniform07.entry row by linarith [hvmin,hv.1])
    nlinarith
  have hbase : (vmin-Uniform07.entry row)^2/Uniform07.cutoff row≤ sourceActiveUtility row v := by
    have hq := div_le_div_of_nonneg_right hquad (Uniform07.cutoff_pos row).le
    have hd := div_le_div_of_nonneg_left (sq_nonneg (v-Uniform07.entry row)) hv0 hv.2
    exact hq.trans hd
  have hcoef := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr (source_fraction_mem row).2.le)
  rw [←mul_div_assoc] at hcoef
  nlinarith only [h1,h2,hfrac,hcoef]

theorem every_omitted_lower_singleton_loses
    {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
    {R error v ell : ℝ} (E : ProductKernels05 row Γ i R error)
    (he : 0≤ error) (hR : Early.bidCap row< R)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) (hv : v∈Ioc (0:ℝ) (Uniform07.cutoff row))
    (hell : 0< ell) (hhalfU : v/2≤ Early.bidCap row)
    (hqhalf : ell≤ q Γ i (v/2)) (hDhalf : duplicate Γ i (v/2)≤ ell/2)
    (herror : 4*Uniform07.cutoff row*error<
      (1-sourceSingletonFraction row)*(Early.bidCap row-Uniform07.entry row)^2/Uniform07.cutoff row)
    (a : JointAction 2) (ha : a.routeCount=1)
    (hab : a.bid∈Ioo (Early.bidCap row) R) :
    ∃ z∈Icc (0:ℝ) (Early.bidCap row),
      (problem Γ i).payoff v a<(problem Γ i).payoff v (two z) := by
  by_cases hav : a.bid≤ v
  · have hgap := actual_active_singleton_uniform_gap E he hR hA hg
      (source_entry_lt_cap row) ⟨hab.1.le.trans hav,hv.2⟩ a ha hab.2 hav
    have hs := source_active_bid_spec row ((source_entry_lt_cap row).trans (hab.1.trans_le hav)) hv.2
    exact ⟨sourceActiveBid row v,⟨(source_entry_positive row).le.trans hs.1.le,hs.2.2.1.le⟩,
      sub_pos.mp ((sub_pos.mpr herror).trans_le hgap)⟩
  · have hnonpos : (problem Γ i).payoff v a≤ 0 := by
      rw [singleton_payoff Γ (by norm_num : 0<2) i a ha,hg]
      simp only [sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (lt_of_not_ge hav).le) (q_nonneg Γ i a.bid)
    have hhalf := half_value_broadcast_payoff_lower Γ i (source_eta_mem row) hA hg hv.1.le hell.le hqhalf hDhalf
    exact ⟨v/2,⟨div_nonneg hv.1.le (by norm_num),hhalfU⟩,
      hnonpos.trans_lt ((div_pos (mul_pos hv.1 hell) (by norm_num)).trans_le hhalf)⟩

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
