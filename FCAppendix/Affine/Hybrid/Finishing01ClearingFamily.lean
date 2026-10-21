import FCAppendix.Affine.Hybrid.Finishing01ClearingScalar
import FCAppendix.Affine.Hybrid.Finishing01MenusCalculus
import FCAppendix.Affine.Hybrid.Finishing01MenusNoisyTransport

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace Primitives
variable (P:Primitives)

def realBaseLaw (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) : Measure ℝ :=
  Measure.map (fun b:P.Bid=>(b:ℝ))
    (pi.1.map measurable_snd.aemeasurable:Measure P.Bid)

instance realBaseLaw_probability (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) : IsProbabilityMeasure (P.realBaseLaw mu pi) :=
  Measure.isProbabilityMeasure_map continuous_subtype_val.measurable.aemeasurable

lemma realBaseLaw_eq_joint_map (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) :
    P.realBaseLaw mu pi=(pi.1:Measure (P.Value×P.Bid)).map
      (fun t:P.Value×P.Bid=>(t.2:ℝ)) := by
  change ((pi.1 : Measure (P.Value × P.Bid)).map Prod.snd).map Subtype.val = _
  rw [Measure.map_map continuous_subtype_val.measurable measurable_snd]
  rfl

lemma realBaseLaw_box (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) : ∀ᵐb∂P.realBaseLaw mu pi,b∈ Icc P.L P.U := by
  rw [P.realBaseLaw_eq_joint_map]
  exact (ae_map_iff (continuous_subtype_val.measurable.comp measurable_snd).aemeasurable
    isClosed_Icc.measurableSet).mpr (Filter.Eventually.of_forall fun t=> t.2.property)

lemma reciprocal_realBaseLaw (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) :
    reciprocalMean (P.realBaseLaw mu pi)=
      ∫t:P.Value×P.Bid,((t.2:ℝ)⁻¹) ∂(pi.1:Measure (P.Value×P.Bid)) := by
  rw [reciprocalMean,P.realBaseLaw_eq_joint_map]
  exact integral_map (continuous_subtype_val.measurable.comp measurable_snd).aemeasurable
    measurable_inv.aestronglyMeasurable

lemma reciprocal_joint_pos (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) :
    0<∫t:P.Value×P.Bid,((t.2:ℝ)⁻¹) ∂(pi.1:Measure (P.Value×P.Bid)) := by
  rw [←P.reciprocal_realBaseLaw]
  exact (one_div_pos.mpr P.U_pos).trans_le
    (reciprocalMean_bounds _ P.L_pos (P.realBaseLaw_box mu pi)).1

lemma price_compact_bounds (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) : P.price mu pi∈ Icc (P.h0*P.L) (P.h0*P.U) := by
  have hH:=reciprocalMean_bounds _ P.L_pos (P.realBaseLaw_box mu pi)
  rw [P.reciprocal_realBaseLaw] at hH
  have hH0:=P.reciprocal_joint_pos mu pi
  unfold price
  constructor
  · apply (le_div_iff₀ hH0).mpr
    have h:=mul_le_mul_of_nonneg_left hH.2 (mul_pos P.h0_pos P.L_pos).le
    have he:P.h0*P.L*(1/P.L)=P.h0 := by field_simp [(P.L_pos).ne']
    nlinarith
  · apply (div_le_iff₀ hH0).mpr
    have h:=mul_le_mul_of_nonneg_left hH.1 (mul_pos P.h0_pos P.U_pos).le
    have he:P.h0*P.U*(1/P.U)=P.h0 := by field_simp [(P.U_pos).ne']
    nlinarith

def compactPrice (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) : P.Price := ⟨P.price mu pi,P.price_compact_bounds mu pi⟩

lemma continuous_price (mu:Measure P.Value) [IsProbabilityMeasure mu] :
    Continuous (P.price mu) := by
  let f:C(P.Value×P.Bid,ℝ):=⟨fun t=>(t.2:ℝ)⁻¹,by
    apply Continuous.inv₀
    · fun_prop
    · exact fun t=>(P.bid_pos t.2).ne'⟩
  have hi:Continuous (fun pi:Law (A:=P.Bid) mu=>∫t,f t ∂(pi.1:Measure (P.Value×P.Bid))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap f).comp continuous_subtype_val
  exact continuous_const.div hi (fun pi=>(P.reciprocal_joint_pos mu pi).ne')

lemma reference_eq_two (v:ℝ) (lam:P.Price) (b:P.Bid) :
    P.reference v lam b=two P.xi P.z v lam (exposure P.xi lam b) := by
  change P.z*(v-(b:ℝ))+(1-P.z)*independentTwo P.eta v b (exposure P.xi lam b)=_
  rw [←Finishing01Menus.bidMenu_eq_physical (show P.eta=1-2*P.xi by rfl)
    P.xi_pos.ne' (P.bid_pos b).ne']
  exact Finishing01Menus.bidMenu_eq_two P.xi_pos.ne' (P.price_pos lam).ne' (P.bid_pos b).ne'

def responseBid (v:P.Value) (lam:P.Price) : P.Bid :=
  ⟨P.beta v lam,(P.qResponse_spec v lam).2.2.1.le,(P.qResponse_spec v lam).2.2.2.le⟩

lemma responseBid_exposure (v:P.Value) (lam:P.Price) :
    exposure P.xi lam (P.responseBid v lam)=P.qResponse v lam := by
  have hq:=(P.qResponse_spec v lam).1
  have hd:1-P.xi*P.qResponse v lam≠0 := by
    have : 0<1-P.xi*P.qResponse v lam := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
    exact this.ne'
  unfold responseBid beta exposure
  dsimp only
  field_simp [hd,P.xi_pos.ne',(P.price_pos lam).ne']
  ring

def UniformActualMenus (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu) : Prop :=
  ∀ eps>0,∀ᶠM in atTop,∀ t:P.Value×P.Bid,
    |P.exactUtility (M-1) (c M) (low M) mu (pi M) t-
      P.reference t.1 (P.price mu (pi M)) t.2|< eps

def EventualActualIC (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu) : Prop :=
  ∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),∀ B':P.Bid,
    P.exactUtility (M-1) (c M) (low M) mu (pi M) (t.1,B')≤
      P.exactUtility (M-1) (c M) (low M) mu (pi M) t

theorem uniform_actual_menus (c:ℕ→ℕ)
    (hc:Tendsto (fun M=>(c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (low:ℕ→ ProbabilityMeasure P.Low) (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:ℕ→ Law (A:=P.Bid) mu) : P.UniformActualMenus c low mu pi := by
  intro eps heps
  obtain ⟨N0,hN0⟩:=Filter.eventually_atTop.mp
    (Finishing01Menus.full_row_reference_limit P P.U P.L_lt_U.le P.box_lower P.box_upper
      c hc P.vhi (P.vlo_pos.le.trans P.value_order) eps heps)
  filter_upwards [eventually_ge_atTop (N0+1)] with M hM
  intro t
  have hN:N0≤ M-1:=by omega
  have hidx:M-1+1=M:=by omega
  have hh:=hN0 (M-1) hN P.U ⟨P.L_lt_U.le,le_rfl⟩
    (Finishing01Menus.lowReal P (low M)) (P.realBaseLaw mu (pi M))
    (P.realBaseLaw_box mu (pi M)) t.1
    (by rw [abs_of_pos (P.value_pos t.1)];exact t.1.property.2)
    t.2 t.2.property
  rw [hidx] at hh
  rw [Finishing01Menus.exactUtility_eq_actualRowInterim]
  change |Finishing01Menus.actualRowInterim P.xi P.z P.L P.U (c M) P.categories
    (Finishing01Menus.lowReal P (low M)) (P.realBaseLaw mu (pi M)) t.1 t.2-
    P.reference t.1 (P.price mu (pi M)) t.2|< eps
  simpa only [price,←P.reciprocal_realBaseLaw] using hh

theorem supported_exposure_concentration (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu)
    (hIC:P.EventualActualIC c low mu pi) (hmenu:P.UniformActualMenus c low mu pi) :
    ∀ delta>0,∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),
      |exposure P.xi (P.price mu (pi M)) t.2-
        P.qResponse t.1 (P.price mu (pi M))|< delta := by
  intro delta hdelta
  let A:ℝ:=(1-P.z)*P.vlo
  have hA:0< A:=mul_pos (sub_pos.mpr P.z_lt_one) P.vlo_pos
  have heps:0< A*delta^2/4:=by positivity
  filter_upwards [hIC,hmenu (A*delta^2/4) heps] with M hM hm
  filter_upwards [hM] with t ht
  let lam:=P.compactPrice mu (pi M)
  let br:=P.responseBid t.1 lam
  have hs:=ht br
  have hu:=hm t
  have hb:=hm (t.1,br)
  have hgap:=P.response_quadratic_gap t.1 lam
    ⟨(P.exposure_interior lam t.2).1.le,(P.exposure_interior lam t.2).2.le⟩
  have href:P.reference t.1 lam br=two P.xi P.z t.1 lam (P.qResponse t.1 lam) := by
    rw [P.reference_eq_two,P.responseBid_exposure]
  rw [←href,←P.reference_eq_two t.1 lam t.2] at hgap
  have hab:=abs_lt.mp hb
  have hau:=abs_lt.mp hu
  by_contra! hn
  have hsq:delta^2≤(exposure P.xi (P.price mu (pi M)) t.2-
      P.qResponse t.1 (P.price mu (pi M)))^2 := by
    nlinarith [sq_abs (exposure P.xi (P.price mu (pi M)) t.2-
      P.qResponse t.1 (P.price mu (pi M)))]
  have hh:=mul_le_mul_of_nonneg_left hsq hA.le
  dsimp only [A,lam,compactPrice,br] at *
  nlinarith

lemma integral_value (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) (f:P.Value→ℝ) (hf:Measurable f) :
    (∫t:P.Value×P.Bid,f t.1 ∂(pi.1:Measure (P.Value×P.Bid)))=∫v,f v ∂mu := by
  have hfst:(pi.1:Measure (P.Value×P.Bid)).map Prod.fst=mu:=pi.property
  calc
    _ = ∫ v, f v ∂((pi.1 : Measure (P.Value × P.Bid)).map Prod.fst) :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := congrArg (fun nu : Measure P.Value => ∫ v, f v ∂nu) hfst

lemma integral_exposure_eq_qbar (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:Law (A:=P.Bid) mu) :
    (∫t:P.Value×P.Bid,exposure P.xi (P.price mu pi) t.2
      ∂(pi.1:Measure (P.Value×P.Bid)))=P.qbar := by
  have hi:Integrable (fun t:P.Value×P.Bid=>(t.2:ℝ)⁻¹)
      (pi.1:Measure (P.Value×P.Bid)) :=
    Integrable.of_bound (by fun_prop) (1/P.L) (Filter.Eventually.of_forall fun t=> by
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (P.bid_pos t.2))]
      exact (reciprocal_box_bounds P.L_pos t.2.property).2)
  have he:∀ t:P.Value×P.Bid,exposure P.xi (P.price mu pi) t.2=
      (1-P.price mu pi*((t.2:ℝ)⁻¹))/P.xi := by intro t; rfl
  simp_rw [he]
  rw [integral_div,integral_sub (integrable_const _) (hi.const_mul _),
    integral_const_mul,integral_const,probReal_univ,one_smul]
  unfold price h0
  field_simp [(P.reciprocal_joint_pos mu pi).ne',P.xi_pos.ne']
  ring

theorem finite_mean_response_tendsto (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu)
    (hIC:P.EventualActualIC c low mu pi) (hmenu:P.UniformActualMenus c low mu pi) :
    Tendsto (fun M=>∫v:P.Value,P.qResponse v (P.price mu (pi M)) ∂mu) atTop (𝓝 P.qbar) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  filter_upwards [P.supported_exposure_concentration c low mu pi hIC hmenu
    (eps/2) (by linarith)] with M hM
  let lam:=P.compactPrice mu (pi M)
  have hi:Integrable (fun t:P.Value×P.Bid=> P.qResponse t.1 lam-exposure P.xi lam t.2)
      ((pi M).1:Measure (P.Value×P.Bid)) := by
    apply Integrable.of_bound (C:=eps/2)
    · apply AEMeasurable.aestronglyMeasurable
      apply Measurable.aemeasurable
      exact ((P.continuous_response.comp (continuous_fst.prodMk continuous_const)).measurable).sub
        (by unfold exposure;fun_prop)
    · filter_upwards [hM] with t ht
      rw [Real.norm_eq_abs,abs_sub_comm]
      exact ht.le
  have hqi:Integrable (fun t:P.Value×P.Bid=> P.qResponse t.1 lam)
      ((pi M).1:Measure (P.Value×P.Bid)) :=
    Integrable.of_bound ((P.continuous_response.comp
      (continuous_fst.prodMk continuous_const)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun t=> by
        rw [Real.norm_eq_abs,abs_of_pos (P.qResponse_spec t.1 lam).1.1]
        exact (P.qResponse_spec t.1 lam).1.2.le)
  have hei:Integrable (fun t:P.Value×P.Bid=> exposure P.xi lam t.2)
      ((pi M).1:Measure (P.Value×P.Bid)) := by
    exact (hqi.sub hi).congr (Filter.Eventually.of_forall fun t=> by dsimp; ring)
  have hn:=norm_integral_le_of_norm_le_const (μ:=((pi M).1:Measure (P.Value×P.Bid)))
    (C:=eps/2) (f:=fun t:P.Value×P.Bid=> P.qResponse t.1 lam-exposure P.xi lam t.2)
    (hM.mono fun t ht=> by change |P.qResponse t.1 (P.price mu (pi M)) - exposure P.xi (P.price mu (pi M)) t.2| ≤ eps/2; rw [abs_sub_comm]; exact ht.le)
  rw [integral_sub hqi hei] at hn
  change ‖(∫ t : P.Value × P.Bid, P.qResponse t.1 (P.price mu (pi M)) ∂((pi M).1 : Measure (P.Value × P.Bid))) - (∫ t : P.Value × P.Bid, exposure P.xi (P.price mu (pi M)) t.2 ∂((pi M).1 : Measure (P.Value × P.Bid)))‖ ≤ _ at hn
  rw [P.integral_value mu (pi M) (fun v : P.Value => P.qResponse v (P.price mu (pi M))) (show Measurable (fun v : P.Value => P.qResponse v (P.price mu (pi M))) from (P.continuous_response.comp (continuous_id.prodMk (continuous_const (y := P.compactPrice mu (pi M))))).measurable), P.integral_exposure_eq_qbar] at hn
  simp only [probReal_univ, mul_one] at hn
  simpa only [Real.norm_eq_abs,Real.dist_eq] using hn.trans_lt (by linarith : eps/2< eps)

theorem full_price_convergence (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:ℕ→ Law (A:=P.Bid) mu) (lam:P.Price)
    (hclear:(∫v:P.Value,P.qResponse v lam ∂mu)=P.qbar)
    (hmean:Tendsto (fun M=>∫v:P.Value,P.qResponse v (P.price mu (pi M)) ∂mu)
      atTop (𝓝 P.qbar)) :
    Tendsto (fun M=> P.price mu (pi M)) atTop (𝓝 (lam:ℝ)) := by
  apply tendsto_of_subseq_tendsto
  intro psi hpsi
  obtain ⟨nu,phi,hphi,hconv⟩:=CompactSpace.tendsto_subseq
    (fun n=> P.compactPrice mu (pi (psi n)))
  have hm: Tendsto (fun n=>∫v:P.Value,P.qResponse v (P.compactPrice mu (pi (psi (phi n)))) ∂mu)
      atTop (𝓝 (∫v:P.Value,P.qResponse v nu ∂mu)) :=
    (P.mean_response_continuous mu).continuousAt.tendsto.comp hconv
  have hm': Tendsto (fun n=>∫v:P.Value,P.qResponse v (P.compactPrice mu (pi (psi (phi n)))) ∂mu)
      atTop (𝓝 P.qbar) :=hmean.comp (hpsi.comp hphi.tendsto_atTop)
  have he:(∫v:P.Value,P.qResponse v nu ∂mu)=P.qbar:=tendsto_nhds_unique hm hm'
  have hnu:nu=lam:=(P.mean_response_strictAnti mu).injective (he.trans hclear.symm)
  refine ⟨phi,?_⟩
  simpa only [hnu,compactPrice,Function.comp_def] using continuous_subtype_val.continuousAt.tendsto.comp hconv

lemma response_price_distance (v:P.Value) (lam nu:P.Price) :
    |P.qResponse v lam-P.qResponse v nu|≤ P.inverseModulus*|(lam:ℝ)-(nu:ℝ)|/P.vlo := by
  have hh:=P.qResponse_distance v v lam nu
  rw [←sub_div,abs_div,abs_of_pos (P.value_pos v)] at hh
  rw [←mul_div_assoc] at hh
  apply hh.trans
  exact div_le_div_of_nonneg_left
    (mul_nonneg P.inverseModulus_pos.le (abs_nonneg _)) P.vlo_pos v.property.1

theorem supported_final_exposure (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu)
    (hIC:P.EventualActualIC c low mu pi) (hmenu:P.UniformActualMenus c low mu pi)
    (lam:P.Price) (hprice:Tendsto (fun M=> P.price mu (pi M)) atTop (𝓝 (lam:ℝ))) :
    ∀ eps>0,∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),
      |exposure P.xi (P.price mu (pi M)) t.2-P.qResponse t.1 lam|< eps := by
  intro eps heps
  have hchange:Tendsto (fun M=> P.inverseModulus*|P.price mu (pi M)-(lam:ℝ)|/P.vlo)
      atTop (𝓝 0) := by
    simpa using ((((tendsto_const_nhds (x := P.inverseModulus)).mul (hprice.sub (tendsto_const_nhds (x := (lam : ℝ)))).abs).div_const P.vlo))
  filter_upwards [P.supported_exposure_concentration c low mu pi hIC hmenu
    (eps/2) (by linarith),hchange.eventually (gt_mem_nhds (by linarith : 0< eps/2))]
    with M hM hchangeM
  filter_upwards [hM] with t ht
  have hr:=P.response_price_distance t.1 (P.compactPrice mu (pi M)) lam
  change |P.qResponse t.1 (P.price mu (pi M)) - P.qResponse t.1 lam| ≤ P.inverseModulus * |P.price mu (pi M) - (lam : ℝ)| / P.vlo at hr
  exact (abs_sub_le _ (P.qResponse t.1 (P.price mu (pi M))) _).trans_lt (by linarith)

def bidExposureModulus : ℝ := P.xi*P.U^2/(P.h0*P.L)
lemma bidExposureModulus_pos : 0< P.bidExposureModulus := by
  unfold bidExposureModulus
  exact div_pos (mul_pos P.xi_pos (sq_pos_of_pos P.U_pos)) (mul_pos P.h0_pos P.L_pos)

lemma bid_distance_of_exposure (v:P.Value) (lam:P.Price) (b:P.Bid) :
    |(b:ℝ)-P.beta v lam|≤ P.bidExposureModulus*
      |exposure P.xi lam b-P.qResponse v lam| := by
  let br:=P.responseBid v lam
  have hid:(b:ℝ)-P.beta v lam=
      P.xi*(b:ℝ)*(br:ℝ)/(lam:ℝ)*(exposure P.xi lam b-exposure P.xi lam br) := by
    change (b:ℝ)-(br:ℝ)=_
    unfold exposure
    field_simp [P.xi_pos.ne',(P.bid_pos b).ne',(P.bid_pos br).ne',(P.price_pos lam).ne']
    ring
  rw [hid,abs_mul,abs_of_pos (div_pos (mul_pos (mul_pos P.xi_pos (P.bid_pos b)) (P.bid_pos br)) (P.price_pos lam)),
    P.responseBid_exposure]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply (div_le_div_of_nonneg_right
    (show P.xi*(b:ℝ)*(br:ℝ)≤ P.xi*P.U^2 by
      have hh := mul_le_mul_of_nonneg_left (mul_le_mul b.property.2 br.property.2 (P.bid_pos br).le P.U_pos.le) P.xi_pos.le
      simpa only [pow_two, mul_assoc] using hh)
    (P.price_pos lam).le).trans
  exact div_le_div_of_nonneg_left (mul_nonneg P.xi_pos.le (sq_nonneg _)) (mul_pos P.h0_pos P.L_pos) lam.property.1

theorem supported_bid_graph (c:ℕ→ℕ) (low:ℕ→ ProbabilityMeasure P.Low)
    (mu:Measure P.Value) [IsProbabilityMeasure mu] (pi:ℕ→ Law (A:=P.Bid) mu)
    (hIC:P.EventualActualIC c low mu pi) (hmenu:P.UniformActualMenus c low mu pi)
    (lam:P.Price) (hprice:Tendsto (fun M=> P.price mu (pi M)) atTop (𝓝 (lam:ℝ))) :
    ∀ eps>0,∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),
      |(t.2:ℝ)-P.beta t.1 lam|< eps := by
  intro eps heps
  let delta:=eps/(2*P.bidExposureModulus)
  have hd:0< delta:=div_pos heps (mul_pos (by norm_num) P.bidExposureModulus_pos)
  have hchange:Tendsto (fun M=>|P.price mu (pi M)-(lam:ℝ)|/(P.xi*P.L)) atTop (𝓝 0) := by
    simpa using ((hprice.sub (tendsto_const_nhds (x := (lam : ℝ)))).abs.div_const (P.xi*P.L))
  filter_upwards [P.supported_final_exposure c low mu pi hIC hmenu lam hprice (delta/2)
    (by linarith),hchange.eventually (gt_mem_nhds (by linarith : 0< delta/2))]
    with M hM hchangeM
  filter_upwards [hM] with t ht
  have hh:=exposure_difference_bound (lam:=(lam:ℝ)) (lam':=P.price mu (pi M))
    P.xi_pos P.L_pos t.2.property.1
  rw [abs_sub_comm (lam:ℝ)] at hh
  have hq:|exposure P.xi lam t.2-P.qResponse t.1 lam|< delta :=
    (abs_sub_le _ (exposure P.xi (P.price mu (pi M)) t.2) _).trans_lt (by linarith)
  exact (P.bid_distance_of_exposure t.1 lam t.2).trans_lt
    ((mul_lt_mul_of_pos_left hq P.bidExposureModulus_pos).trans (by
      dsimp [delta]
      have : P.bidExposureModulus*(eps/(2*P.bidExposureModulus))=eps/2 := by
        field_simp [P.bidExposureModulus_pos.ne']
      rw [this]
      linarith))

theorem unique_clearing_and_full_sequence (c:ℕ→ℕ)
    (hc:Tendsto (fun M=>(c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (low:ℕ→ ProbabilityMeasure P.Low) (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (pi:ℕ→ Law (A:=P.Bid) mu) (hIC:P.EventualActualIC c low mu pi) :
    ∃lam:P.Price,
      (lam:ℝ)∈ Icc (P.vlo*phi P.xi P.z P.qbar) (P.vhi*phi P.xi P.z P.qbar) ∧
      (∫v:P.Value,P.qResponse v lam ∂mu)=P.qbar ∧
      (∀ nu:P.Price,(∫v:P.Value,P.qResponse v nu ∂mu)=P.qbar→ nu=lam) ∧
      Tendsto (fun M=> P.price mu (pi M)) atTop (𝓝 (lam:ℝ)) ∧
      (∀ eps>0,∀ᶠM in atTop,∀ᵐt∂((pi M).1:Measure (P.Value×P.Bid)),
        |(t.2:ℝ)-P.beta t.1 lam|< eps) := by
  obtain ⟨lam,hclear,hunique⟩:=P.exists_unique_clearing mu
  have hmenu:=P.uniform_actual_menus c hc low mu pi
  have hm:=P.finite_mean_response_tendsto c low mu pi hIC hmenu
  have hp:=P.full_price_convergence mu pi lam hclear hm
  exact ⟨lam,P.clearing_source_interval mu lam hclear,hclear,hunique,hp,
    P.supported_bid_graph c low mu pi hIC hmenu lam hp⟩

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
