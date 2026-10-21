import FCAppendix.Affine.Hybrid.Finishing01Definitions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open MeasureTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

lemma integral_lt_integral_of_ae_lt {X : Type*} [MeasurableSpace X]
    {mu : Measure X} [IsProbabilityMeasure mu] {f g : X → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu) (hfg : ∀ᵐ x ∂mu, f x < g x) :
    (∫ x, f x ∂mu) < ∫ x, g x ∂mu := by
  have hle : f ≤ᵐ[mu] g := hfg.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_mono_ae hf hg hle)
  intro heq
  have hae := (integral_eq_iff_of_ae_le hf hg hle).mp heq
  obtain ⟨x, hlt, he⟩ := (hfg.and hae).exists
  exact hlt.ne he

namespace Primitives
variable (P : Primitives)

abbrev Price := ↥(Icc (P.h0*P.L) (P.h0*P.U))

lemma price_pos (lam : P.Price) : 0 < (lam : ℝ) :=
  (mul_pos P.h0_pos P.L_pos).trans_le lam.property.1

lemma exposure_interior (lam : P.Price) (b : P.Bid) :
    exposure P.xi lam b ∈ Ioo (0 : ℝ) 1 := by
  apply exposure_mem_Ioo P.xi_pos (P.bid_pos b)
  · exact (mul_le_mul_of_nonneg_left b.property.2 P.kappa_pos.le).trans_lt
      (P.box_lower.trans_le lam.property.1)
  · exact lam.property.2.trans_lt (P.box_upper.trans_le b.property.1)

def responseDerivative (v lam q : ℝ) : ℝ :=
  2*(1-P.z)*(v*(1-q)-lam)-P.z*lam*P.xi/(1-P.xi*q)^2

lemma responseDerivative_bid (v : ℝ) (lam : P.Price) (b : P.Bid) :
    bidDerivative P.xi P.z v lam b =
      P.responseDerivative v lam (exposure P.xi lam b)*lam/(P.xi*(b:ℝ)^2) := by
  have hb := (P.bid_pos b).ne'
  have hxi := P.xi_pos.ne'
  have hden : 1-P.xi*exposure P.xi lam b = (lam:ℝ)/(b:ℝ) := by
    unfold exposure
    field_simp
    ring
  rw [responseDerivative,hden,bidDerivative]
  field_simp [hb,hxi,(P.price_pos lam).ne']
  ring

lemma continuousOn_responseDerivative (v lam : ℝ) :
    ContinuousOn (P.responseDerivative v lam) (Icc (0 : ℝ) 1) := by
  unfold responseDerivative
  apply ContinuousOn.sub
  · fun_prop
  · apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro q hq
      exact pow_ne_zero _ (show 1-P.xi*q ≠ 0 by
        have : 0 < 1-P.xi*q := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
        exact this.ne')

lemma responseDerivative_zero_iff (v : P.Value) (lam : P.Price)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    P.responseDerivative v lam q = 0 ↔ phi P.xi P.z q = (lam:ℝ)/(v:ℝ) := by
  have he : 1-P.z ≠ 0 := (sub_pos.mpr P.z_lt_one).ne'
  have hv := (P.value_pos v).ne'
  have hqden : 0 < 1-P.xi*q := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
  have hd : 0 < 1+P.z*P.xi/(2*(1-P.z)*(1-P.xi*q)^2) := by
    have hz := P.z_nonneg
    have hxi := P.xi_pos
    have he' := sub_pos.mpr P.z_lt_one
    positivity
  have hfactor : P.responseDerivative v lam q = 2*(1-P.z)*
      ((v:ℝ)*(1-q)-(lam:ℝ)*(1+P.z*P.xi/(2*(1-P.z)*(1-P.xi*q)^2))) := by
    unfold responseDerivative
    field_simp [hqden.ne',he]
    ring
  rw [hfactor,phi,div_eq_div_iff hd.ne' hv]
  constructor
  · intro h
    have hh := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) he)
    linarith
  · intro h
    rw [show (v:ℝ)*(1-q)-(lam:ℝ)*
      (1+P.z*P.xi/(2*(1-P.z)*(1-P.xi*q)^2)) = 0 by linarith]
    ring

lemma exposure_strictMono (lam : P.Price) :
    StrictMono (fun b : P.Bid => exposure P.xi lam b) := by
  intro b c hbc
  have hfrac := div_lt_div_of_pos_left (P.price_pos lam) (P.bid_pos b) hbc
  exact (div_lt_div_iff_of_pos_right P.xi_pos).mpr (by linarith)

lemma exists_response (v : P.Value) (lam : P.Price) :
    ∃q : ℝ, q ∈ Ioo (0 : ℝ) 1 ∧ phi P.xi P.z q = (lam:ℝ)/(v:ℝ) ∧
      (lam:ℝ)/(1-P.xi*q) ∈ Ioo P.L P.U := by
  let lo : P.Bid := ⟨P.L,le_rfl,P.L_lt_U.le⟩
  let hi : P.Bid := ⟨P.U,P.L_lt_U.le,le_rfl⟩
  let ql := exposure P.xi lam lo
  let qu := exposure P.xi lam hi
  have hql := P.exposure_interior lam lo
  have hqu := P.exposure_interior lam hi
  have hqul : ql < qu := P.exposure_strictMono lam P.L_lt_U
  obtain ⟨hleft,hright⟩ := active_menu_endpoint_signs P.xi_pos P.xi_lt_one
    P.z_nonneg P.z_lt_one P.qbar_mem P.L_pos P.L_lt_U.le P.value_surplus
    P.inward_lower P.inward_upper v.property lam.property
  have hl : 0 < P.responseDerivative v lam ql := by
    rw [P.responseDerivative_bid v lam lo] at hleft
    by_contra! hn
    have hm := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hn (P.price_pos lam).le)
      (mul_pos P.xi_pos (sq_pos_of_pos P.L_pos)).le
    exact (not_le_of_gt hleft) hm
  have hu : P.responseDerivative v lam qu < 0 := by
    rw [P.responseDerivative_bid v lam hi] at hright
    by_contra! hn
    have hm := div_nonneg (mul_nonneg hn (P.price_pos lam).le)
      (mul_pos P.xi_pos (sq_pos_of_pos P.U_pos)).le
    exact (not_le_of_gt hright) hm
  obtain ⟨q,hq,hzero⟩ := intermediate_value_Icc' hqul.le
    ((P.continuousOn_responseDerivative v lam).mono
      (Icc_subset_Icc hql.1.le hqu.2.le)) ⟨hu.le,hl.le⟩
  have hqi : q ∈ Ioo ql qu := by
    constructor
    · refine lt_of_le_of_ne hq.1 ?_
      intro heq
      subst q
      linarith
    · refine lt_of_le_of_ne hq.2 ?_
      intro heq
      subst q
      linarith
  have hq01 : q ∈ Ioo (0:ℝ) 1 := ⟨hql.1.trans hqi.1,hqi.2.trans hqu.2⟩
  have hden : 0 < 1-P.xi*q := by nlinarith [P.xi_lt_one,P.xi_pos,hq01.2]
  refine ⟨q,hq01,(P.responseDerivative_zero_iff v lam
    ⟨hq01.1.le,hq01.2.le⟩).mp hzero,?_,?_⟩
  · apply (lt_div_iff₀ hden).mpr
    have hh := (div_lt_iff₀ P.xi_pos).mp hqi.1
    change 1-(lam:ℝ)/P.L < q*P.xi at hh
    have hh' := (lt_div_iff₀ P.L_pos).mp (show 1-P.xi*q < (lam:ℝ)/P.L by linarith)
    nlinarith
  · apply (div_lt_iff₀ hden).mpr
    have hh := (lt_div_iff₀ P.xi_pos).mp hqi.2
    change q*P.xi < 1-(lam:ℝ)/P.U at hh
    have hh' := (div_lt_iff₀ P.U_pos).mp (show (lam:ℝ)/P.U < 1-P.xi*q by linarith)
    nlinarith

def qResponse (v lam : ℝ) : ℝ :=
  if h : ∃q : ℝ, q ∈ Icc (0:ℝ) 1 ∧ phi P.xi P.z q=lam/v
  then h.choose else 0

def beta (v lam : ℝ) : ℝ := lam/(1-P.xi*P.qResponse v lam)

lemma qResponse_spec (v : P.Value) (lam : P.Price) :
    P.qResponse v lam ∈ Ioo (0:ℝ) 1 ∧
    phi P.xi P.z (P.qResponse v lam) = (lam:ℝ)/(v:ℝ) ∧
    P.beta v lam ∈ Ioo P.L P.U := by
  obtain ⟨q,hq,hphi,hb⟩ := P.exists_response v lam
  have hex : ∃q : ℝ,q∈ Icc (0:ℝ) 1 ∧ phi P.xi P.z q=(lam:ℝ)/(v:ℝ) :=
    ⟨q,⟨hq.1.le,hq.2.le⟩,hphi⟩
  have heq : P.qResponse v lam=q := by
    unfold qResponse
    rw [dif_pos hex]
    exact phi_injectiveOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one
      hex.choose_spec.1 ⟨hq.1.le,hq.2.le⟩ (hex.choose_spec.2.trans hphi.symm)
  simpa only [beta,heq] using And.intro hq (And.intro hphi hb)

lemma qResponse_phi (v : P.Value) (lam : P.Price) :
    phi P.xi P.z (P.qResponse v lam)=(lam:ℝ)/(v:ℝ) :=
  (P.qResponse_spec v lam).2.1

lemma qResponse_strictAnti (v : P.Value) :
    StrictAnti (fun lam : P.Price => P.qResponse v lam) := by
  intro lam nu hln
  have h := (div_lt_div_iff_of_pos_right (P.value_pos v)).mpr hln
  rw [←P.qResponse_phi v lam,←P.qResponse_phi v nu] at h
  by_contra! hn
  have hq := P.qResponse_spec v lam
  have hr := P.qResponse_spec v nu
  have hh := (phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn
    ⟨hq.1.1.le,hq.1.2.le⟩ ⟨hr.1.1.le,hr.1.2.le⟩ hn
  linarith

lemma responseDerivative_at_response (v : P.Value) (lam : P.Price) :
    P.responseDerivative v lam (P.qResponse v lam)=0 :=
  (P.responseDerivative_zero_iff v lam
    ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩).mpr
    (P.qResponse_phi v lam)

lemma two_tangent_gap (v lam q r : ℝ)
    (hq : 1-P.xi*q ≠ 0) (hr : 1-P.xi*r ≠ 0) :
    two P.xi P.z v lam q + P.responseDerivative v lam q*(r-q)-
      two P.xi P.z v lam r =
      (1-P.z)*v*(r-q)^2+
        P.z*lam*P.xi^2*(r-q)^2/((1-P.xi*q)^2*(1-P.xi*r)) := by
  unfold two responseDerivative
  field_simp [hq,hr]
  ring

lemma response_quadratic_gap (v : P.Value) (lam : P.Price)
    {q : ℝ} (hq : q∈ Icc (0:ℝ) 1) :
    (1-P.z)*P.vlo*(q-P.qResponse v lam)^2 ≤
      two P.xi P.z v lam (P.qResponse v lam)-two P.xi P.z v lam q := by
  have hr := (P.qResponse_spec v lam).1
  have hd : 0 < 1-P.xi*q := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
  have hdr : 0 < 1-P.xi*P.qResponse v lam := by
    nlinarith [P.xi_pos,P.xi_lt_one,hr.2]
  have hgap := P.two_tangent_gap v lam (P.qResponse v lam) q hdr.ne' hd.ne'
  rw [P.responseDerivative_at_response,zero_mul,add_zero] at hgap
  have hnonneg : 0 ≤ P.z*(lam:ℝ)*P.xi^2*(q-P.qResponse v lam)^2/
      ((1-P.xi*P.qResponse v lam)^2*(1-P.xi*q)) := by
    have hz:=P.z_nonneg
    have hl:=(P.price_pos lam).le
    positivity
  have hmono := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left v.property.1 (sub_pos.mpr P.z_lt_one).le)
    (sq_nonneg (q-P.qResponse v lam))
  linarith

def phiDen (q : ℝ) : ℝ := 1+P.z*P.xi/(2*(1-P.z)*(1-P.xi*q)^2)
def inverseModulus : ℝ := P.phiDen 1

lemma phiDen_pos {q : ℝ} (hq : q∈ Icc (0:ℝ) 1) : 0<P.phiDen q := by
  have hd : 0 < 1-P.xi*q := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
  have hz:=P.z_nonneg
  have hxi:=P.xi_pos
  have he:=sub_pos.mpr P.z_lt_one
  unfold phiDen
  positivity

lemma phiDen_mono : MonotoneOn P.phiDen (Icc (0:ℝ) 1) := by
  intro q hq r hr hqr
  have hqden : 0<1-P.xi*q := by nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
  have hrden : 0<1-P.xi*r := by nlinarith [P.xi_pos,P.xi_lt_one,hr.2]
  have hsq : (1-P.xi*r)^2 ≤ (1-P.xi*q)^2 :=
    (sq_le_sq₀ hrden.le hqden.le).mpr (by nlinarith [P.xi_pos])
  have he:=sub_pos.mpr P.z_lt_one
  have hz:=P.z_nonneg
  have hxi:=P.xi_pos
  unfold phiDen
  have hh := div_le_div_of_nonneg_left (mul_nonneg hz hxi.le)
    (mul_pos (mul_pos (show (0:ℝ)<2 by norm_num) he) (sq_pos_of_pos hrden))
    (mul_le_mul_of_nonneg_left hsq
      (mul_pos (show (0:ℝ)<2 by norm_num) he).le)
  linarith

lemma inverseModulus_pos : 0<P.inverseModulus := P.phiDen_pos ⟨by norm_num,le_rfl⟩

lemma phi_inverse_distance {q r : ℝ}
    (hq : q∈ Icc (0:ℝ) 1) (hr : r∈ Icc (0:ℝ) 1) :
    |q-r| ≤ P.inverseModulus*|phi P.xi P.z q-phi P.xi P.z r| := by
  have hordered : ∀ q r : ℝ, q ∈ Icc (0:ℝ) 1 → r ∈ Icc (0:ℝ) 1 → q ≤ r →
      r-q ≤ P.inverseModulus*(phi P.xi P.z q-phi P.xi P.z r) := by
    intro q r hq hr hqr
    have hd := P.phiDen_mono hq hr hqr
    have hdmax := P.phiDen_mono hq (show (1:ℝ)∈ Icc (0:ℝ) 1 by simp) hq.2
    have hpq : phi P.xi P.z q*P.phiDen q=1-q := by
      change (1-q)/P.phiDen q*P.phiDen q=1-q
      exact div_mul_cancel₀ _ (P.phiDen_pos hq).ne'
    have hpr : phi P.xi P.z r*P.phiDen r=1-r := by
      change (1-r)/P.phiDen r*P.phiDen r=1-r
      exact div_mul_cancel₀ _ (P.phiDen_pos hr).ne'
    have hpr0 : 0≤ phi P.xi P.z r :=
      div_nonneg (sub_nonneg.mpr hr.2) (P.phiDen_pos hr).le
    have hanti : phi P.xi P.z r≤ phi P.xi P.z q :=
      (phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn hq hr hqr
    have h1:=mul_nonneg hpr0 (sub_nonneg.mpr hd)
    have h2:=mul_nonneg (sub_nonneg.mpr hdmax) (sub_nonneg.mpr hanti)
    change r-q≤ P.phiDen 1*(phi P.xi P.z q-phi P.xi P.z r)
    nlinarith
  rcases le_total q r with hqr|hrq
  · rw [abs_of_nonpos (sub_nonpos.mpr hqr),abs_of_nonneg
      (sub_nonneg.mpr ((phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn hq hr hqr))]
    linarith [hordered q r hq hr hqr]
  · rw [abs_of_nonneg (sub_nonneg.mpr hrq),abs_of_nonpos
      (sub_nonpos.mpr ((phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn hr hq hrq))]
    linarith [hordered r q hr hq hrq]

lemma qResponse_distance (v w : P.Value) (lam nu : P.Price) :
    |P.qResponse v lam-P.qResponse w nu| ≤
      P.inverseModulus*|(lam:ℝ)/(v:ℝ)-(nu:ℝ)/(w:ℝ)| := by
  simpa only [P.qResponse_phi] using P.phi_inverse_distance
    ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩
    ⟨(P.qResponse_spec w nu).1.1.le,(P.qResponse_spec w nu).1.2.le⟩

lemma continuous_response :
    Continuous (fun t : P.Value×P.Price => P.qResponse t.1 t.2) := by
  have hratio : Continuous (fun t : P.Value×P.Price => (t.2:ℝ)/(t.1:ℝ)) := by
    apply Continuous.div <;> try fun_prop
    exact fun t => (P.value_pos t.1).ne'
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro eps heps
  obtain ⟨delta,hdelta,hd⟩ := (Metric.continuousAt_iff.mp hratio.continuousAt)
    (eps/P.inverseModulus) (div_pos heps P.inverseModulus_pos)
  refine ⟨delta,hdelta,?_⟩
  intro u hu
  have hh := hd hu
  rw [Real.dist_eq] at hh ⊢
  exact (P.qResponse_distance u.1 t.1 u.2 t.2).trans_lt
    ((mul_lt_mul_of_pos_left hh P.inverseModulus_pos).trans_eq
      (by field_simp [P.inverseModulus_pos.ne']))

lemma continuous_beta : Continuous (fun t : P.Value×P.Price => P.beta t.1 t.2) := by
  unfold beta
  apply Continuous.div
  · fun_prop
  · exact continuous_const.sub (continuous_const.mul P.continuous_response)
  · intro t
    have hq := (P.qResponse_spec t.1 t.2).1
    have : 0<1-P.xi*P.qResponse t.1 t.2 := by
      nlinarith [P.xi_pos,P.xi_lt_one,hq.2]
    exact this.ne'

lemma mean_response_continuous (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    Continuous (fun lam : P.Price => ∫v:P.Value,P.qResponse v lam ∂mu) := by
  let law : ProbabilityMeasure P.Value := ⟨mu,inferInstance⟩
  have h := continuous_law_integral (fun t : P.Price×P.Value => P.qResponse t.2 t.1)
    (P.continuous_response.comp continuous_swap)
  exact h.comp (continuous_id.prodMk (continuous_const : Continuous (fun _:P.Price=>law)))

lemma mean_response_strictAnti (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    StrictAnti (fun lam : P.Price => ∫v:P.Value,P.qResponse v lam ∂mu) := by
  intro lam nu hln
  have hl : Integrable (fun v:P.Value=>P.qResponse v lam) mu :=
    (P.continuous_response.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hn : Integrable (fun v:P.Value=>P.qResponse v nu) mu :=
    (P.continuous_response.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_lt_integral_of_ae_lt hn hl
    (Filter.Eventually.of_forall fun v=>P.qResponse_strictAnti v hln)

lemma response_at_price_endpoints (v : P.Value) :
    P.qbar < P.qResponse v (P.h0*P.L) ∧
      P.qResponse v (P.h0*P.U) < P.qbar := by
  let left : P.Price := ⟨P.h0*P.L,le_rfl,
    mul_le_mul_of_nonneg_left P.L_lt_U.le P.h0_pos.le⟩
  let right : P.Price := ⟨P.h0*P.U,
    mul_le_mul_of_nonneg_left P.L_lt_U.le P.h0_pos.le,le_rfl⟩
  have hl := (P.qResponse_spec v left).2.2.1
  have hr := (P.qResponse_spec v right).2.2.2
  have hlq := (P.qResponse_spec v left).1
  have hrq := (P.qResponse_spec v right).1
  have hdl : 0<1-P.xi*P.qResponse v left := by nlinarith [P.xi_pos,P.xi_lt_one,hlq.2]
  have hdr : 0<1-P.xi*P.qResponse v right := by nlinarith [P.xi_pos,P.xi_lt_one,hrq.2]
  change P.L<P.h0*P.L/(1-P.xi*P.qResponse v left) at hl
  change P.h0*P.U/(1-P.xi*P.qResponse v right)<P.U at hr
  have h1:=(lt_div_iff₀ hdl).mp hl
  have h2:=(div_lt_iff₀ hdr).mp hr
  dsimp [h0] at h1 h2
  change P.qbar < P.qResponse v left ∧ P.qResponse v right < P.qbar
  constructor
  · have hp : 0 < P.L*P.xi := mul_pos P.L_pos P.xi_pos
    nlinarith
  · have hp : 0 < P.U*P.xi := mul_pos P.U_pos P.xi_pos
    nlinarith

theorem exists_unique_clearing (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ∃!lam : P.Price, (∫v:P.Value,P.qResponse v lam ∂mu)=P.qbar := by
  let left : P.Price := ⟨P.h0*P.L,le_rfl,
    mul_le_mul_of_nonneg_left P.L_lt_U.le P.h0_pos.le⟩
  let right : P.Price := ⟨P.h0*P.U,
    mul_le_mul_of_nonneg_left P.L_lt_U.le P.h0_pos.le,le_rfl⟩
  let D : P.Price→ℝ := fun lam => ∫v:P.Value,P.qResponse v lam ∂mu
  letI : PreconnectedSpace P.Price := Subtype.preconnectedSpace isPreconnected_Icc
  have hlow : P.qbar≤ D left := by
    have hh := integral_mono_ae (integrable_const (μ:=mu) P.qbar)
      ((P.continuous_response.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : P.Value => left)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (Filter.Eventually.of_forall fun v=>(P.response_at_price_endpoints v).1.le)
    simpa using hh
  have hhigh : D right≤ P.qbar := by
    have hh := integral_mono_ae
      ((P.continuous_response.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : P.Value => right)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (integrable_const (μ:=mu) P.qbar)
      (Filter.Eventually.of_forall fun v=>(P.response_at_price_endpoints v).2.le)
    simpa using hh
  obtain ⟨lam,hlam⟩ := intermediate_value_univ right left (P.mean_response_continuous mu) ⟨hhigh,hlow⟩
  refine ⟨lam,hlam,?_⟩
  intro nu hnu
  exact (P.mean_response_strictAnti mu).injective (hnu.trans hlam.symm)

lemma clearing_source_interval (mu:Measure P.Value) [IsProbabilityMeasure mu]
    (lam:P.Price) (hclear:(∫v:P.Value,P.qResponse v lam ∂mu)=P.qbar) :
    (lam:ℝ)∈ Icc (P.vlo*phi P.xi P.z P.qbar) (P.vhi*phi P.xi P.z P.qbar) := by
  have hphipos:0<phi P.xi P.z P.qbar := by
    have hanti:=phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one
      ⟨P.qbar_mem.1.le,P.qbar_mem.2.le⟩ (show (1:ℝ)∈ Icc (0:ℝ) 1 by simp)
      P.qbar_mem.2
    simpa only [phi_one] using hanti
  have hi:Integrable (fun v:P.Value=>P.qResponse v lam) mu :=
    Integrable.of_bound ((P.continuous_response.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun v=>by
        rw [Real.norm_eq_abs,abs_of_pos (P.qResponse_spec v lam).1.1]
        exact (P.qResponse_spec v lam).1.2.le)
  constructor
  · by_contra! hbad
    have hq:∀ v:P.Value,P.qbar<P.qResponse v lam := by
      intro v
      have hm:=mul_le_mul_of_nonneg_right v.property.1 hphipos.le
      have hr:(lam:ℝ)/(v:ℝ)<phi P.xi P.z P.qbar :=
        (div_lt_iff₀ (P.value_pos v)).mpr (by nlinarith)
      rw [←P.qResponse_phi v lam] at hr
      by_contra! hn
      have hh:=(phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn
        ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩
        ⟨P.qbar_mem.1.le,P.qbar_mem.2.le⟩ hn
      linarith
    have hlt:=integral_lt_integral_of_ae_lt (integrable_const P.qbar) hi
      (Filter.Eventually.of_forall hq)
    simp [hclear] at hlt
  · by_contra! hbad
    have hq:∀ v:P.Value,P.qResponse v lam<P.qbar := by
      intro v
      have hm:=mul_le_mul_of_nonneg_right v.property.2 hphipos.le
      have hr:phi P.xi P.z P.qbar<(lam:ℝ)/(v:ℝ) :=
        (lt_div_iff₀ (P.value_pos v)).mpr (by nlinarith)
      rw [←P.qResponse_phi v lam] at hr
      by_contra! hn
      have hh:=(phi_strictAntiOn P.xi_pos P.xi_lt_one P.z_nonneg P.z_lt_one).antitoneOn
        ⟨P.qbar_mem.1.le,P.qbar_mem.2.le⟩
        ⟨(P.qResponse_spec v lam).1.1.le,(P.qResponse_spec v lam).1.2.le⟩ hn
      linarith
    have hlt:=integral_lt_integral_of_ae_lt hi (integrable_const P.qbar)
      (Filter.Eventually.of_forall hq)
    simp [hclear] at hlt

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
