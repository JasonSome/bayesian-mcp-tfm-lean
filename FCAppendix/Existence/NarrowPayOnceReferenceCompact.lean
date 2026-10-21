import FCAppendix.Existence.NarrowPayOnceProfileScore

noncomputable section
namespace FCAppendix.Existence.NarrowPayOnce
open Set Filter Topology
open PayOnce PayOnce.OwnImpact CommonList PayOnce.ResponseFactor
open scoped BigOperators

def thetaReferenceBid (n : ℕ) (w rho theta : ℝ) : ℝ :=
  w*(1-rho)^(n-1)/(H n rho+rho*theta*Hslope n rho)
def thetaOwnScale (n : ℕ) (rho theta : ℝ) : ℝ :=
  H n rho/((1+theta)*Hslope n rho)
def thetaCurvature (n : ℕ) (w rho theta : ℝ) : ℝ :=
  let B := thetaReferenceBid n w rho theta
  (n:ℝ)*(w*((n:ℝ)-1)*(1-rho)^(n-2)+
    B*(2*theta*Hslope n rho+rho*Hcurvature n rho*theta^2))*(thetaOwnScale n rho theta/B)^2
def thetaCommonSensitivity (n : ℕ) (w rho theta : ℝ) : ℝ :=
  let B := thetaReferenceBid n w rho theta
  w*(n:ℝ)*(1-rho)^(n-1)*thetaOwnScale n rho theta/B^2

theorem thetaReferenceBid_pos {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : 0≤theta) :
    0<thetaReferenceBid n w rho theta := by
  have hH := H_pos n (by omega) rho hrho.1.le hrho.2.le
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hr : 0<rho := hrho.1
  unfold thetaReferenceBid
  positivity

theorem thetaReferenceBid_le {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : 0≤theta) :
    thetaReferenceBid n w rho theta≤w := by
  have hH := H_pos n (by omega) rho hrho.1.le hrho.2.le
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hr : 0<rho := hrho.1
  have hden : 0<H n rho+rho*theta*Hslope n rho := by positivity
  apply (div_le_iff₀ hden).mpr
  have hh := H_ge_last n (by omega) ⟨hrho.1.le,hrho.2.le⟩
  have hrest : 0≤rho*theta*Hslope n rho := by positivity
  nlinarith

theorem thetaOwnScale_pos {n : ℕ} (hn : 2≤n) {rho theta : ℝ}
    (hrho : rho∈Ioo (0:ℝ) 1) (htheta : 0≤theta) : 0<thetaOwnScale n rho theta := by
  exact div_pos (H_pos n (by omega) rho hrho.1.le hrho.2.le)
    (mul_pos (by linarith) (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩))

theorem thetaCurvature_pos {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : 0≤theta) :
    0<thetaCurvature n w rho theta := by
  have hB := thetaReferenceBid_pos hn hw hrho htheta
  have hk := thetaOwnScale_pos hn hrho htheta
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hQ := Hcurvature_nonneg n hrho.2.le
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : 0<(n:ℝ)-1 := by
    have hh : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    linarith
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hr : 0<rho := hrho.1
  dsimp [thetaCurvature]
  positivity

theorem thetaCommonSensitivity_pos {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : 0≤theta) :
    0<thetaCommonSensitivity n w rho theta := by
  have hB := thetaReferenceBid_pos hn hw hrho htheta
  have hk := thetaOwnScale_pos hn hrho htheta
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  dsimp [thetaCommonSensitivity]
  positivity

theorem thetaCommonSensitivity_le_curvature {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : theta∈Icc (0:ℝ) 1) :
    thetaCommonSensitivity n w rho theta≤(2-2/(n:ℝ))*thetaCurvature n w rho theta := by
  have hB := thetaReferenceBid_pos hn hw hrho htheta.1
  have hk := thetaOwnScale_pos hn hrho htheta.1
  have hD := Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩
  have hQ := Hcurvature_nonneg n hrho.2.le
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hn1 : 0<(n:ℝ)-1 := by
    have hh : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    linarith
  have hz : 0<1-rho := sub_pos.mpr hrho.2
  have hr : 0<rho := hrho.1
  have htheta0 : 0≤theta := htheta.1
  have hcoeff : 0≤2-2/(n:ℝ) := by rw [sub_nonneg,div_le_iff₀ hnR]; nlinarith
  have hscale : 1-rho≤(2-2/(n:ℝ))*((n:ℝ)-1)*thetaOwnScale n rho theta := by
    have hgap := weighted_Hslope_relative_gap hn ⟨hrho.1.le,hrho.2.le⟩
    have hhalf : (1:ℝ)/2≤1/(1+theta) := (le_div_iff₀ (by linarith [htheta.1])).mpr (by linarith [htheta.2])
    have hc0 : 0≤((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho := by
      have hnc : 0≤1-1/(n:ℝ) := by rw [sub_nonneg,div_le_one hnR]; linarith
      have hH := H_pos n (by omega) rho hrho.1.le hrho.2.le
      positivity
    have hh := mul_le_mul_of_nonneg_right hhalf hc0
    have hh' : ((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho≤
        (2-2/(n:ℝ))*((n:ℝ)-1)*(H n rho/(1+theta)) := by
      calc
        _≤2*(1/(1+theta)*(((n:ℝ)-1)*(1-1/(n:ℝ))*H n rho)) := by linarith only [hh]
        _=_ := by ring
    unfold thetaOwnScale
    rw [div_mul_eq_div_div,← mul_div_assoc]
    exact (le_div_iff₀ hD).mpr (by convert hgap.trans hh' using 1)
  have hpow : (1-rho)^(n-1)=(1-rho)^(n-2)*(1-rho) := by
    rw [← pow_succ]; congr 1; omega
  have hmain : thetaCommonSensitivity n w rho theta≤
      (2-2/(n:ℝ))*((n:ℝ)*(w*((n:ℝ)-1)*(1-rho)^(n-2))*
        (thetaOwnScale n rho theta/thetaReferenceBid n w rho theta)^2) := by
    dsimp [thetaCommonSensitivity]
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_left hscale
      (by positivity : 0≤w*(n:ℝ)*(1-rho)^(n-2)*thetaOwnScale n rho theta/(thetaReferenceBid n w rho theta)^2)
    convert hh using 1 <;> first | rfl | field_simp
  refine hmain.trans ?_
  dsimp [thetaCurvature]
  gcongr
  apply le_add_of_nonneg_right
  positivity

theorem theta_reference_gap_pos {n : ℕ} (hn : 2≤n) {w rho theta : ℝ}
    (hw : 0<w) (hrho : rho∈Ioo (0:ℝ) 1) (htheta : theta∈Icc (0:ℝ) 1) :
    0<thetaCurvature n w rho theta-
      |thetaCurvature n w rho theta-thetaCommonSensitivity n w rho theta| := by
  have ha := thetaCurvature_pos hn hw hrho htheta.1
  have he := thetaCommonSensitivity_pos hn hw hrho htheta.1
  have hle := thetaCommonSensitivity_le_curvature hn hw hrho htheta
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hstrict : (2-2/(n:ℝ))*thetaCurvature n w rho theta<2*thetaCurvature n w rho theta := by
    have hh : 0<2/(n:ℝ) := div_pos (by norm_num) hnR
    nlinarith
  exact sub_pos.mpr (abs_lt.mpr ⟨by linarith,by linarith⟩)

def referenceParameterBox (lo hi : ℝ) : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc 0 1

theorem continuousAt_thetaReferenceBid {n : ℕ} (hn : 2≤n) (w : ℝ)
    (x : ℝ×ℝ) (hx : x.1∈Ioo (0:ℝ) 1 ∧ 0≤x.2) :
    ContinuousAt (fun y : ℝ×ℝ=>thetaReferenceBid n w y.1 y.2) x := by
  have hH := H_pos n (by omega) x.1 hx.1.1.le hx.1.2.le
  have hD := Hslope_pos hn ⟨hx.1.1.le,hx.1.2.le⟩
  have hr : 0<x.1 := hx.1.1
  have ht : 0≤x.2 := hx.2
  have hden : 0<H n x.1+x.1*x.2*Hslope n x.1 := by positivity
  unfold thetaReferenceBid H Hslope at *
  apply ContinuousAt.div <;> first | fun_prop | exact hden.ne'

theorem continuousAt_thetaOwnScale {n : ℕ} (hn : 2≤n)
    (x : ℝ×ℝ) (hx : x.1∈Ioo (0:ℝ) 1 ∧ 0≤x.2) :
    ContinuousAt (fun y : ℝ×ℝ=>thetaOwnScale n y.1 y.2) x := by
  have hD := Hslope_pos hn ⟨hx.1.1.le,hx.1.2.le⟩
  have ht : 0≤x.2 := hx.2
  have hden : 0<(1+x.2)*Hslope n x.1 := by positivity
  unfold thetaOwnScale H Hslope at *
  apply ContinuousAt.div <;> first | fun_prop | exact hden.ne'

theorem continuousAt_thetaCurvature {n : ℕ} (hn : 2≤n) {w : ℝ} (hw : 0<w)
    (x : ℝ×ℝ) (hx : x.1∈Ioo (0:ℝ) 1 ∧ 0≤x.2) :
    ContinuousAt (fun y : ℝ×ℝ=>thetaCurvature n w y.1 y.2) x := by
  have hB := continuousAt_thetaReferenceBid hn w x hx
  have hk := continuousAt_thetaOwnScale hn x hx
  have hB0 := (thetaReferenceBid_pos hn hw hx.1 hx.2).ne'
  have hD : Continuous (Hslope n) := by unfold Hslope; fun_prop
  have hQ : Continuous (Hcurvature n) := by unfold Hcurvature; fun_prop
  dsimp only [thetaCurvature]
  fun_prop

theorem continuousAt_thetaCommonSensitivity {n : ℕ} (hn : 2≤n) {w : ℝ} (hw : 0<w)
    (x : ℝ×ℝ) (hx : x.1∈Ioo (0:ℝ) 1 ∧ 0≤x.2) :
    ContinuousAt (fun y : ℝ×ℝ=>thetaCommonSensitivity n w y.1 y.2) x := by
  have hB := continuousAt_thetaReferenceBid hn w x hx
  have hk := continuousAt_thetaOwnScale hn x hx
  have hB0 := (thetaReferenceBid_pos hn hw hx.1 hx.2).ne'
  have hB2 : (thetaReferenceBid n w x.1 x.2)^2≠0 := pow_ne_zero _ hB0
  dsimp only [thetaCommonSensitivity]
  fun_prop

theorem exists_uniform_reference_gap {n : ℕ} (hn : 2≤n) {w lo hi : ℝ}
    (hw : 0<w) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa : ℝ, 0<kappa ∧ ∀rho∈Icc lo hi, ∀theta∈Icc (0:ℝ) 1,
      kappa≤thetaReferenceBid n w rho theta ∧
      thetaReferenceBid n w rho theta≤w ∧ kappa≤thetaCurvature n w rho theta ∧
      kappa≤thetaCurvature n w rho theta-
        |thetaCurvature n w rho theta-thetaCommonSensitivity n w rho theta| := by
  let s := referenceParameterBox lo hi
  let f := fun x : ℝ×ℝ=>min (thetaReferenceBid n w x.1 x.2)
    (min (thetaCurvature n w x.1 x.2) (thetaCurvature n w x.1 x.2-
      |thetaCurvature n w x.1 x.2-thetaCommonSensitivity n w x.1 x.2|))
  have hs : IsCompact s := isCompact_Icc.prod isCompact_Icc
  have hsne : s.Nonempty := ⟨(lo,0),⟨⟨le_rfl,hlohi⟩,⟨le_rfl,zero_le_one⟩⟩⟩
  have hin (x : ℝ×ℝ) (hx : x∈s) : x.1∈Ioo (0:ℝ) 1 ∧ 0≤x.2 :=
    ⟨⟨hlo.trans_le hx.1.1,hx.1.2.trans_lt hhi⟩,hx.2.1⟩
  have hf : ContinuousOn f s := by
    intro x hx
    have hB := continuousAt_thetaReferenceBid hn w x (hin x hx)
    have ha := continuousAt_thetaCurvature hn hw x (hin x hx)
    have he := continuousAt_thetaCommonSensitivity hn hw x (hin x hx)
    have hcont : ContinuousAt f x := hB.min (ha.min (ha.sub (ha.sub he).abs))
    exact hcont.continuousWithinAt
  obtain ⟨x,hx,hmin⟩ := hs.exists_isMinOn hsne hf
  have hfx : 0<f x := by
    exact lt_min (thetaReferenceBid_pos hn hw (hin x hx).1 hx.2.1)
      (lt_min (thetaCurvature_pos hn hw (hin x hx).1 hx.2.1)
        (theta_reference_gap_pos hn hw (hin x hx).1 hx.2))
  refine ⟨f x,hfx,?_⟩
  intro rho hrho theta htheta
  have hy : (rho,theta)∈s := ⟨hrho,htheta⟩
  have hm := hmin hy
  have hr : rho∈Ioo (0:ℝ) 1 := ⟨hlo.trans_le hrho.1,hrho.2.trans_lt hhi⟩
  exact ⟨hm.trans (min_le_left _ _),thetaReferenceBid_le hn hw hr htheta.1,
    hm.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hm.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

theorem thetaReferenceBid_eq_referenceBid (n : ℕ) (R c w : ℝ) :
    thetaReferenceBid n w (density R c) (1/R)=referenceBid n R c w := by
  unfold thetaReferenceBid referenceBid
  congr 1
  ring

theorem thetaOwnScale_eq_referenceOwnScale {n : ℕ} (hn : 2≤n) {R rho : ℝ}
    (hR : 0<R) (hrho : rho∈Ioo (0:ℝ) 1) :
    thetaOwnScale n rho (1/R)=referenceOwnScale n R rho := by
  have hD := (Hslope_pos hn ⟨hrho.1.le,hrho.2.le⟩).ne'
  have hM : R+1≠0 := (show 0<R+1 by linarith).ne'
  have hT : 1+1/R≠0 := (show 0<1+1/R by positivity).ne'
  unfold thetaOwnScale referenceOwnScale
  field_simp

theorem thetaCurvature_eq_referenceCurvature {n : ℕ} (hn : 2≤n) {R c w : ℝ}
    (hR : 0<R) (hrho : density R c∈Ioo (0:ℝ) 1) :
    thetaCurvature n w (density R c) (1/R)=
      referenceCurvature n R (density R c) w (referenceBid n R c w) := by
  dsimp [thetaCurvature,referenceCurvature]
  rw [thetaReferenceBid_eq_referenceBid,thetaOwnScale_eq_referenceOwnScale hn hR hrho]
  congr 2
  ring

theorem thetaCommonSensitivity_eq_referenceCommonSensitivity {n : ℕ} (hn : 2≤n) {R c w : ℝ}
    (hR : 0<R) (hrho : density R c∈Ioo (0:ℝ) 1) :
    thetaCommonSensitivity n w (density R c) (1/R)=
      referenceCommonSensitivity n R (density R c) w (referenceBid n R c w) := by
  dsimp [thetaCommonSensitivity,referenceCommonSensitivity]
  rw [thetaReferenceBid_eq_referenceBid,thetaOwnScale_eq_referenceOwnScale hn hR hrho]

theorem exists_uniform_finite_reference_gap {n : ℕ} (hn : 2≤n) {w lo hi : ℝ}
    (hw : 0<w) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa : ℝ, 0<kappa ∧ ∀R c : ℕ, 1≤c → c≤R → density R c∈Icc lo hi →
      let rho := density R c
      let B := referenceBid n R c w
      kappa≤B ∧ B≤w ∧ kappa≤referenceCurvature n R rho w B ∧
      kappa≤referenceCurvature n R rho w B-
        |referenceCurvature n R rho w B-referenceCommonSensitivity n R rho w B| := by
  obtain ⟨kappa,hkappa,hall⟩ := exists_uniform_reference_gap hn hw hlo hlohi hhi
  refine ⟨kappa,hkappa,?_⟩
  intro R c hc hcR hrho
  have hR : 0<R := by omega
  have hRreal : (0:ℝ)<R := by exact_mod_cast hR
  have hRone : (1:ℝ)≤R := by exact_mod_cast hR
  have htheta : 1/(R:ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(one_div_pos.mpr hRreal).le,(div_le_one hRreal).mpr hRone⟩
  have hrho0 : density R c∈Ioo (0:ℝ) 1 := ⟨hlo.trans_le hrho.1,hrho.2.trans_lt hhi⟩
  simpa only [thetaReferenceBid_eq_referenceBid,thetaCurvature_eq_referenceCurvature hn hRreal hrho0,
    thetaCommonSensitivity_eq_referenceCommonSensitivity hn hRreal hrho0] using hall _ hrho _ htheta

end FCAppendix.Existence.NarrowPayOnce
