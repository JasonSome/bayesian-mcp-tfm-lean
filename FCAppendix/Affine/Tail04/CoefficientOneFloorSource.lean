import FCAppendix.Affine.Tail04.CoefficientOneEarly

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne.SourceFloor
open Set OriginalValues

variable (P : ValueParameters)

def xi (eta : ℝ) : ℝ := (1-eta)/2
def mixed : ℝ := 5*P.theta^2/partialMass
def height (eta : ℝ) : ℝ := 1-xi eta*(3/5)
def multiplier (eta : ℝ) : ℝ :=
  2*(1-(3/5:ℝ))/(1+(1-mixed P)*xi eta/(2*mixed P*(height eta)^2))

lemma mixed_pos : 0< mixed P := by
  unfold mixed
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos P.theta_pos))
    (by norm_num [partialMass])

lemma mixed_le_half : mixed P≤1/2 := by
  have ht:=P.theta_small
  have ht0:=P.theta_pos
  unfold mixed partialMass
  nlinarith

theorem multiplier_bound (eta : ℝ) (hη0 : 0< eta) (hη1 : eta<1) :
    0< multiplier P eta ∧ multiplier P eta≤(16/(5*xi eta))*mixed P := by
  have hx : 0< xi eta := by unfold xi;linarith
  have hx1 : xi eta<1/2 := by unfold xi;linarith
  have he:=mixed_pos P
  have he1:=mixed_le_half P
  have hH : 0< height eta := by unfold height;linarith
  have hH1 : height eta≤1 := by unfold height;linarith
  have hH2 : (height eta)^2≤1 := by nlinarith
  let den:=1+(1-mixed P)*xi eta/(2*mixed P*(height eta)^2)
  have h1e : 0 < 1-mixed P := by linarith
  have hd : 0< den := by dsimp only [den];positivity
  have hl : 0< multiplier P eta := by unfold multiplier;exact div_pos (by norm_num) hd
  have hp : multiplier P eta*den=4/5 := by
    unfold multiplier
    change (2*(1-(3/5:ℝ))/den)*den=4/5
    rw [div_mul_cancel₀ _ hd.ne']
    norm_num
  have hden : den*(2*mixed P*(height eta)^2)=
      2*mixed P*(height eta)^2+(1-mixed P)*xi eta := by
    dsimp only [den]
    field_simp [he.ne',hH.ne']
  have hid : multiplier P eta*(2*mixed P*(height eta)^2+(1-mixed P)*xi eta)=
      (8/5)*mixed P*(height eta)^2 := by
    rw [←hden,←mul_assoc,hp]
    ring
  have hsmall:=mul_le_mul_of_nonneg_left hH2
    (by positivity : 0≤(8/5:ℝ)*mixed P)
  have hplus : 0≤ multiplier P eta*(2*mixed P*(height eta)^2) := by positivity
  have hmix := mul_le_mul_of_nonneg_left (by linarith : (1/2:ℝ)≤1-mixed P)
    (by positivity : 0≤ multiplier P eta*xi eta)
  have hproduct : multiplier P eta*xi eta≤(16/5)*mixed P := by nlinarith
  have hdiv : multiplier P eta≤((16/5)*mixed P)/xi eta :=
    (le_div_iff₀ hx).mpr hproduct
  refine ⟨hl,?_⟩
  convert! hdiv using 1
  field_simp

theorem upper_gap_of_source (eta xi2 R lambdaLo tau : ℝ)
    (hη0 : 0< eta) (hη1 : eta<1) (hxi2 : 0< xi2)
    (hR : 0< R) (htau : 0< tau)
    (hfloor : R<2*multiplier P eta)
    (hrelative : ((1-xi eta)+tau)*R≤ lambdaLo)
    (hcenter : P.vA=11*xi2/(10*P.theta))
    (htheta : P.theta≤11*xi2*tau^2/(128*xi eta)) :
    R<(P.vA-P.w)*mixed P*(1-(1-lambdaLo/R)/xi eta)^2 := by
  have hx : 0< xi eta := by unfold xi;linarith
  have he:=mixed_pos P
  have ht:=P.theta_pos
  have hwidth : P.w≤ P.vA/2 := by linarith [P.partial_active_gap]
  have hgap : tau/xi eta≤1-(1-lambdaLo/R)/xi eta := by
    have hrel : (1-xi eta)+tau≤ lambdaLo/R := (le_div_iff₀ hR).mpr hrelative
    apply (div_le_iff₀ hx).mpr
    have heq : (1-(1-lambdaLo/R)/xi eta)*xi eta=xi eta-1+lambdaLo/R := by
      field_simp [hx.ne']
      ring
    rw [heq]
    linarith
  have hgap0 : 0≤1-(1-lambdaLo/R)/xi eta :=
    (by positivity : 0≤ tau/xi eta).trans hgap
  have hsq : (tau/xi eta)^2≤(1-(1-lambdaLo/R)/xi eta)^2 :=
    (sq_le_sq₀ (div_pos htau hx).le hgap0).mpr hgap
  have ht0 : 0< P.vA-P.w := by linarith [P.d0_pos,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  have hsmall : P.theta*(128*xi eta)≤11*xi2*tau^2 :=
    (le_div_iff₀ (by positivity : 0<128*xi eta)).mp htheta
  have hvalue : 32*xi eta/(5*tau^2)≤ P.vA-P.w := by
    have hh : 32*xi eta/(5*tau^2)≤11*xi2/(20*P.theta) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have heq : 11*xi2/(20*P.theta)=P.vA/2 := by
      rw [hcenter]
      field_simp [ht.ne']
      ring
    rw [heq] at hh
    linarith
  have hbase : 32/(5*xi eta)≤(P.vA-P.w)*(tau/xi eta)^2 := by
    have hh:=mul_le_mul_of_nonneg_right hvalue (sq_nonneg (tau/xi eta))
    have heq : (32*xi eta/(5*tau^2))*(tau/xi eta)^2=32/(5*xi eta) := by
      field_simp [hx.ne',htau.ne']
    rwa [heq] at hh
  have hfail : 32/(5*xi eta)≤(P.vA-P.w)*(1-(1-lambdaLo/R)/xi eta)^2 :=
    hbase.trans (mul_le_mul_of_nonneg_left hsq ht0.le)
  have hmult:=(multiplier_bound P eta hη0 hη1).2
  have hh:=mul_le_mul_of_nonneg_left hfail he.le
  calc
    R < 2*multiplier P eta := hfloor
    _ ≤ 2*((16/(5*xi eta))*mixed P) := mul_le_mul_of_nonneg_left hmult (by norm_num)
    _ = mixed P*(32/(5*xi eta)) := by ring
    _ ≤ mixed P*((P.vA-P.w)*(1-(1-lambdaLo/R)/xi eta)^2) := hh
    _ = (P.vA-P.w)*mixed P*(1-(1-lambdaLo/R)/xi eta)^2 := by ring

def scalarInput (eta xi2 U R lambdaLo tau : ℝ)
    (hη0 : 0< eta) (hη1 : eta<1) (hxi2 : 0< xi2)
    (hU : 0< U) (hUR : U< R) (hRt : R< P.vA-P.w)
    (hlam : 0< lambdaLo) (hlamR : lambdaLo< R)
    (htau : 0< tau) (hfloor : R<2*multiplier P eta)
    (hrelative : ((1-xi eta)+tau)*R≤ lambdaLo)
    (hcenter : P.vA=11*xi2/(10*P.theta))
    (htheta : P.theta≤11*xi2*tau^2/(128*xi eta)) : ScalarInput P where
  eta:=eta
  U:=U
  R:=R
  lambdaLo:=lambdaLo
  eta_pos:=hη0
  eta_lt_one:=hη1
  U_pos:=hU
  cap_below_floor:=hUR
  floor_below_upper:=hRt
  multiplier_pos:=hlam
  multiplier_below_floor:=hlamR
  canonical_gap:=by
    have hp : 0< tau*R := mul_pos htau (hU.trans hUR)
    change (1-xi eta)*R< lambdaLo
    nlinarith
  upper_gap:=by
    exact upper_gap_of_source P eta xi2 R lambdaLo tau hη0 hη1 hxi2
      (hU.trans hUR) htau hfloor hrelative hcenter htheta

end FCAppendix.Affine.Tail04.CoefficientOne.SourceFloor
