import FCAppendix.Affine.Hybrid.Tail03.Analytic

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set

def sourceCenterMoment (p : Center) (r : Fin 2) : ℝ := activeMass p*e0 p r
def sourceMomentDeficit (p : Center) (r : Fin 2) : ℝ := activeMass p*deficit p r

def sourceMomentUpdate (p : Center) (M W : Fin 2 → ℝ) (r : Fin 2) : ℝ :=
  ((1-xi p/2)*M r-(xi p/2)*sourceMomentDeficit p r)/W r

lemma sourceCenterMoment_pos (p : Center) (r : Fin 2) : 0 < sourceCenterMoment p r :=
  mul_pos (activeMass_pos p) (e0_pos p r)

lemma lambda0_unit (p : Center) (r : Fin 2) : lambda0 p r ∈ Icc (0:ℝ) 1 := by
  have hx := xi_pos p
  have hx1 := xi_lt_half p
  fin_cases r <;> norm_num [lambda0,q0] <;> constructor <;> linarith

lemma sourceMoment_center_identity (p : Center) (r : Fin 2) :
    (1-xi p/2)*sourceCenterMoment p r-(xi p/2)*sourceMomentDeficit p r =
      lambda0 p r*sourceCenterMoment p r := by
  have he := (e0_pos p r).ne'
  have hd : deficit p r=(2*q0 r-1)*e0 p r :=
    (div_eq_iff he).mp (deficit_div_e0 p r)
  unfold sourceCenterMoment sourceMomentDeficit lambda0
  rw [hd]
  ring

theorem sourceMomentUpdate_error (p : Center) (M W : Fin 2 → ℝ)
    {rho : ℝ} (hr0 : 0 ≤ rho) (hrhalf : rho ≤ 1/2)
    (hM : ∀ r,|M r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho)
    (hW : ∀ r,|W r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho)
    (r : Fin 2) :
    0 < W r ∧ |sourceMomentUpdate p M W r-lambda0 p r|≤4*rho := by
  let c := sourceCenterMoment p r
  let a := 1-xi p/2
  let l := lambda0 p r
  have hc : 0 < c := sourceCenterMoment_pos p r
  have ha0 : 0 ≤ a := by dsimp [a];linarith [xi_lt_half p]
  have ha1 : a ≤ 1 := by dsimp [a];linarith [xi_pos p]
  have hl := lambda0_unit p r
  have hl0 : 0≤ l := hl.1
  have hl1 : l≤1 := hl.2
  have hcR : 0 ≤ c*rho := mul_nonneg hc.le hr0
  have hMr := hM r
  have hWr := hW r
  change |M r-c|≤ c*rho at hMr
  change |W r-c|≤ c*rho at hWr
  have hWlower : c/2 ≤ W r := by
    have hw := (abs_le.mp hWr).1
    have hm := mul_le_mul_of_nonneg_left hrhalf hc.le
    linarith
  have hWp : 0 < W r := (half_pos hc).trans_le hWlower
  have hcenter := sourceMoment_center_identity p r
  have hid : (1-xi p/2)*M r-(xi p/2)*sourceMomentDeficit p r-l*W r =
      a*(M r-c)-l*(W r-c) := by
    dsimp [a,c,l]
    nlinarith only [hcenter]
  have hA : a*|M r-c|≤ c*rho :=
    (mul_le_mul_of_nonneg_left hMr ha0).trans
      (mul_le_of_le_one_left hcR ha1)
  have hL : l*|W r-c|≤ c*rho :=
    (mul_le_mul_of_nonneg_left hWr hl0).trans
      (mul_le_of_le_one_left hcR hl1)
  have hbound : |(1-xi p/2)*M r-(xi p/2)*sourceMomentDeficit p r-l*W r|≤2*c*rho := by
    rw [hid]
    have hh := abs_sub_le (a*(M r-c)) 0 (l*(W r-c))
    simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg ha0,abs_of_nonneg hl0] at hh
    linarith
  refine ⟨hWp,?_⟩
  unfold sourceMomentUpdate
  change |((1-xi p/2)*M r-(xi p/2)*sourceMomentDeficit p r)/W r-l|≤4*rho
  rw [div_sub' hWp.ne',abs_div,abs_of_pos hWp,mul_comm (W r) l]
  apply (div_le_iff₀ hWp).mpr
  have hh := mul_le_mul_of_nonneg_left hWlower (show 0≤4*rho by positivity)
  nlinarith

theorem exists_sourceMoment_rectangle_tolerance (p : Center) (lo hi : Fin 2 → ℝ)
    (hbox : ∀ r,lo r< lambda0 p r ∧ lambda0 p r< hi r) :
    ∃ rho : ℝ,0< rho ∧ rho<1/2 ∧
      ∀ M W : Fin 2 → ℝ,
        (∀ r,|M r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho) →
        (∀ r,|W r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho) →
        ∀ r,lo r< sourceMomentUpdate p M W r ∧ sourceMomentUpdate p M W r< hi r := by
  let d := min (min (lambda0 p 0-lo 0) (hi 0-lambda0 p 0))
    (min (lambda0 p 1-lo 1) (hi 1-lambda0 p 1))
  have hd : 0< d := lt_min
    (lt_min (sub_pos.mpr (hbox 0).1) (sub_pos.mpr (hbox 0).2))
    (lt_min (sub_pos.mpr (hbox 1).1) (sub_pos.mpr (hbox 1).2))
  let rho := min (d/8) (1/4)
  have hr : 0< rho := lt_min (by positivity) (by norm_num)
  have hrhalf : rho<1/2 := (min_le_right _ _).trans_lt (by norm_num)
  have hrd : 4*rho< d := by
    have hh : rho≤ d/8 := min_le_left _ _
    linarith
  have hdlo (r : Fin 2) : d≤ lambda0 p r-lo r := by
    fin_cases r
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
  have hdhi (r : Fin 2) : d≤ hi r-lambda0 p r := by
    fin_cases r
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rho,hr,hrhalf,?_⟩
  intro M W hM hW r
  have hh := (sourceMomentUpdate_error p M W hr.le hrhalf.le hM hW r).2
  have hlim := abs_le.mp hh
  exact ⟨by linarith [hdlo r],by linarith [hdhi r]⟩

structure SourceRelativeMomentParameters (p : Center) (lo hi : Fin 2 → ℝ) where
  rho : ℝ
  u : ℝ
  zeta : ℝ
  rho_pos : 0 < rho
  rho_half : rho < 1/2
  u_pos : 0 < u
  u_lt_width : u < width p
  zeta_pos : 0 < zeta
  zeta_small : zeta < 1/100
  moment_error : 2*zeta+u*(1+2/width p) < rho
  coefficient_error : 2*zeta+u*(1+2/width p) < xi p/1000
  invariant : ∀ M W : Fin 2 → ℝ,
    (∀ r,|M r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho) →
    (∀ r,|W r-sourceCenterMoment p r|≤ sourceCenterMoment p r*rho) →
    ∀ r,lo r< sourceMomentUpdate p M W r ∧ sourceMomentUpdate p M W r< hi r

theorem exists_sourceRelativeMomentParameters (p : Center) (lo hi : Fin 2 → ℝ)
    (hbox : ∀ r,lo r< lambda0 p r ∧ lambda0 p r< hi r) :
    Nonempty (SourceRelativeMomentParameters p lo hi) := by
  obtain ⟨rho,hr,hrhalf,hinv⟩ := exists_sourceMoment_rectangle_tolerance p lo hi hbox
  let eps := min rho (xi p/1000)
  let C := 1+2/width p
  let u := min (width p/2) (eps/(8*C))
  let zeta := min (1/200) (eps/8)
  have heps : 0< eps := lt_min hr (div_pos (xi_pos p) (by norm_num))
  have hwidth := width_pos p
  have hC : 0< C := by dsimp [C];positivity
  have hu : 0< u := lt_min (by positivity) (by positivity)
  have hz : 0< zeta := lt_min (by norm_num) (by positivity)
  have hCu : u*C≤ eps/8 := by
    have hh : u≤ eps/(8*C) := min_le_right _ _
    have hh' := (le_div_iff₀ (show 0<8*C by positivity)).mp hh
    nlinarith
  have hze : zeta≤ eps/8 := min_le_right _ _
  have herror : 2*zeta+u*C< eps := by nlinarith
  refine ⟨{
    rho := rho
    u := u
    zeta := zeta
    rho_pos := hr
    rho_half := hrhalf
    u_pos := hu
    u_lt_width := ?_
    zeta_pos := hz
    zeta_small := ?_
    moment_error := ?_
    coefficient_error := ?_
    invariant := hinv }⟩
  · have hh : u≤ width p/2 := min_le_left _ _
    linarith
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · exact herror.trans_le (min_le_left _ _)
  · exact herror.trans_le (min_le_right _ _)

end FCAppendix.Affine.Hybrid.Tail03
