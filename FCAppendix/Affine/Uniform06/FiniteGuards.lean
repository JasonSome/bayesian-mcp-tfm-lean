import FCAppendix.Affine.Uniform06.FiniteMean
import FCAppendix.Affine.Uniform06.PrefixRoot

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FiniteGuards

open Set MeasureTheory
open FCAppendix.Affine.ClippedResidual
open scoped BigOperators

def clip01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clip01_bounds (x : ℝ) : clip01 x ∈ Icc (0:ℝ) 1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clip01_zero {x : ℝ} (hx : x ≤ 0) : clip01 x=0 := by
  unfold clip01
  rw [min_eq_right (hx.trans zero_le_one),max_eq_left hx]

theorem clip01_one {x : ℝ} (hx : 1 ≤ x) : clip01 x=1 := by
  simp [clip01,min_eq_left hx]

theorem clip01_self {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : clip01 x=x := by
  rw [clip01,min_eq_right hx.2,max_eq_right hx.1]

theorem clip01_monotone : Monotone clip01 := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_left _ hxy)

theorem clip01_increment {x y : ℝ} (hxy : x ≤ y) :
    clip01 y-clip01 x ≤ y-x := by
  by_cases hy : y ≤ 0
  · rw [clip01_zero hy,clip01_zero (hxy.trans hy)]
    linarith
  by_cases hx : x ≤ 0
  · rw [clip01_zero hx]
    have hy0 : 0 ≤ y := (lt_of_not_ge hy).le
    have hcy : clip01 y ≤ y := by
      exact max_le hy0 (min_le_right _ _)
    linarith
  by_cases hx1 : 1 ≤ x
  · rw [clip01_one hx1,clip01_one (hx1.trans hxy)]
    linarith
  have hxI : x ∈ Icc (0:ℝ) 1 := ⟨(lt_of_not_ge hx).le,(lt_of_not_ge hx1).le⟩
  rw [clip01_self hxI]
  have hcy : clip01 y ≤ y := max_le (lt_of_not_ge hy).le (min_le_right _ _)
  linarith

theorem clip01_lipschitz (x y : ℝ) : |clip01 x-clip01 y| ≤ |x-y| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr (clip01_monotone hxy)),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa only [neg_sub] using clip01_increment hxy
  · rw [abs_of_nonneg (sub_nonneg.mpr (clip01_monotone hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact clip01_increment hyx

theorem continuous_clip01 : Continuous clip01 :=
  continuous_const.max (continuous_const.min continuous_id)

def ramp (inner outer x : ℝ) : ℝ := clip01 ((x-outer)/(inner-outer))

theorem ramp_bounds (inner outer x : ℝ) : ramp inner outer x ∈ Icc (0:ℝ) 1 :=
  clip01_bounds _

theorem ramp_monotone {inner outer : ℝ} (h : outer < inner) :
    Monotone (ramp inner outer) := by
  intro x y hxy
  exact clip01_monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy _)
    (sub_pos.mpr h).le)

theorem ramp_lipschitz {inner outer : ℝ} (h : outer < inner) (x y : ℝ) :
    |ramp inner outer x-ramp inner outer y| ≤ |x-y| /(inner-outer) := by
  have hh := clip01_lipschitz ((x-outer)/(inner-outer)) ((y-outer)/(inner-outer))
  have he : (x-outer)/(inner-outer)-(y-outer)/(inner-outer)=(x-y)/(inner-outer) := by ring
  simpa only [ramp,he,abs_div,abs_of_pos (sub_pos.mpr h)] using hh

theorem ramp_zero {inner outer x : ℝ} (h : outer < inner) (hx : x ≤ outer) :
    ramp inner outer x=0 :=
  clip01_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr h).le)

theorem ramp_positive_slack {inner outer x : ℝ} (h : outer < inner)
    (hp : 0 < ramp inner outer x) : outer < x := by
  by_contra hx
  rw [ramp_zero h (le_of_not_gt hx)] at hp
  exact lt_irrefl _ hp

theorem normalized_ramp_lipschitz {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (x y : ℝ) :
    |ramp (2*ε*M) (ε*M) x-ramp (2*ε*M) (ε*M) y| ≤ |x-y| /(ε*M) := by
  have hh := ramp_lipschitz (show ε*M < 2*ε*M by nlinarith [mul_pos hε hM]) x y
  convert! hh using 1
  ring

theorem abs_product_sub_product_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Icc (0:ℝ) 1)
    (hg : ∀ i ∈ s, g i ∈ Icc (0:ℝ) 1) :
    |∏ i ∈ s, f i-∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i-g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hf' : ∀ i ∈ s, f i ∈ Icc (0:ℝ) 1 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' : ∀ i ∈ s, g i ∈ Icc (0:ℝ) 1 := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hga := hg a (Finset.mem_insert_self _ _)
    have hpg0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg (fun i hi => (hg' i hi).1)
    have hpg1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one (fun i hi => (hg' i hi).1)
      (fun i hi => (hg' i hi).2)
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha]
    have he : f a*(∏ i ∈ s, f i)-g a*(∏ i ∈ s, g i)=
        f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))+(f a-g a)*(∏ i ∈ s, g i) := by ring
    rw [he]
    calc
      _ ≤ |f a*((∏ i ∈ s, f i)-(∏ i ∈ s, g i))|+
          |(f a-g a)*(∏ i ∈ s, g i)| := abs_add_le _ _
      _ = f a*|(∏ i ∈ s, f i)-(∏ i ∈ s, g i)|+|f a-g a| *(∏ i ∈ s, g i) := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfa.1,abs_of_nonneg hpg0]
      _ ≤ |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)|+|f a-g a| :=
        add_le_add (by nlinarith only [hfa.2,mul_le_mul_of_nonneg_right hfa.2 (abs_nonneg ((∏ i ∈ s, f i)-(∏ i ∈ s, g i)))])
          (by nlinarith [abs_nonneg (f a-g a)])
      _ ≤ |f a-g a|+∑ i ∈ s, |f i-g i| := by linarith [ih hf' hg']

def eligibility (ξ L r b : ℝ) : ℝ := clip01 ((4*exposure ξ L b-r)/r)

theorem eligibility_bounds (ξ L r b : ℝ) : eligibility ξ L r b ∈ Icc (0:ℝ) 1 :=
  clip01_bounds _

theorem eligibility_lipschitz {ξ L r : ℝ} (hξ : 0 < ξ) (hL : 0 < L)
    (hr : 0 < r) (a b : ℝ) :
    |eligibility ξ L r a-eligibility ξ L r b| ≤ (4/(r*ξ*L))*|a-b| := by
  have hh := clip01_lipschitz ((4*exposure ξ L a-r)/r) ((4*exposure ξ L b-r)/r)
  have he : (4*exposure ξ L a-r)/r-(4*exposure ξ L b-r)/r=
      (4/r)*(exposure ξ L a-exposure ξ L b) := by ring
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (by norm_num) hr.le)] at hh
  have hlast := mul_le_mul_of_nonneg_left (FiniteMean.exposure_lipschitz hξ hL (a := a) (b := b))
    (show 0 ≤ 4/r by positivity)
  exact hh.trans (by convert! hlast using 1; ring)

theorem eligibility_zero {ξ L r b : ℝ} (hr : 0 < r)
    (hp : exposure ξ L b ≤ r/4) : eligibility ξ L r b=0 := by
  apply clip01_zero
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le

theorem psi_lipschitz {d z : ℝ} (hd : 0 < d) (a b : ℝ) :
    |PrefixRoot.psi d z a-PrefixRoot.psi d z b| ≤ |a-b| /d := by
  have ordered {a b : ℝ} (hab : a ≤ b) :
      PrefixRoot.psi d z b-PrefixRoot.psi d z a ≤ (b-a)/d := by
    let A := max 0 (a-z)
    let B := max 0 (b-z)
    have hA : 0 ≤ A := le_max_left _ _
    have hB : 0 ≤ B := le_max_left _ _
    have hAB : A ≤ B := max_le_max_left _ (sub_le_sub_right hab _)
    have hdiff : B-A ≤ b-a := by
      dsimp [A,B]
      by_cases haz : a ≤ z
      · rw [max_eq_left (sub_nonpos.mpr haz),sub_zero]
        apply max_le
        · linarith
        · linarith
      · rw [max_eq_right (by linarith : 0 ≤ a-z),max_eq_right (by linarith : 0 ≤ b-z)]
        ring_nf
        exact le_rfl
    have he : B/(d+B)-A/(d+A)=d*(B-A)/((d+A)*(d+B)) := by
      field_simp [show d+A ≠ 0 by positivity,show d+B ≠ 0 by positivity]
      ring
    change B/(d+B)-A/(d+A) ≤ _
    rw [he]
    have hden : d*d ≤ (d+A)*(d+B) := by nlinarith
    have hh : d*(B-A)/((d+A)*(d+B)) ≤ (B-A)/d := by
      apply (div_le_div_iff₀ (by positivity) hd).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hden)]
    exact hh.trans (div_le_div_of_nonneg_right hdiff hd.le)
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (PrefixRoot.psi_monotone_bid hd hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using ordered hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (PrefixRoot.psi_monotone_bid hd hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact ordered hba

def slacks (ξ L a r d z : ℝ) (other : Fin 5 → ℝ) (b : ℝ) : Fin 5 → ℝ :=
  ![other 0+exposure ξ (L-a) b,other 1-exposure ξ (L+a) b,
    other 2+eligibility ξ L r b,other 3+PrefixRoot.psi d z b,other 4]

def alpha (ε M : ℝ) (seeded : Prop) [Decidable seeded] (s : Fin 5 → ℝ) : ℝ :=
  if seeded then ∏ k : Fin 5, ramp (2*ε*M) (ε*M) (s k) else 0

theorem alpha_bounds (ε M : ℝ) (seeded : Prop) [Decidable seeded] (s : Fin 5 → ℝ) :
    alpha ε M seeded s ∈ Icc (0:ℝ) 1 := by
  unfold alpha
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun k _ => (ramp_bounds _ _ _).1),
      Finset.prod_le_one (fun k _ => (ramp_bounds _ _ _).1) (fun k _ => (ramp_bounds _ _ _).2)⟩
  · norm_num

theorem alpha_increment {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (seeded : Prop) [Decidable seeded] (s t : Fin 5 → ℝ) :
    |alpha ε M seeded s-alpha ε M seeded t| ≤
      (∑ k : Fin 5, |s k-t k|)/(ε*M) := by
  unfold alpha
  split_ifs
  · have hh := abs_product_sub_product_le Finset.univ
      (fun k : Fin 5 => ramp (2*ε*M) (ε*M) (s k))
      (fun k : Fin 5 => ramp (2*ε*M) (ε*M) (t k))
      (fun _ _ => ramp_bounds _ _ _) (fun _ _ => ramp_bounds _ _ _)
    exact hh.trans (by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro k _
      exact normalized_ramp_lipschitz hε hM _ _)
  · simp only [sub_self,abs_zero]
    exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (mul_pos hε hM).le

def ownGuardConstant (ξ L a r d : ℝ) : ℝ :=
  1/(ξ*(L-a))+1/(ξ*(L+a))+4/(r*ξ*L)+1/d

theorem actual_five_slack_increment {ξ L a r d ε M z : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < L-a) (hhi : 0 < L+a) (hL : 0 < L)
    (hr : 0 < r) (hd : 0 < d) (hε : 0 < ε) (hM : 0 < M)
    (other : Fin 5 → ℝ) (seeded : Prop) [Decidable seeded] (x y : ℝ) :
    |alpha ε M seeded (slacks ξ L a r d z other x)-
      alpha ε M seeded (slacks ξ L a r d z other y)| ≤
        ownGuardConstant ξ L a r d/(ε*M)*|x-y| := by
  have hh := alpha_increment hε hM seeded (slacks ξ L a r d z other x)
    (slacks ξ L a r d z other y)
  have hs : (∑ k : Fin 5, |slacks ξ L a r d z other x k-slacks ξ L a r d z other y k|) ≤
      ownGuardConstant ξ L a r d*|x-y| := by
    have h0 := FiniteMean.exposure_lipschitz hξ hlo (a := x) (b := y)
    have h1 := FiniteMean.exposure_lipschitz hξ hhi (a := x) (b := y)
    have h2 := eligibility_lipschitz hξ hL hr x y
    have h3 := psi_lipschitz (z := z) hd x y
    simp only [Fin.sum_univ_succ,slacks,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero] at ⊢
    have e0 : other 0+exposure ξ (L-a) x-(other 0+exposure ξ (L-a) y)=
        exposure ξ (L-a) x-exposure ξ (L-a) y := by ring
    have e1 : other 1-exposure ξ (L+a) x-(other 1-exposure ξ (L+a) y)=
        -(exposure ξ (L+a) x-exposure ξ (L+a) y) := by ring
    have e2 : other 2+eligibility ξ L r x-(other 2+eligibility ξ L r y)=
        eligibility ξ L r x-eligibility ξ L r y := by ring
    have e3 : other 3+PrefixRoot.psi d z x-(other 3+PrefixRoot.psi d z y)=
        PrefixRoot.psi d z x-PrefixRoot.psi d z y := by ring
    rw [e0,e1,e2,e3,sub_self,abs_zero,abs_neg]
    unfold ownGuardConstant
    simp only [div_eq_mul_inv] at h0 h1 h2 h3 ⊢
    nlinarith only [h0,h1,h2,h3]
  have hfinal := div_le_div_of_nonneg_right hs (mul_pos hε hM).le
  exact hh.trans (by convert! hfinal using 1; ring)

theorem seed_availability_rival_only {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (b : ι → ℝ) (i : ι) {cut x : ℝ} (hx : cut < x) :
    (∃ j ∈ S, Function.update b i x j ≤ cut) ↔ ∃ j ∈ S.erase i, b j ≤ cut := by
  constructor
  · rintro ⟨j,hj,hval⟩
    have hji : j ≠ i := by
      intro he
      subst j
      simp only [Function.update_self] at hval
      exact (not_le_of_gt hx) hval
    exact ⟨j,Finset.mem_erase.mpr ⟨hji,hj⟩,by simpa [Function.update_of_ne hji] using hval⟩
  · rintro ⟨j,hj,hval⟩
    obtain ⟨hji,hjS⟩ := Finset.mem_erase.mp hj
    exact ⟨j,hjS,by simpa [Function.update_of_ne hji] using hval⟩

theorem sampled_h_gap {ξ U b B ε : ℝ} (hξ : 0 < ξ) (_hξ1 : ξ < 1)
    (hU : 0 < U) (hb : 0 < b) (hBU : B ≤ U) (hbU : b ≤ U)
    (hε : 0 < ε) (hreceipt : (1-ξ/2)*U+ε ≤ b) :
    ε/(ξ*U) ≤ 1/2-exposure ξ b B := by
  have hm := LowChernoff.exposure_monotone_bid hξ hb hBU
  have hκU : (1-ξ)*U ≤ b := by nlinarith [mul_pos hξ hU]
  have hform : exposure ξ b U=(1-b/U)/ξ := by
    by_cases he : b=U
    · subst b
      rw [exposure_zero le_rfl,div_self hU.ne']
      ring
    · exact exposure_of_between hξ hb (lt_of_le_of_ne hbU he) hκU
  rw [hform] at hm
  have hg : ε/(ξ*U) ≤ 1/2-(1-b/U)/ξ := by
    apply (div_le_iff₀ (mul_pos hξ hU)).mpr
    have he : (1/2-(1-b/U)/ξ)*(ξ*U)=b-(1-ξ/2)*U := by
      field_simp [hξ.ne',hU.ne']
      ring
    rw [he]
    linarith
  linarith

end FCAppendix.Affine.Uniform06.FiniteGuards
