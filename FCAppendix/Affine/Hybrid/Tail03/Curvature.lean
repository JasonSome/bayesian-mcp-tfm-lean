import FCAppendix.Affine.Hybrid.Tail03.Analytic

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology
open scoped BigOperators

namespace Raw

def cap (x : ℝ) := 1+x/50
def gap (x : ℝ) := x/50
def mass (t : ℝ) := 67/100-t^2
def coeff (t : ℝ) : Fin 2 → ℝ :=
  ![(1-t)*10*t/(9*mass t),5*(8/25+t^2)/(4*mass t)]
def fail (x l b : ℝ) := (cap x-b)*(l/b-(1-x))
def fail1 (x l b : ℝ) := 1-x-l*cap x/b^2
def fail2 (x l b : ℝ) := 2*l*cap x/b^3
def dup (x l b : ℝ) := (cap x-b)*(1-l/b)
def dup1 (x l b : ℝ) := -1+l*cap x/b^2
def dup2 (x l b : ℝ) := -2*l*cap x/b^3

def F (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*(fail x (lam r) b)^2
def F1 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*
    (2*fail x (lam r) b*fail1 x (lam r) b)
def F2 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*
    (2*(fail1 x (lam r) b)^2+2*fail x (lam r) b*fail2 x (lam r) b)
def D (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*(dup x (lam r) b)^2
def D1 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*
    (2*dup x (lam r) b*dup1 x (lam r) b)
def D2 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  ∑ r, coeff t r/(gap x^2*x^2)*
    (2*(dup1 x (lam r) b)^2+2*dup x (lam r) b*dup2 x (lam r) b)
def H (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  b*(-F x t lam b+(1-2*x)*D x t lam b)
def H1 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  -F x t lam b+(1-2*x)*D x t lam b+
    b*(-F1 x t lam b+(1-2*x)*D1 x t lam b)
def H2 (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  2*(-F1 x t lam b+(1-2*x)*D1 x t lam b)+
    b*(-F2 x t lam b+(1-2*x)*D2 x t lam b)
def determinant (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) :=
  F2 x t lam b+t*(H1 x t lam b*F2 x t lam b-H2 x t lam b*F1 x t lam b)

lemma fail_hasDerivAt (x l b : ℝ) (hb : b≠0) :
    HasDerivAt (fail x l) (fail1 x l b) b := by
  have hi := (hasDerivAt_const b l).div (hasDerivAt_id b) hb
  convert! ((hasDerivAt_const b (cap x)).sub (hasDerivAt_id b)).mul
    (hi.sub_const (1-x)) using 1
  dsimp [fail,fail1]
  field_simp [hb]
  ring

lemma fail1_hasDerivAt (x l b : ℝ) (hb : b≠0) :
    HasDerivAt (fail1 x l) (fail2 x l b) b := by
  have hp := (hasDerivAt_const b (l*cap x)).div ((hasDerivAt_id b).pow 2) (pow_ne_zero 2 hb)
  convert! (hasDerivAt_const b (1-x)).sub hp using 1
  dsimp [fail1,fail2]
  field_simp [hb]
  ring

lemma dup_hasDerivAt (x l b : ℝ) (hb : b≠0) :
    HasDerivAt (dup x l) (dup1 x l b) b := by
  have hi := (hasDerivAt_const b l).div (hasDerivAt_id b) hb
  convert! ((hasDerivAt_const b (cap x)).sub (hasDerivAt_id b)).mul
    ((hasDerivAt_const b 1).sub hi) using 1
  dsimp [dup,dup1]
  field_simp [hb]
  ring

lemma dup1_hasDerivAt (x l b : ℝ) (hb : b≠0) :
    HasDerivAt (dup1 x l) (dup2 x l b) b := by
  have hp := (hasDerivAt_const b (l*cap x)).div ((hasDerivAt_id b).pow 2) (pow_ne_zero 2 hb)
  convert! (hasDerivAt_const b (-1)).add hp using 1
  dsimp [dup1,dup2]
  field_simp [hb]
  ring

lemma F_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (F x t lam) (F1 x t lam b) b := by
  unfold F F1
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    ((fail_hasDerivAt x (lam r) b hb).pow 2).const_mul
      (coeff t r/(gap x^2*x^2))) using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma F1_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (F1 x t lam) (F2 x t lam b) b := by
  unfold F1 F2
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    (((fail_hasDerivAt x (lam r) b hb).const_mul 2).mul
      (fail1_hasDerivAt x (lam r) b hb)).const_mul
      (coeff t r/(gap x^2*x^2))) using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma D_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (D x t lam) (D1 x t lam b) b := by
  unfold D D1
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    ((dup_hasDerivAt x (lam r) b hb).pow 2).const_mul
      (coeff t r/(gap x^2*x^2))) using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma D1_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (D1 x t lam) (D2 x t lam b) b := by
  unfold D1 D2
  convert! HasDerivAt.fun_sum (fun r (_ : r∈Finset.univ) =>
    (((dup_hasDerivAt x (lam r) b hb).const_mul 2).mul
      (dup1_hasDerivAt x (lam r) b hb)).const_mul
      (coeff t r/(gap x^2*x^2))) using 1
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma H_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (H x t lam) (H1 x t lam b) b := by
  convert! (hasDerivAt_id b).mul ((F_hasDerivAt x t lam b hb).neg.add
    ((D_hasDerivAt x t lam b hb).const_mul (1-2*x))) using 1
  dsimp [H,H1]
  ring

lemma H1_hasDerivAt (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ) (hb : b≠0) :
    HasDerivAt (H1 x t lam) (H2 x t lam b) b := by
  have hd0 := (F_hasDerivAt x t lam b hb).neg.add
    ((D_hasDerivAt x t lam b hb).const_mul (1-2*x))
  have hd1 := (F1_hasDerivAt x t lam b hb).neg.add
    ((D1_hasDerivAt x t lam b hb).const_mul (1-2*x))
  convert! hd0.add ((hasDerivAt_id b).mul hd1) using 1
  dsimp [H1,H2]
  ring

lemma failure_square_curvature {x l b : ℝ} (hx : 0< x) (hxhalf : x<1/2)
    (hl : (1-x)*cap x< l) (hb : b∈Icc (1:ℝ) (cap x)) :
    0≤ fail x l b ∧ fail1 x l b<0 ∧ 0< fail2 x l b ∧
      0<2*(fail1 x l b)^2+2*fail x l b*fail2 x l b := by
  have hcap : 0< cap x := by unfold cap; linarith
  have hb0 : 0< b := by linarith [hb.1]
  have hk : 0<1-x := by linarith
  have hl0 : 0< l := (mul_pos hk hcap).trans hl
  have hd : 0< l/b-(1-x) := by
    have : (1-x)*b< l := (mul_le_mul_of_nonneg_left hb.2 hk.le).trans_lt hl
    exact sub_pos.mpr ((lt_div_iff₀ hb0).2 this)
  have hf : 0≤ fail x l b := mul_nonneg (sub_nonneg.mpr hb.2) hd.le
  have hs : b^2≤(cap x)^2 := (sq_le_sq₀ hb0.le hcap.le).2 hb.2
  have hder : fail1 x l b<0 := by
    unfold fail1
    have : (1-x)*b^2< l*cap x := by
      nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hs),
        mul_pos hcap (sub_pos.mpr hl)]
    have hh := (lt_div_iff₀ (sq_pos_of_pos hb0)).2 this
    linarith
  have hf2 : 0< fail2 x l b := by unfold fail2; positivity
  refine ⟨hf,hder,hf2,?_⟩
  have hsq := sq_pos_of_ne_zero hder.ne
  have hprod := mul_nonneg hf hf2.le
  nlinarith

lemma zero_F2_pos {x : ℝ} (hx : 0< x) (hxhalf : x<1/2)
    (lam : Fin 2 → ℝ) (hl : (1-x)*cap x< lam 1)
    {b : ℝ} (hb : b∈Icc (1:ℝ) (cap x)) : 0< F2 x 0 lam b := by
  have hc := (failure_square_curvature hx hxhalf hl hb).2.2.2
  have hd : 0< gap x^2*x^2 := by unfold gap; positivity
  norm_num [F2,Fin.sum_univ_two,coeff,mass]
  exact mul_pos (div_pos (by norm_num) hd) hc

lemma central_bulk_zero_formula {x : ℝ} (hx : x≠0) :
    -(11*x/10)*F1 x 0 (fun r => 1-x*q0 r) 1=
      (11/10:ℝ)*(40/67)*(1+(1-9*x/10)/5) := by
  norm_num [F1,coeff,mass,fail,fail1,cap,gap,q0,Fin.sum_univ_two]
  field_simp [hx]
  ring

lemma central_bulk_zero_bound {x : ℝ} (hx : 0< x) :
    -(11*x/10)*F1 x 0 (fun r => 1-x*q0 r) 1 < 264/335 := by
  rw [central_bulk_zero_formula hx.ne']
  nlinarith

lemma rational_continuity (x t : ℝ) (lam : Fin 2 → ℝ) (b : ℝ)
    (hx : x≠0) (ha : mass t≠0) (hb : b≠0) :
    ContinuousAt (fun z : (ℝ × (Fin 2 → ℝ)) × ℝ => F1 x z.1.1 z.1.2 z.2) ((t,lam),b) ∧
    ContinuousAt (fun z : (ℝ × (Fin 2 → ℝ)) × ℝ => F2 x z.1.1 z.1.2 z.2) ((t,lam),b) ∧
    ContinuousAt (fun z : (ℝ × (Fin 2 → ℝ)) × ℝ => H1 x z.1.1 z.1.2 z.2) ((t,lam),b) ∧
    ContinuousAt (fun z : (ℝ × (Fin 2 → ℝ)) × ℝ => H2 x z.1.1 z.1.2 z.2) ((t,lam),b) := by
  have hg : gap x≠0 := by unfold gap; exact div_ne_zero hx (by norm_num)
  simp only [F1,F2,H1,H2,F,D,D1,D2,coeff,fail,fail1,fail2,dup,dup1,dup2,mass,
    Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] at *
  constructor
  · fun_prop (disch := first | assumption | positivity)
  constructor
  · fun_prop (disch := first | assumption | positivity)
  constructor <;> fun_prop (disch := first | assumption | positivity)

end Raw

def served1 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  -p.theta*Raw.F1 (xi p) p.theta lam b
def served2 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  -p.theta*Raw.F2 (xi p) p.theta lam b
def payment1 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  1+p.theta*Raw.H1 (xi p) p.theta lam b
def payment2 (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) : ℝ :=
  p.theta*Raw.H2 (xi p) p.theta lam b

lemma normalized_coeff_identity (p : Center) (r : Fin 2) :
    regimeWeight p r*e0 p r=p.theta*Raw.coeff p.theta r := by
  fin_cases r <;>
    simp [regimeWeight,e0,Raw.coeff,Raw.mass,activeMass,partialMass,delta]; ring

lemma normalized_served (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    served p lam b=1-p.theta*Raw.F (xi p) p.theta lam b := by
  simp only [served,Raw.F,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_assoc, failure_factor p lam r hb]
  calc
    regimeWeight p r*(e0 p r/(width p^2*xi p^2)*
        ((B p-b)*(lam r/b-kappa p))^2)
        = (regimeWeight p r*e0 p r)/(width p^2*xi p^2)*
            ((B p-b)*(lam r/b-kappa p))^2 := by ring
    _ = (p.theta*Raw.coeff p.theta r)/(width p^2*xi p^2)*
          ((B p-b)*(lam r/b-kappa p))^2 := by rw [normalized_coeff_identity]
    _ = p.theta*(Raw.coeff p.theta r/(Raw.gap (xi p)^2*xi p^2)*
          (Raw.fail (xi p) (lam r) b)^2) := by
      simp only [Raw.fail,Raw.cap,Raw.gap,B,kappa,width_eq]
      ring

lemma normalized_duplicates (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    duplicates p lam b=p.theta*Raw.D (xi p) p.theta lam b := by
  simp only [duplicates,Raw.D,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    regimeWeight p r*mixedProb p r b*(exposure p lam r b)^2
        = (regimeWeight p r*e0 p r)/(width p^2*xi p^2)*
            ((B p-b)*(1-lam r/b))^2 := by
      unfold mixedProb exposure
      field_simp [hb,(xi_pos p).ne',(width_pos p).ne']
    _ = (p.theta*Raw.coeff p.theta r)/(width p^2*xi p^2)*
          ((B p-b)*(1-lam r/b))^2 := by rw [normalized_coeff_identity]
    _ = p.theta*(Raw.coeff p.theta r/(Raw.gap (xi p)^2*xi p^2)*
          (Raw.dup (xi p) (lam r) b)^2) := by
      simp only [Raw.dup,Raw.cap,Raw.gap,B,width_eq]
      ring

lemma normalized_payment (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    payment p lam b=b+p.theta*Raw.H (xi p) p.theta lam b := by
  unfold payment
  rw [normalized_served p lam hb,normalized_duplicates p lam hb]
  have he : p.eta2=1-2*xi p := by unfold xi; ring
  rw [he]
  unfold Raw.H
  ring

lemma served_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    HasDerivAt (served p lam) (served1 p lam b) b := by
  have h := (hasDerivAt_const b 1).sub
    ((Raw.F_hasDerivAt (xi p) p.theta lam b hb).const_mul p.theta)
  have hd : HasDerivAt (fun z => 1-p.theta*Raw.F (xi p) p.theta lam z)
      (served1 p lam b) b := by
    convert! h using 1
    simp only [served1, zero_sub, neg_mul]
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hb] with z hz
  exact normalized_served p lam hz

lemma served1_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    HasDerivAt (served1 p lam) (served2 p lam b) b := by
  exact (Raw.F1_hasDerivAt (xi p) p.theta lam b hb).const_mul (-p.theta)

lemma payment_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    HasDerivAt (payment p lam) (payment1 p lam b) b := by
  have h := (hasDerivAt_id b).add
    ((Raw.H_hasDerivAt (xi p) p.theta lam b hb).const_mul p.theta)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hb] with z hz
  exact normalized_payment p lam hz

lemma payment1_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) {b : ℝ} (hb : b≠0) :
    HasDerivAt (payment1 p lam) (payment2 p lam b) b := by
  convert! (hasDerivAt_const b 1).add
    ((Raw.H1_hasDerivAt (xi p) p.theta lam b hb).const_mul p.theta) using 1
  simp only [payment2, zero_add]

lemma utility_hasDerivAt (p : Center) (lam : Fin 2 → ℝ) (v : ℝ) {b : ℝ} (hb : b≠0) :
    HasDerivAt (utility p lam v) (v*served1 p lam b-payment1 p lam b) b :=
  ((served_hasDerivAt p lam hb).const_mul v).sub (payment_hasDerivAt p lam hb)

lemma determinant_identity (p : Center) (lam : Fin 2 → ℝ) (b : ℝ) :
    payment2 p lam b*served1 p lam b-payment1 p lam b*served2 p lam b=
      p.theta*Raw.determinant (xi p) p.theta lam b := by
  unfold payment2 served1 payment1 served2 Raw.determinant
  ring

lemma derivatives_at_B (p : Center) (lam : Fin 2 → ℝ) :
    served1 p lam (B p)=0 ∧ payment1 p lam (B p)=1 := by
  simp [served1,payment1,Raw.F1,Raw.H1,Raw.F,Raw.D,Raw.D1,Raw.fail,Raw.dup,Raw.cap,B]

structure ExplicitDerivativeInequalities (p : Center) (rect : Rectangle p) : Prop where
  served_pos : ∀ lam∈rect.box, ∀ b∈Ico (1:ℝ) (B p), 0< served1 p lam b
  curvature : ∃ c>0, ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
    c*p.theta≤-served2 p lam b
  payment_pos : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p), 9/10< payment1 p lam b
  determinant_pos : ∀ lam∈rect.box, ∀ b∈Icc (1:ℝ) (B p),
    0< payment2 p lam b*served1 p lam b-payment1 p lam b*served2 p lam b
  bulk : ∀ lam∈rect.box, bulkValue p*served1 p lam 1<4/5

end FCAppendix.Affine.Hybrid.Tail03
