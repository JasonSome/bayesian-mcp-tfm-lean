import FCAppendix.Affine.Hybrid.Tail03.BoundaryCoefficients

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set

def boundaryK {p : Center} {rect : Rectangle p} (d : BoundaryCoefficientBounds p rect) : ℝ :=
  d.C/(2*d.Amin)
def boundaryH {p : Center} {rect : Rectangle p} (d : BoundaryCoefficientBounds p rect) : ℝ :=
  3*d.C*(boundaryK d)^2+2*B p*d.C*boundaryK d+
    (d.C+B p*d.C)*(boundaryK d)^2
def boundaryOptimizerError {p : Center} {rect : Rectangle p}
    (d : BoundaryCoefficientBounds p rect) : ℝ := boundaryH d/(2*d.Amin)
def boundaryCostError {p : Center} {rect : Rectangle p}
    (d : BoundaryCoefficientBounds p rect) : ℝ :=
  boundaryOptimizerError d*(d.Amax*boundaryK d+1/2)+
    d.C*(boundaryK d)^3+B p*d.C*(boundaryK d)^2

lemma boundary_constants_positive {p : Center} {rect : Rectangle p}
    (d : BoundaryCoefficientBounds p rect) :
    0< boundaryK d ∧ 0< boundaryH d ∧ 0< boundaryOptimizerError d ∧ 0< boundaryCostError d := by
  have hC : 0< d.C := lt_of_lt_of_le (by norm_num) d.C_ge_one
  have hAmin : 0< d.Amin := d.Amin_pos
  have hB : 0< B p := (by norm_num : (0:ℝ)<1).trans (B_gt_one p)
  have hAmax : 0< d.Amax :=
    d.Amin_pos.trans_le ((d.leading_bounds (lambda0 p) rect.center_mem).1.trans
      (d.leading_bounds (lambda0 p) rect.center_mem).2)
  have hK : 0< boundaryK d := by unfold boundaryK; positivity
  have hH : 0< boundaryH d := by unfold boundaryH; positivity
  have hE : 0< boundaryOptimizerError d := by unfold boundaryOptimizerError; positivity
  exact ⟨hK,hH,hE,by unfold boundaryCostError; positivity⟩

lemma quantitative_boundary_step (p : Center) (rect : Rectangle p)
    (d : BoundaryCoefficientBounds p rect) (lam : Fin 2 → ℝ) (hlam : lam∈rect.box)
    {v b : ℝ} (hv : 1≤ v) (hb : b∈Ioo (1:ℝ) (B p))
    (hfo : v*served1 p lam b=payment1 p lam b) :
    |b-(B p-1/(2*leadingA p lam*v))|≤ boundaryOptimizerError d/v^2 ∧
      |(v-utility p lam v b)-(B p-1/(4*leadingA p lam*v))|≤ boundaryCostError d/v^2 := by
  let y := B p-b
  let A := leadingA p lam
  let a := failureCoeff p lam b
  let a1 := failureCoeff1 p lam b
  let c := paymentCoeff p lam b
  let c1 := paymentCoeff1 p lam b
  let K := boundaryK d
  let H := boundaryH d
  let E := boundaryOptimizerError d
  have hv0 : 0< v := lt_of_lt_of_le (by norm_num) hv
  have hb0 : 0< b := (by norm_num : (0:ℝ)<1).trans hb.1
  have hB0 : 0< B p := hb0.trans hb.2
  have hy0 : 0< y := sub_pos.mpr hb.2
  have hAminPos : 0< d.Amin := d.Amin_pos
  have hAmin : d.Amin≤ A := (d.leading_bounds lam hlam).1
  have hAmax : A≤ d.Amax := (d.leading_bounds lam hlam).2
  have hA0 : 0< A := d.Amin_pos.trans_le hAmin
  have ha : A≤ a := d.failure_lower lam hlam b ⟨hb.1.le,hb.2.le⟩
  have ha1 : a1≤0 := d.failure_deriv_nonpos lam hlam b ⟨hb.1.le,hb.2.le⟩
  have hcoeff := d.bound lam hlam b ⟨hb.1.le,hb.2.le⟩
  have hAabs : |a-A|≤ d.C*y := d.failure_lipschitz lam hlam b ⟨hb.1.le,hb.2.le⟩
  have hC0 : 0< d.C := lt_of_lt_of_le (by norm_num) d.C_ge_one
  have hconst := boundary_constants_positive d
  have hK0 : 0< K := hconst.1
  have hH0 : 0< H := hconst.2.1
  have hE0 : 0< E := hconst.2.2.1
  have hder := exact_boundary_derivatives p lam hb0.ne'
  have hEq : v*(2*y*a-y^2*a1)=1+(y^2-2*b*y)*c+b*y^2*c1 := by
    rw [hder.1,hder.2] at hfo
    exact hfo
  have hTy : v*(2*y*a-y^2*a1)≤ d.C := by
    rw [←hder.1,hfo]
    exact (abs_le.mp hcoeff.2.2.2).2
  have hxy : v*y≤ K := by
    have h1 := mul_nonneg (show 0≤2*y from by positivity) (sub_nonneg.mpr (hAmin.trans ha))
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) ha1
    have h3 := mul_nonneg hv0.le (by nlinarith : 0≤2*y*a-y^2*a1-2*y*d.Amin)
    unfold K boundaryK
    apply (le_div_iff₀ (by positivity : 0<2*d.Amin)).2
    nlinarith
  have hyK : y≤ K/v := (le_div_iff₀ hv0).2 (by nlinarith)
  have hz0 : 0≤ v*y := mul_nonneg hv0.le hy0.le
  have hz2 : (v*y)^2≤ K^2 := (sq_le_sq₀ hz0 hK0.le).2 hxy
  have hysq : y^2≤ K^2/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv0)).2
    nlinarith only [hz2]
  have hvysq : v*y^2≤ K^2/v := by
    apply (le_div_iff₀ hv0).2
    nlinarith only [hz2]
  have hysq' : y^2≤ K^2/v :=
    hysq.trans (div_le_div_of_nonneg_left (sq_nonneg K) hv0 (by nlinarith only [hv]))
  have hz3 : (v*y)^3≤ K^3 := pow_le_pow_left₀ hz0 hxy 3
  have hvycu : v*y^3≤ K^3/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv0)).2
    nlinarith only [hz3]
  have hres : 2*A*v*y-1=
      -2*v*y*(a-A)+v*y^2*a1+(y^2-2*b*y)*c+b*y^2*c1 := by nlinarith only [hEq]
  have hares : |-2*v*y*(a-A)|≤2*d.C*v*y^2 := by
    rw [abs_mul,abs_mul,abs_mul,abs_neg,abs_of_pos hv0,abs_of_pos hy0]
    norm_num
    have hh := mul_le_mul_of_nonneg_left hAabs (show 0≤2*v*y by positivity)
    nlinarith only [hh]
  have ha1res : |v*y^2*a1|≤ d.C*v*y^2 := by
    rw [abs_mul,abs_mul,abs_of_pos hv0,abs_of_nonneg (sq_nonneg y)]
    have hh := mul_le_mul_of_nonneg_left hcoeff.1 (show 0≤ v*y^2 by positivity)
    nlinarith only [hh]
  have hcres : |(y^2-2*b*y)*c|≤ d.C*y^2+2*B p*d.C*y := by
    rw [abs_mul]
    have hdiff : |y^2-2*b*y|≤ y^2+2*B p*y := by
      have hh := abs_sub (y^2) (2*b*y)
      rw [abs_of_nonneg (sq_nonneg y),abs_of_nonneg (show 0≤2*b*y by positivity)] at hh
      have hbmul := mul_le_mul_of_nonneg_right hb.2.le (show 0≤2*y by positivity)
      nlinarith only [hh,hbmul]
    have hh := mul_le_mul hdiff hcoeff.2.1 (abs_nonneg c)
      (show 0≤ y^2+2*B p*y by positivity)
    nlinarith only [hh]
  have hc1res : |b*y^2*c1|≤ B p*d.C*y^2 := by
    rw [abs_mul,abs_mul,abs_of_pos hb0,abs_of_nonneg (sq_nonneg y)]
    have h1 := mul_le_mul_of_nonneg_left hcoeff.2.2.1 (show 0≤ b*y^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hb.2.le (show 0≤ d.C*y^2 by positivity)
    nlinarith only [h1,h2]
  have hresbound : |2*A*v*y-1|≤ H/v := by
    rw [hres]
    have hsum1:=abs_add_le (-2*v*y*(a-A)) (v*y^2*a1)
    have hsum2:=abs_add_le (-2*v*y*(a-A)+v*y^2*a1) ((y^2-2*b*y)*c)
    have hsum3:=abs_add_le (-2*v*y*(a-A)+v*y^2*a1+(y^2-2*b*y)*c) (b*y^2*c1)
    have hr0 : |-2*v*y*(a-A)+v*y^2*a1+(y^2-2*b*y)*c+b*y^2*c1|≤
        3*d.C*v*y^2+2*B p*d.C*y+(d.C+B p*d.C)*y^2 := by
      nlinarith only [hsum1,hsum2,hsum3,hares,ha1res,hcres,hc1res]
    apply hr0.trans
    have h1 := mul_le_mul_of_nonneg_left hvysq (show 0≤3*d.C by positivity)
    have h2 := mul_le_mul_of_nonneg_left hyK (show 0≤2*B p*d.C by positivity)
    have h3 := mul_le_mul_of_nonneg_left hysq' (show 0≤ d.C+B p*d.C by positivity)
    calc
      _ = 3*d.C*(v*y^2)+(2*B p*d.C)*y+(d.C+B p*d.C)*y^2:=by ring
      _ ≤ 3*d.C*(K^2/v)+(2*B p*d.C)*(K/v)+(d.C+B p*d.C)*(K^2/v):=
        add_le_add (add_le_add h1 h2) h3
      _ = H/v:=by dsimp [H,boundaryH,K];ring
  have hoptidentity : b-(B p-1/(2*A*v))=-(2*A*v*y-1)/(2*A*v) := by
    dsimp [y]
    field_simp [hA0.ne',hv0.ne']
    ring
  have hopt : |b-(B p-1/(2*A*v))|≤ E/v^2 := by
    rw [hoptidentity,abs_div,abs_neg,abs_of_pos (show 0<2*A*v by positivity)]
    calc
      |2*A*v*y-1|/(2*A*v) ≤ (H/v)/(2*A*v) :=
        div_le_div_of_nonneg_right hresbound (by positivity)
      _ = (H/(2*A))/v^2 := by field_simp [hA0.ne',hv0.ne']
      _ ≤ E/v^2 := by
        have hh := div_le_div_of_nonneg_left hH0.le
          (show 0<2*d.Amin by positivity) (by nlinarith only [hAmin] : 2*d.Amin≤2*A)
        exact div_le_div_of_nonneg_right hh (sq_nonneg v)
  have hyerror : |y-1/(2*A*v)|≤ E/v^2 := by
    have heq : y-1/(2*A*v)=-(b-(B p-1/(2*A*v))) := by dsimp [y]; ring
    rw [heq,abs_neg]
    exact hopt
  have hfactor : |v*A*y-1/2|≤ d.Amax*K+1/2 := by
    have h0 : 0≤ v*A*y := by positivity
    have h1 := mul_le_mul_of_nonneg_left hxy hA0.le
    have h2 := mul_le_mul_of_nonneg_right hAmax hK0.le
    have hh := abs_sub (v*A*y) (1/2)
    rw [abs_of_nonneg h0] at hh
    norm_num at hh
    nlinarith only [h1,h2,hh]
  have hmain : |(y-1/(2*A*v))*(v*A*y-1/2)|≤
      E*(d.Amax*K+1/2)/v^2 := by
    rw [abs_mul]
    have hAmax0 : 0< d.Amax := hA0.trans_le hAmax
    have hh := mul_le_mul hyerror hfactor (abs_nonneg _)
      (show 0≤ E/v^2 by positivity)
    convert! hh using 1
    ring
  have hcorrection : |v*(a-A)*y^2|≤ d.C*K^3/v^2 := by
    rw [abs_mul,abs_mul,abs_of_pos hv0,abs_of_nonneg (sq_nonneg y)]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAabs hv0.le) (sq_nonneg y)
    have hh' := mul_le_mul_of_nonneg_left hvycu hC0.le
    calc
      _≤d.C*(v*y^3):=by nlinarith only [hh]
      _≤d.C*(K^3/v^2):=hh'
      _=_:=by ring
  have hpayment : |b*c*y^2|≤ B p*d.C*K^2/v^2 := by
    rw [abs_mul,abs_mul,abs_of_pos hb0,abs_of_nonneg (sq_nonneg y)]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff.2.1 hb0.le) (sq_nonneg y)
    have hh' := mul_le_mul_of_nonneg_right hb.2.le (show 0≤ d.C*y^2 by positivity)
    have hh'' := mul_le_mul_of_nonneg_left hysq (show 0≤ B p*d.C by positivity)
    change b*|c| *y^2≤b*d.C*y^2 at hh
    calc
      _≤b*d.C*y^2:=hh
      _≤B p*d.C*y^2:=by nlinarith only [hh']
      _≤B p*d.C*(K^2/v^2):=hh''
      _=_:=by ring
  have hcostid : (v-utility p lam v b)-(B p-1/(4*A*v))=
      (y-1/(2*A*v))*(v*A*y-1/2)+v*(a-A)*y^2+b*c*y^2 := by
    unfold utility
    rw [(exact_boundary_factorizations p lam b).1,(exact_boundary_factorizations p lam b).2]
    dsimp [y,a,c]
    field_simp [hA0.ne',hv0.ne']
    ring
  refine ⟨hopt,?_⟩
  rw [hcostid]
  have hh0:=abs_add_le ((y-1/(2*A*v))*(v*A*y-1/2)) (v*(a-A)*y^2)
  have hh1:=abs_add_le ((y-1/(2*A*v))*(v*A*y-1/2)+v*(a-A)*y^2) (b*c*y^2)
  have hh : |(y-1/(2*A*v))*(v*A*y-1/2)+v*(a-A)*y^2+b*c*y^2|≤
      |(y-1/(2*A*v))*(v*A*y-1/2)|+|v*(a-A)*y^2|+|b*c*y^2|:=by
    linarith only [hh0,hh1]
  have htotal := hh.trans (add_le_add (add_le_add hmain hcorrection) hpayment)
  convert! htotal using 1
  dsimp [boundaryCostError,K,E]
  ring

theorem uniform_boundary_Taylor (p : Center) (rect : Rectangle p)
    (h : RectangleAnalyticCertificate p rect) : Nonempty (BoundaryTaylorData p rect) := by
  classical
  obtain ⟨W⟩ := shrink_rectangle_choose_cap_constant p rect h
  obtain ⟨d⟩ := boundary_coefficient_bounds p rect h W
  obtain ⟨V,hV,hresponse⟩ := uniform_floor_threshold p rect h
  let V0 : ℝ := max V 1
  have hV0 : 0< V0 := hV.trans_le (le_max_left _ _)
  have hr : ∀ lam∈rect.box, ∀ v,V0≤ v →
      ∃ b∈Ioo (1:ℝ) (B p),v*served1 p lam b=payment1 p lam b ∧
        (∀ c∈Icc (1:ℝ) (B p),utility p lam v c≤ utility p lam v b) ∧
        (∀ c∈Icc (1:ℝ) (B p),utility p lam v c=utility p lam v b → c=b) := by
    intro lam hlam v hv
    exact hresponse lam hlam v ((le_max_left _ _).trans hv)
  let response : (Fin 2 → ℝ) → ℝ → ℝ := fun lam v =>
    if hvalid : lam∈rect.box ∧ V0≤ v then (hr lam hvalid.1 v hvalid.2).choose else 1
  have hspec : ∀ lam∈rect.box, ∀ v,V0≤ v →
      response lam v∈Ioo (1:ℝ) (B p) ∧
      v*served1 p lam (response lam v)=payment1 p lam (response lam v) ∧
      (∀ c∈Icc (1:ℝ) (B p),utility p lam v c≤ utility p lam v (response lam v)) ∧
      (∀ c∈Icc (1:ℝ) (B p),utility p lam v c=utility p lam v (response lam v) → c=response lam v) := by
    intro lam hlam v hv
    dsimp [response]
    rw [dif_pos ⟨hlam,hv⟩]
    exact (hr lam hlam v hv).choose_spec
  let error := max (boundaryOptimizerError d) (boundaryCostError d)
  have herr : 0≤ error := (boundary_constants_positive d).2.2.1.le.trans (le_max_left _ _)
  refine ⟨{
    toLeadingWindow := W
    V0 := V0
    error := error
    V0_pos := hV0
    error_nonneg := herr
    response := response
    response_mem := fun lam hlam v hv => (hspec lam hlam v hv).1
    response_optimal := fun lam hlam v hv => (hspec lam hlam v hv).2.2.1
    response_unique := fun lam hlam v hv => (hspec lam hlam v hv).2.2.2
    response_first_order := fun lam hlam v hv => (hspec lam hlam v hv).2.1
    optimizer_error := ?_
    cost_error := ?_ }⟩
  · intro lam hlam v hv
    have hh := quantitative_boundary_step p rect d lam hlam
      ((le_max_right _ _).trans hv) (hspec lam hlam v hv).1 (hspec lam hlam v hv).2.1
    exact hh.1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg v))
  · intro lam hlam v hv
    have hh := quantitative_boundary_step p rect d lam hlam
      ((le_max_right _ _).trans hv) (hspec lam hlam v hv).1 (hspec lam hlam v hv).2.1
    exact hh.2.trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg v))

end FCAppendix.Affine.Hybrid.Tail03
