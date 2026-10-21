import FCAppendix.Affine.LowBody.NoisyRaisingLoss

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_update_mono {ξ x y : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (i : ι) (hb : ∀j,j≠i → 0  ≤  b j) (hx : 0  ≤  x) (hxy : x  ≤  y) :
    EqualCapacity.positiveMarginal ξ c (Function.update b i x) i  ≤
      EqualCapacity.positiveMarginal ξ c (Function.update b i y) i := by
  classical
  by_cases heq : x=y
  · simp only [heq,le_refl]
  have hlt : x<y:=lt_of_le_of_ne hxy heq
  let bp:=Function.update b i x
  let bq:=Function.update b i y
  let p:=EqualCapacity.positiveMarginal ξ c bp
  let q:=EqualCapacity.positiveMarginal ξ c bq
  let term : ι→ℝ:=fun j=>(q j-p j)*(bp j*(1-ξ*p j)-bq j*(1-ξ*q j))
  have hcross : ∑j,term j  ≤  0:=EqualCapacity.positive_kernel_cross hξ hξ1 c bp bq
  have hrest : 0  ≤  ∑j∈Finset.univ.erase i,term j := by
    apply Finset.sum_nonneg
    intro j hj
    have hji : j≠i:=(Finset.mem_erase.mp hj).1
    have he : term j=ξ*b j*(q j-p j)^2 := by
      simp only [term,bp,bq,Function.update_of_ne hji]
      ring
    rw [he]
    exact mul_nonneg (mul_nonneg hξ.le (hb j hji)) (sq_nonneg _)
  have hsum : (∑j,term j)=term i+∑j∈Finset.univ.erase i,term j:=
    (Finset.add_sum_erase Finset.univ term (Finset.mem_univ i)).symm
  rw [hsum] at hcross
  have hf : term i  ≤  0:=by linarith
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 bp
  have hq:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 bq
  change p i  ≤  q i
  by_contra hn
  have hqp : q i-p i<0:=sub_neg.mpr (lt_of_not_ge hn)
  have hq1 : q i  ≤  1:=hq.2.1 i
  have hq0 : 0  ≤  q i:=hq.1 i
  have hcoef : 0<1-ξ*q i:=by nlinarith [mul_le_mul_of_nonneg_left hq1 hξ.le]
  have hleft : ξ*x*(q i-p i)  ≤  0:=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hξ.le hx) hqp.le
  have hright : 0<(y-x)*(1-ξ*q i):=mul_pos (sub_pos.mpr hlt) hcoef
  have hbr : x*(1-ξ*p i)-y*(1-ξ*q i)<0:=by nlinarith
  have hterm : 0<term i := by
    change 0<(q i-p i)*(bp i*(1-ξ*p i)-bq i*(1-ξ*q i))
    simp only [bp,bq,Function.update_self]
    exact mul_pos_of_neg_of_neg hqp hbr
  linarith

theorem equalPayoff_update_loss_le_two_new {ξ x y w : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (i : ι) (hb : ∀j,j≠i → 0  ≤  b j)
    (hx : 0  ≤  x) (hxy : x  ≤  y) (hw : 0  ≤  w) :
    equalPayoff ξ c i w (Function.update b i x)-
      equalPayoff ξ c i w (Function.update b i y)  ≤  2*y := by
  let p:=EqualCapacity.positiveMarginal ξ c (Function.update b i x) i
  let q:=EqualCapacity.positiveMarginal ξ c (Function.update b i y) i
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i x)
  have hq:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i y)
  have hp0 : 0  ≤  p:=hp.1 i
  have hp1 : p  ≤  1:=hp.2.1 i
  have hq0 : 0  ≤  q:=hq.1 i
  have hq1 : q  ≤  1:=hq.2.1 i
  have hpq : p  ≤  q:=positiveMarginal_update_mono hξ hξ1 c b i hb hx hxy
  have hs : 0  ≤  (q-p)*(2-p-q):=mul_nonneg (sub_nonneg.mpr hpq) (by linarith)
  have hservice : 2*p-p^2  ≤  2*q-q^2:=by nlinarith [hs]
  have hvalue:=mul_le_mul_of_nonneg_left hservice hw
  have hp2 : p^2  ≤  p:=by nlinarith
  have hξp : ξ*p^2  ≤  p^2:=by nlinarith [mul_le_mul_of_nonneg_right hξ1.le (sq_nonneg p)]
  have holdCost : 0  ≤  x*(2*p-2*ξ*p^2):=mul_nonneg hx (by nlinarith)
  have hnewCost : y*(2*q-2*ξ*q^2)  ≤  2*y := by
    have hc : 2*q-2*ξ*q^2  ≤  2:=by nlinarith [mul_nonneg hξ.le (sq_nonneg q)]
    nlinarith [mul_le_mul_of_nonneg_left hc (hx.trans hxy)]
  change (w*(2*p-p^2)-Function.update b i x i*(2*p-2*ξ*p^2))-
    (w*(2*q-q^2)-Function.update b i y i*(2*q-2*ξ*q^2))  ≤  2*y
  simp only [Function.update_self]
  linarith

lemma categoryLaw_eq_low_law (s a h : ℝ) (hs : 0  ≤  s) (ha : 0  ≤  a) (hh : 0  ≤  h)
    (hsum : s+a+h=1) (G H : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure H] :
    categoryLaw s a h hs ha hh hsum G=categoryLaw s a h hs ha hh hsum H := by
  apply FiniteLaw.ext
  intro k
  rw [categoryLaw_mass,categoryLaw_mass]

variable {N : ℕ}

theorem patternPayoff_small_bid_loss (c : ℕ) {ξ w x y : ℝ}
    (hξ : 0<ξ) (hξh : ξ  ≤  1/2) (ω : Fin N→RowRival)
    (hx : 0  ≤  x) (hxy : x  ≤  y) (hyw : y  ≤  w)
    (hω : ∀j,(ω j).1=0 → 0  ≤  (ω j).2) :
    literalRowPayoff ξ c w (x,ω)-literalRowPayoff ξ c w (y,ω)  ≤  2*y := by
  classical
  have hξ1 : ξ<1:=by linarith
  have hy : 0  ≤  y:=hx.trans hxy
  have hw : 0  ≤  w:=hy.trans hyw
  have hκ : 1/2  ≤  1-ξ:=by linarith
  let b:=rowBids x ω
  have hb : b 0=x:=rfl
  have hne : ∀j,j≠(0:Fin (N+1)) → 0  ≤  b j:=fun j _=>rowBids_nonneg x ω hx hω j
  unfold literalRowPayoff patternPayoff
  dsimp only
  by_cases he : (patternTemplate c (fun j=>(ω j).1)).residual₀=
      (patternTemplate c (fun j=>(ω j).1)).residual₁
  · rw [if_pos he,if_pos he]
    have hh:=equalPayoff_update_loss_le_two_new hξ hξ1
      (patternTemplate c (fun j=>(ω j).1)).residual₀ b 0 hne hx hxy hw
    simpa only [b,rowBids_update] using hh
  · rw [if_neg he,if_neg he]
    by_cases heq : x=y
    · simp only [heq,sub_self]
      positivity
    · have hlt : x<y:=lt_of_le_of_ne hxy heq
      let T:=patternTemplate c (fun j=>(ω j).1)
      let P:=T.selection (1-ξ) b
      let Q:=T.selection (1-ξ) (Function.update b 0 y)
      have hcopy:=T.focalCopy_selection_mono (κ:=1-ξ) (by linarith) b 0 y (by simpa only [hb] using hlt)
      have hjump:=purePayoff_loss_le_duplicate (κ:=1-ξ) b 0 (by simpa only [hb] using hxy.trans hyw) P Q hcopy
      have hprice:=purePayoff_price_loss hκ b 0 y (by simpa only [hb] using hxy) Q (w:=w)
      have hdup : (if focalCopy P 0≠2 ∧ focalCopy Q 0=2 then (2*(1-ξ)-1)*b 0 else 0)  ≤
          (2*(1-ξ)-1)*x := by
        rw [hb]
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (by linarith) hx
      have hsum : purePayoff (1-ξ) w b P 0-purePayoff (1-ξ) w (Function.update b 0 y) Q 0  ≤  2*y := by
        rw [hb] at hprice
        nlinarith [mul_nonneg hξ.le hy]
      simpa only [P,Q,T,b,rowBids_update] using hsum

theorem expected_literalSmoothed_small_bid_loss {d : ℝ} (c : ℕ) {ξ ε w x y : ℝ}
    (hξ : 0<ξ) (hξh : ξ ≤ 1/2) (hε : 0 ≤ ε) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hyw : y*(1+ε) ≤ w) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    (∫ω : Fin N→RowRival,literalSmoothedRowPayoff ξ ε c w x ω-
      literalSmoothedRowPayoff ξ ε c w y ω
      ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw mu))) ≤ 2*y*(1+ε) := by
  have hξ1 : ξ<1:=by linarith
  have hy : 0 ≤ y:=hx.trans hxy
  let ν:=Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw mu))
  letI : IsProbabilityMeasure (rivalLaw s a h (realLowLaw mu)):=
    rivalLaw_isProbability s a h hs ha hh hsum (realLowLaw mu)
  rw [integral_literalSmoothed_sub hξ hξ1 ε c w x y ν]
  have hi:=(integrable_literal_noisyRow hξ hξ1 ε c w x ν).sub
    (integrable_literal_noisyRow hξ hξ1 ε c w y ν)
  have hb:=integral_mono_ae hi.integral_prod_right (integrable_const (2*y*(1+ε))) (by
    filter_upwards [uniformNoise_support,hi.prod_left_ae] with z hz hiz
    have hn0 : 0 ≤ 1+ε*z:=by nlinarith [mul_nonneg hε hz.1]
    have hn1 : 1+ε*z ≤ 1+ε:=by
      have hh:=mul_le_mul_of_nonneg_left hz.2 hε
      linarith
    have hnew : y*(1+ε*z) ≤ w:=(mul_le_mul_of_nonneg_left hn1 hy).trans hyw
    have hrow:=integral_mono_ae hiz (integrable_const (2*(y*(1+ε*z)))) (by
      filter_upwards [lowRowProfile_nonnegative s a h hs ha hh hsum mu N] with ω hω
      simp only [Pi.sub_apply]
      exact patternPayoff_small_bid_loss c hξ hξh ω (mul_nonneg hx hn0)
        (mul_le_mul_of_nonneg_right hxy hn0) hnew hω)
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hrow
    have hprice:=mul_le_mul_of_nonneg_left hn1 (by positivity : 0 ≤ 2*y)
    dsimp only [ν] at *
    linarith)
  simpa only [Pi.sub_apply,integral_const,probReal_univ,smul_eq_mul,one_mul] using hb

end FCAppendix.Affine.LowBody
