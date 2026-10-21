import FCAppendix.Affine.LowBody.NoisyEqualPayoff

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem abs_affine_payoff_change {ξ p q w x y : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hp0 : 0≤p) (hp1 : p≤1)
    (hq0 : 0≤q) (hq1 : q≤1) :
    |(w*(2*q-q^2)-y*(2*q-2*ξ*q^2))-(w*(2*p-p^2)-x*(2*p-2*ξ*p^2))|≤
      (2*|w|+6*|x|)*|q-p|+2*|y-x| := by
  have hsum : |q+p|≤2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hsuccess : |2-q-p|≤2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hprice : |2-2*ξ*(q+p)|≤6 := by
    calc
      _≤|(2:ℝ)|+|2*ξ*(q+p)|:=abs_sub _ _
      _=2+2*ξ*|q+p|:=by rw [abs_mul,abs_mul,abs_of_pos hξ]; norm_num
      _≤6:=by nlinarith
  have hξq : ξ*q^2≤1 := by
    have hh:=mul_le_mul_of_nonneg_right hξ1.le (sq_nonneg q)
    nlinarith
  have hcharge : |2*q-2*ξ*q^2|≤2 := abs_le.mpr
    ⟨by nlinarith,by nlinarith [mul_nonneg hξ.le (sq_nonneg q)]⟩
  have he : (w*(2*q-q^2)-y*(2*q-2*ξ*q^2))-(w*(2*p-p^2)-x*(2*p-2*ξ*p^2))=
      w*(q-p)*(2-q-p)-x*(q-p)*(2-2*ξ*(q+p))-(y-x)*(2*q-2*ξ*q^2) := by ring
  rw [he]
  calc
    _≤|w*(q-p)*(2-q-p)|+|x*(q-p)*(2-2*ξ*(q+p))|+|(y-x)*(2*q-2*ξ*q^2)|:=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _=|w| *|q-p| *|2-q-p|+|x| *|q-p| *|2-2*ξ*(q+p)|+|y-x| *|2*q-2*ξ*q^2|:=by
      simp only [abs_mul]
    _≤|w| *|q-p| *2+|x| *|q-p| *6+|y-x| *2:=by gcongr
    _=(2*|w|+6*|x|)*|q-p|+2*|y-x|:=by ring

theorem abs_equalPayoff_update_sub_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (i : ι) (w x y : ℝ) :
    |equalPayoff ξ c i w (Function.update b i y)-equalPayoff ξ c i w (Function.update b i x)|≤
      (2*|w|+6*|x|)*|EqualCapacity.positiveMarginal ξ c (Function.update b i y) i-
        EqualCapacity.positiveMarginal ξ c (Function.update b i x) i|+2*|y-x| := by
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i x)
  have hq:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 (Function.update b i y)
  simpa only [equalPayoff,Function.update_self] using
    abs_affine_payoff_change hξ hξ1 (hp.1 i) (hp.2.1 i) (hq.1 i) (hq.2.1 i)
      (w:=w) (x:=x) (y:=y)

theorem positiveMarginal_update_sq_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (i : ι) (x y : ℝ) (hx : 0≤x)
    (hb : ∀j,j≠i→0≤b j) :
    ξ*x*(EqualCapacity.positiveMarginal ξ c (Function.update b i y) i-
      EqualCapacity.positiveMarginal ξ c (Function.update b i x) i)^2≤|y-x| := by
  have hb' : ∀j,0≤Function.update b i x j := by
    intro j
    by_cases hj:j=i
    · subst j
      simpa only [Function.update_self] using hx
    · simpa only [Function.update_of_ne hj] using hb j hj
  have hs : (∑j,|Function.update b i y j-Function.update b i x j|)=|y-x| := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Function.update_of_ne hj]
    · simp
  simpa only [Function.update_self,hs] using
    EqualCapacity.positive_kernel_perturbation hξ hξ1 c
      (Function.update b i x) (Function.update b i y) hb' i

theorem equalPayoff_uniform_update {ξ a B W : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ha : 0<a) (haB : a≤B) (hW : 0≤W) :
    ∀ε>0,∃δ>0,∀(c : ℕ)(b : ι→ℝ)(i : ι)(w x y : ℝ),
      (∀j,j≠i→0≤b j)→|w|≤W→a≤x→x≤B→|y-x|<δ→
      |equalPayoff ξ c i w (Function.update b i y)-equalPayoff ξ c i w (Function.update b i x)|<ε := by
  intro ε hε
  let C:=2*W+6*B
  have hB : 0<B:=ha.trans_le haB
  have hC : 0≤C:=by dsimp [C]; positivity
  let t:=ε/(2*(C+1))
  have ht : 0<t:=by dsimp [t]; positivity
  refine ⟨min (ε/4) (ξ*a*t^2),lt_min (by positivity) (by positivity),?_⟩
  intro c b i w x y hb hw hax hxB hdist
  have hdx : |y-x|<ε/4:=hdist.trans_le (min_le_left _ _)
  have hsmall : |y-x|<ξ*a*t^2:=hdist.trans_le (min_le_right _ _)
  have hquad:=positiveMarginal_update_sq_le hξ hξ1 c b i x y (ha.le.trans hax) hb
  let dp:=EqualCapacity.positiveMarginal ξ c (Function.update b i y) i-
      EqualCapacity.positiveMarginal ξ c (Function.update b i x) i
  have hcoef : 0<ξ*a:=mul_pos hξ ha
  have hquad' : ξ*a*dp^2≤|y-x| := by
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hax hξ.le) (sq_nonneg dp)
    exact hh.trans hquad
  have hsq : dp^2<t^2:=by nlinarith
  have hdp : |dp|<t:=abs_lt_of_sq_lt_sq hsq ht.le
  have hbound:=abs_equalPayoff_update_sub_le hξ hξ1 c b i w x y
  have hxabs : |x|≤B:=by rw [abs_of_nonneg (ha.le.trans hax)]; exact hxB
  have hconst : 2*|w|+6*|x|≤C:=by dsimp [C]; linarith
  have hCt : C*t≤ε/2 := by
    have he : (2*(C+1))*t=ε:=by dsimp [t]; field_simp
    nlinarith
  calc
    _≤C*|dp|+2*|y-x|:=hbound.trans (by gcongr)
    _≤C*t+2*|y-x|:=by gcongr
    _<ε:=by linarith

end FCAppendix.Affine.LowBody
