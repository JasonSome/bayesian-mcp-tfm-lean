import FCAppendix.Affine.LowBody.PureFiniteEnvelope

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set
open scoped BigOperators
variable {J : ℕ}

lemma pure_harmfulInterval_active {κ d L U : ℝ} (hκ : 0<κ) (hκ1 : κ≤1)
    (hd : d<κ*L) (hsep : κ*U<L) (T : LowBody.PureTemplate (Fin J))
    (active : Finset (Fin J)) (b : Fin J→ℝ) (i : Fin J) (y : ℝ)
    (hi : L≤b i) (hy : b i≤y) (hyU : y≤U)
    (hA : ∀j,j∈active→L≤b j)
    (hsmall : ∀j,j∈T.support→j∉active→j≠i→b j≤d)
    (hh : T.harmfulInterval κ b i y) :
    ∃j∈active,j≠i ∧ b j∈Icc (b i) y := by
  obtain ⟨_,_,j,hjs,hji,hcross⟩:=hh
  have hLU : L≤U:=hi.trans (hy.trans hyU)
  have hLpos : 0<L := by
    by_contra hn
    have hL : L≤0:=le_of_not_gt hn
    have hmul:=mul_le_mul_of_nonpos_right hκ1 hL
    have hU:=mul_le_mul_of_nonneg_left hLU hκ.le
    nlinarith
  have hdL : d<L := by
    have hm:=mul_le_mul_of_nonneg_right hκ1 hLpos.le
    nlinarith
  have hja : j∈active := by
    by_contra hn
    have hbj:=hsmall j hjs hn hji
    rcases hcross with hc | hc
    · linarith [hc.1]
    · have hx:=mul_le_mul_of_nonneg_left hi hκ.le
      linarith [hc.1]
  refine ⟨j,hja,hji,?_⟩
  rcases hcross with hc | hc
  · exact hc
  · have hbL:=hA j hja
    have hm:=mul_le_mul_of_nonneg_left hyU hκ.le
    linarith [hc.2]

theorem pure_finite_loss_active {κ d L U w : ℝ} (hκ : 1/2≤κ) (hκ1 : κ≤1)
    (hd : d<κ*L) (hsep : κ*U<L) (hU : 0≤U)
    (T : LowBody.PureTemplate (Fin J)) (active : Finset (Fin J))
    (b : Fin J→ℝ) (hb : ∀j,0≤b j) (hz : ∀j,j∉T.support→b j=0)
    (i : Fin J) (his : i∈T.support) (hi : 0<b i) (hiL : L≤b i) (hiw : b i≤w)
    (y : ℝ) (hy : b i<y) (hyU : y≤U)
    (hA : ∀j,j∈active→L≤b j)
    (hsmall : ∀j,j∈T.support→j∉active→j≠i→b j≤d) :
    LowBody.purePayoff κ w b (T.selection κ b) i-
      LowBody.purePayoff κ w (Function.update b i y) (T.selection κ (Function.update b i y)) i≤
        (2*κ-1)*U*(∑j:Fin J,if j∈active ∧ j≠i ∧ b j∈Icc (b i) y then (1:ℝ) else 0)+
          2*κ*(y-b i) := by
  have hjump : T.intervalLoss κ b i y≤
      (2*κ-1)*U*(∑j:Fin J,if j∈active ∧ j≠i ∧ b j∈Icc (b i) y then (1:ℝ) else 0) := by
    have hc : 0≤(2*κ-1)*U:=mul_nonneg (by linarith) hU
    have hs : 0≤∑j:Fin J,if j∈active ∧ j≠i ∧ b j∈Icc (b i) y then (1:ℝ) else 0 :=
      Finset.sum_nonneg (fun j _=>by split_ifs <;> norm_num)
    unfold LowBody.PureTemplate.intervalLoss
    split_ifs with he
    · obtain ⟨j,hja,hji,hcross⟩:=pure_harmfulInterval_active (by linarith) hκ1 hd hsep T active b i y
        hiL hy.le hyU hA hsmall he
      have hone : (1:ℝ)≤∑j:Fin J,if j∈active ∧ j≠i ∧ b j∈Icc (b i) y then (1:ℝ) else 0 := by
        have hh:=Finset.single_le_sum (s:=Finset.univ)
          (f:=fun j:Fin J=>if j∈active ∧ j≠i ∧ b j∈Icc (b i) y then (1:ℝ) else 0)
          (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ j)
        simpa only [if_pos (show j∈active ∧ j≠i ∧ b j∈Icc (b i) y from ⟨hja,hji,hcross⟩)] using hh
      calc
        _≤(2*κ-1)*U:=mul_le_mul_of_nonneg_left (hy.le.trans hyU) (by linarith)
        _≤_:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hc
    · exact mul_nonneg hc hs
  have hh:=T.finite_payoff_loss hκ b hb hz i his hi hiw y hy
  linarith

end FCAppendix.Affine.Hybrid
