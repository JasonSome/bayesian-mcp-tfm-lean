import FCAppendix.Affine.LowBody.PatternFiniteEnvelope
import FCAppendix.Affine.LowBody.EqualUniformEnvelope

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
variable {N : ℕ}

theorem patternPayoff_uniform_raise {ξ a B W : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (ha : 0<a) (haB : a≤B) (hW : 0≤W) :
    ∀ε>0,∃δ>0,∀(c : ℕ)(ω : Fin N→RowRival)(w x y : ℝ),
      (∀j,(ω j).1=0 → 0≤(ω j).2)→|w|≤W→a≤x→x≤B→x≤w→x<y→y-x<δ→
      patternPayoff ξ c (fun j=>(ω j).1) w (rowBids x ω)-
        patternPayoff ξ c (fun j=>(ω j).1) w (rowBids y ω)≤
        rowIntervalLoss c (1-ξ) x y ω+2*(1-ξ)*(y-x)+ε := by
  classical
  intro ε hε
  have hξ1 : ξ<1:=by linarith
  obtain ⟨δ,hδ,huniform⟩:=equalPayoff_uniform_update (ι:=Fin (N+1)) hξ hξ1 ha haB hW ε hε
  refine ⟨δ,hδ,?_⟩
  intro c ω w x y hω hw hax hxB hxw hxy hdist
  have hx : 0≤x:=(ha.trans_le hax).le
  have hκ : 0≤1-ξ:=by linarith
  have hloss : 0≤rowIntervalLoss c (1-ξ) x y ω := by
    unfold rowIntervalLoss
    split_ifs
    · exact mul_nonneg (by linarith) hx
    · exact le_rfl
  have hprice : 0≤2*(1-ξ)*(y-x):=mul_nonneg (by positivity) (sub_nonneg.mpr hxy.le)
  by_cases he : (patternTemplate c (fun j=>(ω j).1)).residual₀=
      (patternTemplate c (fun j=>(ω j).1)).residual₁
  · have hraw : ∀j : Fin (N+1),j≠0 → 0≤rowBids 0 ω j := by
      intro j _
      exact rowBids_nonneg 0 ω le_rfl hω j
    have hh:=huniform (patternTemplate c (fun j=>(ω j).1)).residual₀
      (rowBids 0 ω) 0 w x y hraw hw hax hxB (by rw [abs_of_pos (sub_pos.mpr hxy)];exact hdist)
    rw [rowBids_update,rowBids_update] at hh
    simp only [patternPayoff,if_pos he]
    have hbound:= (abs_lt.mp hh).1
    linarith
  · have hh:=pure_patternPayoff_finite_loss c hξh ω hx hxw hxy hω he
    linarith

end FCAppendix.Affine.LowBody
