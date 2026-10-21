import FCAppendix.Affine.LowBody.PureFiniteEnvelope
import FCAppendix.Affine.LowBody.ResidualOutcomes
import FCAppendix.Affine.LowBody.HarmfulJumpBound

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
open scoped BigOperators
variable {N : ℕ}

def rowBids (x : ℝ) (ω : Fin N→RowRival) : Fin (N+1)→ℝ :=
  Fin.cons x (fun j=>if (ω j).1=0 then (ω j).2 else 0)

lemma rowBids_nonneg (x : ℝ) (ω : Fin N→RowRival) (hx : 0≤x)
    (hω : ∀j,(ω j).1=0 → 0≤(ω j).2) : ∀i,0≤rowBids x ω i := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact hx
  · by_cases hj : (ω j).1=0
    · simpa only [rowBids,Fin.cons_succ,if_pos hj] using hω j hj
    · simp only [rowBids,Fin.cons_succ,if_neg hj,le_refl]

lemma rowBids_outside (c : ℕ) (x : ℝ) (ω : Fin N→RowRival) :
    ∀i,i∉(patternTemplate c (fun j=>(ω j).1)).support → rowBids x ω i=0 := by
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · intro hi
    exact False.elim (hi (focal_mem_patternTemplate c _))
  · intro hi
    have hj : (ω j).1≠0 := by
      intro he
      apply hi
      simp [patternTemplate,patternRow,rowLowList,he]
    simp only [rowBids,Fin.cons_succ,if_neg hj]

lemma rowBids_update (x y : ℝ) (ω : Fin N→RowRival) :
    Function.update (rowBids x ω) 0 y=rowBids y ω := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [rowBids]
  · simp only [Function.update_of_ne (Fin.succ_ne_zero j),rowBids,Fin.cons_succ]

lemma pattern_bothUnderflow_of_positive_residuals (c : ℕ) (kind : Fin N→Fin 4)
    (h₀ : 0<(patternTemplate c kind).residual₀)
    (h₁ : 0<(patternTemplate c kind).residual₁) : BothUnderflow c kind := by
  unfold BothUnderflow
  rw [sum_firstHigher,sum_secondHigher]
  change 0 < min (1+classCount 0 (patternRow kind))
    (c-classCount 1 (patternRow kind)-classCount 2 (patternRow kind)) at h₀
  change 0 < min (1+classCount 0 (patternRow kind))
    (c-classCount 1 (patternRow kind)-classCount 3 (patternRow kind)) at h₁
  constructor <;> omega

def rowHarmfulInterval (c : ℕ) (κ x y : ℝ) (ω : Fin N→RowRival) : Prop :=
  ω∈rowBothUnderflow c ∧ ∃j : Fin N,(ω j).1=0 ∧
    ((ω j).2∈Icc x y ∨ (ω j).2∈Icc (κ*x) (κ*y))

def rowIntervalLoss (c : ℕ) (κ x y : ℝ) (ω : Fin N→RowRival) : ℝ := by
  classical
  exact if rowHarmfulInterval c κ x y ω then (2*κ-1)*x else 0

lemma pattern_harmfulInterval_to_row (c : ℕ) (κ x y : ℝ) (ω : Fin N→RowRival)
    (he : (patternTemplate c (fun j=>(ω j).1)).harmfulInterval κ (rowBids x ω) 0 y) :
    rowHarmfulInterval c κ x y ω := by
  obtain ⟨h₀,h₁,j,hj,hj0,hjbid⟩:=he
  refine ⟨pattern_bothUnderflow_of_positive_residuals c _ h₀ h₁,?_⟩
  rcases Fin.eq_zero_or_eq_succ j with heq | ⟨k,rfl⟩
  · exact False.elim (hj0 heq)
  · have hk : (ω k).1=0 := by
      by_contra hn
      simp [patternTemplate,patternRow,rowLowList,hn] at hj
    refine ⟨k,hk,?_⟩
    simpa only [rowBids,Fin.cons_zero,Fin.cons_succ,if_pos hk] using hjbid

lemma intervalLoss_le_rowIntervalLoss (c : ℕ) {κ x : ℝ} (hκ : 1/2≤κ) (hx : 0≤x)
    (y : ℝ) (ω : Fin N→RowRival) :
    (patternTemplate c (fun j=>(ω j).1)).intervalLoss κ (rowBids x ω) 0 y≤
      rowIntervalLoss c κ x y ω := by
  classical
  have hcost : 0≤(2*κ-1)*x:=mul_nonneg (by linarith) hx
  unfold PureTemplate.intervalLoss rowIntervalLoss
  by_cases he : (patternTemplate c (fun j=>(ω j).1)).harmfulInterval κ (rowBids x ω) 0 y
  · rw [if_pos he,if_pos (pattern_harmfulInterval_to_row c κ x y ω he)]
    simp only [rowBids,Fin.cons_zero,le_refl]
  · rw [if_neg he]
    split_ifs
    · exact hcost
    · exact le_rfl

theorem pure_patternPayoff_finite_loss (c : ℕ) {ξ w x y : ℝ}
    (hξ : ξ≤1/2) (ω : Fin N→RowRival) (hx : 0≤x) (hxw : x≤w) (hxy : x<y)
    (hω : ∀j,(ω j).1=0 → 0≤(ω j).2)
    (hne : (patternTemplate c (fun j=>(ω j).1)).residual₀≠
      (patternTemplate c (fun j=>(ω j).1)).residual₁) :
    patternPayoff ξ c (fun j=>(ω j).1) w (rowBids x ω)-
      patternPayoff ξ c (fun j=>(ω j).1) w (rowBids y ω)≤
      rowIntervalLoss c (1-ξ) x y ω+2*(1-ξ)*(y-x) := by
  let T:=patternTemplate c (fun j=>(ω j).1)
  have hκ : 1/2≤1-ξ:=by linarith
  have hh:=T.finite_payoff_loss_nonnegative hκ (rowBids x ω) (rowBids_nonneg x ω hx hω)
    (rowBids_outside c x ω) 0 (focal_mem_patternTemplate c _) hxw y hxy
  rw [rowBids_update] at hh
  have hb:=intervalLoss_le_rowIntervalLoss c hκ hx y ω
  change purePayoff (1-ξ) w (rowBids x ω) (T.selection (1-ξ) (rowBids x ω)) 0-
    purePayoff (1-ξ) w (rowBids y ω) (T.selection (1-ξ) (rowBids y ω)) 0≤_ at hh
  simp only [patternPayoff,if_neg hne]
  dsimp only [T] at hh
  simp only [rowBids,Fin.cons_zero] at *
  linarith

lemma equalPayoff_zero_bid {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ξ : ℝ) (c : ℕ) (i : ι) (w : ℝ) (b : ι→ℝ) (hb : b i=0) :
    equalPayoff ξ c i w b=0 := by
  have hi : i∉Existence.PayOnceBounded.positiveSupport b:=by
    rw [Existence.PayOnceBounded.mem_positiveSupport,hb]
    exact lt_irrefl 0
  have hp : EqualCapacity.positiveMarginal ξ c b i=0:=
    EqualCapacity.onSupport_outside ξ c _ b i hi
  simp [equalPayoff,hp]

lemma equalPayoff_ge_neg_two_bid {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ w : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (i : ι) (b : ι→ℝ)
    (hw : 0≤w) (hb : 0≤b i) : -2*b i≤equalPayoff ξ c i w b := by
  let p:=EqualCapacity.positiveMarginal ξ c b i
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b
  have hp0 : 0≤p:=hp.1 i
  have hp1 : p≤1:=hp.2.1 i
  have hs : 0≤w*(2*p-p^2):=mul_nonneg hw (by nlinarith)
  have hc : 2*p-2*ξ*p^2≤2:=by nlinarith [mul_nonneg hξ.le (sq_nonneg p)]
  have hcharge:=mul_le_mul_of_nonneg_left hc hb
  change -2*b i≤w*(2*p-p^2)-b i*(2*p-2*ξ*p^2)
  nlinarith

theorem patternPayoff_zero_bid_loss (c : ℕ) {ξ w y : ℝ}
    (hξ : 0<ξ) (hξh : ξ≤1/2) (ω : Fin N→RowRival) (hw : 0≤w) (hy : 0<y)
    (hω : ∀j,(ω j).1=0 → 0≤(ω j).2) :
    patternPayoff ξ c (fun j=>(ω j).1) w (rowBids 0 ω)-
      patternPayoff ξ c (fun j=>(ω j).1) w (rowBids y ω)≤2*y := by
  classical
  have hξ1 : ξ<1:=by linarith
  by_cases he : (patternTemplate c (fun j=>(ω j).1)).residual₀=
      (patternTemplate c (fun j=>(ω j).1)).residual₁
  · simp only [patternPayoff,if_pos he]
    rw [equalPayoff_zero_bid ξ _ 0 w (rowBids 0 ω) (by simp [rowBids])]
    have hh:=equalPayoff_ge_neg_two_bid hξ hξ1
      (patternTemplate c (fun j=>(ω j).1)).residual₀ 0 (rowBids y ω) hw
      (by simpa only [rowBids,Fin.cons_zero] using hy.le)
    simpa only [rowBids,Fin.cons_zero] using (by linarith :
      0-equalPayoff ξ (patternTemplate c (fun j=>(ω j).1)).residual₀ 0 w (rowBids y ω)≤2*rowBids y ω 0)
  · have hh:=pure_patternPayoff_finite_loss c hξh ω le_rfl hw hy hω he
    have hloss : rowIntervalLoss c (1-ξ) 0 y ω=0:=by
      unfold rowIntervalLoss
      split_ifs <;> ring
    rw [hloss] at hh
    nlinarith [mul_nonneg hξ.le hy.le]

end FCAppendix.Affine.LowBody
