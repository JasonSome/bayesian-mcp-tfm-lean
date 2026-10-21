import FCAppendix.Affine.Hybrid.UpperCountBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def fullCategoryCount {r N : ℕ} (fixed : Fin r→Fin 4) (row : Fin N→Fin 4) (k : Fin 4) : ℕ:=
  categoryCount k fixed+categoryCount k row

def activeResidual (c A H : ℕ) : ℕ:=min A (c-H)

theorem active_residuals_interior_of_close {M c A H₀ H₁ : ℕ} {ρ a h δ : ℝ}
    (hM : 0 < M) (hcap : |(c:ℝ)-(M:ℝ)*ρ| ≤ M*δ)
    (hactive : |(A:ℝ)-(M:ℝ)*a| ≤ M*δ)
    (hupper₀ : |(H₀:ℝ)-(M:ℝ)*(h/2)| ≤ M*δ)
    (hupper₁ : |(H₁:ℝ)-(M:ℝ)*(h/2)| ≤ M*δ)
    (hlower : 2*δ<ρ-h/2) (hupper : 3*δ<a+h/2-ρ) :
    H₀<c ∧ H₁<c ∧ c<H₀+A ∧ c<H₁+A ∧
      activeResidual c A H₀=c-H₀ ∧ activeResidual c A H₁=c-H₁ ∧
      (activeResidual c A H₀=activeResidual c A H₁↔H₀=H₁) := by
  have hm : (0:ℝ)<M:=Nat.cast_pos.mpr hM
  have hc:=abs_le.mp hcap
  have ha:=abs_le.mp hactive
  have hh₀:=abs_le.mp hupper₀
  have hh₁:=abs_le.mp hupper₁
  have hlo:=mul_lt_mul_of_pos_left hlower hm
  have hhi:=mul_lt_mul_of_pos_left hupper hm
  have h₀ : H₀<c:=by exact_mod_cast (show (H₀:ℝ)<c by nlinarith)
  have h₁ : H₁<c:=by exact_mod_cast (show (H₁:ℝ)<c by nlinarith)
  have hA₀ : c<H₀+A:=by exact_mod_cast (show (c:ℝ)<H₀+A by nlinarith)
  have hA₁ : c<H₁+A:=by exact_mod_cast (show (c:ℝ)<H₁+A by nlinarith)
  have hr₀ : activeResidual c A H₀=c-H₀:=min_eq_right (by omega)
  have hr₁ : activeResidual c A H₁=c-H₁:=min_eq_right (by omega)
  refine ⟨h₀,h₁,hA₀,hA₁,hr₀,hr₁,?_⟩
  rw [hr₀,hr₁]
  omega

lemma upperDifference_eq_counts {N : ℕ} (row : Fin N→Fin 4) :
    upperDifference row=(categoryCount 2 row:ℤ)-(categoryCount 3 row:ℤ) := by
  unfold upperDifference categoryCount hitCount
  push_cast
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  generalize hk : row i=k
  fin_cases k <;> norm_num [upperStep,Fin.ext_iff]

lemma full_upper_counts_equal_iff {r N : ℕ} (fixed : Fin r→Fin 4) (row : Fin N→Fin 4) :
    fullCategoryCount fixed row 2=fullCategoryCount fixed row 3↔
      upperDifference fixed+upperDifference row=0 := by
  rw [upperDifference_eq_counts,upperDifference_eq_counts]
  unfold fullCategoryCount
  omega

theorem equal_activeResidual_probability_le {r : ℕ} {ρ a h δ : ℝ}
    (s : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 < h) (hh1 : h ≤ 1) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (fixed : Fin r→Fin 4)
    (N c : ℕ) (hN : 0 < N) (hδ : 0 ≤ δ) (hroom : (r:ℝ) ≤ N*δ/2)
    (hcap : |(c:ℝ)-(N+r:ℕ)*ρ| ≤ (N+r:ℕ)*δ)
    (hlower : 2*δ<ρ-h/2) (hupper : 3*δ<a+h/2-ρ) :
    (CommonList.iid (categoryLaw s a h hs ha hh.le hsum G) N).prob (fun row=>
      activeResidual c (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 2)=
      activeResidual c (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 3)) ≤
      8*Real.exp (-(N:ℝ)*δ^2/2)+
        (4*(1-h)/((N:ℝ)*h)+Real.sqrt (2/((N:ℝ)*h/2+1))) := by
  let C:=categoryLaw s a h hs ha hh.le hsum G
  let Bad : (Fin N→Fin 4)→Prop:=fun row=>∃k : Fin 4,
    (N+r:ℕ)*δ ≤ |(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-(N+r:ℕ)*C.mass k|
  have hsub:= (CommonList.iid C N).prob_mono (E:=fun row=>
      activeResidual c (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 2)=
      activeResidual c (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 3))
    (F:=fun row=>Bad row ∨ upperDifference fixed+upperDifference row=0) (by
      intro row heq
      by_cases hb : Bad row
      · exact Or.inl hb
      · right
        have hgood (k : Fin 4) :
            |(fullCategoryCount fixed row k:ℝ)-(N+r:ℕ)*C.mass k| ≤ (N+r:ℕ)*δ:=by
          have hk : ¬(N+r:ℕ)*δ ≤
              |(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-(N+r:ℕ)*C.mass k|:=
            fun hk=>hb ⟨k,hk⟩
          simpa only [fullCategoryCount,Nat.cast_add] using (lt_of_not_ge hk).le
        have hA:=hgood 1
        have hH₀:=hgood 2
        have hH₁:=hgood 3
        simp only [C,categoryLaw_mass,Fin.isValue] at hA hH₀ hH₁
        have hi:=active_residuals_interior_of_close (M:=N+r) (by omega) hcap hA hH₀ hH₁ hlower hupper
        exact (full_upper_counts_equal_iff fixed row).mp (hi.2.2.2.2.2.2.mp heq))
  have hu:=(CommonList.iid C N).prob_union_le Bad
    (fun row=>upperDifference fixed+upperDifference row=0)
  have hbad:=forced_fractional_count_exception_le C fixed N hδ hroom
  have htie:=forced_upperDifference_probability_le s a h hs ha hh hh1 hsum G fixed N hN 0
  exact hsub.trans (hu.trans (add_le_add hbad htie))

end FCAppendix.Affine.Hybrid
