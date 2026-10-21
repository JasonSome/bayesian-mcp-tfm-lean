import FCAppendix.Affine.Hybrid.TypicalCounts

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def countExceptionError (h δ : ℝ) (N : ℕ) : ℝ:=
  8*Real.exp (-(N:ℝ)*δ^2/2)+upperTieError h N

theorem countExceptionError_tendsto_zero {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) :
    Tendsto (countExceptionError h δ) atTop (𝓝 0) := by
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ=>Real.exp (-(N:ℝ)*δ^2/2)) atTop (𝓝 0) := by
    have hc : 0 < δ^2/2:=by positivity
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hNat.const_mul_atTop hc) using 1
    funext N
    congr 1
    ring
  change Tendsto (fun N : ℕ=>8*Real.exp (-(N:ℝ)*δ^2/2)+upperTieError h N) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using (he.const_mul 8).add (upperTieError_tendsto_zero hh)

theorem exists_eventual_source_count_bounds (s a h ρ : ℝ)
    (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s+a+h=1)
    (hlower : h/2<ρ) (hupper : ρ<a+h/2)
    (c : ℕ→ℕ) (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ)) :
    ∃δ : ℝ,0 < δ ∧ δ<s ∧ 2*δ<ρ-h/2 ∧ 3*δ<a+h/2-ρ ∧
      ∀r : ℕ,∀ᶠN : ℕ in atTop,
        ∀(G : Measure ℝ)(_hG : IsProbabilityMeasure G)(fixed : Fin r→Fin 4),
          let C:=categoryLaw s a h hs.le ha hh.le hsum G
          (CommonList.iid C N).prob (fun row=>∃k : Fin 4,
            (N+r:ℕ)*δ ≤ |(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-(N+r:ℕ)*C.mass k|) ≤
              8*Real.exp (-(N:ℝ)*δ^2/2) ∧
          (CommonList.iid C N).prob (fun row=>
            activeResidual (c (N+r)) (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 2)=
            activeResidual (c (N+r)) (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 3)) ≤
              countExceptionError h δ N := by
  let δ:=min ((ρ-h/2)/4) (min ((a+h/2-ρ)/6) (s/2))
  have hδ : 0 < δ:=lt_min (by linarith) (lt_min (by linarith) (half_pos hs))
  have hδlo : δ ≤ (ρ-h/2)/4:=min_le_left _ _
  have hδhi : δ ≤ (a+h/2-ρ)/6:=(min_le_right _ _).trans (min_le_left _ _)
  have hδs : δ ≤ s/2:=(min_le_right _ _).trans (min_le_right _ _)
  have hδlower : 2*δ<ρ-h/2:=by linarith
  have hδupper : 3*δ<a+h/2-ρ:=by linarith
  have hh1 : h ≤ 1:=by linarith [hs.le]
  refine ⟨δ,hδ,by linarith,hδlower,hδupper,?_⟩
  intro r
  have hcap:=hc.comp (tendsto_add_atTop_nat r)
  have hcapClose : ∀ᶠN : ℕ in atTop,|(c (N+r):ℝ)/(N+r:ℕ)-ρ|<δ:=by
    simpa only [Real.dist_eq,Function.comp_def] using (Metric.tendsto_nhds.mp hcap) δ hδ
  have hNat : Tendsto (fun N : ℕ=>(N:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have hprefixGrow : Tendsto (fun N : ℕ=>(N:ℝ)*δ/2) atTop atTop := by
    convert hNat.const_mul_atTop (half_pos hδ) using 1
    funext N
    ring
  have hprefix : ∀ᶠN : ℕ in atTop,(r:ℝ) ≤ (N:ℝ)*δ/2:=
    hprefixGrow.eventually (eventually_ge_atTop (r:ℝ))
  filter_upwards [hcapClose,hprefix,eventually_gt_atTop (0:ℕ)] with N hcapN hprefixN hN
  intro G hG fixed
  letI:=hG
  have hM : (0:ℝ)<(N+r:ℕ):=Nat.cast_pos.mpr (by omega)
  have hscaled : |(c (N+r):ℝ)-(N+r:ℕ)*ρ| ≤ (N+r:ℕ)*δ := by
    have he : (c (N+r):ℝ)/(N+r:ℕ)-ρ=
        ((c (N+r):ℝ)-(N+r:ℕ)*ρ)/(N+r:ℕ):=by field_simp
    rw [he,abs_div,abs_of_pos hM] at hcapN
    have hx:=(div_lt_iff₀ hM).mp hcapN
    linarith
  refine ⟨forced_fractional_count_exception_le _ fixed N hδ.le hprefixN,?_⟩
  exact equal_activeResidual_probability_le s hs.le ha hh hh1 hsum G fixed N (c (N+r)) hN
    hδ.le hprefixN hscaled hδlower hδupper

theorem source_equal_activeResidual_tendsto_zero (s a h ρ : ℝ)
    (hs : 0 < s) (ha : 0 ≤ a) (hh : 0 < h) (hsum : s+a+h=1)
    (hlower : h/2<ρ) (hupper : ρ<a+h/2)
    (c : ℕ→ℕ) (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (r : ℕ) (G : Measure ℝ) [IsProbabilityMeasure G] (fixed : Fin r→Fin 4) :
    Tendsto (fun N : ℕ=>(CommonList.iid (categoryLaw s a h hs.le ha hh.le hsum G) N).prob
      (fun row=>activeResidual (c (N+r)) (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 2)=
        activeResidual (c (N+r)) (fullCategoryCount fixed row 1) (fullCategoryCount fixed row 3)))
      atTop (𝓝 0) := by
  obtain ⟨δ,hδ,_hδs,_hδlo,_hδhi,hbounds⟩:=
    exists_eventual_source_count_bounds s a h ρ hs ha hh hsum hlower hupper c hc
  apply squeeze_zero' (Eventually.of_forall (fun _=>FiniteLaw.prob_nonneg _ _))
    ((hbounds r).mono (fun N hN=>(hN G inferInstance fixed).2))
    (countExceptionError_tendsto_zero hh hδ)

end FCAppendix.Affine.Hybrid
