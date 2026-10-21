import FCAppendix.Affine.LowBody.NoisyExpectedLoss
import FCAppendix.Affine.LowBody.ClusterLossBound

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
open scoped BigOperators
variable {d : ℝ}

lemma lowRowProfile_nonnegative (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] (N : ℕ) :
    ∀ᵐω ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw mu)),
      ∀j,(ω j).1=0 → 0 ≤ (ω j).2 := by
  let F : (Fin N→Fin 4)×(Fin N→LowValue d)→Fin N→RowRival:=
    fun p j=>lowRowPoint (p.1 j,p.2 j)
  have hm : Measurable F:=measurable_pi_lambda _ (fun j=>
    measurable_lowRowPoint.comp (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))
  have hE : MeasurableSet {ω : Fin N→RowRival | ∀j,(ω j).1=0 → 0 ≤ (ω j).2} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro j
    have hmj : Measurable (fun ω : Fin N→RowRival=>ω j):=measurable_pi_apply j
    have hzero : MeasurableSet {ω : Fin N→RowRival | (ω j).1=0}:=
      measurableSet_eq_fun hmj.fst measurable_const
    have hnonneg : MeasurableSet {ω : Fin N→RowRival | 0≤(ω j).2}:=
      measurableSet_le measurable_const hmj.snd
    have heq : {ω : Fin N→RowRival | (ω j).1=0 → 0≤(ω j).2}=
        {ω : Fin N→RowRival | (ω j).1=0}ᶜ∪{ω : Fin N→RowRival | 0≤(ω j).2}:=by
      ext ω
      simp only [mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or]
    rw [heq]
    exact hzero.compl.union hnonneg
  rw [←lowRowProfile_law s a h hs ha hh hsum mu N]
  apply (ae_map_iff hm.aemeasurable hE).mpr
  apply ae_of_all
  intro p j hj
  change p.1 j=0 at hj
  simpa only [F,lowRowPoint,if_pos hj] using (p.2 j).property.1

lemma rowIntervalLoss_le_cluster_indicator {N : ℕ} (c : ℕ) {κ x U : ℝ}
    (hκ : 1/2 ≤ κ) (hx : 0 ≤ x) (hxU : x ≤ U) (y : ℝ)
    (B C : Set ℝ) (hB : Icc x y⊆B) (hC : Icc (κ*x) (κ*y)⊆C)
    (ω : Fin (N+1)→RowRival) :
    rowIntervalLoss c κ x y ω ≤ (harmfulCluster c (B∪C)).indicator (fun _=>(2*κ-1)*U) ω := by
  classical
  have hc : 0 ≤ (2*κ-1)*U:=mul_nonneg (by linarith) (hx.trans hxU)
  by_cases he : rowHarmfulInterval c κ x y ω
  · have hm : ω∈harmfulCluster c (B∪C) := by
      obtain ⟨hu,j,hj,hbid⟩:=he
      refine ⟨hu,j,hj,?_⟩
      exact hbid.elim (fun hh=>Or.inl (hB hh)) (fun hh=>Or.inr (hC hh))
    rw [Set.indicator_of_mem hm]
    simp only [rowIntervalLoss,if_pos he]
    exact mul_le_mul_of_nonneg_left hxU (by linarith)
  · rw [rowIntervalLoss,if_neg he]
    exact Set.indicator_nonneg (fun _ _=>hc) _

theorem expected_patternPayoff_uniform_raise {N : ℕ} {ξ l U W : ℝ}
    (hξ : 0<ξ) (hξh : ξ ≤ 1/2) (hl : 0<l) (hlU : l ≤ U) (hW : 0 ≤ W)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    ∀ε>0,∃δ>0,∀(c : ℕ)(w x y : ℝ)(B C : Set ℝ),
      MeasurableSet B→MeasurableSet C→Icc x y⊆B→Icc ((1-ξ)*x) ((1-ξ)*y)⊆C→
      |w| ≤ W→l ≤ x→x ≤ U→x ≤ w→x<y→y-x<δ→
      (∫ω : Fin (N+1)→RowRival,literalRowPayoff ξ c w (x,ω)-literalRowPayoff ξ c w (y,ω)
        ∂Measure.pi (fun _ : Fin (N+1)=>rivalLaw s a h (realLowLaw mu))) ≤
      ((2*(1-ξ)-1)*U)*(N+1:ℕ)*s*((realLowLaw mu).real B+(realLowLaw mu).real C)*
        (CommonList.iid (categoryLaw s a h hs ha hh hsum (realLowLaw mu)) N).prob (BothUnderflow c)+
        2*(1-ξ)*(y-x)+ε := by
  classical
  intro ε hε
  obtain ⟨δ,hδ,hpoint⟩:=patternPayoff_uniform_raise (N:=N+1) hξ hξh hl hlU hW ε hε
  refine ⟨δ,hδ,?_⟩
  intro c w x y B C hB hC hcoverB hcoverC hw hlx hxU hxw hxy hdist
  let ν:=Measure.pi (fun _ : Fin (N+1)=>rivalLaw s a h (realLowLaw mu))
  let cost:=(2*(1-ξ)-1)*U
  have hκ : 1/2 ≤ 1-ξ:=by linarith
  have hx : 0 ≤ x:=(hl.trans_le hlx).le
  have hcost : 0 ≤ cost:=mul_nonneg (by linarith) (hl.le.trans hlU)
  letI : IsProbabilityMeasure (rivalLaw s a h (realLowLaw mu)):=
    rivalLaw_isProbability s a h hs ha hh hsum (realLowLaw mu)
  have hmeasX : Measurable (fun ω : Fin (N+1)→RowRival=>literalRowPayoff ξ c w (x,ω)):=
    (measurable_literalRowPayoff hξ (by linarith) c w).comp (measurable_const.prodMk measurable_id)
  have hmeasY : Measurable (fun ω : Fin (N+1)→RowRival=>literalRowPayoff ξ c w (y,ω)):=
    (measurable_literalRowPayoff hξ (by linarith) c w).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun ω=>literalRowPayoff ξ c w (x,ω)-literalRowPayoff ξ c w (y,ω)) ν := by
    apply Integrable.of_bound (hmeasX.sub hmeasY).aestronglyMeasurable
      ((|w|+(3+2*|1-ξ|)*|x|)+(|w|+(3+2*|1-ξ|)*|y|))
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add
      (abs_literalRowPayoff_le hξ (by linarith) c w x ω)
      (abs_literalRowPayoff_le hξ (by linarith) c w y ω))
  have hms := measurableSet_harmfulCluster_set (N:=N) c (B∪C) (hB.union hC)
  have hind : Integrable ((harmfulCluster c (B∪C)).indicator (fun _=>cost)) ν :=
    (integrable_const cost).indicator hms
  have hbound := integral_mono_ae hi (hind.add (integrable_const (2*(1-ξ)*(y-x)+ε))) (by
    filter_upwards [lowRowProfile_nonnegative s a h hs ha hh hsum mu (N+1)] with ω hω
    have hp:=hpoint c ω w x y hω hw hlx hxU hxw hxy hdist
    have he:=rowIntervalLoss_le_cluster_indicator c hκ hx hxU y B C hcoverB hcoverC ω
    change _ ≤ (harmfulCluster c (B∪C)).indicator (fun _=>cost) ω+_
    unfold literalRowPayoff
    dsimp only
    dsimp only [cost] at *
    linarith)
  simp only [Pi.add_apply] at hbound
  rw [integral_add hind (integrable_const _),integral_const,probReal_univ,smul_eq_mul,one_mul] at hbound
  have hevent:=expected_two_cluster_loss s a h hs ha hh hsum (realLowLaw mu) (N:=N) c B C hB hC cost hcost
  exact hbound.trans (by dsimp only [ν] at *;dsimp only [cost] at *;linarith)

end FCAppendix.Affine.LowBody
