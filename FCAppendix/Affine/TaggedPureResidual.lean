import FCAppendix.Affine.TaggedLocalInformation
import FCAppendix.Affine.ResidualPotential

noncomputable section
namespace FCAppendix.Affine.TaggedLocal
open MeasureTheory Game Set
open scoped BigOperators

def otherUpper {m : ℕ} (d U : ℝ) (L : LocalList m) : ℕ :=
  m-localCount d U L 0-localCount d U L 1-localCount d U L 2

def ownResidual {m : ℕ} (c : ℕ) (d U : ℝ) (L : LocalList m) : ℕ :=
  c-localCount d U L 1-localCount d U L 2

def otherResidual {m : ℕ} (c : ℕ) (d U : ℝ) (L : LocalList m) : ℕ :=
  c-localCount d U L 1-otherUpper d U L

def residual₀ {m : ℕ} (c : ℕ) (d U : ℝ) (j : Fin 2) (L : LocalList m) : ℕ :=
  if j=0 then ownResidual c d U L else otherResidual c d U L

def residual₁ {m : ℕ} (c : ℕ) (d U : ℝ) (j : Fin 2) (L : LocalList m) : ℕ :=
  if j=0 then otherResidual c d U L else ownResidual c d U L

lemma measurable_otherUpper {m : ℕ} (d U : ℝ) :
    Measurable (otherUpper (m:=m) d U) :=
  ((measurable_const.sub (measurable_localCount d U 0)).sub
    (measurable_localCount d U 1)).sub (measurable_localCount d U 2)

lemma measurable_ownResidual {m : ℕ} (c : ℕ) (d U : ℝ) :
    Measurable (ownResidual (m:=m) c d U) :=
  (measurable_const.sub (measurable_localCount d U 1)).sub (measurable_localCount d U 2)

lemma measurable_otherResidual {m : ℕ} (c : ℕ) (d U : ℝ) :
    Measurable (otherResidual (m:=m) c d U) :=
  (measurable_const.sub (measurable_localCount d U 1)).sub (measurable_otherUpper d U)

lemma measurable_residual₀ {m : ℕ} (c : ℕ) (d U : ℝ) (j : Fin 2) :
    Measurable (residual₀ (m:=m) c d U j) := by
  unfold residual₀
  split
  · exact measurable_ownResidual c d U
  · exact measurable_otherResidual c d U

lemma measurable_residual₁ {m : ℕ} (c : ℕ) (d U : ℝ) (j : Fin 2) :
    Measurable (residual₁ (m:=m) c d U j) := by
  unfold residual₁
  split
  · exact measurable_otherResidual c d U
  · exact measurable_ownResidual c d U

lemma lowList_visible {m : ℕ} (d U : ℝ) (L : LocalList m) (i : Fin m)
    (hi : lowList d U L i≠none) : L i≠none := by
  unfold lowList at hi
  split at hi
  · exact hi
  · exact False.elim (hi rfl)

def pureLowPolicy {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (c : ℕ) (d U : ℝ)
    (j : Fin 2) : LocalPolicy m c Unit := fun L _ => by
  let P := ResidualPotential.selection κ (lowList d U L)
    (residual₀ c d U j L) (residual₁ c d U j L)
  have hf := ResidualPotential.selection_feasible κ hκ (lowList d U L)
    (residual₀ c d U j L) (residual₁ c d U j L)
  by_cases hj : j=0
  · refine ⟨P.1, ?_, ?_⟩
    · exact hf.1.1.trans (by simp [residual₀,hj,ownResidual]; omega)
    · exact fun i hi => lowList_visible d U L i (hf.1.2 i hi)
  · refine ⟨P.2, ?_, ?_⟩
    · exact hf.2.1.trans (by simp [residual₁,hj,ownResidual]; omega)
    · exact fun i hi => lowList_visible d U L i (hf.2.2 i hi)

lemma pureLowPolicy_val {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (c : ℕ) (d U : ℝ)
    (j : Fin 2) (L : LocalList m) (seed : Unit) :
    (pureLowPolicy κ hκ c d U j L seed).val =
      if j=0 then (ResidualPotential.selection κ (lowList d U L)
        (residual₀ c d U j L) (residual₁ c d U j L)).1
      else (ResidualPotential.selection κ (lowList d U L)
        (residual₀ c d U j L) (residual₁ c d U j L)).2 := by
  unfold pureLowPolicy
  split <;> simp_all

theorem measurable_pureLowPolicy {m : ℕ} (κ : ℝ) (hκ : 0≤κ)
    (c : ℕ) (d U : ℝ) (j : Fin 2) :
    Measurable (fun z : LocalList m × Unit => (pureLowPolicy κ hκ c d U j z.1 z.2).val) := by
  simp_rw [pureLowPolicy_val]
  have hm : Measurable (fun L : LocalList m => ResidualPotential.selection κ (lowList d U L)
      (residual₀ c d U j L) (residual₁ c d U j L)) :=
    ResidualPotential.measurable_selection measurable_const (measurable_lowList d U)
      (measurable_residual₀ c d U j) (measurable_residual₁ c d U j)
  by_cases hj : j=0
  · simpa only [hj,if_true,Function.comp_def] using (hm.fst.comp measurable_fst)
  · simpa only [hj,if_false,Function.comp_def] using (hm.snd.comp measurable_fst)

theorem residuals_observe {m : ℕ} (c : ℕ) (kind : Fin m→Fin 3) (x : Realization m 2)
    {d U : ℝ} (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x)
    (j : Fin 2) :
    residual₀ c d U j (observe x j)=c-countKind kind 1-upperAt kind x 0 ∧
    residual₁ c d U j (observe x j)=c-countKind kind 1-upperAt kind x 1 := by
  have hp := counts_partition kind x hr
  fin_cases j
  · obtain ⟨hl,ha,hh⟩ := local_counts_correct kind x hdU hb hr 0
    simp [residual₀,residual₁,ownResidual,otherResidual,otherUpper,hl,ha,hh]
    omega
  · obtain ⟨hl,ha,hh⟩ := local_counts_correct kind x hdU hb hr 1
    simp [residual₀,residual₁,ownResidual,otherResidual,otherUpper,hl,ha,hh]
    omega

theorem pureLowPolicy_observe {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (c : ℕ)
    (kind : Fin m→Fin 3) (x : Realization m 2) {d U : ℝ}
    (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x)
    (j : Fin 2) (seed : Unit) :
    (pureLowPolicy κ hκ c d U j (observe x j) seed).val =
      let P := ResidualPotential.selection κ
        (fun i => if kind i=0 then some (x.action i).bid else none)
        (c-countKind kind 1-upperAt kind x 0) (c-countKind kind 1-upperAt kind x 1)
      if j=0 then P.1 else P.2 := by
  obtain ⟨h₀,h₁⟩ := residuals_observe c kind x hdU hb hr j
  rw [pureLowPolicy_val,lowList_observe kind x hdU hb hr,h₀,h₁]

lemma low_revenue_eq_realized {m : ℕ} (κ : ℝ) (kind : Fin m→Fin 3)
    (x : Realization m 2) (r : ℕ) (S T : Finset (Fin m))
    (hS : LocallyFeasible (fun i => if kind i=0 then some (x.action i).bid else none) r S) :
    LowBody.CompleteInformation.revenue κ
      (ResidualPotential.bid (fun i => if kind i=0 then some (x.action i).bid else none)) S T =
      LowBody.CompleteInformation.revenue κ (fun i => (x.action i).bid) S T := by
  unfold LowBody.CompleteInformation.revenue
  apply Finset.sum_congr rfl
  intro i hi
  have hk : kind i=0 := by
    by_contra hn
    exact hS.2 i hi (by simp [hn])
  have hbid : ResidualPotential.bid
      (fun i => if kind i=0 then some (x.action i).bid else none) i=(x.action i).bid := by
    simp [ResidualPotential.bid,hk,Bayes.entryBid,max_eq_left (x.action i).bid_nonneg]
  rw [hbid]

theorem pureLowPolicy_nash {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (c : ℕ)
    (kind : Fin m→Fin 3) (x : Realization m 2) {d U : ℝ}
    (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) :
    let L : LocalList m := fun i => if kind i=0 then some (x.action i).bid else none
    let S₀ := (pureLowPolicy κ hκ c d U 0 (observe x 0) ()).val
    let S₁ := (pureLowPolicy κ hκ c d U 1 (observe x 1) ()).val
    (∀ S, LocallyFeasible L (c-countKind kind 1-upperAt kind x 0) S →
      LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) S S₁ ≤
        LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) S₀ S₁) ∧
    (∀ T, LocallyFeasible L (c-countKind kind 1-upperAt kind x 1) T →
      LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) T S₀ ≤
        LowBody.CompleteInformation.revenue κ (ResidualPotential.bid L) S₁ S₀) := by
  dsimp only
  rw [pureLowPolicy_observe κ hκ c kind x hdU hb hr 0 (),
    pureLowPolicy_observe κ hκ c kind x hdU hb hr 1 ()]
  simpa only [Fin.isValue,ite_true,Fin.reduceEq,ite_false] using
    ResidualPotential.selection_nash κ hκ
      (fun i => if kind i=0 then some (x.action i).bid else none)
      (c-countKind kind 1-upperAt kind x 0) (c-countKind kind 1-upperAt kind x 1)

theorem pureLowPolicy_nash_realized {m : ℕ} (κ : ℝ) (hκ : 0≤κ) (c : ℕ)
    (kind : Fin m→Fin 3) (x : Realization m 2) {d U : ℝ}
    (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) :
    let L : LocalList m := fun i => if kind i=0 then some (x.action i).bid else none
    let S₀ := (pureLowPolicy κ hκ c d U 0 (observe x 0) ()).val
    let S₁ := (pureLowPolicy κ hκ c d U 1 (observe x 1) ()).val
    (∀ S, LocallyFeasible L (c-countKind kind 1-upperAt kind x 0) S →
      LowBody.CompleteInformation.revenue κ (fun i => (x.action i).bid) S S₁ ≤
        LowBody.CompleteInformation.revenue κ (fun i => (x.action i).bid) S₀ S₁) ∧
    (∀ T, LocallyFeasible L (c-countKind kind 1-upperAt kind x 1) T →
      LowBody.CompleteInformation.revenue κ (fun i => (x.action i).bid) T S₀ ≤
        LowBody.CompleteInformation.revenue κ (fun i => (x.action i).bid) S₁ S₀) := by
  dsimp only
  rw [pureLowPolicy_observe κ hκ c kind x hdU hb hr 0 (),
    pureLowPolicy_observe κ hκ c kind x hdU hb hr 1 ()]
  simp only [Fin.isValue,ite_true,Fin.reduceEq,ite_false]
  have hf := ResidualPotential.selection_feasible κ hκ
    (fun i => if kind i=0 then some (x.action i).bid else none)
    (c-countKind kind 1-upperAt kind x 0) (c-countKind kind 1-upperAt kind x 1)
  have hm := ResidualPotential.selection_nash κ hκ
    (fun i => if kind i=0 then some (x.action i).bid else none)
    (c-countKind kind 1-upperAt kind x 0) (c-countKind kind 1-upperAt kind x 1)
  constructor
  · intro S hS
    have hh := hm.1 S hS
    rwa [low_revenue_eq_realized κ kind x _ S _ hS,
      low_revenue_eq_realized κ kind x _ _ _ hf.1] at hh
  · intro T hT
    have hh := hm.2 T hT
    rwa [low_revenue_eq_realized κ kind x _ T _ hT,
      low_revenue_eq_realized κ kind x _ _ _ hf.2] at hh

end FCAppendix.Affine.TaggedLocal
