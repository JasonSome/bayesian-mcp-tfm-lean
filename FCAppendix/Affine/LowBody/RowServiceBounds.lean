import FCAppendix.Affine.LowBody.NoisyRow

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace PureTemplate

theorem selection_contains_left (T : PureTemplate ι) {κ : ℝ} (hκ : 0<κ)
    (b : ι→ℝ) (i : ι) (hi : i∈T.support) (hbi : 0<b i)
    (hc : T.support.card≤T.residual₀) : i∈(T.selection κ b).1 := by
  classical
  have hf:=T.selection_feasible κ b
  by_contra hn
  have hs : insert i (T.selection κ b).1⊆T.support:=Finset.insert_subset hi hf.2.1
  have hcard : (insert i (T.selection κ b).1).card≤T.residual₀:=
    (Finset.card_le_card hs).trans hc
  have hm:=(T.selection_nash κ b).1 _ hcard hs
  unfold CompleteInformation.revenue at hm
  rw [Finset.sum_insert hn] at hm
  have hpos : 0<(if i∈(T.selection κ b).2 then κ*b i else b i) := by
    split <;> first | exact mul_pos hκ hbi | exact hbi
  linarith

theorem selection_contains_right (T : PureTemplate ι) {κ : ℝ} (hκ : 0<κ)
    (b : ι→ℝ) (i : ι) (hi : i∈T.support) (hbi : 0<b i)
    (hc : T.support.card≤T.residual₁) : i∈(T.selection κ b).2 := by
  classical
  have hf:=T.selection_feasible κ b
  by_contra hn
  have hs : insert i (T.selection κ b).2⊆T.support:=Finset.insert_subset hi hf.2.2.2
  have hcard : (insert i (T.selection κ b).2).card≤T.residual₁:=
    (Finset.card_le_card hs).trans hc
  have hm:=(T.selection_nash κ b).2 _ hcard hs
  unfold CompleteInformation.revenue at hm
  rw [Finset.sum_insert hn] at hm
  have hpos : 0<(if i∈(T.selection κ b).1 then κ*b i else b i) := by
    split <;> first | exact mul_pos hκ hbi | exact hbi
  linarith

theorem selection_empty_left (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ)
    (hc : T.residual₀=0) : (T.selection κ b).1=∅ := by
  apply Finset.card_eq_zero.mp
  have hf:=T.selection_feasible κ b
  have hh:=(hf.1)
  rw [hc] at hh
  exact Nat.eq_zero_of_le_zero hh

theorem selection_empty_right (T : PureTemplate ι) (κ : ℝ) (b : ι→ℝ)
    (hc : T.residual₁=0) : (T.selection κ b).2=∅ := by
  apply Finset.card_eq_zero.mp
  have hf:=T.selection_feasible κ b
  have hh:=hf.2.2.1
  rw [hc] at hh
  exact Nat.eq_zero_of_le_zero hh

end PureTemplate

omit [Fintype ι] in
theorem purePayoff_le_value_sub_bid {κ w : ℝ} (hκ : 1/2≤κ)
    (b : ι→ℝ) (P : Finset ι × Finset ι) (i : ι) (hb : 0≤b i) (hbw : b i≤w) :
    purePayoff κ w b P i≤w-b i := by
  unfold purePayoff
  split_ifs <;> nlinarith

theorem equalPayoff_le_value_sub_bid {ξ w : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (i : ι) (b : ι→ℝ) (hb : 0≤b i) (hbw : b i≤w) :
    equalPayoff ξ c i w b≤w-b i := by
  have hξ1 : ξ<1:=by linarith
  have hp:=EqualCapacity.positiveMarginal_spec ξ c hξ hξ1 b
  let p:=EqualCapacity.positiveMarginal ξ c b i
  have hp0 : 0≤p:=hp.1 i
  have hp1 : p≤1:=hp.2.1 i
  have hs : 2*p-p^2≤1:=by nlinarith [sq_nonneg (p-1)]
  have hcost : 0≤(1-2*ξ)*b i*p^2 :=
    mul_nonneg (mul_nonneg (by linarith) hb) (sq_nonneg p)
  have hu:=mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hbw)
  change w*(2*p-p^2)-b i*(2*p-2*ξ*p^2)≤_
  nlinarith

theorem positiveMarginal_one_of_underloaded {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : ι→ℝ) (hc : (Existence.PayOnceBounded.positiveSupport b).card≤c)
    (i : ι) (hi : 0<b i) : EqualCapacity.positiveMarginal ξ c b i=1 := by
  let S:=Existence.PayOnceBounded.positiveSupport b
  have him : i∈S:=(Existence.PayOnceBounded.mem_positiveSupport b i).mpr hi
  have hpos : ∀j : S,0<b j.1:=fun j=>(Existence.PayOnceBounded.mem_positiveSupport b j.1).mp j.2
  have hk:=EqualCapacity.kernel_underloaded hξ hξ1 c (fun j : S=>b j.1) hpos (by simpa using hc)
  change EqualCapacity.onSupport ξ c S b i=1
  unfold EqualCapacity.onSupport
  rw [dif_pos him,hk]

theorem positiveMarginal_zero_capacity {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (b : ι→ℝ) (i : ι) : EqualCapacity.positiveMarginal ξ 0 b i=0 := by
  have hp:=EqualCapacity.positiveMarginal_spec ξ 0 hξ hξ1 b
  have hs:=Finset.single_le_sum (fun j _=>hp.1 j) (Finset.mem_univ i)
  rw [hp.2.2] at hs
  exact le_antisymm (by simpa only [Nat.zero_min,Nat.cast_zero] using hs) (hp.1 i)

section Patterns
variable {N : ℕ}

theorem patternTemplate_card (c : ℕ) (kind : Fin N→Fin 4) :
    (patternTemplate c kind).support.card=1+classCount 0 (patternRow kind) := by
  have hh:=rowLowList_card (0:ℝ) (patternRow kind)
  simpa only [patternTemplate,Option.isSome_iff_ne_none] using hh

theorem focal_mem_patternTemplate (c : ℕ) (kind : Fin N→Fin 4) :
    (0:Fin (N+1))∈(patternTemplate c kind).support := by
  simp [patternTemplate,rowLowList]

def LocalUnderflow (c : ℕ) (j : Fin 2) (kind : Fin N→Fin 4) : Prop :=
  classCount 0 (patternRow kind)+classCount 1 (patternRow kind)+
    classCount ⟨2+j.val,by omega⟩ (patternRow kind)<c

theorem pattern_residual_full_of_localUnderflow (c : ℕ) (j : Fin 2)
    (kind : Fin N→Fin 4) (hu : LocalUnderflow c j kind) :
    rowResidual c j (patternRow kind)=(patternTemplate c kind).support.card := by
  rw [patternTemplate_card]
  unfold rowResidual LocalUnderflow at *
  apply Nat.min_eq_left
  omega

end Patterns

end FCAppendix.Affine.LowBody
