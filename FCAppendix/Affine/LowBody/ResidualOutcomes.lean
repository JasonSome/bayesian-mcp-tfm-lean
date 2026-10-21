import FCAppendix.Affine.LowBody.RowServiceBounds
import FCAppendix.Affine.LowBody.CategoricalTails

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pureServed (P : Finset ι × Finset ι) (i : ι) : ℝ :=
  if i∈P.1 ∨ i∈P.2 then 1 else 0

def pureDuplicate (P : Finset ι × Finset ι) (i : ι) : ℝ :=
  if i∈P.1 ∧ i∈P.2 then 1 else 0

omit [Fintype ι] in
theorem purePayoff_outcomes (ξ w : ℝ) (b : ι→ℝ) (P : Finset ι × Finset ι) (i : ι) :
    purePayoff (1-ξ) w b P i=
      (w-b i)*pureServed P i-(1-2*ξ)*b i*pureDuplicate P i := by
  by_cases h₀ : i∈P.1
  · by_cases h₁ : i∈P.2
    · simp [purePayoff,focalCopy,pureServed,pureDuplicate,h₀,h₁]
      ring
    · simp [purePayoff,focalCopy,pureServed,pureDuplicate,h₀,h₁]
  · by_cases h₁ : i∈P.2
    · simp [purePayoff,focalCopy,pureServed,pureDuplicate,h₀,h₁]
    · simp [purePayoff,focalCopy,pureServed,pureDuplicate,h₀,h₁]

section Patterns
variable {N : ℕ}

def patternServed (ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ) : ℝ :=
  let T:=patternTemplate c kind
  if T.residual₀=T.residual₁ then
    let p:=EqualCapacity.positiveMarginal ξ T.residual₀ b 0
    2*p-p^2
  else pureServed (T.selection (1-ξ) b) 0

def patternDuplicate (ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ) : ℝ :=
  let T:=patternTemplate c kind
  if T.residual₀=T.residual₁ then
    (EqualCapacity.positiveMarginal ξ T.residual₀ b 0)^2
  else pureDuplicate (T.selection (1-ξ) b) 0

def patternPayoff (ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (w : ℝ)
    (b : Fin (N+1)→ℝ) : ℝ :=
  let T:=patternTemplate c kind
  if T.residual₀=T.residual₁ then equalPayoff ξ T.residual₀ 0 w b
  else purePayoff (1-ξ) w b (T.selection (1-ξ) b) 0

theorem patternPayoff_outcomes (ξ : ℝ) (c : ℕ) (kind : Fin N→Fin 4) (w : ℝ)
    (b : Fin (N+1)→ℝ) : patternPayoff ξ c kind w b=
      (w-b 0)*patternServed ξ c kind b-(1-2*ξ)*b 0*patternDuplicate ξ c kind b := by
  unfold patternPayoff patternServed patternDuplicate
  dsimp only
  split_ifs
  · unfold equalPayoff
    ring
  · exact purePayoff_outcomes ξ w b _ 0

theorem pattern_outcomes_bounds {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ) :
    0≤patternServed ξ c kind b ∧ patternServed ξ c kind b≤1 ∧
    0≤patternDuplicate ξ c kind b ∧ patternDuplicate ξ c kind b≤1 := by
  unfold patternServed patternDuplicate
  dsimp only
  split_ifs
  · have hp:=EqualCapacity.positiveMarginal_spec ξ (patternTemplate c kind).residual₀ hξ hξ1 b
    have hp0:=hp.1 0
    have hp1:=hp.2.1 0
    refine ⟨by nlinarith,by nlinarith [sq_nonneg (EqualCapacity.positiveMarginal ξ
      (patternTemplate c kind).residual₀ b 0-1)],sq_nonneg _,by nlinarith⟩
  · unfold pureServed pureDuplicate
    split_ifs <;> norm_num

theorem patternServed_one_of_underflow {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ)
    (hb : 0<b 0) (hmask : ∀i,i∉(patternTemplate c kind).support→b i=0)
    (j : Fin 2) (hu : LocalUnderflow c j kind) : patternServed ξ c kind b=1 := by
  classical
  let T:=patternTemplate c kind
  have hfull : rowResidual c j (patternRow kind)=T.support.card :=
    pattern_residual_full_of_localUnderflow c j kind hu
  have hi : (0:Fin (N+1))∈T.support:=focal_mem_patternTemplate c kind
  unfold patternServed
  dsimp only
  split_ifs with heq
  · have hc : (Existence.PayOnceBounded.positiveSupport b).card≤T.residual₀ := by
      have hh : Existence.PayOnceBounded.positiveSupport b⊆T.support := by
        intro i hip
        by_contra hn
        have hp:=(Existence.PayOnceBounded.mem_positiveSupport b i).mp hip
        rw [hmask i hn] at hp
        exact lt_irrefl 0 hp
      have hj : rowResidual c j (patternRow kind)=T.residual₀ := by
        fin_cases j
        · rfl
        · exact heq.symm
      rw [hj] at hfull
      exact (Finset.card_le_card hh).trans hfull.ge
    rw [positiveMarginal_one_of_underloaded hξ hξ1 T.residual₀ b hc 0 hb]
    norm_num
  · unfold pureServed
    apply if_pos
    fin_cases j
    · exact Or.inl (T.selection_contains_left (by linarith : 0<1-ξ) b 0 hi hb hfull.ge)
    · exact Or.inr (T.selection_contains_right (by linarith : 0<1-ξ) b 0 hi hb hfull.ge)

theorem sum_firstHigher (kind : Fin N→Fin 4) :
    (∑i,firstHigher (kind i))=classCount 1 (patternRow kind)+classCount 2 (patternRow kind) := by
  unfold classCount patternRow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∀k : Fin 4,firstHigher k=(if k=1 then 1 else 0)+(if k=2 then 1 else 0) := by
    intro k; fin_cases k <;> norm_num [firstHigher,Fin.ext_iff]
  exact h (kind i)

theorem sum_secondHigher (kind : Fin N→Fin 4) :
    (∑i,secondHigher (kind i))=classCount 1 (patternRow kind)+classCount 3 (patternRow kind) := by
  unfold classCount patternRow
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h : ∀k : Fin 4,secondHigher k=(if k=1 then 1 else 0)+(if k=3 then 1 else 0) := by
    intro k; fin_cases k <;> norm_num [secondHigher,Fin.ext_iff]
  exact h (kind i)

theorem patternDuplicate_zero_of_not_bothUnderflow {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ)
    (hu : ¬BothUnderflow c kind) : patternDuplicate ξ c kind b=0 := by
  classical
  have hz : (patternTemplate c kind).residual₀=0 ∨ (patternTemplate c kind).residual₁=0 := by
    unfold BothUnderflow at hu
    rw [sum_firstHigher,sum_secondHigher] at hu
    simp only [patternTemplate,rowResidual]
    by_cases h₀ : classCount 1 (patternRow kind)+classCount 2 (patternRow kind)<c
    · right
      have h₁ : c≤classCount 1 (patternRow kind)+classCount 3 (patternRow kind) := by omega
      change min (1+classCount 0 (patternRow kind))
        (c-classCount 1 (patternRow kind)-classCount 3 (patternRow kind))=0
      omega
    · left
      change min (1+classCount 0 (patternRow kind))
        (c-classCount 1 (patternRow kind)-classCount 2 (patternRow kind))=0
      omega
  unfold patternDuplicate
  dsimp only
  split_ifs with heq
  · have h0 : (patternTemplate c kind).residual₀=0 := hz.elim id (fun h=>heq.trans h)
    rw [h0,positiveMarginal_zero_capacity hξ hξ1]
    norm_num
  · unfold pureDuplicate
    apply if_neg
    intro hh
    rcases hz with h | h
    · rw [(patternTemplate c kind).selection_empty_left (1-ξ) b h] at hh
      exact Finset.notMem_empty 0 hh.1
    · rw [(patternTemplate c kind).selection_empty_right (1-ξ) b h] at hh
      exact Finset.notMem_empty 0 hh.2

theorem patternPayoff_comparison_lower {ξ w : ℝ} (hξ : 0<ξ) (hξh : ξ≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) (b : Fin (N+1)→ℝ)
    (hb : 0<b 0) (hbw : b 0≤w/2)
    (hmask : ∀i,i∉(patternTemplate c kind).support→b i=0) :
    patternPayoff ξ c kind w b≥w/2*((if LocalUnderflow c 0 kind then 1 else 0)-
      (if BothUnderflow c kind then 1 else 0)) := by
  classical
  have hξ1 : ξ<1:=by linarith
  have hw : 0≤w:=by linarith
  have hout:=pattern_outcomes_bounds hξ hξ1 c kind b
  have hc : 0≤(1-2*ξ)*b 0:=mul_nonneg (by linarith) hb.le
  have hcost : (1-2*ξ)*b 0≤w/2 := by
    have ht : (1-2*ξ)*b 0≤b 0:=by nlinarith
    exact ht.trans hbw
  have hd:=mul_le_mul_of_nonneg_left hout.2.2.2 hc
  have hs:=mul_nonneg (by linarith : 0≤w-b 0) hout.1
  rw [patternPayoff_outcomes]
  by_cases hu : LocalUnderflow c 0 kind
  · rw [if_pos hu,patternServed_one_of_underflow hξ hξ1 c kind b hb hmask 0 hu]
    by_cases hj : BothUnderflow c kind
    · rw [if_pos hj]
      nlinarith
    · rw [if_neg hj,patternDuplicate_zero_of_not_bothUnderflow hξ hξ1 c kind b hj]
      nlinarith
  · rw [if_neg hu]
    by_cases hj : BothUnderflow c kind
    · rw [if_pos hj]
      nlinarith
    · rw [if_neg hj,patternDuplicate_zero_of_not_bothUnderflow hξ hξ1 c kind b hj]
      nlinarith

end Patterns
end FCAppendix.Affine.LowBody
