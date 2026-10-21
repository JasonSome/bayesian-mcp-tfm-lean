import FCAppendix.Affine.LowBody.PureTemplate

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def relabelPair (e : Equiv.Perm ι) (P : Finset ι × Finset ι) : Finset ι × Finset ι :=
  (P.1.map e.toEmbedding,P.2.map e.toEmbedding)

omit [Fintype ι] [DecidableEq ι] in
lemma relabelPair_symm (e : Equiv.Perm ι) (P : Finset ι × Finset ι) :
    relabelPair e.symm (relabelPair e P)=P := by
  ext i <;> simp [relabelPair]

omit [Fintype ι] in
lemma potential_relabel (κ : ℝ) (b : ι→ℝ) (e : Equiv.Perm ι)
    (P : Finset ι × Finset ι) :
    CompleteInformation.potential κ (b ∘ e.symm) (relabelPair e P).1 (relabelPair e P).2=
      CompleteInformation.potential κ b P.1 P.2 := by
  unfold relabelPair
  rw [CompleteInformation.potential,←Finset.map_union,←Finset.map_inter]
  simp only [Finset.sum_map,Equiv.coe_toEmbedding,Function.comp_apply,Equiv.symm_apply_apply]
  rfl

omit [Fintype ι] in
lemma focalCopy_relabel (e : Equiv.Perm ι) (P : Finset ι × Finset ι) (i : ι) :
    focalCopy (relabelPair e P) (e i)=focalCopy P i := by
  simp [focalCopy,relabelPair]

namespace PureTemplate

def relabel (T : PureTemplate ι) (e : Equiv.Perm ι) : PureTemplate ι where
  support:=T.support.map e.toEmbedding
  residual₀:=T.residual₀
  residual₁:=T.residual₁

omit [Fintype ι] [DecidableEq ι] in
lemma feasible_relabel_iff (T : PureTemplate ι) (e : Equiv.Perm ι)
    (P : Finset ι × Finset ι) :
    (T.relabel e).Feasible (relabelPair e P) ↔ T.Feasible P := by
  simp [Feasible,relabel,relabelPair,Finset.map_subset_map]

omit [Fintype ι] [DecidableEq ι] in
lemma relabel_symm (T : PureTemplate ι) (e : Equiv.Perm ι) :
    (T.relabel e).relabel e.symm=T := by
  cases T
  simp only [relabel]
  congr 1
  ext i
  simp

theorem selection_relabel_pullback_max (T : PureTemplate ι) (e : Equiv.Perm ι)
    (κ : ℝ) (b : ι→ℝ) :
    let Q:=relabelPair e.symm ((T.relabel e).selection κ (b ∘ e.symm))
    T.Feasible Q ∧ ∀P,T.Feasible P →
      CompleteInformation.potential κ b P.1 P.2≤CompleteInformation.potential κ b Q.1 Q.2 := by
  let S:=(T.relabel e).selection κ (b ∘ e.symm)
  have hS:=(T.relabel e).selection_feasible κ (b ∘ e.symm)
  have hQ : T.Feasible (relabelPair e.symm S) := by
    simpa only [relabel_symm] using
      ((T.relabel e).feasible_relabel_iff e.symm S).mpr hS
  refine ⟨hQ,?_⟩
  intro P hP
  have hh:=(T.relabel e).selection_max κ (b ∘ e.symm) (relabelPair e P)
    ((T.feasible_relabel_iff e P).mpr hP)
  rw [potential_relabel] at hh
  have he:=potential_relabel κ (b ∘ e.symm) e.symm S
  have hbid : (b ∘ e.symm) ∘ e=b:=by funext i;simp
  rw [show e.symm.symm=e from rfl,hbid] at he
  exact hh.trans_eq he.symm

theorem selection_focalCopy_relabel (T : PureTemplate ι) (e : Equiv.Perm ι)
    (κ : ℝ) (b : ι→ℝ) (i : ι)
    (hgeneric : ∀P Q,T.Feasible P → T.Feasible Q →
      CompleteInformation.potential κ b P.1 P.2=CompleteInformation.potential κ b Q.1 Q.2 →
      focalCopy P i=focalCopy Q i) :
    focalCopy ((T.relabel e).selection κ (b ∘ e.symm)) (e i)=
      focalCopy (T.selection κ b) i := by
  let S:=(T.relabel e).selection κ (b ∘ e.symm)
  let Q:=relabelPair e.symm S
  obtain ⟨hQ,hmQ⟩:=T.selection_relabel_pullback_max e κ b
  have hP:=T.selection_feasible κ b
  have he : CompleteInformation.potential κ b (T.selection κ b).1 (T.selection κ b).2=
      CompleteInformation.potential κ b Q.1 Q.2 :=
    le_antisymm (hmQ _ hP) (T.selection_max κ b Q hQ)
  have hc:=hgeneric (T.selection κ b) Q hP hQ he
  have hs : focalCopy Q i=focalCopy S (e i) := by
    simpa only [Q,Equiv.symm_apply_apply] using focalCopy_relabel e.symm S (e i)
  exact (hc.trans hs).symm

theorem selection_payoff_relabel (T : PureTemplate ι) (e : Equiv.Perm ι)
    (κ w : ℝ) (b : ι→ℝ) (i : ι)
    (hgeneric : ∀P Q,T.Feasible P → T.Feasible Q →
      CompleteInformation.potential κ b P.1 P.2=CompleteInformation.potential κ b Q.1 Q.2 →
      focalCopy P i=focalCopy Q i) :
    purePayoff κ w (b ∘ e.symm) ((T.relabel e).selection κ (b ∘ e.symm)) (e i)=
      purePayoff κ w b (T.selection κ b) i := by
  simp only [purePayoff,T.selection_focalCopy_relabel e κ b i hgeneric,
    Function.comp_apply,Equiv.symm_apply_apply]

end PureTemplate
end FCAppendix.Affine.LowBody
