import FCAppendix.Affine.Hybrid.NormalizedGuardRegion

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical
open scoped BigOperators

def exclusiveQuota (z : ℝ) (A : ℕ) : ℕ:=⌊z*(A:ℝ)/2⌋₊
def residualDifference (d₀ d₁ : ℕ) : ℕ:=max d₀ d₁-min d₀ d₁

def finiteCountPoint (M A small ell gap : ℕ) : Fin 4→ℝ:=
  ![(A:ℝ)/M,(small:ℝ)/M,(ell:ℝ)/M,(gap:ℝ)/M]

theorem exists_guardedData_of_count_region {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ L U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ<1) (hL : 0 < L)
    (M A small large ell : ℕ) (hM : 0 < M) (hcard : Fintype.card ι=A)
    (horder : small ≤ large)
    (hregion : NormalizedGuardRegion ξ L U (finiteCountPoint M A small ell (large-small)))
    (b : ι→ℝ) (hb : ∀i,b i∈Icc L U) (E₁ E₂ : Finset ι) (hdis : Disjoint E₁ E₂)
    (hE₁ : E₁.card=ell+(large-small)) (hE₂ : E₂.card=ell) :
    ∃Q : GuardedData ι,Q.xi=ξ ∧ Q.bid=b ∧ Q.owner₁=E₁ ∧ Q.owner₂=E₂ ∧
      Q.residual=small-ell ∧ Q.owner₁.card+Q.residual=large ∧
      Q.owner₂.card+Q.residual=small := by
  let gap:=large-small
  let D:=Finset.univ\(E₁∪E₂)
  let r:=small-ell
  have hm : (0:ℝ)<M:=Nat.cast_pos.mpr hM
  have hDM : normalizedMixed (finiteCountPoint M A small ell gap)=
      ((A:ℝ)-2*ell-gap)/(M:ℝ):=by dsimp [normalizedMixed,finiteCountPoint];ring
  have hRM : normalizedResidual (finiteCountPoint M A small ell gap)=
      ((small:ℝ)-ell)/(M:ℝ):=by dsimp [normalizedResidual,finiteCountPoint];ring
  have hDpos : 2*ell+gap<A := by
    have hh:=(div_pos_iff_of_pos_right hm).mp (hDM ▸ hregion.1)
    have hh' : ((2*ell+gap:ℕ):ℝ)<A:=by push_cast;nlinarith
    exact_mod_cast hh'
  have hrpos : ell<small := by
    have hh:=(div_pos_iff_of_pos_right hm).mp (hRM ▸ hregion.2.1)
    exact_mod_cast (show (ell:ℝ)<small by linarith)
  have hDc : D.card=A-(2*ell+gap) := by
    dsimp only [D]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hcard,
      Finset.card_union_of_disjoint hdis,hE₁,hE₂]
    dsimp only [gap]
    omega
  have hDne : D.Nonempty:=Finset.card_pos.mp (by rw [hDc];omega)
  have hDreal : (D.card:ℝ)=(A:ℝ)-2*ell-gap := by
    rw [hDc,Nat.cast_sub hDpos.le]
    push_cast
    ring
  have hrreal : (r:ℝ)=(small:ℝ)-ell:=by rw [Nat.cast_sub hrpos.le]
  have hfactor : normalizedFactor ξ (finiteCountPoint M A small ell gap)=
      finiteReceiptFactor ξ D.card r := by
    rw [normalizedFactor,hDM,hRM,finiteReceiptFactor,hDreal,hrreal]
    field_simp
  let Q:=guardedDataOfBox hξ hξ1 hL b hb E₁ E₂ hdis r hDne
    (by rw [←hfactor];exact hregion.2.2.2.1.le)
    (by rw [←hfactor];exact hregion.2.2.2.2.1)
    (by rw [←hfactor];exact hregion.2.2.2.2.2)
  refine ⟨Q,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · change E₁.card+(small-ell)=large
    rw [hE₁]
    omega
  · change E₂.card+(small-ell)=small
    rw [hE₂]
    omega

end FCAppendix.Affine.Hybrid
