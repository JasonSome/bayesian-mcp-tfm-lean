import FCAppendix.Affine.Hybrid.FiniteSelector
import FCAppendix.Affine.Hybrid.SourceCountBounds

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology Classical
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteReceiptFactor (ξ : ℝ) (D r : ℕ) : ℝ:=1-ξ*(r:ℝ)/(D:ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma finiteMultiplier_box_bounds {ξ L U : ℝ} (hL : 0 < L) (b : ι→ℝ)
    (D : Finset ι) (hne : D.Nonempty) (r : ℕ)
    (hb : ∀i∈D,b i∈Icc L U) (hg : 0 ≤ finiteReceiptFactor ξ D.card r) :
    finiteReceiptFactor ξ D.card r*L ≤ finiteMultiplier ξ b D r ∧
      finiteMultiplier ξ b D r ≤ finiteReceiptFactor ξ D.card r*U := by
  have hc : (0:ℝ)<D.card:=Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have hU : 0 < U:=by obtain ⟨i,hi⟩:=hne;exact hL.trans_le ((hb i hi).1.trans (hb i hi).2)
  have hsum : 0<∑i∈D,(b i)⁻¹:=reciprocal_sum_pos b D hne (fun i hi=>hL.trans_le (hb i hi).1)
  have hlo : (D.card:ℝ) ≤ U*(∑i∈D,(b i)⁻¹) := by
    have hh:=Finset.sum_le_sum (s:=D) (f:=fun _=>1/U) (g:=fun i=>(b i)⁻¹) (fun i hi=>by
      simpa only [one_div] using one_div_le_one_div_of_le (hL.trans_le (hb i hi).1) (hb i hi).2)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hm:=mul_le_mul_of_nonneg_left hh hU.le
    have he : U*((D.card:ℝ)*(1/U))=D.card:=by field_simp
    rw [he] at hm
    exact hm
  have hhi : L*(∑i∈D,(b i)⁻¹) ≤ D.card := by
    have hh:=Finset.sum_le_sum (s:=D) (f:=fun i=>(b i)⁻¹) (g:=fun _=>1/L) (fun i hi=>by
      simpa only [one_div] using one_div_le_one_div_of_le hL (hb i hi).1)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    have hm:=mul_le_mul_of_nonneg_left hh hL.le
    have he : L*((D.card:ℝ)*(1/L))=D.card:=by field_simp
    rw [he] at hm
    exact hm
  have he : (D.card:ℝ)-ξ*r=finiteReceiptFactor ξ D.card r*D.card := by
    unfold finiteReceiptFactor
    field_simp
  unfold finiteMultiplier
  rw [he]
  constructor
  · apply (le_div_iff₀ hsum).mpr
    have hh:=mul_le_mul_of_nonneg_left hhi hg
    nlinarith only [hh]
  · apply (div_le_iff₀ hsum).mpr
    have hh:=mul_le_mul_of_nonneg_left hlo hg
    nlinarith only [hh]

def guardedDataOfBox {ξ L U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ<1) (hL : 0 < L)
    (b : ι→ℝ) (hb : ∀i,b i∈Icc L U) (E₁ E₂ : Finset ι)
    (hdis : Disjoint E₁ E₂) (r : ℕ)
    (hne : (Finset.univ\(E₁∪E₂)).Nonempty)
    (hg : 0 ≤ finiteReceiptFactor ξ (Finset.univ\(E₁∪E₂)).card r)
    (hlower : (1-ξ)*U<finiteReceiptFactor ξ (Finset.univ\(E₁∪E₂)).card r*L)
    (hupper : finiteReceiptFactor ξ (Finset.univ\(E₁∪E₂)).card r*U<L) : GuardedData ι where
  xi:=ξ
  xi_pos:=hξ
  xi_lt_one:=hξ1
  bid:=b
  bid_pos:=fun i=>hL.trans_le (hb i).1
  owner₁:=E₁
  owner₂:=E₂
  owners_disjoint:=hdis
  residual:=r
  mixed_nonempty:=hne
  lower_guard:=by
    intro i
    have hh:=finiteMultiplier_box_bounds hL b (Finset.univ\(E₁∪E₂)) hne r (fun i _=>hb i) hg
    have hi:=mul_le_mul_of_nonneg_left (hb i).2 (show 0 ≤ 1-ξ by linarith)
    exact hi.trans_lt (hlower.trans_le hh.1)
  upper_guard:=by
    intro i
    have hh:=finiteMultiplier_box_bounds hL b (Finset.univ\(E₁∪E₂)) hne r (fun i _=>hb i) hg
    exact hh.2.trans_lt (hupper.trans_le (hb i).1)

end FCAppendix.Affine.Hybrid
