import FCAppendix.Affine.Tail04.EqualReceiptLaw
import FCAppendix.Affine.Tail04.EqualPrivateActiveRelabel

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualSortedReceiptLaw
open MeasureTheory Set Classical
open EqualPrivateSignal EqualReceiptLaw SortedAllNoise

theorem receipt_sorted {N H c : ℕ} {R V B ξ : ℝ} (hξ : 0< ξ)
    (μ : WeakProbability.Law (Signal H R V)) (b : Fin N→ Icc (1:ℝ) B) (i : Fin N) :
    receipt (c:=c) (ξ:=ξ) μ (sortedBox b) i=
      receipt (c:=c) (ξ:=ξ) μ b (PrivateRowSorting.permutation (fun j=>(b j:ℝ)) i) := by
  let σ:=PrivateRowSorting.permutation (fun j=>(b j:ℝ))
  have hq:=EqualPrivateActiveRelabel.policyMean_relabel (c:=c) (ξ:=ξ) hξ
    (by norm_num : (0:ℝ)<1) σ.symm (b,μ) i
  have he : EqualPrivateActiveRelabel.relabelParameters σ.symm (b,μ)=(sortedBox b,μ) := by
    rfl
  rw [he] at hq
  simp only [receipt,hq,sortedBox,Equiv.symm_symm,σ]

theorem ae_sorted_receipts_ne {N H c : ℕ} {R V B ξ : ℝ} (hξ : 0< ξ) (hξ1 : ξ<1)
    (μ : WeakProbability.Law (Signal H R V))
    (hμ : ∀ a : ℝ,0< a→∀ᵐ s ∂WeakProbability.toMeasure μ,∀ j,partialBid (s j)≠a)
    (ν : ProbabilityMeasure (Icc (1:ℝ) B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) B))] (a : ℝ) :
    ∀ᵐ b ∂Measure.pi (fun _ : Fin N=>(ν : Measure (Icc (1:ℝ) B))),∀ i : Fin N,
      receipt (c:=c) (ξ:=ξ) μ (sortedBox b) i≠a := by
  filter_upwards [ae_receipts_ne (c:=c) hξ hξ1 μ hμ ν a] with b hb
  intro i
  rw [receipt_sorted hξ μ b i]
  exact hb _

end FCAppendix.Affine.Tail04.EqualSortedReceiptLaw
