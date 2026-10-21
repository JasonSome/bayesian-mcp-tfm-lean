import FCAppendix.Affine.LowBody.NoisyEqualPayoff
import FCAppendix.Existence.R01PayOnceNativeSymmetry

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma isKernel_equiv (e : ι≃κ) (ξ : ℝ) (c : ℕ) (b p : κ→ℝ)
    (hp : IsKernel ξ c b p) : IsKernel ξ c (b ∘ e) (p ∘ e) := by
  obtain ⟨hp0,hp1,hps,z,hz,hpt⟩:=hp
  refine ⟨fun i=>hp0 (e i),fun i=>hp1 (e i),?_,z,hz,?_,?_,?_⟩
  · simp only [Function.comp_apply]
    rw [Equiv.sum_comp e p,hps,Fintype.card_congr e]
  · exact fun i=>hpt.1 (e i)
  · exact fun i=>hpt.2.1 (e i)
  · exact fun i=>hpt.2.2 (e i)

theorem kernelMarginal_equiv (e : ι≃κ) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : κ→ℝ) (hb : ∀i,0<b i) :
    kernelMarginal ξ c (b ∘ e)=kernelMarginal ξ c b ∘ e := by
  exact isKernel_unique hξ c (b ∘ e) (fun i=>hb (e i)) _ _
    (kernelMarginal_spec hξ hξ1 c _ (fun i=>hb (e i)))
    (isKernel_equiv e ξ c b _ (kernelMarginal_spec hξ hξ1 c b hb))

variable [DecidableEq ι] [DecidableEq κ]

theorem positiveMarginal_equiv (e : ι≃κ) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (b : κ→ℝ) (i : ι) :
    positiveMarginal ξ c (b ∘ e) i=positiveMarginal ξ c b (e i) := by
  have hmem : i∈Existence.PayOnceBounded.positiveSupport (b ∘ e) ↔
      e i∈Existence.PayOnceBounded.positiveSupport b := by
    simp only [Existence.PayOnceBounded.mem_positiveSupport,Function.comp_apply]
  by_cases hi : i∈Existence.PayOnceBounded.positiveSupport (b ∘ e)
  · have hei:=hmem.mp hi
    have hp : ∀j : ↥(Existence.PayOnceBounded.positiveSupport b),0<b j.1:=
      fun j=>(Existence.PayOnceBounded.mem_positiveSupport b j.1).mp j.2
    have he:=congrFun (kernelMarginal_equiv
      (Existence.PayOnceBounded.positiveSupportEquiv e b) hξ hξ1 c
      (fun j : ↥(Existence.PayOnceBounded.positiveSupport b)=>b j.1) hp) ⟨i,hi⟩
    dsimp only [positiveMarginal,onSupport]
    rw [dif_pos hi,dif_pos hei]
    exact he
  · have hei : e i∉Existence.PayOnceBounded.positiveSupport b:=fun h=>hi (hmem.mpr h)
    simp only [positiveMarginal,onSupport,dif_neg hi,dif_neg hei]

end FCAppendix.Affine.EqualCapacity

namespace FCAppendix.Affine.LowBody
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem equalPayoff_relabel (e : Equiv.Perm ι) {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (w : ℝ) (b : ι→ℝ) (i : ι) :
    equalPayoff ξ c (e i) w (b ∘ e.symm)=equalPayoff ξ c i w b := by
  unfold equalPayoff
  rw [EqualCapacity.positiveMarginal_equiv e.symm hξ hξ1]
  simp only [Equiv.symm_apply_apply,Function.comp_apply]

end FCAppendix.Affine.LowBody
