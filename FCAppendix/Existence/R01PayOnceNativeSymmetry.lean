import FCAppendix.Existence.R01PayOnceMixedGame
import FCAppendix.Finite.IdentitySymmetry

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def positiveSupportEquiv (e : ι≃κ) (b : κ→ℝ) :
    ↥(positiveSupport (b ∘ e))≃↥(positiveSupport b) where
  toFun i:=⟨e i.1,by simpa only [mem_positiveSupport,Function.comp_apply] using i.2⟩
  invFun i:=⟨e.symm i.1,by simpa only [mem_positiveSupport,Function.comp_apply,
    Equiv.apply_symm_apply] using i.2⟩
  left_inv i:=Subtype.ext (e.symm_apply_apply i.1)
  right_inv i:=Subtype.ext (e.apply_symm_apply i.1)

theorem positiveMarginal_relabel (e : ι≃κ) (n c : ℕ) (hn : 2≤n)
    (b : κ→ℝ) (i : ι) :
    positiveMarginal n c (b ∘ e) i=positiveMarginal n c b (e i) := by
  have hmem : i∈positiveSupport (b ∘ e) ↔ e i∈positiveSupport b := by
    simp only [mem_positiveSupport,Function.comp_apply]
  by_cases hi : i∈positiveSupport (b ∘ e)
  · have hei:=hmem.mp hi
    have hp : ∀j : ↥(positiveSupport b),0<b j.1:=fun j=>(mem_positiveSupport b j.1).mp j.2
    have he:=congrFun (kernel_equiv (positiveSupportEquiv e b) n c hn
      (fun j : ↥(positiveSupport b)=>b j.1) hp) ⟨i,hi⟩
    dsimp only [positiveMarginal,onSupport]
    rw [dif_pos hi,dif_pos hei]
    exact he
  · have hei : e i∉positiveSupport b:=fun h=>hi (hmem.mpr h)
    simp only [positiveMarginal,onSupport,dif_neg hi,dif_neg hei]

end FCAppendix.Existence.PayOnceBounded

namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded
variable {m n c : ℕ} (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    {W : ℝ} (κ : Kernel ℝ (FloorAction 0 W)) [IsMarkovKernel κ]
    (G : Schedule n) (g : ℝ) (hg : 0≤g)
local notation "Gamma"=>mixedGame m n c hn F κ G g hg

theorem mixedGame_equivariant : PolicyLawEquivariant Gamma := by
  intro e j L _hL
  let f:=fun s=>((Gamma).policy j L s).val
  let f':=fun s=>((Gamma).policy j (L ∘ e.symm) s).val
  let T:=fun S : Finset (Fin m)=>S.map e.toEmbedding
  have hf : Measurable f:=measurable_policy_at_list Gamma j L
  have hf' : Measurable f':=measurable_policy_at_list Gamma j (L ∘ e.symm)
  have hT : Measurable T:=measurable_of_countable _
  have he : FiniteLaw.ofMeasure (Gamma).seedLaw f' hf'=
      FiniteLaw.ofMeasure (Gamma).seedLaw (T ∘ f) (hT.comp hf) := by
    rw [← FiniteLaw.ofMeasure_map (Gamma).seedLaw f hf T hT]
    change seedLottery Gamma j (L ∘ e.symm)=(seedLottery Gamma j L).map T
    rw [mixedGame_seedLottery,mixedGame_seedLottery]
    have hp : listMarginal n c (L ∘ e.symm)=listMarginal n c L ∘ e.symm := by
      funext i
      exact positiveMarginal_relabel e.symm n c hn (listBids L) i
    rw [hp]
    exact ExactCapacity.symmetricLottery_equivariant _ e
  have hx:=congrArg FiniteLaw.probabilityMeasure he
  simpa only [FiniteLaw.probabilityMeasure_ofMeasure,f,f',T,Function.comp_def] using hx

theorem mixedGame_outcome_eq (i l : Fin m) (a : JointAction n) :
    (problem Gamma i).outcome a=(problem Gamma l).outcome a :=
  outcome_eq_of_policyLawEquivariant Gamma (mixedGame_equivariant hn F κ G g hg) i l a

end FCAppendix.Bayes.PayOnceConstruction
