import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

noncomputable section
namespace FCAppendix.Affine.Tail04.SumBorel
open MeasureTheory Set

instance {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] : BorelSpace (X ⊕ Y) := by
  constructor
  apply le_antisymm
  · intro s hs
    letI : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
    haveI : BorelSpace (X ⊕ Y) := ⟨rfl⟩
    have h0 := (Topology.IsOpenEmbedding.inl (X := X) (Y := Y)).measurableEmbedding
    have h1 := (Topology.IsOpenEmbedding.inr (X := X) (Y := Y)).measurableEmbedding
    have hh0 := h0.measurableSet_image' ((measurableSet_sum_iff.mp hs).1)
    have hh1 := h1.measurableSet_image' ((measurableSet_sum_iff.mp hs).2)
    have he : Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) = s := by
      apply Set.Subset.antisymm
      · intro z hz
        rcases hz with ⟨u, hu, rfl⟩ | ⟨t, ht, rfl⟩
        · exact hu
        · exact ht
      · intro z hz
        cases z with
        | inl u => exact Or.inl ⟨u, hz, rfl⟩
        | inr t => exact Or.inr ⟨t, hz, rfl⟩
    rw [← he]
    exact hh0.union hh1
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr
      ⟨(hs.preimage continuous_inl).measurableSet, (hs.preimage continuous_inr).measurableSet⟩

end FCAppendix.Affine.Tail04.SumBorel
