import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Constructions.SumProd

namespace FCAppendix.Existence
open MeasureTheory Set Topology

instance sumBorelSpace {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] : BorelSpace (X ⊕ Y) := by
  constructor
  apply le_antisymm
  · intro S hS
    obtain ⟨hl,hr⟩ := measurableSet_sum_iff.mp hS
    letI : MeasurableSpace (X ⊕ Y) := borel (X ⊕ Y)
    letI : BorelSpace (X ⊕ Y) := ⟨rfl⟩
    have hli : MeasurableEmbedding (@Sum.inl X Y) := IsOpenEmbedding.inl.measurableEmbedding
    have hri : MeasurableEmbedding (@Sum.inr X Y) := IsOpenEmbedding.inr.measurableEmbedding
    have he : S=Sum.inl '' (Sum.inl ⁻¹' S) ∪ Sum.inr '' (Sum.inr ⁻¹' S) := by
      ext z
      cases z <;> simp
    rw [he]
    exact (hli.measurableSet_image.mpr hl).union (hri.measurableSet_image.mpr hr)
  · apply MeasurableSpace.generateFrom_le
    intro S hS
    rw [measurableSet_sum_iff]
    exact ⟨(hS.preimage continuous_inl).measurableSet,(hS.preimage continuous_inr).measurableSet⟩

end FCAppendix.Existence
