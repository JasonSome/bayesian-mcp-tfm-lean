import FCAppendix.Affine.UniformFinite.SourceGuards

noncomputable section
namespace FCAppendix.Affine.UniformFinite.OwnBid
open Classical

private def rowCode (M : ℕ) (row : Source.CountRow M) :
    Finset (Fin M) × Fin (M+1) × Fin (M+1) :=
  (row.lower, ⟨row.upper0,by have h := row.partition; omega⟩,
    ⟨row.upper1,by have h := row.partition; omega⟩)

private theorem rowCode_injective (M : ℕ) : Function.Injective (rowCode M) := by
  intro x y he
  have hL := congrArg (fun z : Finset (Fin M) × Fin (M+1) × Fin (M+1) => z.1) he
  have h0 := congrArg (fun z : Finset (Fin M) × Fin (M+1) × Fin (M+1) => z.2.1.val) he
  have h1 := congrArg (fun z : Finset (Fin M) × Fin (M+1) × Fin (M+1) => z.2.2.val) he
  cases x
  cases y
  dsimp only [rowCode] at hL h0 h1
  cases hL
  cases h0
  cases h1
  rfl

instance countRowFinite (M : ℕ) : Finite (Source.CountRow M) :=
  Finite.of_injective (rowCode M) (rowCode_injective M)

noncomputable instance countRowFintype (M : ℕ) : Fintype (Source.CountRow M) := Fintype.ofFinite _

instance countRowNonempty (M : ℕ) : Nonempty (Source.CountRow M) :=
  ⟨⟨Finset.univ,0,0,by simp⟩⟩

end FCAppendix.Affine.UniformFinite.OwnBid

namespace FCAppendix.Affine.UniformFinite.Source
instance countRowMeasurableSpace (M : ℕ) : MeasurableSpace (CountRow M) := ⊤
instance countRowMeasurableSingletonClass (M : ℕ) : MeasurableSingletonClass (CountRow M) :=
  ⟨fun _ => trivial⟩
instance countRowStandardBorelSpace (M : ℕ) : StandardBorelSpace (CountRow M) := by infer_instance
end FCAppendix.Affine.UniformFinite.Source
