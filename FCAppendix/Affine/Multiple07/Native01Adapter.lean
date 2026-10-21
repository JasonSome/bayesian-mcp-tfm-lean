import FCAppendix.Affine.Hybrid.Native02.PrimitiveProducer
import FCAppendix.Affine.Hybrid.Native02.FrozenActiveAdapter
import FCAppendix.Affine.Multiple07.Native02Primitives

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

theorem native02_frozenActiveFamily_from_actual01 (p : Hybrid.Native02.PrimitiveInput) :
    Nonempty (Hybrid.Native02.FrozenActiveFamily p) :=
  Hybrid.Native02.primitive_active_producer p

theorem sourceNative02_frozenActiveFamily (r : Partition) :
    Nonempty (Hybrid.Native02.FrozenActiveFamily (sourceNative02Input r)) :=
  native02_frozenActiveFamily_from_actual01 (sourceNative02Input r)

end FCAppendix.Affine.Multiple07
