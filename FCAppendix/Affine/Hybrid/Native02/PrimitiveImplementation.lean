import FCAppendix.Affine.Hybrid.Native02.PrimitiveProducer
import FCAppendix.Affine.Hybrid.Native02.Implementation

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02

theorem native_affine_implementation_from_primitives (p : PrimitiveInput) :
    Nonempty (NativeImplementation p) :=
  native_affine_implementation primitive_active_producer p

end FCAppendix.Affine.Hybrid.Native02
