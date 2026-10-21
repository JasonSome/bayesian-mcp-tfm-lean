import FCAppendix.Affine.Uniform07Finishing.Early.PrimitiveGuards
import FCAppendix.Affine.UniformFinite.PrimitiveScalarBoundary

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07

namespace UniformFinitePrimitiveGuards

theorem entropy_gap {i : Row} (h : UniformFinitePrimitiveGuards i) :
    Ample.binaryKL rho ((1+cutoff i)/2) +
      (Ample.binaryKL delta (cutoff i) +
        (1-delta)*Ample.binaryKL (1/2-delta/(1-delta)) (1/2)) <
      Ample.binaryKL delta (entry i+cutoff i/200) := by
  have hm : 0 < (atomMarginQ i : ℝ) := by
    cases i <;> norm_num [atomMarginQ]
  have hg := h.entropy_margins.1
  change (atomMarginQ i : ℝ) <
    atomRateJ i-atomRateI0 i-atomRateI1 i at hg
  have hs : atomRateI0 i+atomRateI1 i< atomRateJ i := by linarith
  simpa only [atomRateI0,atomRateI1,atomRateJ,binaryEntropy,
    Ample.binaryKL,categoryCutoff] using hs

theorem double_lower_gap {i : Row} (h : UniformFinitePrimitiveGuards i) :
    2*Ample.binaryKL rho ((1+cutoff i)/2) <
      Ample.binaryKL delta (entry i+cutoff i/200) := by
  simpa only [atomRateI0,atomRateJ,binaryEntropy,Ample.binaryKL,
    categoryCutoff] using h.entropy_margins.2

theorem sourceEntropyCertificate {i : Row} (h : UniformFinitePrimitiveGuards i) :
    UniformFinite.SourceEntropyCertificate i :=
  ⟨h.entropy_gap,h.double_lower_gap⟩

end UniformFinitePrimitiveGuards

theorem concrete05_source_entropy_certificate (i : Row) :
    UniformFinite.SourceEntropyCertificate i :=
  (Uniform07.uniform_finite_primitive_guards i).sourceEntropyCertificate

end FCAppendix.Affine.Uniform07Finishing.Early
