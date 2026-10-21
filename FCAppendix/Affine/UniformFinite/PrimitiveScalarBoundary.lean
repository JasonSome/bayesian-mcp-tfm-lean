import FCAppendix.Affine.Uniform07.Parameters
import FCAppendix.Ample.RateSystem

noncomputable section
namespace FCAppendix.Affine.UniformFinite

structure SourceEntropyCertificate (i : Uniform07.Row) : Prop where
  entropy_gap :
    Ample.binaryKL Uniform07.rho ((1+Uniform07.cutoff i)/2) +
      (Ample.binaryKL Uniform07.delta (Uniform07.cutoff i) +
        (1-Uniform07.delta)*Ample.binaryKL
          (1/2-Uniform07.delta/(1-Uniform07.delta)) (1/2)) <
      Ample.binaryKL Uniform07.delta (Uniform07.entry i+Uniform07.cutoff i/200)
  double_lower_gap :
    2*Ample.binaryKL Uniform07.rho ((1+Uniform07.cutoff i)/2) <
      Ample.binaryKL Uniform07.delta (Uniform07.entry i+Uniform07.cutoff i/200)

end FCAppendix.Affine.UniformFinite
