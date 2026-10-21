import FCAppendix.Affine.Uniform07.ParameterCertificate
import FCAppendix.Affine.Uniform07.ExactIntegral

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Early
open FCAppendix.Affine.Uniform07 MeasureTheory Set

def chi : ℝ := 69 / 100
def smallValue (i : Row) : ℝ := cutoff i / 200
def floorStart (i : Row) : ℝ := entry i + cutoff i / 400
def categoryCutoff (i : Row) : ℝ := entry i + cutoff i / 200
def clip01 (u : ℝ) : ℝ := max 0 (min 1 u)

def lowerFloor (i : Row) (v : ℝ) : ℝ :=
  chi * max (v - smallValue i) 0 *
    clip01 ((v - floorStart i) / (categoryCutoff i - floorStart i))

def capRatioQ (i : Row) : ℚ := xQ i / (kappaQ i + xiQ i * xQ i) + 1 / 200
def bidCap (i : Row) : ℝ := (capRatioQ i : ℝ) * cutoff i
def floorMaximum (i : Row) : ℝ := chi * (cutoff i - smallValue i)
def demandRatio (i : Row) : ℝ := (cutoff i - delta) / (2 * cutoff i)
def samplingMargin (i : Row) : ℝ :=
  (54/100 : ℝ) * cutoff i * xi i * demandRatio i / 16

def fullFloorStartQ (i : Row) : ℚ := max (xQ i + 1 / 200) (1 / 200 + (54 / 100) / (69 / 100))
def fullFloorStart (i : Row) : ℝ := (fullFloorStartQ i : ℝ) * cutoff i
def floorDemand (i : Row) : ℝ :=
  (1 - (fullFloorStartQ i : ℝ) - (54 / 69 : ℝ) *
    Real.log ((199 / 200 : ℝ) / ((fullFloorStartQ i : ℝ) - 1 / 200))) / xi i

def seedTailMass (i : Row) : ℝ := 1 - (fullFloorStartQ i : ℝ)

def seedDemandLower (i : Row) : ℝ := (20 / 21 : ℝ) * seedTailMass i
def seedPsi (i : Row) (z b : ℝ) : ℝ :=
  max (b - z) 0 / (cutoff i / 1000 + max (b - z) 0)

def activeSeedStartQ : Row → ℚ | .first => 17 / 20 | .second => 4 / 5
def activeSeedLevelQ (i : Row) : ℚ := xQ i + 1 / 100
def normalizedProductBid (i : Row) (y : ℝ) : ℝ :=
  x i * y / (kappa i * y + xi i * x i)
def activeSeedDemandLower (i : Row) : ℝ :=
  (1 - (activeSeedStartQ i : ℝ)) *
    (normalizedProductBid i (activeSeedStartQ i) - (activeSeedLevelQ i : ℝ)) /
    (1 / 1000 + normalizedProductBid i (activeSeedStartQ i) -
      (activeSeedLevelQ i : ℝ))

def binaryEntropy (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))
def atomRateI0 (i : Row) : ℝ := binaryEntropy rho ((1 + cutoff i) / 2)
def atomRateI1 (i : Row) : ℝ := binaryEntropy delta (cutoff i) +
  (1 - delta) * binaryEntropy (1 / 2 - delta / (1 - delta)) (1 / 2)
def atomRateJ (i : Row) : ℝ := binaryEntropy delta (categoryCutoff i)
def atomMarginQ : Row → ℚ | .first => 13890 / 10^9 | .second => 17325 / 10^9

def lowThetaQ : Row → ℚ | .first => 27 / 100 | .second => 23 / 100
def lowStartQ (i : Row) : ℚ := max (xQ i + 1 / 200) (1 / 200 + (501 / 1000) / (69 / 100))
def lowPieceLeftQ (i : Row) : ℚ := lowStartQ i - 1 / 200
def lowPieceRightQ : ℚ := 199 / 200
def lowPieceAQ (i : Row) : ℚ := 1 / xiQ i
def lowPieceCQ (i : Row) : ℚ := (501 / 690) / xiQ i

def lowTransform (i : Row) : ℝ :=
  (1 - cutoff i) * Real.exp (-(lowThetaQ i : ℝ) / 2) + cutoff i *
    ((lowStartQ i : ℝ) + pieceZ (lowPieceAQ i) (lowPieceCQ i)
      (lowThetaQ i) (lowPieceLeftQ i) lowPieceRightQ)
def lowCanonicalRate (i : Row) : ℝ :=
  -(lowThetaQ i : ℝ) * rho - Real.log (lowTransform i)
def lowMarginQ : Row → ℚ | .first => 53735 / 10^10 | .second => 38930 / 10^10

def earlyCutoffBox : Row → Box
  | .first => ⟨107351067373897 / 10^17, 1073510673739 / 10^15⟩
  | .second => ⟨11119204390639 / 10^16, 111192043906393 / 10^17⟩

theorem earlyCutoffBox_ok (i : Row) : (earlyCutoffBox i).Holds (cutoff i) := by
  cases i with
  | first =>
    norm_num [earlyCutoffBox,Box.Holds]
    exact ⟨cutoff_first_enclosure.1.le, cutoff_first_enclosure.2.le⟩
  | second =>
    norm_num [earlyCutoffBox,Box.Holds]
    exact ⟨cutoff_second_enclosure.1.le, cutoff_second_enclosure.2.le⟩

end FCAppendix.Affine.Uniform07Finishing.Early
