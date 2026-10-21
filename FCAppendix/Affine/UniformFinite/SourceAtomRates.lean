import FCAppendix.Affine.UniformFinite.AtomEventRates
import FCAppendix.Affine.UniformFinite.PrimitiveScalarBoundary
import FCAppendix.Affine.Uniform05Rows
import FCAppendix.Affine.Uniform07Finishing.FinitePrimitiveCertificate

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set Filter Topology
open Uniform05

theorem zc_pos (i : Row) : 0< zc i := by
  unfold zc
  linarith [lambda_pos i,t_pos i]

theorem zc_lt_delta (i : Row) : zc i< Uniform07.delta := by
  have hr:=requiredDemand_lt_coarse_upper i
  have he:=unconditional_requiredDemand i
  have ht:=t_pos i
  have hm:=mul_lt_mul_of_pos_left hr ht
  cases i <;> norm_num [zc,lambda,x,demandUpper,delta,Uniform07.delta] at * <;> nlinarith

theorem zc_lt_one (i : Row) : zc i<1 :=
  (zc_lt_delta i).trans (by norm_num [Uniform07.delta])

def Lprob (i : Row) (M : ℕ) : ℝ :=
  AtomEvents.lowerEvent (t i) (t_pos i).le (t_lt_one i).le M
def Hprob (i : Row) (M : ℕ) : ℝ := AtomEvents.boundaryEvent (t i) M
def Eprob (i : Row) (M : ℕ) : ℝ :=
  AtomEvents.duplicateEvent (zc i) (zc_pos i).le (zc_lt_one i).le M
def atomCoefficient (i : Row) (M : ℕ) : ℝ :=
  4*eta i*((M-1:ℕ):ℝ)*Eprob i M/((1-chi)*Lprob i M*Hprob i M)

theorem source_entropy_gap (i : Row) :
    AtomEvents.lowerRate (t i)+AtomEvents.boundaryRate (t i)< AtomEvents.duplicateRate (zc i) := by
  have h:=(Uniform07.uniform_finite_primitive_guards i).entropy_gap
  simpa only [AtomEvents.lowerRate,AtomEvents.boundaryRate,AtomEvents.duplicateRate,
    t_eq_canonical,lambda_eq_canonical,zc] using h

theorem source_double_lower_gap (i : Row) :
    2*AtomEvents.lowerRate (t i)< AtomEvents.duplicateRate (zc i) := by
  have h:=(Uniform07.uniform_finite_primitive_guards i).double_lower_gap
  simpa only [AtomEvents.lowerRate,AtomEvents.duplicateRate,t_eq_canonical,lambda_eq_canonical,zc]
    using h

theorem atomCoefficient_tendsto_zero (i : Row) : Tendsto (atomCoefficient i) atTop (𝓝 0) := by
  convert! (AtomEvents.sourceCoefficient_tendsto_zero (eta i) chi (t i) (zc i)
      (eta_range i).1 (by norm_num [chi]) (t_pos i) (t_lt_one i) (zc_pos i) (zc_lt_delta i)
      (source_entropy_gap i)) using 1

theorem atomCoefficient_eventually_small (i : Row) : ∀ᶠM : ℕ in atTop,atomCoefficient i M<1/2 :=
  (atomCoefficient_tendsto_zero i).eventually_lt_const (by norm_num : (0:ℝ)<1/2)

theorem E_over_L_square_tendsto_zero (i : Row) :
    Tendsto (fun M=> Eprob i M/(Lprob i M)^2) atTop (𝓝 0) := by
  simpa only [Eprob,Lprob] using AtomEvents.duplicate_over_lower_square_tendsto_zero
    (t i) (zc i) (t_pos i) (t_lt_one i) (zc_pos i) (zc_lt_delta i) (source_double_lower_gap i)

theorem eventually_source_events_positive (i : Row) :
    ∀ᶠM : ℕ in atTop,0< Lprob i M ∧0< Hprob i M ∧0< Eprob i M :=
  AtomEvents.eventually_LHE_pos (t i) (zc i) (t_pos i) (t_lt_one i) (zc_pos i) (zc_lt_one i)

end FCAppendix.Affine.UniformFinite
