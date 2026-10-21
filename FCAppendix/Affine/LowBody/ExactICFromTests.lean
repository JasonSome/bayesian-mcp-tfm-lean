import FCAppendix.Affine.LowBody.ExactPayoffBounds
import FCAppendix.Affine.LowBody.ICFromContinuousTests

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
variable {N : ℕ}

attribute [local irreducible] exactExpectedPayoff

theorem fixed_positive_bid_IC_of_tests {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hB : 0<B)
    (c : ℕ) (categories : FiniteLaw (Fin 4)) (G : ProbabilityMeasure (LowValue d))
    [NullSingletonClass (G : Measure (LowValue d))]
    (pi : ProbabilityMeasure (LowValue d×LowValue d))
    (hpos : ∀ᵐx ∂(pi : Measure (LowValue d×LowValue d)),0<x.2.1)
    (htest : ∀a : C(LowValue d×LowValue d,ℝ),
      (∀x,0≤a x)→(∀x : LowValue d×LowValue d,x.1.1≤B→a x=0)→
      ∫x,a x*(exactExpectedPayoff N d ξ c categories G (x.1.1,B)-
        exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)) ∂(pi : Measure (LowValue d×LowValue d))≤0) :
    ∀ᵐx ∂(pi : Measure (LowValue d×LowValue d)),B<x.1.1→exactExpectedPayoff N d ξ c categories G (x.1.1,B)≤
      exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1) := by
  let s : Set (LowValue d×LowValue d):={x | x.2.1=0 ∨ x.1.1≤B}
  let f : LowValue d×LowValue d→ℝ:=fun x=>
    exactExpectedPayoff N d ξ c categories G (x.1.1,B)-
      exactExpectedPayoff N d ξ c categories G (x.1.1,x.2.1)
  have hs : IsClosed s := (isClosed_eq continuous_snd.subtype_val continuous_const).union
    (isClosed_le continuous_fst.subtype_val continuous_const)
  have hf : Measurable f :=
    ((measurable_exactExpectedPayoff hξ hξ1 c categories G).comp
      (measurable_fst.subtype_val.prodMk measurable_const)).sub
    ((measurable_exactExpectedPayoff hξ hξ1 c categories G).comp
      (measurable_fst.subtype_val.prodMk measurable_snd.subtype_val))
  let K : ℝ:=3+2*|1-ξ|
  let C : ℝ:=2*|d|+K*(|B|+|d|)
  have hC : 0≤C:=by dsimp [C,K]; positivity
  have hbound (x : LowValue d×LowValue d) : |f x|≤C := by
    have hw : |x.1.1|≤|d| := by rw [abs_of_nonneg x.1.property.1]; exact x.1.property.2.trans (le_abs_self d)
    have hb : |x.2.1|≤|d| := by rw [abs_of_nonneg x.2.property.1]; exact x.2.property.2.trans (le_abs_self d)
    have hd:=abs_exactExpectedPayoff_le (N:=N) hξ hξ1 c categories G (x.1.1,B)
    have hi:=abs_exactExpectedPayoff_le (N:=N) hξ hξ1 c categories G (x.1.1,x.2.1)
    exact (abs_sub _ _).trans (by dsimp [C,K]; nlinarith [abs_nonneg (1-ξ)])
  have hcont : ∀x∉s,ContinuousAt f x := by
    intro x hx
    have hp : 0<x.2.1 := lt_of_le_of_ne x.2.property.1 (fun he=>hx (Or.inl he.symm))
    have hd:= (continuousAt_exactExpectedPayoff (N:=N) hξ hξ1 c categories G (x.1.1,B) hB).comp
      (f:=fun y : LowValue d×LowValue d=>(y.1.1,B)) (x:=x) (by fun_prop)
    have hi:= (continuousAt_exactExpectedPayoff (N:=N) hξ hξ1 c categories G (x.1.1,x.2.1) hp).comp
      (f:=fun y : LowValue d×LowValue d=>(y.1.1,y.2.1)) (x:=x) (by fun_prop)
    exact hd.sub hi
  have hh:=ae_nonpos_outside_closed_of_tests (pi : Measure (LowValue d×LowValue d)) f hf s hs hcont hC hbound
    (fun a ha has=>htest a ha (fun x hx=>has x (Or.inr hx)))
  filter_upwards [hh,hpos] with x hx hp hw
  exact sub_nonpos.mp (hx (by
    rintro (hzero|hn)
    · exact hp.ne' hzero
    · exact not_le_of_gt hw hn))

end FCAppendix.Affine.LowBody
