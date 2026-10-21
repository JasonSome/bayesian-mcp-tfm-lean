import FCAppendix.Affine.Hybrid.PureRelabel
import FCAppendix.Affine.Hybrid.EqualRelabel
import FCAppendix.Affine.LowBody.NullHyperplanes
import FCAppendix.Affine.LowBody.ResidualOutcomes

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def PureTemplate.userPayoff (T : PureTemplate ι) (ξ w : ℝ) (b : ι→ℝ) (i : ι) : ℝ:=
  if T.residual₀=T.residual₁ then equalPayoff ξ T.residual₀ i w b
  else purePayoff (1-ξ) w b (T.selection (1-ξ) b) i

lemma PureTemplate.userPayoff_relabel (T : PureTemplate ι) (e : Equiv.Perm ι)
    {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (w : ℝ) (b : ι→ℝ) (i : ι)
    (hgeneric : ∀P Q,T.Feasible P → T.Feasible Q →
      CompleteInformation.potential (1-ξ) b P.1 P.2=CompleteInformation.potential (1-ξ) b Q.1 Q.2 →
      focalCopy P i=focalCopy Q i) :
    (T.relabel e).userPayoff ξ w (b ∘ e.symm) (e i)=T.userPayoff ξ w b i := by
  unfold userPayoff
  simp only [relabel]
  by_cases he : T.residual₀=T.residual₁
  · rw [if_pos he,if_pos he]
    exact equalPayoff_relabel e hξ hξ1 T.residual₀ w b i
  · rw [if_neg he,if_neg he]
    exact T.selection_payoff_relabel e (1-ξ) w b i hgeneric

theorem ae_pattern_userPayoff_relabel {N : ℕ} {d ξ b : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hb : b≠0) (mu : Measure (LowValue d))
    [IsProbabilityMeasure mu] [NullSingletonClass mu] (c : ℕ) (kind : Fin N→Fin 4)
    (e : Equiv.Perm (Fin (N+1))) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀w : ℝ,
      ((patternTemplate c kind).relabel e).userPayoff ξ w
        (actualPatternBids kind d b r ∘ e.symm) (e 0)=
        patternPayoff ξ c kind w (actualPatternBids kind d b r) := by
  filter_upwards [ae_pattern_ties_same_focalCopy (sub_pos.mpr hξ1) hb mu kind] with r hr w
  exact (patternTemplate c kind).userPayoff_relabel e hξ hξ1 w
    (actualPatternBids kind d b r) 0 (fun P Q _ _ h=>hr P Q h)

end FCAppendix.Affine.LowBody
