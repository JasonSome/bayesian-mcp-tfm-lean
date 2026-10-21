import FCAppendix.Affine.LowBody.HiddenRoute
import FCAppendix.Existence.RankEnvelopeRoutes

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Bayes Set
open Existence.RankEnvelope
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem native_broadcast_duplicates_lower (Gamma : FiniteGame m 2 c Seed)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount=2) (delta : ℝ)
    (hmean : 1-delta ≤ meanAcceptProb Gamma i a.bid) :
    1-2*delta ≤ ((problem Gamma i).outcome a).duplicates := by
  have hl:=load_eq_mean Gamma (by norm_num : 0<2) i a
  rw [hk,Nat.cast_ofNat] at hl
  unfold CountLaw.duplicates
  linarith [((problem Gamma i).outcome a).success_le_one]

theorem native_hidden_upper_excluded (Gamma : FiniteGame m 2 c Seed) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : Gamma.A=Schedule.affine 2 η hη0 hη1)
    (hg : Gamma.g=0) {q : ℝ→ℝ} (hq : Monotone q) (hq1 : ∀x,q x ≤ 1)
    {t R v delta : ℝ} (hR : 0<R) (hRt : R<t) (hqt : 0<q t)
    (hint : IntegrableOn (fun x=>1-q x) (Ioi t))
    (hguard : error q t R<η*R*(1-2*delta)) (hv : t ≤ v)
    (i : Fin m) (a : JointAction 2) (hk : a.routeCount=2) (hb : R ≤ a.bid)
    (hmean : 1-delta ≤ meanAcceptProb Gamma i a.bid) :
    (problem Gamma i).payoff v a<utility q t R v := by
  have hD:=native_broadcast_duplicates_lower Gamma i a hk delta hmean
  by_cases hbv : a.bid ≤ v
  · have hE:=error_nonneg hRt.le hq1
    have hd : 0 ≤ 1-2*delta:=by
      by_contra hn
      have hh:=mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hη0 hR.le) (le_of_not_ge hn)
      linarith
    have hu:=two_route_upper_bound ((problem Gamma i).outcome a) hη0 hη1 hR.le hb hbv hd hD Gamma.G
    change ((problem Gamma i).outcome a).utility v a.bid Gamma.g Gamma.A Gamma.G<_
    rw [hA,hg]
    have hU:=utility_error_bound hq (R:=R) hv hq1 hint
    linarith
  · have hu:=affine_above_value_nonpositive ((problem Gamma i).outcome a) hη0 hη1
      a.bid_nonneg (le_of_not_ge hbv) Gamma.G
    change ((problem Gamma i).outcome a).utility v a.bid Gamma.g Gamma.A Gamma.G<_
    rw [hA,hg]
    exact hu.trans_lt (utility_pos hq hRt hqt hv)

end FCAppendix.Affine.Hybrid
