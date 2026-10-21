import FCAppendix.Existence.NarrowPayOnceAnalyticFamily
import FCAppendix.Existence.NarrowPayOnceNativeUsers

noncomputable section
namespace FCAppendix.Bayes.PayOnceNarrow
open Set Filter Topology MeasureTheory ProbabilityTheory Game CommonList PayOnce
open Existence.NarrowPayOnce

structure NativeEquilibrium (n R c : ℕ) (w0 kappa eps delta C slopeLo slopeHi : ℝ)
    (nu : Measure (Icc (w0-delta) (w0+delta))) [IsProbabilityMeasure nu] (g : ℝ) where
  analytic : AnalyticEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu
  nativeGame : FiniteGame (R+1) n c unitInterval
  posterior : PosteriorSystem nativeGame
  values : nativeGame.F=nu.map (fun v : Icc (w0-delta) (w0+delta)=>(v:ℝ)+g)
  bid_rule : nativeGame.A=Schedule.once n
  base_rule : nativeGame.G=Schedule.once n
  fee : nativeGame.g=g
  users : UsersOptimal nativeGame
  proposers : PosteriorProposerOptimalAE nativeGame posterior
  symmetric : SymmetricProposersOnPath nativeGame
  pure : ∀v : analytic.control.valueBand,
    nativeGame.σ ((v:ℝ)+g)=Measure.dirac (playedAction analytic.control analytic.bid v)
  bid_law : realBidLaw nativeGame=nu.map analytic.bid.val
  positive : ∀(i : Fin (R+1)) (v : analytic.control.valueBand),
    0<(problem nativeGame i).payoff ((v:ℝ)+g) (playedAction analytic.control analytic.bid v)
  route_gain : ∀(i : Fin (R+1)) (v : analytic.control.valueBand) (a : JointAction n),
    a.bid=analytic.bid.val v → a.routeCount<n →
    (problem nativeGame i).payoff ((v:ℝ)+g) a<
      (problem nativeGame i).payoff ((v:ℝ)+g) (playedAction analytic.control analytic.bid v)

namespace NativeEquilibrium
variable {n R c : ℕ} {w0 kappa eps delta C slopeLo slopeHi g : ℝ}
  {nu : Measure (Icc (w0-delta) (w0+delta))} [IsProbabilityMeasure nu]
  (E : NativeEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu g)

theorem bidLaw_atomless [NullSingletonClass nu] : NullSingletonClass (realBidLaw E.nativeGame) := by
  rw [E.bid_law]
  exact E.analytic.bid_law_atomless
end NativeEquilibrium

def nativeOfAnalytic {n R c : ℕ} {w0 kappa eps delta C slopeLo slopeHi : ℝ}
    {nu : Measure (Icc (w0-delta) (w0+delta))} [IsProbabilityMeasure nu]
    (E : AnalyticEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu)
    (g : ℝ) (hg : 0≤g) : NativeEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu g where
  analytic:=E
  nativeGame:=game E.control nu E.bid g hg
  posterior:=posterior E.control nu E.bid g hg
  values:=rfl
  bid_rule:=rfl
  base_rule:=rfl
  fee:=rfl
  users:=usersOptimal E.control nu E.bid g hg E.stationary E.globalOptimal
  proposers:=proposer_optimal E.control nu E.bid g hg
  symmetric:=symmetric E.control nu E.bid g hg
  pure:=strategy_at_physical E.control nu E.bid g hg
  bid_law:=real_bid_law E.control nu E.bid g hg
  positive:=played_payoff_positive E.control nu E.bid g hg E.stationary
  route_gain:=fewer_routes_strict E.control nu E.bid g hg E.stationary

theorem exists_uniform_native_family {n : ℕ} (hn : 2≤n) {w0 lo hi : ℝ}
    (hw0 : 0<w0) (hlo : 0<lo) (hlohi : lo≤hi) (hhi : hi<1) :
    ∃kappa eps deltaStar C slopeLo slopeHi : ℝ,
      0<kappa ∧ 0<eps ∧ 0<deltaStar ∧ 0<C ∧ 0<slopeLo ∧ 0<slopeHi ∧ deltaStar≤w0/2 ∧
      ∀(R c : ℕ),1≤c → c≤R → density R c∈Icc lo hi →
      ∀delta∈Icc (0:ℝ) deltaStar,
      ∀(nu : Measure (Icc (w0-delta) (w0+delta))) [IsProbabilityMeasure nu],
      ∀(g : ℝ),0≤g → Nonempty (NativeEquilibrium n R c w0 kappa eps delta C slopeLo slopeHi nu g) := by
  obtain ⟨kappa,eps,deltaStar,C,slopeLo,slopeHi,hk,he,hd,hC,hL,hH,hdw,hfamily⟩ :=
    exists_uniform_analytic_family hn hw0 hlo hlohi hhi
  refine ⟨kappa,eps,deltaStar,C,slopeLo,slopeHi,hk,he,hd,hC,hL,hH,hdw,?_⟩
  intro R c hc hcR hrho delta hdelta nu _ g hg
  obtain ⟨E⟩:=hfamily R c hc hcR hrho delta hdelta nu
  exact ⟨nativeOfAnalytic E g hg⟩

end FCAppendix.Bayes.PayOnceNarrow
