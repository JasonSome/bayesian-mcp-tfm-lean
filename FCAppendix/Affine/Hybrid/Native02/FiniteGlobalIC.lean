import FCAppendix.Affine.Hybrid.Native02.PrimitiveMenuMargins

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set MeasureTheory ProbabilityTheory Game Bayes Filter Topology

theorem active_finite_global_IC {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (hg : G.g=0)
    (i : Fin m) (v d L U R u2 u1 m1 ex2 delta eps : ℝ)
    (hdL : d< L) (hLU : L≤ U) (hUR : U< R) (he : 0≤ eps)
    (hsmall : 2*eps< delta)
    (hgap0 : delta≤ u2) (hgap1 : u1+delta≤ u2)
    (hgapM : m1+delta≤ u2) (hgapE : ex2+delta≤ u2)
    (hgapR : v-R+delta≤ u2)
    (star test : JointAction 2) (htest : test.bid∈ Icc L U) (htest2 : test.routeCount=2)
    (hIC : ∀ a : JointAction 2,a.bid∈ Icc L U→ a.routeCount=2→
      (problem G i).payoff v a≤(problem G i).payoff v star)
    (hvalue : u2-eps≤(problem G i).payoff v test)
    (hlow : ∀ a : JointAction 2,a.bid≤ d→(problem G i).payoff v a≤ eps)
    (hbox1 : ∀ a : JointAction 2,a.routeCount=1→ a.bid∈ Icc L U→
      (problem G i).payoff v a≤ u1+eps)
    (hex1 : ∀ a : JointAction 2,a.routeCount=1→ d< a.bid→ a.bid< R→ a.bid∉Icc L U→
      (problem G i).payoff v a≤ m1+eps)
    (hex2 : ∀ a : JointAction 2,a.routeCount=2→ d< a.bid→ a.bid< R→ a.bid∉Icc L U→
      (problem G i).payoff v a≤ ex2+eps) :
    (problem G i).BestResponse v star := by
  have hinc : u2-eps≤(problem G i).payoff v star :=
    hvalue.trans (hIC test htest htest2)
  have hstar : 0≤(problem G i).payoff v star := by linarith
  have hupper (a : JointAction 2) (ha : R≤ a.bid) :
      (problem G i).payoff v a≤(problem G i).payoff v star := by
    apply (raw_above_floor_payoff_le G hg i v R a ha).trans
    apply max_le
    · linarith
    · exact hstar
  apply all_joint_actions_of_finite_bounds G hg i v d L U R hdL hLU hUR star hstar
  · intro a ha
    have := hlow a ha
    linarith
  · intro a ha hb
    have := hbox1 a ha hb
    linarith
  · intro a ha hb
    exact hIC a hb ha
  · intro a ha hd hr hb
    have := hex1 a ha hd hr hb
    linarith
  · intro a ha hd hr hb
    have := hex2 a ha hd hr hb
    linarith
  · intro a _ ha
    exact hupper a ha
  · intro a _ ha
    exact hupper a ha

theorem upper_finite_global_IC {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (G : FiniteGame m 2 c Seed) (hg : G.g=0)
    (i : Fin m) (v d L U R u2 u1 m1 m2 delta eps : ℝ)
    (hdL : d< L) (hLU : L≤ U) (hUR : U< R) (he : 0≤ eps)
    (hsmall : 2*eps< delta)
    (hgap0 : delta≤ v-R) (hgap2 : u2+delta≤ v-R)
    (hgap1 : u1+delta≤ v-R) (hgapM : m1+delta≤ v-R)
    (hgapE : m2+delta≤ v-R)
    (star : JointAction 2) (hinc : v-R-eps≤(problem G i).payoff v star)
    (hlow : ∀ a : JointAction 2,a.bid≤ d→(problem G i).payoff v a≤ eps)
    (hbox1 : ∀ a : JointAction 2,a.routeCount=1→ a.bid∈ Icc L U→
      (problem G i).payoff v a≤ u1+eps)
    (hbox2 : ∀ a : JointAction 2,a.routeCount=2→ a.bid∈ Icc L U→
      (problem G i).payoff v a≤ u2+eps)
    (hex1 : ∀ a : JointAction 2,a.routeCount=1→ d< a.bid→ a.bid< R→ a.bid∉Icc L U→
      (problem G i).payoff v a≤ m1+eps)
    (hex2 : ∀ a : JointAction 2,a.routeCount=2→ d< a.bid→ a.bid< R→ a.bid∉Icc L U→
      (problem G i).payoff v a≤ m2+eps)
    (hupper1 : ∀ a : JointAction 2,a.routeCount=1→ R≤ a.bid→
      (problem G i).payoff v a≤(problem G i).payoff v star)
    (hupper2 : ∀ a : JointAction 2,a.routeCount=2→ R≤ a.bid→
      (problem G i).payoff v a≤(problem G i).payoff v star) :
    (problem G i).BestResponse v star := by
  have hstar : 0≤(problem G i).payoff v star := by linarith
  apply all_joint_actions_of_finite_bounds G hg i v d L U R hdL hLU hUR star hstar
  · intro a ha
    have := hlow a ha
    linarith
  · intro a ha hb
    have := hbox1 a ha hb
    linarith
  · intro a ha hb
    have := hbox2 a ha hb
    linarith
  · intro a ha hd hr hb
    have := hex1 a ha hd hr hb
    linarith
  · intro a ha hd hr hb
    have := hex2 a ha hd hr hb
    linarith
  · exact hupper1
  · exact hupper2

end FCAppendix.Affine.Hybrid.Native02
