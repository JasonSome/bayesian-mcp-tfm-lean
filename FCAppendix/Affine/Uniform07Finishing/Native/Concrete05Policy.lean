import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Adapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators

theorem upper_value_measure_eq (row : Uniform07.Row) :
    UniformFinite.OriginalPopulation.upperValue row=
      (sourceUpperValueLaw row : Measure ℝ) := by
  rw [sourceUpperValueLaw_literal]
  simp only [UniformFinite.OriginalPopulation.upperValue,Uniform05.t_eq_canonical]
  congr 1
  ext S hS
  rw [Measure.restrict_apply hS,Measure.restrict_apply hS]
  apply measure_congr
  filter_upwards [(volume : Measure ℝ).ae_ne (Uniform07.cutoff row)] with v hv
  apply propext
  constructor
  · rintro ⟨hS,hlo,hhi⟩
    exact ⟨hS,hlo.le,hhi⟩
  · rintro ⟨hS,hlo,hhi⟩
    exact ⟨hS,lt_of_le_of_ne hlo (Ne.symm hv),hhi⟩

def upperPriorityLaw (row : Uniform07.Row) (m : ℕ) (hm : 2≤ m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    UniformFinite.OriginalPopulation.UpperPriorityLaw row R where
  sigma := Kernel.deterministic (Hybrid.upperAction (sourceUpperBid row m R))
    (Hybrid.measurable_upperAction _ (sourceUpperBid_measurable row m hc R))
  markov := inferInstance
  priority := by
    rw [upper_value_measure_eq]
    filter_upwards [sourceUpperValueLaw_support row] with v hv
    have hb := (source_upper_envelope row m hm hc hR hRt).bid_bounds v hv.1
    rw [Kernel.deterministic_apply]
    apply (ae_dirac_iff (by
      exact (measurableSet_le measurable_const (measurable_bid 2)).inter
        (measurableSet_eq_fun (measurable_routeCount 2) measurable_const))).mpr
    simpa only [
      Hybrid.upperAction,max_eq_left (hR.le.trans hb.1)] using
      (show R≤ sourceUpperBid row m R v ∧ (1:ℕ)=1 from ⟨hb.1,rfl⟩)

theorem upperPriorityLaw_kernel (row : Uniform07.Row) (m : ℕ) (hm : 2≤ m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) (v : ℝ) :
    (upperPriorityLaw row m hm hc R hR hRt).sigma v=
      Measure.dirac (Hybrid.upperAction (sourceUpperBid row m R) v) := rfl

theorem upperPriorityLaw_joint (row : Uniform07.Row) (m : ℕ) (hm : 2≤ m)
    (hc : 1≤ Uniform07.capacity m) (R : ℝ) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    (UniformFinite.OriginalPopulation.upperJoint
      (upperPriorityLaw row m hm hc R hR hRt) : Measure (ℝ×JointAction 2))=
        (sourceUpperJoint row m hc R : Measure (ℝ×JointAction 2)) := by
  change UniformFinite.OriginalPopulation.upperValue row⊗ₘ
    Kernel.deterministic (Hybrid.upperAction (sourceUpperBid row m R))
      (Hybrid.measurable_upperAction _ (sourceUpperBid_measurable row m hc R))=_
  rw [upper_value_measure_eq,Measure.compProd_deterministic]
  rfl

section Market
variable {row : Uniform07.Row} {m : ℕ} {R : ℝ}

def game (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  W.game (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt)

def belief (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) : PosteriorSystem (game W hc hR hRt) :=
  W.belief (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt)

theorem value_law (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    (game W hc hR hRt).F=Uniform07.uniformLaw := rfl

theorem joint_law (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    (game W hc hR hRt).F⊗ₘ(game W hc hR hRt).σ=
      (sourcePopulation row m hc R (lowerJoint W.finite.restricted) :
        Measure (ℝ×JointAction 2)) := by
  let E := W.finite.restricted
  let H := upperPriorityLaw row m E.cluster.market_two_le hc R hR hRt
  letI : NeZero m := E.marketNeZero
  change (UniformFinite.Late.StrictOriginal.game E H).F⊗ₘ
    (UniformFinite.Late.StrictOriginal.game E H).σ=_
  rw [UniformFinite.Late.StrictOriginal.game_joint,
    UniformFinite.OriginalPopulation.fullLaw_mixture,sourcePopulation_literal]
  rw [show (UniformFinite.OriginalPopulation.upperJoint H : Measure (ℝ×JointAction 2))=
      (sourceUpperJoint row m hc R : Measure (ℝ×JointAction 2)) from
    upperPriorityLaw_joint row m E.cluster.market_two_le hc R hR hRt]
  simp only [Uniform05.t_eq_canonical,lowerJoint]
  rfl

theorem user_law (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    userLaw (game W hc hR hRt)=
      (sourcePopulation row m hc R (lowerJoint W.finite.restricted) :
        Measure (ℝ×JointAction 2)).prod (permLaw 2) := by
  rw [userLaw,joint_law]

theorem proposer_optimal (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    ∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal (Uniform07.capacity m)
        (beliefReceipts (game W hc hR hRt).A
          (posteriorCountBelief (game W hc hR hRt) (belief W hc hR hRt) j L) L)
        ((game W hc hR hRt).policy j L s).val :=
  W.proposer_optimal
    (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt)

theorem fixed_lower_kernel (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) (v : UniformFinite.Value row) :
    (game W hc hR hRt).σ v=(W.finite.restricted.sigma v).map
      (fun q=>UniformFinite.OriginalPopulation.lowerAction row (v,q)) :=
  W.lower_kernel
    (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt) v

theorem fixed_upper_kernel (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) (v : ℝ) (hv : Uniform07.cutoff row< v) :
    (game W hc hR hRt).σ v=
      Measure.dirac (Hybrid.upperAction (sourceUpperBid row m R) v) := by
  let E := W.finite.restricted
  let H := upperPriorityLaw row m E.cluster.market_two_le hc R hR hRt
  letI : NeZero m := E.marketNeZero
  change (UniformFinite.Late.StrictOriginal.game E H).σ v=_
  rw [UniformFinite.Late.StrictOriginal.game_nonlower_kernel E H v]
  · rfl
  · rw [Uniform05.t_eq_canonical]
    exact fun h=>not_lt_of_ge h.2 hv

theorem common_broadcast_IC (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) :
    ∀ᵐp∂(W.finite.restricted.pi.1 :
        Measure (UniformFinite.Value row×unitInterval)),
      ∀u : Fin m,∀a : JointAction 2,a.routeCount=2→ a.bid< R→
        (problem (game W hc hR hRt) u).payoff p.1 a≤
          (problem (game W hc hR hRt) u).payoff p.1
            (UniformFinite.OriginalPopulation.lowerAction row p) :=
  (W.actual
    (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt)).broadcast_IC

theorem fixed_lower_count_law
    (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) (u : Fin m) (v : UniformFinite.Value row) :
    typeOutcome (game W hc hR hRt) u v=W.typeLaw u v :=
  W.typeOutcome_eq
    (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt) u v

theorem fixed_lower_trace_integral
    (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (hc : 1≤ Uniform07.capacity m) (hR : 0< R)
    (hRt : R< Uniform07.cutoff row) (u : Fin m) (v : UniformFinite.Value row)
    (f : Bool×Bool→ℝ) :
    (W.typeTraceLaw u v).expect f=
      ∫a,∫ω,f (UniformFinite.NativeRoutes.sampleTrace (game W hc hR hRt) u a ω)
        ∂sampleLaw (game W hc hR hRt) ∂(game W hc hR hRt).σ v :=
  W.typeTraceLaw_fixed_kernel
    (upperPriorityLaw row m W.finite.restricted.cluster.market_two_le hc R hR hRt) u v f

end Market
end FCAppendix.Affine.Uniform07Finishing.Concrete05
