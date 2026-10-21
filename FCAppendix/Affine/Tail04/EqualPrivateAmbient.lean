import FCAppendix.Affine.Tail04.FrontierPushforward
import FCAppendix.Affine.Tail04.PrivatePayoffContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateAmbient
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateFrontier EqualPrivateContinuity
open Existence.Distributional
open scoped BigOperators

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

def widen {a b b' : ℝ} (h : b≤ b') (x : Icc a b) : Icc a b' :=
  ⟨x, x.2.1,x.2.2.trans h⟩

lemma continuous_widen {a b b' : ℝ} (h : b≤ b') : Continuous (widen (a:=a) h) :=
  continuous_subtype_val.subtype_mk _

def entry {R V W : ℝ} (hVW : V≤ W) : Unit⊕Icc R V→ Unit⊕Icc R W :=
  Sum.map id (widen hVW)

lemma continuous_entry {R V W : ℝ} (hVW : V≤ W) : Continuous (entry (R:=R) hVW) :=
  continuous_sum_dom.mpr ⟨continuous_inl,continuous_inr.comp (continuous_widen hVW)⟩

def signal {H : ℕ} {R V W : ℝ} (hVW : V≤ W) (s : Signal H R V) : Signal H R W :=
  fun j => entry hVW (s j)

lemma continuous_signal {H : ℕ} {R V W : ℝ} (hVW : V≤ W) :
    Continuous (signal (H:=H) (R:=R) hVW) :=
  continuous_pi (fun j => (continuous_entry hVW).comp (continuous_apply j))

@[simp] lemma marks_signal {H : ℕ} {R V W : ℝ} (hVW : V≤ W) (s : Signal H R V) :
    marks (signal hVW s)=marks s := by
  funext j
  simp only [marks,signal]
  cases h : s j <;> rfl

@[simp] lemma partialBid_entry {R V W : ℝ} (hVW : V≤ W) (x : Unit⊕Icc R V) :
    partialBid (entry hVW x)=partialBid x := by
  cases x <;> rfl

@[simp] lemma selected_signal {N H c : ℕ} {R V W : ℝ}
    (hVW : V≤ W) (s : Signal H R V) (a : Action N H c) :
    selected (signal hVW s) a=selected s a := by
  unfold selected
  rw [marks_signal]

lemma activeIndicator_signal {N H c : ℕ} {R V W : ℝ}
    (hVW : V≤ W) (i : Fin N) (s : Signal H R V) (a : Action N H c) :
    activeIndicator N H c R W i (signal hVW s,a)=activeIndicator N H c R V i (s,a) := by
  simp only [activeIndicator,ContinuousMap.coe_mk,selected_signal]

lemma privateReceipt_signal {N H c : ℕ} {R V W : ℝ}
    (hVW : V≤ W) (s : Signal H R V) (a : Action N H c) :
    privateReceipt N H c R W (signal hVW s,a)=privateReceipt N H c R V (s,a) := by
  simp only [privateReceipt,ContinuousMap.coe_mk,selected_signal,signal,partialBid_entry]

def law {H : ℕ} {R V W : ℝ} (hVW : V≤ W) (μ : WeakProbability.Law (Signal H R V)) :
    WeakProbability.Law (Signal H R W) :=
  ⟨μ.val.map (continuous_signal hVW).measurable.aemeasurable⟩

lemma continuous_law {H : ℕ} {R V W : ℝ} (hVW : V≤ W) :
    Continuous (law (H:=H) (R:=R) hVW) :=
  WeakProbability.continuous_mk.comp
    ((ProbabilityMeasure.continuous_map (continuous_signal hVW)).comp WeakProbability.continuous_val)

def parameter {N H : ℕ} {R V W B B' : ℝ} (hVW : V≤ W) (hBB' : B≤ B')
    (p : PolicyParameters N H R V 1 B) : PolicyParameters N H R W 1 B' :=
  (fun i => widen hBB' (p.1 i),law hVW p.2)

lemma continuous_parameter {N H : ℕ} {R V W B B' : ℝ} (hVW : V≤ W) (hBB' : B≤ B') :
    Continuous (parameter (N:=N) (H:=H) (R:=R) hVW hBB') :=
  (continuous_pi (fun i => (continuous_widen hBB').comp
    ((continuous_apply i).comp continuous_fst))).prodMk ((continuous_law hVW).comp continuous_snd)

@[simp] lemma bids_parameter {N H : ℕ} {R V W B B' : ℝ}
    (hVW : V≤ W) (hBB' : B≤ B') (p : PolicyParameters N H R V 1 B) :
    EqualPrivateMeasurable.bids (parameter hVW hBB' p)=EqualPrivateMeasurable.bids p := rfl

theorem policyMean_parameter {N H c : ℕ} {R V W B B' ξ : ℝ}
    (hVW : V≤ W) (hBB' : B≤ B') (hξ : 0< ξ)
    (p : PolicyParameters N H R V 1 B) :
    policyMean N H c R W ξ 1 B' (parameter hVW hBB' p)=
      policyMean N H c R V ξ 1 B p := by
  let p' := parameter hVW hBB' p
  let x := activeIndicator N H c R V
  let y := activeIndicator N H c R W
  let r := privateReceipt N H c R V
  let s := privateReceipt N H c R W
  let μ := WeakProbability.toMeasure p.2
  let f := signal (H:=H) (R:=R) hVW
  have hf : Continuous f := continuous_signal hVW
  let π : Plan (A:=Action N H c) μ :=
    ⟨(policyLaw N H c R V ξ 1 B p).val,
      congrArg (fun ν : ProbabilityMeasure (Signal H R V) => (ν : Measure (Signal H R V)))
        (EqualPrivateMeasurable.planLaw_spec x r ξ 1 B p).1⟩
  let τ : Plan (A:=Action N H c) (μ.map f) :=
    ⟨(policyLaw N H c R W ξ 1 B' p').val,
      congrArg (fun ν : ProbabilityMeasure (Signal H R W) => (ν : Measure (Signal H R W)))
        (EqualPrivateMeasurable.planLaw_spec y s ξ 1 B' p').1⟩
  have hπ : IntegralOptimal π (score x r (EqualPrivateMeasurable.bids p) (marginal x π) ξ) :=
    integralOptimal_of_gap_eq_zero x r (EqualPrivateMeasurable.bids p) ξ μ π
      (EqualPrivateMeasurable.planLaw_spec x r ξ 1 B p).2
  have hτ : IntegralOptimal τ (score y s (EqualPrivateMeasurable.bids p) (marginal y τ) ξ) := by
    exact integralOptimal_of_gap_eq_zero y s (EqualPrivateMeasurable.bids p') ξ (μ.map f) τ
      (EqualPrivateMeasurable.planLaw_spec y s ξ 1 B' p').2
  have hh := FrontierPushforward.mean_eq μ f hf x r y s
    (activeIndicator_signal hVW) (privateReceipt_signal hVW)
    (EqualPrivateMeasurable.bids p) ξ hξ
    (fun i => (by norm_num : (0:ℝ)<1).trans_le (p.1 i).2.1) π τ hπ hτ
  exact hh.symm

theorem privateValue_signal {N H c : ℕ} {R V W ξ : ℝ}
    (hVW : V≤ W) (b q : Fin N→ℝ) (s : Signal H R V) (j : Fin H) :
    PrivatePayoffContinuity.privateValue (c:=c) ξ j (b,q,signal hVW s)=
      PrivatePayoffContinuity.privateValue (c:=c) ξ j (b,q,s) := by
  have he : PrivatePayoffContinuity.inputScore (c:=c) ξ (b,q,signal hVW s)=
      PrivatePayoffContinuity.inputScore (c:=c) ξ (b,q,s) := by
    funext a
    simp only [PrivatePayoffContinuity.inputScore,revenue,selected_signal,signal,partialBid_entry]
  simp only [PrivatePayoffContinuity.privateValue,PrivatePayoffContinuity.chosen,he,
    privateIndicator,ContinuousMap.coe_mk,selected_signal]

end FCAppendix.Affine.Tail04.EqualPrivateAmbient
