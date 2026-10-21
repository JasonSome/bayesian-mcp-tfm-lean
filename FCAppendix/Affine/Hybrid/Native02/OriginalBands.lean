import FCAppendix.Affine.Hybrid.Native02.OriginalPopulation
import FCAppendix.Affine.Hybrid.Native02.NullTypes

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

def OriginalBandSupport (d vlo vhi _t L U R : ℝ) (x : ℝ×JointAction 2) : Prop :=
  (x.1≤ d→ x.2.bid≤ d ∧ x.2.routeCount=2) ∧
  (x.1∈ Icc vlo vhi→ x.2.bid∈ Icc L U ∧ x.2.routeCount=2) ∧
  (vhi< x.1→ R≤ x.2.bid ∧ x.2.routeCount=1)

theorem original_joint_band_support {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (s a h d vlo vhi t L U R : ℝ)
    (hdv : d< vlo) (hvv : vlo≤ vhi) (hvt : vhi< t)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint s a h PL PA PH)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),
      x.1≤ d ∧ x.2.bid≤ d ∧ x.2.routeCount=2)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),
      x.1∈ Icc vlo vhi ∧ x.2.bid∈ Icc L U ∧ x.2.routeCount=2)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),
      t≤ x.1 ∧ R≤ x.2.bid ∧ x.2.routeCount=1) :
    ∀ᵐx ∂G.F⊗ₘG.σ,OriginalBandSupport d vlo vhi t L U R x := by
  rw [hjoint]
  apply original_population_mixture_ae s a h PL PA PH
    (OriginalBandSupport d vlo vhi t L U R)
  · filter_upwards [hL] with x hx
    refine ⟨fun _=> hx.2,?_,?_⟩
    · intro hv
      have := hdv.trans_le hv.1
      exact False.elim ((not_lt.mpr hx.1) this)
    · intro ht
      have := (hdv.trans_le hvv).trans ht
      exact False.elim ((not_lt.mpr hx.1) this)
  · filter_upwards [hA] with x hx
    refine ⟨?_,fun _=> hx.2,?_⟩
    · intro hv
      have := hdv.trans_le hx.1.1
      exact False.elim ((not_lt.mpr hv) this)
    · intro ht
      exact False.elim ((not_lt.mpr hx.1.2) ht)
  · filter_upwards [hH] with x hx
    refine ⟨?_,?_,fun _=> hx.2⟩
    · intro hv
      have := ((hdv.trans_le hvv).trans hvt).trans_le hx.1
      exact False.elim ((not_lt.mpr hv) this)
    · intro hv
      exact False.elim ((not_lt.mpr (hx.1.trans hv.2)) hvt)

theorem original_conditional_band_support {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (d vlo vhi t L U R : ℝ)
    (hjoint : ∀ᵐx ∂G.F⊗ₘG.σ,OriginalBandSupport d vlo vhi t L U R x) :
    ∀ᵐv ∂G.F,∀ᵐa ∂G.σ v,OriginalBandSupport d vlo vhi t L U R (v,a) :=
  Measure.ae_ae_of_ae_compProd hjoint

theorem original_family_band_support {M C : ℕ→ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (F : Measure ℝ)
    (hF : ∀ k,(G k).F=F) (d vlo vhi t L U R : ℝ)
    (hjoint : ∀ k,∀ᵐx ∂(G k).F⊗ₘ(G k).σ,OriginalBandSupport d vlo vhi t L U R x) :
    ∃S : Set ℝ,MeasurableSet S ∧ (∀ᵐv ∂F,v∈ S) ∧
      ∀ v∈ S,∀ k,∀ᵐa ∂(G k).σ v,OriginalBandSupport d vlo vhi t L U R (v,a) := by
  apply exists_measurable_common_conull F
  apply ae_all_iff.mpr
  intro k
  simpa only [hF k] using original_conditional_band_support (G k) d vlo vhi t L U R (hjoint k)

end FCAppendix.Affine.Hybrid.Native02
