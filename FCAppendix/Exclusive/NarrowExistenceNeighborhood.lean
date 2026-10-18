import FCAppendix.Exclusive.NarrowExistenceReference
import FCAppendix.Exclusive.NarrowLocalIdentification
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set Filter Topology

abbrev RowState := Fin 5 → ℝ

def normalizedR (S' T' H' : ℝ → ℝ) (x : RowState) : ℝ :=
  x 3*S' (1-x 0) - x 2*T' (1-x 0) - x 4*H' (1-x 0)

def normalizedCurvature (r : ℝ) (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (x : RowState) : ℝ :=
  -ownHessian r (x 0) (x 1) (x 2) (normalizedR S' T' H' x)
    (normalizedR S'' T'' H'' x) (T (1-x 0)) (T' (1-x 0))

def normalizedInfluence (r : ℝ) (S' S'' T' T'' H' H'' : ℝ → ℝ)
    (x : RowState) : ℝ :=
  crossCoefficient r (x 0) (x 1) (x 2) (normalizedR S' T' H' x)
    (normalizedR S'' T'' H'' x) (T' (1-x 0))

theorem continuous_normalizedR (S' T' H' : ℝ → ℝ)
    (hS : Continuous S') (hT : Continuous T') (hH : Continuous H') :
    Continuous (normalizedR S' T' H') := by
  unfold normalizedR
  fun_prop

theorem continuous_normalizedCurvature (r : ℝ)
    (S' S'' T T' T'' H' H'' : ℝ → ℝ)
    (hS : Continuous S') (hS' : Continuous S'')
    (hT : Continuous T) (hT' : Continuous T') (hT'' : Continuous T'')
    (hH : Continuous H') (hH' : Continuous H'') :
    Continuous (normalizedCurvature r S' S'' T T' T'' H' H'') := by
  unfold normalizedCurvature ownHessian normalizedR
  fun_prop

theorem continuous_normalizedInfluence (r : ℝ)
    (S' S'' T' T'' H' H'' : ℝ → ℝ)
    (hS : Continuous S') (hS' : Continuous S'')
    (hT' : Continuous T') (hT'' : Continuous T'')
    (hH : Continuous H') (hH' : Continuous H'') :
    Continuous (normalizedInfluence r S' S'' T' T'' H' H'') := by
  unfold normalizedInfluence crossCoefficient normalizedR
  fun_prop

theorem compact_curvature_neighborhood {X : Type*} [MetricSpace X]
    (K C : X → ℝ) (hK : Continuous K) (hC : Continuous C)
    (A : Set X) (hA : IsCompact A) (hne : A.Nonempty)
    (hpos : ∀ x ∈ A, 0 < K x)
    (hbound : ∀ x ∈ A, |C x| ≤ (2/3:ℝ)*K x) :
    ∃ kappa delta : ℝ, 0 < kappa ∧ 0 < delta ∧
      ∀ x ∈ A, ∀ y : X, dist y x < delta →
        kappa < K y ∧ |C y| < (3/4:ℝ)*K y := by
  obtain ⟨x0, hx0, hmin⟩ := hA.exists_isMinOn hne hK.continuousOn
  have h0 := hpos x0 hx0
  let kappa := K x0/2
  let U : Set X := {x | kappa < K x ∧ |C x| < (3/4:ℝ)*K x}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const hK).inter (isOpen_lt hC.abs (hK.const_mul (3/4:ℝ)))
  have hAU : A ⊆ U := by
    intro x hx
    have hm := hmin hx
    change K x0 ≤ K x at hm
    have hp := hpos x hx
    have hb := hbound x hx
    change kappa < K x ∧ |C x| < (3/4:ℝ)*K x
    dsimp [kappa]
    constructor <;> linarith
  obtain ⟨delta, hd, hthick⟩ := hA.exists_thickening_subset_open hopen hAU
  refine ⟨kappa, delta, by dsimp [kappa]; positivity, hd, ?_⟩
  intro x hx y hdist
  apply hthick
  exact Metric.mem_thickening_iff.mpr ⟨x, hx, hdist⟩

theorem compact_curvature_bounds {X : Type*} [TopologicalSpace X]
    (K C : X → ℝ) (hK : Continuous K) (hC : Continuous C)
    (A : Set X) (hA : IsCompact A) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ A, |K x| ≤ B ∧ |C x| ≤ B := by
  obtain ⟨B, hB⟩ := hA.bddAbove_image (hK.abs.add hC.abs).continuousOn
  refine ⟨max B 0+1, by positivity, ?_⟩
  intro x hx
  have hh : |K x|+|C x| ≤ B := hB ⟨x, hx, rfl⟩
  have hm : B ≤ max B 0+1 := by linarith [le_max_left B 0]
  constructor <;> linarith [abs_nonneg (K x), abs_nonneg (C x)]

theorem compact_relative_curvature_neighborhood {X : Type*} [MetricSpace X]
    (K C K0 C0 : X → ℝ)
    (hK : Continuous K) (hC : Continuous C) (hK0 : Continuous K0) (hC0 : Continuous C0)
    (A : Set X) (hA : IsCompact A)
    (hpos : ∀ x ∈ A, 0 < K0 x)
    (hKeq : ∀ x ∈ A, K x = K0 x) (hCeq : ∀ x ∈ A, C x = C0 x) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x ∈ A, ∀ y : X, dist y x < delta →
        0 < K0 y ∧ |K y-K0 y| < K0 y/12 ∧ |C y-C0 y| < K0 y/24 := by
  let U : Set X := {x | 0 < K0 x ∧
    |K x-K0 x| < K0 x/12 ∧ |C x-C0 x| < K0 x/24}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const hK0).inter
      ((isOpen_lt (hK.sub hK0).abs (hK0.div_const 12)).inter
        (isOpen_lt (hC.sub hC0).abs (hK0.div_const 24)))
  have hAU : A ⊆ U := by
    intro x hx
    have hp := hpos x hx
    change 0 < K0 x ∧ |K x-K0 x| < K0 x/12 ∧ |C x-C0 x| < K0 x/24
    simp only [hKeq x hx, hCeq x hx, sub_self, abs_zero]
    exact ⟨hp, by positivity, by positivity⟩
  obtain ⟨delta, hd, hthick⟩ := hA.exists_thickening_subset_open hopen hAU
  refine ⟨delta, hd, ?_⟩
  intro x hx y hdist
  apply hthick
  exact Metric.mem_thickening_iff.mpr ⟨x, hx, hdist⟩

end FCAppendix.Exclusive.Narrow.Existence
