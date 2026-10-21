import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05ProductKernels

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover Crossover.Physical

variable {M c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def productErrorSet (row : Uniform07.Row) (Γ : FiniteGame M 2 c Seed) (R : ℝ) : Set ℝ :=
  insert 0 {x | ∃i : Fin M,∃b∈Ico (0:ℝ) R,
    x=max |q Γ i b-sourceProductMarginal row b|
      |duplicate Γ i b-(sourceProductMarginal row b)^2|}

theorem productErrorSet_nonempty (row : Uniform07.Row)
    (Γ : FiniteGame M 2 c Seed) (R : ℝ) : (productErrorSet row Γ R).Nonempty :=
  ⟨0,Or.inl rfl⟩

theorem productErrorSet_bddAbove (row : Uniform07.Row)
    (Γ : FiniteGame M 2 c Seed) (R : ℝ) : BddAbove (productErrorSet row Γ R) := by
  refine ⟨1,?_⟩
  rintro x (rfl|⟨i,b,hb,rfl⟩)
  · norm_num
  · have h:=physical_moment_bounds Γ i hb.1
    have hq0:=q_nonneg Γ i b
    have hq1:=h.2.2.1.trans h.2.2.2
    have hd1:=h.2.1.trans hq1
    have hp0:=sourceProductMarginal_nonneg row b
    have hp1:=sourceProductMarginal_le_one row b
    have hp2 : (sourceProductMarginal row b)^2≤ 1 := by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
    have hq : |q Γ i b-sourceProductMarginal row b|≤ 1 := by
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    have hd : |duplicate Γ i b-(sourceProductMarginal row b)^2|≤ 1 := by
      exact abs_le.mpr ⟨by linarith [h.1],by nlinarith [sq_nonneg (sourceProductMarginal row b)]⟩
    exact max_le hq hd

def productError (row : Uniform07.Row) (Γ : FiniteGame M 2 c Seed) (R : ℝ) : ℝ :=
  sSup (productErrorSet row Γ R)

theorem productError_nonnegative (row : Uniform07.Row)
    (Γ : FiniteGame M 2 c Seed) (R : ℝ) : 0≤ productError row Γ R :=
  le_csSup (productErrorSet_bddAbove row Γ R) (Or.inl rfl)

theorem productError_le (row : Uniform07.Row) (Γ : FiniteGame M 2 c Seed)
    (R : ℝ) {e : ℝ} (he : 0≤ e)
    (h : ∀i : Fin M,Nonempty (ProductKernels05 row Γ i R e)) :
    productError row Γ R≤ e := by
  apply csSup_le (productErrorSet_nonempty row Γ R)
  rintro x (rfl|⟨i,b,hb,rfl⟩)
  · exact he
  · let H:=Classical.choice (h i)
    exact max_le (H.marginal b hb) (H.duplicate b hb)

theorem productError_kernels (row : Uniform07.Row) (Γ : FiniteGame M 2 c Seed)
    (R : ℝ) (i : Fin M) : ProductKernels05 row Γ i R (productError row Γ R) where
  marginal b hb := by
    have hh : max |q Γ i b-sourceProductMarginal row b|
        |duplicate Γ i b-(sourceProductMarginal row b)^2|≤ productError row Γ R :=
      le_csSup (productErrorSet_bddAbove row Γ R) (Or.inr ⟨i,b,hb,rfl⟩)
    exact (le_max_left _ _).trans hh
  duplicate b hb := by
    have hh : max |q Γ i b-sourceProductMarginal row b|
        |duplicate Γ i b-(sourceProductMarginal row b)^2|≤ productError row Γ R :=
      le_csSup (productErrorSet_bddAbove row Γ R) (Or.inr ⟨i,b,hb,rfl⟩)
    exact (le_max_right _ _).trans hh

theorem native_productError_tendsto (row : Uniform07.Row) {market : ℕ→ℕ}
    (hmarket : Tendsto market atTop atTop)
    (E : ∀k,UniformFinite.ExactRestrictedLaw row (market k))
    (hc : ∀k,1≤ Uniform07.capacity (market k)) :
    Tendsto (fun k=>productError row
      (exactNativeGame (E k) (hc k) (sourceLowerPriceCeiling row))
      (sourceLowerPriceCeiling row)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hh:=hmarket.eventually (eventual_native_product_kernels row (half_pos hε))
  obtain ⟨K,hK⟩:=eventually_atTop.1 hh
  refine ⟨K,?_⟩
  intro k hk
  have hbound:=productError_le row
    (exactNativeGame (E k) (hc k) (sourceLowerPriceCeiling row))
    (sourceLowerPriceCeiling row) (half_pos hε).le
    (fun i=>hK k hk (E k) (hc k) i)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (productError_nonnegative _ _ _)]
  exact hbound.trans_lt (by linarith)

def productFamilyOfExactLaws (row : Uniform07.Row) {market : ℕ→ℕ}
    (hmarket : Tendsto market atTop atTop)
    (E : ∀k,UniformFinite.ExactRestrictedLaw row (market k))
    (hc : ∀k,1≤ Uniform07.capacity (market k)) :
    ProductFamily05 (fun k=>exactNativeGame (E k) (hc k) (sourceLowerPriceCeiling row))
      row (fun _=>sourceLowerPriceCeiling row) where
  error k := productError row
    (exactNativeGame (E k) (hc k) (sourceLowerPriceCeiling row)) (sourceLowerPriceCeiling row)
  errorNonnegative := Filter.Eventually.of_forall (fun _=>productError_nonnegative _ _ _)
  errorSmall := native_productError_tendsto row hmarket E hc
  floorAboveCap := Filter.Eventually.of_forall (fun _=>(source_auxiliary_floor_guards row).2.1)
  kernels := Filter.Eventually.of_forall (fun k i=>⟨productError_kernels row
    (exactNativeGame (E k) (hc k) (sourceLowerPriceCeiling row)) (sourceLowerPriceCeiling row) i⟩)

def LowerFamily.product (F : LowerFamily) (row : Uniform07.Row) :
    ProductFamily05 (fun k=>(F.marketData row k).native) row
      (fun _=>sourceLowerPriceCeiling row) :=
  productFamilyOfExactLaws row (tail_population_tendsto F.start)
    (fun k=>(F.construction row k).finite.restricted)
    (fun k=>(F.marketData row k).capacity_positive)

theorem LowerFamily.product_error_literal (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    (F.product row).error k=productError row (F.marketData row k).native
      (sourceLowerPriceCeiling row) := rfl

end FCAppendix.Affine.Uniform07Finishing.Concrete05
