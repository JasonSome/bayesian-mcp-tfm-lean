import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapCounts

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators
variable {M : ℕ}

theorem abs_empirical_update_le {Ω : Type*} (f : Ω→ℝ)
    (hf : ∀x,f x∈Icc (0:ℝ) 1) (x : Fin M→Ω) (a : Fin M) (fixed : Ω)
    (hM : 0< M) :
    |(∑j,f (Function.update x a fixed j))/(M:ℝ)-(∑j,f (x j))/(M:ℝ)|≤ 1/M := by
  have hMr : (0:ℝ)< M := by exact_mod_cast hM
  have h1:=sum_unit_change_le (fun j=>f (Function.update x a fixed j)) (fun j=>f (x j)) a
    (fun j hj=>by rw [Function.update_of_ne hj])
    (by simpa only [Function.update_self] using (hf fixed).2) (hf (x a)).1
  have h2:=sum_unit_change_le (fun j=>f (x j)) (fun j=>f (Function.update x a fixed j)) a
    (fun j hj=>by rw [Function.update_of_ne hj]) (hf (x a)).2
    (by simpa only [Function.update_self] using (hf fixed).1)
  rw [←sub_div,abs_div,abs_of_pos hMr]
  apply div_le_div_of_nonneg_right _ hMr.le
  rw [abs_le]
  constructor <;> linarith

theorem scalar_control_after_update {Ω : Type*} (f : Ω→ℝ)
    (hf : ∀x,f x∈Icc (0:ℝ) 1) (x : Fin M→Ω) (a : Fin M) (fixed : Ω)
    (hM : 0< M) {δ center : ℝ} (hinv : 1/(M:ℝ)≤δ/2)
    (hx : |(∑j,f (x j))/(M:ℝ)-center|<δ/2) :
    |(∑j,f (Function.update x a fixed j))/(M:ℝ)-center|<δ := by
  have hs:=abs_empirical_update_le f hf x a fixed hM
  have ht:=abs_add_le
    ((∑j,f (Function.update x a fixed j))/(M:ℝ)-(∑j,f (x j))/(M:ℝ))
    ((∑j,f (x j))/(M:ℝ)-center)
  rw [sub_add_sub_cancel] at ht
  linarith

theorem menuGood_after_update (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (x : Fin M→ UniformFinite.Source.Observation i) (a : Fin M)
    (fixed : UniformFinite.Source.Observation i) (hM : 0< M) {δ : ℝ}
    (hinv : 1/(M:ℝ)≤δ/2) (hx : UniformFinite.Source.MenuGood i G (δ/2) x) :
    UniformFinite.Source.MenuGood i G δ (Function.update x a fixed) := by
  refine ⟨fun k=>scalar_control_after_update (UniformFinite.Source.sourceStatistic i G k)
    (UniformFinite.Source.sourceStatistic_bounds i G k) x a fixed hM hinv (hx.1 k),?_⟩
  exact scalar_control_after_update (UniformFinite.Source.centralStatistic i G)
    (UniformFinite.Source.centralStatistic_bounds i G) x a fixed hM hinv hx.2

theorem menu_bad_le (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (hM : 0< M) {δ : ℝ} (hδ : 0≤δ) :
    (Measure.pi (fun _ : Fin M=>UniformFinite.Source.observationLaw i G)).real
      {x|¬UniformFinite.Source.MenuGood i G δ x}≤
        18*Real.exp (-2*(M:ℝ)*δ^2) := by
  let E : Set (Fin M→ UniformFinite.Source.Observation i):=
    {x|∃k : Fin 8,δ≤|(∑j,UniformFinite.Source.sourceStatistic i G k (x j))/(M:ℝ)-
      UniformFinite.Source.sourceMean i G k|}
  let F : Set (Fin M→ UniformFinite.Source.Observation i):=
    {x|δ≤|(∑j,UniformFinite.Source.centralStatistic i G (x j))/(M:ℝ)-
      UniformFinite.Source.meanResidual i|}
  have heq : {x|¬UniformFinite.Source.MenuGood i G δ x}=E∪F := by
    ext x
    simp only [UniformFinite.Source.MenuGood,mem_setOf_eq,mem_union,E,F,
      not_and_or,not_forall,not_lt]
  have hE:=UniformFinite.Source.sourceStatistic_deviation_le i G M hM hδ
  have hF:=Probability.iid_empiricalMean_two_sided_le
    (UniformFinite.Source.observationLaw i G)
    (UniformFinite.Source.measurable_centralStatistic i G).aemeasurable
    (Eventually.of_forall (UniformFinite.Source.centralStatistic_bounds i G)) M hM hδ
  rw [UniformFinite.Source.centralStatistic_mean] at hF
  have hu:=measureReal_union_le
    (μ:=Measure.pi (fun _ : Fin M=>UniformFinite.Source.observationLaw i G)) E F
  rw [heq]
  change _≤ 16*Real.exp (-2*(M:ℝ)*δ^2) at hE
  change _≤ 2*Real.exp (-2*(M:ℝ)*δ^2) at hF
  linarith

theorem updated_menu_bad_le (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (a : Fin M) (fixed : UniformFinite.Source.Observation i)
    (hM : 0< M) {δ : ℝ} (hδ : 0≤δ) (hinv : 1/(M:ℝ)≤δ/2) :
    (Measure.pi (fun _ : Fin M=>UniformFinite.Source.observationLaw i G)).real
      {x|¬UniformFinite.Source.MenuGood i G δ (Function.update x a fixed)}≤
        18*Real.exp (-(M:ℝ)*δ^2/2) := by
  have hs : {x|¬UniformFinite.Source.MenuGood i G δ (Function.update x a fixed)}⊆
      {x|¬UniformFinite.Source.MenuGood i G (δ/2) x} := by
    intro x hx hgood
    exact hx (menuGood_after_update i G x a fixed hM hinv hgood)
  have hb:=menu_bad_le i G hM (show 0≤δ/2 by positivity)
  have he : -2*(M:ℝ)*(δ/2)^2=-(M:ℝ)*δ^2/2 := by ring
  rw [he] at hb
  exact (measureReal_mono hs).trans hb

def zeroObservation (i : Uniform07.Row) : UniformFinite.Source.Observation i :=
  Sum.inl (0,UniformFinite.Late.Exceptional.zeroBid i)

def zeroFocalObservation (i : Uniform07.Row) (a : Fin M)
    (x : Fin M→ UniformFinite.Source.Observation i) : Fin M→ UniformFinite.Source.Observation i :=
  Function.update x a (zeroObservation i)

theorem measurable_zeroFocalObservation (i : Uniform07.Row) (a : Fin M) :
    Measurable (zeroFocalObservation i a) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j=a
  · subst j
    simp only [zeroFocalObservation,Function.update_self]
    exact measurable_const
  · simpa only [zeroFocalObservation,Function.update_of_ne hj] using measurable_pi_apply j

theorem zeroFocalObservation_mem (i : Uniform07.Row) (a : Fin M)
    (x : Fin M→ UniformFinite.Source.Observation i) :
    a∈(UniformFinite.Source.observationCountRow i (zeroFocalObservation i a x)).lower := by
  simp [UniformFinite.Source.observationCountRow,UniformFinite.Source.countRowOfKind,
    zeroFocalObservation,zeroObservation,UniformFinite.Source.observationKind]

@[simp] theorem zeroFocalObservation_bid (i : Uniform07.Row) (a : Fin M)
    (x : Fin M→ UniformFinite.Source.Observation i) :
    UniformFinite.Source.observationBid i (zeroFocalObservation i a x a)=0 := by
  simp only [zeroFocalObservation,Function.update_self,zeroObservation,
    UniformFinite.Source.observationBid,UniformFinite.Late.Exceptional.zeroBid]
  rfl

end FCAppendix.Affine.Uniform07Finishing.Concrete05
