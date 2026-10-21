import FCAppendix.Affine.Uniform06.EntryGoodOptimizer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryFullRestoration

open MeasureTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition
open ActualEntryGoodGeometry EntryLiteralResponseGeometry EntryLiteralCanonicalTransfer
open EntryLiteralResponseMoments EntryGoodKernelBounds EntryFiniteConstructor
open EntryConstructedSource EntryConstructedSource.EarlyArray
open EntryProducedMoments EntryGoodOptimizer

variable {N C : ℕ}

def count (j : Fin 4) (r : Fin N→ Fin 4) : ℕ := (Finset.univ.filter (fun k => r k=j)).card

lemma count_eq_classCount (j : Fin 4) (r : Fin N→ RowRival) :
    count j (fun k => (r k).1)=LowBody.classCount j r := by
  classical
  simp only [count,LowBody.classCount,Finset.card_eq_sum_ones,Finset.sum_filter]

def CountContract (i : Row) (g : GuardData) (cm : (Fin N→ Fin 4)→ℝ) : Prop :=
  ∀ r : Fin N→ Fin 4,(∀ j,r j≠1) →
    |(count 0 r:ℝ)-(N:ℝ)*cutoff i|< epsilon i*(N:ℝ) →
    |(count 2 r:ℝ)-(N:ℝ)*((1-cutoff i)/2)|< epsilon i*(N:ℝ) →
    |(count 3 r:ℝ)-(N:ℝ)*((1-cutoff i)/2)|< epsilon i*(N:ℝ) →
      2*g.margin*g.population≤ cm r

theorem Inputs.with_count {ν : Measure RowRival} {i : Row} {g : GuardData}
    {b A U ε c q lo γ w s k : ℝ}
    (h : Inputs ν i g N C b A U ε c q lo γ w s) (hk : 2*g.margin*g.population≤ k) :
    Inputs ν i {g with countMargin := k} N C b A U ε c q lo γ w s := {
  rivals_pos := h.rivals_pos
  epsilon_nonneg := h.epsilon_nonneg
  lo_pos := h.lo_pos
  cap_pos := h.cap_pos
  strip_pos := h.strip_pos
  radius_pos := h.radius_pos
  «prefix» := h.prefix.update_countMargin k
  requiredDemand_eq := h.requiredDemand_eq
  lower_price := h.lower_price
  cap_receipt := h.cap_receipt
  half_receipt := h.half_receipt
  bid_window := h.bid_window
  bid_cap := h.bid_cap
  strip_above := h.strip_above
  means := {
    lower := h.means.lower
    upper0 := h.means.upper0
    upper1 := h.means.upper1
    lowerDemand := h.means.lowerDemand
    upperDemand := h.means.upperDemand
    weight := h.means.weight
    rejection := h.means.rejection
    seed := h.means.seed
    strip := h.means.strip }
  floor_error := h.floor_error
  residual_positive := h.residual_positive
  residual_room := h.residual_room
  demand_margin := h.demand_margin
  weight_margin := h.weight_margin
  rejection_margin := h.rejection_margin
  seed_margin := h.seed_margin
  strip_margin := h.strip_margin
  count_margin := hk
  sample_weight_margin := h.sample_weight_margin }

theorem actual_count_on_good (i : Row) (G : Measure (ℝ×ℝ)) (g : GuardData)
    (cm : (Fin N→ Fin 4)→ℝ) (hc : CountContract i g cm)
    {b A U c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i (normalizeCount g) N C b A U
      (epsilon i) c q lo γ w s)
    (r : Fin N→ RowRival) (hno : ∀ j,(r j).1≠1)
    (hr : r∈RivalGood.good (RawMixedSource.source i G) (tests (xi i) g A U) N (epsilon i)) :
    2*g.margin*g.population≤ cm (fun j => (r j).1) := by
  have he := empirical_errors (RawMixedSource.source i G) (normalizeCount g) h.rivals_pos r hr
  apply hc (fun j => (r j).1) hno
  · have hh := he 0
    rw [h.means.lower] at hh
    simpa only [tests,RivalGood.statistics,Matrix.cons_val_zero,RawGoodGeometry.sum_tag_eq_count,
      count_eq_classCount] using hh
  · have hh := he 1
    rw [h.means.upper0] at hh
    change |(∑ j,RivalGood.tag 2 (r j))-(N:ℝ)*((1-cutoff i)/2)|<epsilon i*(N:ℝ) at hh
    simpa only [RawGoodGeometry.sum_tag_eq_count,count_eq_classCount] using hh
  · have hh := he 2
    rw [h.means.upper1] at hh
    change |(∑ j,RivalGood.tag 3 (r j))-(N:ℝ)*((1-cutoff i)/2)|<epsilon i*(N:ℝ) at hh
    simpa only [RawGoodGeometry.sum_tag_eq_count,count_eq_classCount] using hh

theorem continuation_canonical_moments {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {ξ κ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (g : GuardData) (T : PureTemplate ι)
    (B : ι→ℝ) (j : ι) (hα : guardAlpha ξ g T B=1) :
    (continuationLaw ξ κ g T B).expect (LiteralExperiment.first j)=
      (canonicalLaw ξ g T B).expect (LiteralExperiment.first j) ∧
    (continuationLaw ξ κ g T B).expect (duplicate j)=
      (canonicalLaw ξ g T B).expect (duplicate j) := by
  by_cases he : T.residual₀=T.residual₁
  · have hzero : imbalance T=0 := by simp [imbalance,small,he]
    constructor
    · rw [continuationLaw,if_pos he,empty_completion_first hξ hξ1,
        canonical_path_first hξ hξ1,hzero]
      simp only [pathLaw,FiniteLaw.expect_dirac,finalSet,Finset.notMem_empty,if_false]
    · rw [continuationLaw,if_pos he,empty_completion_duplicate hξ hξ1,
        canonical_path_duplicate hξ hξ1,hzero]
      simp only [pathLaw,FiniteLaw.expect_dirac,finalSet]
  · constructor <;> simp only [continuationLaw,if_neg he,FiniteLaw.expect_mixture,
      hα,one_mul,sub_self,zero_mul,add_zero]

theorem original_row_on_good (i : Row) (G : Measure (ℝ×ℝ)) (g : GuardData)
    (cm : (Fin N→ Fin 4)→ℝ) (hc : CountContract i g cm)
    {b₀ A U c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i (normalizeCount g) N C b₀ A U
      (epsilon i) c q lo γ w s)
    (r : Fin N→ RowRival) (hno : ∀ j,(r j).1≠1)
    (hr : r∈RivalGood.good (RawMixedSource.source i G) (tests (xi i) g A U) N (epsilon i)) :
    ∀ b : ℝ,
      (rowLaw (xi i) (kappa i) C g cm b r).expect (LiteralExperiment.first 0)=
        (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (LiteralExperiment.first 0) ∧
      (rowLaw (xi i) (kappa i) C g cm b r).expect (duplicate 0)=
        (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (duplicate 0) := by
  have hcount := actual_count_on_good i G g cm hc h r hno hr
  have hh := Inputs.with_count h hcount
  intro b
  have hα := good_alpha (RawMixedSource.source i G) i _ hh r hno hr b
  have hm := continuation_canonical_moments (κ:=kappa i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ])
    {g with countMargin := cm (fun j => (r j).1)}
    (patternTemplate C (fun j => (r j).1)) (rowBids b r) 0 hα
  simpa only [rowLaw,canonicalLaw_update_countMargin] using hm

lemma integral_restriction_error {Ξ : Type*} [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsFiniteMeasure ν] (H : Set Ξ) (hH : MeasurableSet H)
    (f : Ξ→ℝ) (hi : Integrable f ν) (hb : ∀ x,f x∈Icc (0:ℝ) 1) :
    0≤(∫ x,f x ∂ν)-(∫ x in H,f x ∂ν) ∧
      (∫ x,f x ∂ν)-(∫ x in H,f x ∂ν)≤ν.real Hᶜ := by
  have he : (∫ x,f x ∂ν)=(∫ x in H,f x ∂ν)+(∫ x in Hᶜ,f x ∂ν) := by
    rw [← integral_indicator hH,← integral_indicator hH.compl,
      ← integral_add (hi.indicator hH) (hi.indicator hH.compl)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by by_cases hx : x∈H <;> simp [hx]
  rw [he,add_sub_cancel_left]
  refine ⟨integral_nonneg fun x => (hb x).1,?_⟩
  have hh : (∫ x in Hᶜ,f x ∂ν)≤∫ _x in Hᶜ,(1:ℝ) ∂ν :=
    integral_mono hi.integrableOn (integrable_const (1:ℝ)) (fun x => (hb x).2)
  simpa only [integral_const,measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_one] using hh

theorem full_kernel_error (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (cm : (Fin N→ Fin 4)→ℝ) (hc : CountContract i g cm)
    {b₀ A U c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i (normalizeCount g) N C b₀ A U
      (epsilon i) c q lo γ w s) :
    ∀ b : ℝ,
      let S := actualSuccess (cutoff i) (xi i) (kappa i) (G.map Prod.snd) C N g cm b
      let D := actualDuplicate (cutoff i) (xi i) (kappa i) (G.map Prod.snd) C N g cm b
      let Q := canonicalGoodMarginal i G C N g b A U (epsilon i)
      let R := canonicalGoodDuplicate i G C N g b A U (epsilon i)
      let e := 18*Real.exp (-2*(N:ℝ)*(epsilon i)^2)
      (S-(2*Q-R))∈Icc (0:ℝ) e ∧ (D-R)∈Icc (0:ℝ) e := by
  let ν := RawMixedSource.source i G
  let P := Measure.pi (fun _ : Fin N => ν)
  let H := RivalGood.good ν (tests (xi i) g A U) N (epsilon i)
  have hH : MeasurableSet H := RivalGood.measurable_good ν _
    (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _) N (epsilon i)
  have hno : ∀ᵐ r ∂P,∀ j,(r j).1≠1 := ae_all_iff.mpr fun j =>
    (measurePreserving_eval (fun _ : Fin N => ν) j).quasiMeasurePreserving.ae (raw_no_tag_one i G)
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hbad : P.real Hᶜ≤18*Real.exp (-2*(N:ℝ)*(epsilon i)^2) := by
    simpa only [Fintype.card_fin,Nat.cast_ofNat,show (2:ℝ)*9=18 by norm_num] using
      RivalGood.good_complement_le ν (tests (xi i) g A U)
        (fun k => (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _ k).aemeasurable)
        (fun k => ae_of_all _ fun r => RivalGood.statistics_unit (xi_pos i) h.prefix.lower_pos
          (by linarith [h.prefix.lower_pos,h.radius_pos]) h.prefix.rejectionScale_pos k r)
        N h.rivals_pos (epsilon_bounds i).1.le
  intro b
  let FS := fun r : Fin N→ RowRival => (rowLaw (xi i) (kappa i) C g cm b r).expect (LiteralExperiment.first 0)
  let FD := fun r : Fin N→ RowRival => (rowLaw (xi i) (kappa i) C g cm b r).expect (duplicate 0)
  have hS := integrable_row_first (xi_pos i) hξ1 (kappa i) C g cm b P
  have hD := integrable_row_duplicate (xi_pos i) hξ1 (kappa i) C g cm b P
  have hSG : (∫ r in H,FS r ∂P)=2*canonicalGoodMarginal i G C N g b A U (epsilon i)-
      canonicalGoodDuplicate i G C N g b A U (epsilon i) := by
    have heq : ∀ᵐ r ∂P.restrict H,FS r=2*(canonicalLaw (xi i) g
        (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (fairMarginal 0)-
      (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (duplicate 0) := by
      filter_upwards [ae_restrict_mem hH,ae_restrict_of_ae hno] with r hr hn
      have he := (original_row_on_good i G g cm hc h r hn hr b).1
      have hid := expect_first_add_duplicate (canonicalLaw (xi i) g
        (patternTemplate C (fun j => (r j).1)) (rowBids b r)) 0
      dsimp only [FS]
      linarith
    rw [integral_congr_ae heq]
    have hCI : Integrable (fun r : Fin N→ RowRival =>
        (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (fairMarginal 0)) (P.restrict H) := by
      apply Integrable.of_mem_Icc 0 1
      · have hm : Measurable (fun x : (Fin N→Fin 4)×(Fin (N+1)→ℝ) =>
            (canonicalLaw (xi i) g (patternTemplate C x.1) x.2).expect (fairMarginal 0)) := by
          apply measurable_from_prod_countable_right
          intro k
          exact measurable_canonical_fair (xi_pos i) hξ1 g (patternTemplate C k) 0
        exact (hm.comp ((measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst).prodMk
          (measurable_rowBids.comp (measurable_const.prodMk measurable_id)))).aemeasurable
      · exact ae_of_all _ fun r => expect_fair_bounds _ 0
    have hDI : Integrable (fun r : Fin N→ RowRival =>
        (canonicalLaw (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids b r)).expect (duplicate 0)) (P.restrict H) := by
      apply Integrable.of_mem_Icc 0 1
      · have hm : Measurable (fun x : (Fin N→Fin 4)×(Fin (N+1)→ℝ) =>
            (canonicalLaw (xi i) g (patternTemplate C x.1) x.2).expect (duplicate 0)) := by
          apply measurable_from_prod_countable_right
          intro k
          exact measurable_canonical_duplicate (xi_pos i) hξ1 g (patternTemplate C k) 0
        exact (hm.comp ((measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst).prodMk
          (measurable_rowBids.comp (measurable_const.prodMk measurable_id)))).aemeasurable
      · exact ae_of_all _ fun r => expect_duplicate_bounds _ 0
    rw [integral_sub (hCI.const_mul 2) hDI,integral_const_mul]
    rfl
  have hDG : (∫ r in H,FD r ∂P)=canonicalGoodDuplicate i G C N g b A U (epsilon i) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hH,ae_restrict_of_ae hno] with r hr hn
    exact (original_row_on_good i G g cm hc h r hn hr b).2
  have heS := integral_restriction_error P H hH FS hS (fun r =>
    continuation_first_bounds (xi i) (kappa i) _ _ _ 0)
  have heD := integral_restriction_error P H hH FD hD (fun r =>
    continuation_duplicate_bounds (xi i) (kappa i) _ _ _ 0)
  rw [hSG] at heS
  rw [hDG] at heD
  exact ⟨⟨heS.1,heS.2.trans hbad⟩,⟨heD.1,heD.2.trans hbad⟩⟩

end FCAppendix.Affine.Uniform06.EntryFullRestoration
