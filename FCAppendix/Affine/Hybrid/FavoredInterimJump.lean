import FCAppendix.Affine.Hybrid.FavoredExpectedAtom
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma measurable_ownerSetPayoff (xi eta v : ℝ) (r : ℕ) (i : ι) (E : Finset ι) :
    Measurable (fun b : ι→ℝ=>ownerSetPayoff xi eta v b r i E) := by
  by_cases hi : i∈E
  · simp only [ownerSetPayoff,if_pos hi]
    exact measurable_const.sub (measurable_pi_apply i)
  · have hs : Measurable (fun b : ι→ℝ=>∑j∈Finset.univ\E,(b j)⁻¹) :=
      Finset.measurable_sum _ (fun j _=>(measurable_pi_apply j).inv)
    have hl : Measurable (fun b : ι→ℝ=>finiteMultiplier xi b (Finset.univ\E) r) :=
      measurable_const.div hs
    have hq : Measurable (fun b : ι→ℝ=>exposure xi
        (finiteMultiplier xi b (Finset.univ\E) r) (b i)) :=
      (measurable_const.sub (hl.div (measurable_pi_apply i))).div_const xi
    simp only [ownerSetPayoff,if_neg hi]
    unfold independentTwo
    exact (measurable_const.mul ((measurable_const.mul hq).sub (hq.pow_const 2))).sub
      ((measurable_pi_apply i).mul ((measurable_const.mul hq).sub
        (measurable_const.mul (hq.pow_const 2))))

lemma measurable_sourceOwnerPayoff [Nonempty ι] (xi eta v : ℝ) (r K1 K2 : ℕ) (i : ι) :
    Measurable (fun b : ι→ℝ=>sourceOwnerPayoff xi eta v b r K1 K2 i) := by
  unfold sourceOwnerPayoff FiniteLaw.expect
  exact Finset.measurable_sum _ (fun AB _=>
    (measurable_sourceOwnersLaw_mass K1 K2 AB).mul
      (measurable_ownerSetPayoff xi eta v r i (AB.1∪AB.2)))

lemma abs_finite_expect_le_sum {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω→ℝ) :
    |P.expect f|≤∑t,|f t| := by
  unfold FiniteLaw.expect
  calc
    _ ≤ ∑t,|P.mass t*f t| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑t,P.mass t*|f t| := by
      apply Finset.sum_congr rfl
      intro t _
      rw [abs_mul,abs_of_nonneg (P.nonneg t)]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro t _
      have hm : P.mass t≤1 := by
        have hh:=Finset.single_le_sum (fun s _=>P.nonneg s) (Finset.mem_univ t)
        rwa [P.total] at hh
      exact mul_le_of_le_one_left (abs_nonneg _) hm

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_boxBids {L U : ℝ} :
    Continuous (fun x : ι→Icc L U=>fun j=>(x j:ℝ)) := by
  apply continuous_pi
  intro j
  exact continuous_subtype_val.comp (continuous_apply j)

theorem exists_sourceOwnerPayoff_box_bound [Nonempty ι] {L U : ℝ} (hL : 0<L)
    (xi eta v : ℝ) (r K1 K2 : ℕ) (i : ι) (hN : 2≤Fintype.card ι)
    (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι) :
    ∃C:ℝ,∀b : ι→ℝ,(∀j,b j∈Icc L U)→
      ‖sourceOwnerPayoff xi eta v b r K1 K2 i‖≤C := by
  have hc (t : ι) : Continuous (fun x : ι→Icc L U=>
      favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r (K1+K2) i t) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    change Tendsto (fun y : ι→Icc L U=>favoredTargetPayoff xi eta v (fun j=>(y j:ℝ)) r (K1+K2) i t)
      (𝓝 x) (𝓝 (favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r (K1+K2) i t))
    have hfc:=continuousAt_favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r (K1+K2) i t hN (by omega) hKN
      (fun j=>hL.trans_le (x j).property.1)
    have hbc : Tendsto (fun y : ι→Icc L U=>fun j=>(y j:ℝ)) (𝓝 x) (𝓝 (fun j=>(x j:ℝ))) :=
      continuous_boxBids.tendsto x
    have hh:=hfc.tendsto.comp hbc
    simpa only [Function.comp_def] using hh
  have hsum : Continuous (fun x : ι→Icc L U=>
      ∑t,|favoredTargetPayoff xi eta v (fun j=>(x j:ℝ)) r (K1+K2) i t|) :=
    continuous_finsetSum _ (fun t _=>(hc t).abs)
  obtain ⟨C,hC⟩:=(isCompact_range hsum).isBounded.exists_norm_le
  refine ⟨C,?_⟩
  intro b hb
  let x : ι→Icc L U:=fun j=>⟨b j,hb j⟩
  have hh:=hC _ ⟨x,rfl⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _=>abs_nonneg _))] at hh
  rw [Real.norm_eq_abs,sourceOwnerPayoff_eq_rank xi eta v b r K1 K2 i hN hK0 hKN.le]
  exact (abs_finite_expect_le_sum _ _).trans hh

theorem tendsto_interim_sourceOwnerPayoff_right [Nonempty ι] {L U : ℝ}
    (hL : 0<L) (B : Icc L U) (xi eta v : ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2) (hKN : K1+K2<Fintype.card ι)
    (mu : Measure (ι→Icc L U)) [IsFiniteMeasure mu] :
    Tendsto (fun z=>∫x,sourceOwnerPayoff xi eta v
        (Function.update (fun j=>(x j:ℝ)) i z) r K1 K2 i ∂mu)
      (𝓝[>] (B:ℝ)) (𝓝 ((∫x,sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i ∂mu)+
        ∫x,sourceOwnerJump xi eta v (focalBoxBids B i x) r (K1+K2) i ∂mu)) := by
  have hb0 : 0<(B:ℝ) := hL.trans_le B.property.1
  obtain ⟨C,hC⟩:=exists_sourceOwnerPayoff_box_bound (L:=L/2) (U:=U+1) (by linarith : 0<L/2)
    xi eta v r K1 K2 i hN hK0 hKN
  have hbds : ∀ᶠz in 𝓝[>] (B:ℝ),z∈Icc (L/2) (U+1) :=
    (show ∀ᶠz in 𝓝 (B:ℝ),z∈Icc (L/2) (U+1) from
      Icc_mem_nhds (by linarith [B.property.1]) (by linarith [B.property.2])).filter_mono
      nhdsWithin_le_nhds
  have hmeas (z : ℝ) : Measurable (fun x : ι→Icc L U=>
      sourceOwnerPayoff xi eta v (Function.update (fun j=>(x j:ℝ)) i z) r K1 K2 i) :=
    (measurable_sourceOwnerPayoff xi eta v r K1 K2 i).comp
      (continuous_boxBids.update i continuous_const).measurable
  have hbound : ∀ᶠz in 𝓝[>] (B:ℝ),∀ᵐx ∂mu,
      ‖sourceOwnerPayoff xi eta v (Function.update (fun j=>(x j:ℝ)) i z) r K1 K2 i‖≤C := by
    filter_upwards [hbds] with z hz
    exact Eventually.of_forall (fun x=>hC _ (fun j=>by
      by_cases hj : j=i
      · subst j; simpa only [Function.update_self] using hz
      · simp only [Function.update_of_ne hj]
        exact ⟨by linarith [(x j).property.1],by linarith [(x j).property.2]⟩))
  have hlim : ∀ᵐx ∂mu,Tendsto
      (fun z=>sourceOwnerPayoff xi eta v (Function.update (fun j=>(x j:ℝ)) i z) r K1 K2 i)
      (𝓝[>] (B:ℝ)) (𝓝 (sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i+
        sourceOwnerJump xi eta v (focalBoxBids B i x) r (K1+K2) i)) := by
    filter_upwards [] with x
    simpa only [focalBoxBids,Function.update_self,Function.update_idem,sourceOwnerJump] using
      tendsto_sourceOwnerPayoff_right xi eta v (focalBoxBids B i x) r K1 K2 i hN hK0 hKN
        (fun j=>hL.trans_le (focalBoxBids_mem B i x j).1)
  have hh:=tendsto_integral_filter_of_dominated_convergence (fun _=>C)
    (Eventually.of_forall (fun z=>(hmeas z).aestronglyMeasurable)) hbound (integrable_const C) hlim
  have hibase : Integrable (fun x=>sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i) mu := by
    apply (integrable_const C).mono'
      ((measurable_sourceOwnerPayoff xi eta v r K1 K2 i).comp
        (continuous_focalBoxBids B i).measurable).aestronglyMeasurable
    exact Eventually.of_forall (fun x=>hC _ (fun j=>
      ⟨by linarith [(focalBoxBids_mem B i x j).1],by linarith [(focalBoxBids_mem B i x j).2]⟩))
  rwa [integral_add hibase (integrable_sourceOwnerJump_box hL B xi eta v r (K1+K2) i
    hN (by omega) hKN mu)] at hh

theorem eventually_interim_gain_of_atom [Nonempty ι] {xi eta v L U vmin : ℝ}
    (hL : 0<L) (B : Icc L U) (hBU : (B:ℝ)<U) (r K1 K2 : ℕ)
    (i j : ι) (hij : i≠j) (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2)
    (hKN : K1+K2<Fintype.card ι) (heta : 0<eta) (hUv : U<vmin) (hvv : vmin≤v)
    (nu : Measure (Icc L U)) [IsProbabilityMeasure nu] (hatom : 0<nu.real {B}) :
    let C:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vmin-U) (eta*L)/2)/
      ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))
    ∀ᶠz in 𝓝[>] (B:ℝ),z∈Icc L U ∧
      (∫x,sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i
        ∂Measure.pi (fun _ : ι=>nu))+C*nu.real {B}/2<
      ∫x,sourceOwnerPayoff xi eta v (Function.update (fun j=>(x j:ℝ)) i z) r K1 K2 i
        ∂Measure.pi (fun _ : ι=>nu) := by
  dsimp only
  let C:=(1-fillFraction (ι:=ι) (K1+K2))*(min (vmin-U) (eta*L)/2)/
    ((Fintype.card ι:ℝ)*((Fintype.card ι:ℝ)+1))
  have hNr : 1<(Fintype.card ι:ℝ) := by exact_mod_cast (show 1<Fintype.card ι by omega)
  have hKr : ((K1+K2:ℕ):ℝ)<Fintype.card ι := by exact_mod_cast hKN
  have hfill : fillFraction (ι:=ι) (K1+K2)<1 := by
    unfold fillFraction
    exact (div_lt_one (by linarith)).mpr (by linarith)
  have hmin : 0 < min (vmin-U) (eta*L) := lt_min (sub_pos.mpr hUv) (mul_pos heta hL)
  have hC : 0<C := by positivity
  have hjump:=iid_expected_sourceOwnerJump_lower_atom (xi:=xi) hL B r (K1+K2) i j hij
    hN (by omega) hKN heta hUv hvv nu
  have hh:=tendsto_interim_sourceOwnerPayoff_right hL B xi eta v r K1 K2 i hN hK0 hKN
    (Measure.pi (fun _ : ι=>nu))
  have hgain:=hh.eventually (Ioi_mem_nhds (show
      (∫x,sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i
        ∂Measure.pi (fun _ : ι=>nu))+C*nu.real {B}/2<
      (∫x,sourceOwnerPayoff xi eta v (focalBoxBids B i x) r K1 K2 i
        ∂Measure.pi (fun _ : ι=>nu))+
      ∫x,sourceOwnerJump xi eta v (focalBoxBids B i x) r (K1+K2) i
        ∂Measure.pi (fun _ : ι=>nu) from by
    have hp:=mul_pos hC hatom
    change C*nu.real {B}≤_ at hjump
    linarith))
  have hx : ∀ᶠz in 𝓝[>] (B:ℝ),(B:ℝ)<z := self_mem_nhdsWithin
  have hupper : ∀ᶠz in 𝓝[>] (B:ℝ),z<U :=
    (show ∀ᶠz in 𝓝 (B:ℝ),z<U from Iio_mem_nhds hBU).filter_mono nhdsWithin_le_nhds
  filter_upwards [hgain,hx,hupper] with z hz hzl hzu
  exact ⟨⟨B.property.1.trans hzl.le,hzu.le⟩,hz⟩

end FCAppendix.Affine.Hybrid
