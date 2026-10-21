import FCAppendix.Affine.Hybrid.ActivePhysicalPattern
import FCAppendix.Affine.Hybrid.ActivePatternCountBounds
import FCAppendix.Affine.Hybrid.SourceUniformMenus
import FCAppendix.Affine.Hybrid.Finishing01MenusCalculus

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finishing01Menus
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

lemma measurePreserving_iid_restrict {ι κ : Type*} [Fintype ι] [Fintype κ]
    (G : Measure ℝ) [IsProbabilityMeasure G] (e : ι→κ)
    (he : Function.Injective e) :
    MeasurePreserving (fun x : κ→ℝ => fun i : ι => x (e i))
      (Measure.pi (fun _ : κ => G)) (Measure.pi (fun _ : ι => G)) := by
  have hi : iIndepFun (fun j : κ => fun x : κ→ℝ => x j)
      (Measure.pi (fun _ : κ => G)) :=
    iIndepFun_pi (fun _ : κ => measurable_id.aemeasurable)
  have hir := iIndepFun.precomp he hi
  have hm := iIndepFun.map_fun_eq_pi_map
    (fun i : ι => (measurable_pi_apply (e i)).aemeasurable) hir
  have heval : (fun i : ι => (Measure.pi (fun _ : κ => G)).map
      (fun x : κ→ℝ => x (e i)))=fun _ : ι => G := by
    funext i
    exact (measurePreserving_eval (fun _ : κ => G) (e i)).map_eq
  rw [heval] at hm
  exact ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)),hm⟩

variable {N : ℕ}

def activeSubtypeBids (kind : Fin N→ Fin 4) (b : ℝ) (x : Fin N→ℝ) :
    ActivePatternIndex kind→ℝ := fun i => Fin.cases b x i.val

lemma measurable_activeSubtypeBids (kind : Fin N→ Fin 4) (b : ℝ) :
    Measurable (activeSubtypeBids kind b) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : Fin N→ℝ => Fin.cons (α:=fun _ : Fin (N+1) => ℝ) b x i.val)
  have hc : Continuous (fun x : Fin N→ℝ => Fin.cons (α:=fun _ : Fin (N+1) => ℝ) b x) :=
    continuous_const.finCons continuous_id
  exact ((continuous_apply i.val).comp hc).measurable

lemma activeSubtypeBids_eq_updated_restrict (kind : Fin N→ Fin 4) (b : ℝ)
    (x : Fin (N+1)→ℝ) :
    Function.update (fun i : ActivePatternIndex kind => x i.val)
      (activePatternFocal kind) b=
        activeSubtypeBids kind b (fun j => x j.succ) := by
  funext i
  by_cases hi : i.val=0
  · have he : i=activePatternFocal kind := Subtype.ext hi
    subst i
    rw [Function.update_self]
    rfl
  · have he : i≠activePatternFocal kind := fun hh => hi (congrArg Subtype.val hh)
    rw [Function.update_of_ne he]
    obtain ⟨j,hj⟩ := Fin.eq_succ_of_ne_zero hi
    simp only [activeSubtypeBids,hj,Fin.cases_succ]

theorem integral_activeSubtypeBids (G : Measure ℝ) [IsProbabilityMeasure G]
    (kind : Fin N→ Fin 4) (b : ℝ)
    (f : (ActivePatternIndex kind→ℝ)→ℝ) (hf : Measurable f) :
    (∫x : Fin N→ℝ, f (activeSubtypeBids kind b x)
      ∂Measure.pi (fun _ : Fin N => G))=
      ∫y : ActivePatternIndex kind→ℝ,
        f (Function.update y (activePatternFocal kind) b)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => G) := by
  have hactive := measurePreserving_iid_restrict G
    (fun i : ActivePatternIndex kind => i.val) Subtype.val_injective
  have htail := measurePreserving_iid_restrict G
    (Fin.succ : Fin N→ Fin (N+1)) (Fin.succ_injective N)
  have hu : Measurable (fun y : ActivePatternIndex kind→ℝ =>
      f (Function.update y (activePatternFocal kind) b)) :=
    hf.comp (measurable_fixedFocalRow _ _)
  have ha := integral_map (μ:=Measure.pi (fun _ : Fin (N+1) => G))
    hactive.measurable.aemeasurable hu.aestronglyMeasurable
  rw [hactive.map_eq] at ha
  have ht := integral_map (μ:=Measure.pi (fun _ : Fin (N+1) => G))
    htail.measurable.aemeasurable
    ((hf.comp (measurable_activeSubtypeBids kind b)).aestronglyMeasurable)
  rw [htail.map_eq] at ht
  simp only [Function.comp_def] at ht
  rw [ht,ha]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => congrArg f
    (activeSubtypeBids_eq_updated_restrict kind b x).symm)

theorem sourceOwnerPayoff_eq_of_sum_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ η v : ℝ) (b : ι→ℝ) (r K₀ K₁ J₀ J₁ : ℕ) (i : ι)
    (hN : 2≤ Fintype.card ι) (hpos : 0<K₀+K₁)
    (hbound : K₀+K₁≤ Fintype.card ι) (hsum : K₀+K₁=J₀+J₁) :
    sourceOwnerPayoff ξ η v b r K₀ K₁ i=
      sourceOwnerPayoff ξ η v b r J₀ J₁ i := by
  rw [sourceOwnerPayoff_eq_favored ξ η v b r K₀ K₁ i hN hpos hbound,
    sourceOwnerPayoff_eq_favored ξ η v b r J₀ J₁ i hN
      (by omega) (by omega),hsum]

theorem guarded_mono_upper {ξ L T W : ℝ} (hξ1 : ξ<1) (hTW : T≤ W)
    (c : ℕ) (z : ℝ) (kind : Fin N→ Fin 4)
    (hg : activePatternGuarded ξ L W c z kind) :
    activePatternGuarded ξ L T c z kind := by
  rcases hg with ⟨hN,hne,hK,hKN,hr,hseed⟩
  rcases hr with ⟨hmix,hres,hresmix,hfactor,hlo,hhi⟩
  refine ⟨hN,hne,hK,hKN,⟨hmix,hres,hresmix,hfactor,?_,?_⟩,hseed⟩
  · exact (mul_le_mul_of_nonneg_left hTW (sub_pos.mpr hξ1).le).trans_lt hlo
  · exact (mul_le_mul_of_nonneg_left hTW hfactor.le).trans_lt hhi

def patternInterim (ξ z L U : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (F G : Measure ℝ) (v b : ℝ) : ℝ :=
  ∫xy : (Fin N→ℝ)×(Fin N→ℝ),
    activePhysicalPatternPayoff ξ z L U c kind (v,b,xy)
    ∂(Measure.pi (fun _ : Fin N => F)).prod
      (Measure.pi (fun _ : Fin N => G))

def actualRowInterim (ξ z L U : ℝ) (c : ℕ) (C : FiniteLaw (Fin 4))
    (F G : Measure ℝ) (v b : ℝ) : ℝ :=
  (CommonList.iid C N).expect
    (fun kind => patternInterim ξ z L U c kind F G v b)

theorem measurable_patternInterim {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (z L U : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    Measurable (fun p : ℝ×ℝ => patternInterim ξ z L U c kind F G p.1 p.2) := by
  have hm : Measurable (fun pr : (ℝ×ℝ)×((Fin N→ℝ)×(Fin N→ℝ)) =>
      activePhysicalPatternPayoff ξ z L U c kind (pr.1.1,pr.1.2,pr.2)) :=
    (measurable_activePhysicalPatternPayoff hξ hξ1 z L U c kind).comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_actualRowInterim {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (z L U : ℝ) (c : ℕ) (C : FiniteLaw (Fin 4))
    (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G] :
    Measurable (fun p : ℝ×ℝ => actualRowInterim (N:=N) ξ z L U c C F G p.1 p.2) := by
  unfold actualRowInterim FiniteLaw.expect
  exact Finset.measurable_sum _ (fun kind _ => measurable_const.mul
    (measurable_patternInterim hξ hξ1 z L U c kind F G))

lemma ae_iid_box (G : Measure ℝ) [IsProbabilityMeasure G] {L U : ℝ}
    (hG : ∀ᵐb∂G,b∈ Icc L U) :
    ∀ᵐx : Fin N→ℝ ∂Measure.pi (fun _ : Fin N => G),∀ j,x j∈ Icc L U := by
  rw [ae_all_iff]
  intro j
  exact (measurePreserving_eval (fun _ : Fin N => G) j).quasiMeasurePreserving.ae hG

theorem abs_physicalPatternPayoff_le {ξ L U : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hL : 0<L)
    (z : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (v b : ℝ) (low active : Fin N→ℝ)
    (hb : b∈ Icc L U) (ha : ∀ j,active j∈ Icc L U) :
    |activePhysicalPatternPayoff ξ z L U c kind (v,b,low,active)|≤|v|+3*U := by
  have hbp : 0<b := hL.trans_le hb.1
  have hbabs : |b|≤ U := by rw [abs_of_pos hbp]; exact hb.2
  have hU : 0<U := hbp.trans_le hb.2
  have hown : activePhysicalBids kind (v,b,low,active) 0=b := rfl
  have hact : ∀ i,activePhysicalActiveBids kind (v,b,low,active) i∈ Icc L U := by
    intro i
    have hh (j : Fin (N+1)) : Fin.cases b active j∈ Icc L U := by
      exact Fin.cases hb ha j
    exact hh i.val
  unfold activePhysicalPatternPayoff
  dsimp only
  split_ifs with hg heq
  · have heta : |1-2*ξ|≤1 := abs_le.mpr ⟨by linarith,by linarith⟩
    exact (abs_sourceOwnerPayoff_activePattern hξ hξ1 hL heta c z kind hg
      v _ hact).trans (by linarith)
  · have hh := LowBody.abs_equalPayoff_le hξ hξ1
      (activePatternTemplate c kind).residual₀ 0 v
      (activePhysicalBids kind (v,b,low,active))
    rw [hown] at hh
    exact hh.trans (by linarith)
  · have hk : |1-ξ|≤1 := by rw [abs_of_pos (by linarith : 0<1-ξ)]; linarith
    have hh := LowBody.abs_purePayoff_le (1-ξ) v
      (activePhysicalBids kind (v,b,low,active))
      ((activePatternTemplate c kind).selection (1-ξ)
        (activePhysicalBids kind (v,b,low,active))) 0
    rw [hown] at hh
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg b)])

theorem abs_patternInterim_le {ξ L U : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hL : 0<L)
    (z : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hG : ∀ᵐb∂G,b∈ Icc L U) (v b : ℝ) (hb : b∈ Icc L U) :
    |patternInterim ξ z L U c kind F G v b|≤|v|+3*U := by
  have ha := (measurePreserving_snd
    (μ:=Measure.pi (fun _ : Fin N => F))
    (ν:=Measure.pi (fun _ : Fin N => G))).quasiMeasurePreserving.ae (ae_iid_box G hG)
  have hbnd : ∀ᵐxy : (Fin N→ℝ)×(Fin N→ℝ)
      ∂(Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G)),
      ‖activePhysicalPatternPayoff ξ z L U c kind (v,b,xy)‖≤|v|+3*U := by
    filter_upwards [ha] with xy hxy
    simpa only [Real.norm_eq_abs] using
      abs_physicalPatternPayoff_le hξ hξ1 hL z c kind v b xy.1 xy.2 hb hxy
  simpa only [patternInterim,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hbnd

theorem patternInterim_guarded_eq {ξ L U : ℝ}
    (_hξ : 0<ξ) (_hξ1 : ξ<1) (_hL : 0<L)
    (z : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (F G : Measure ℝ) [IsProbabilityMeasure F] [IsProbabilityMeasure G]
    (hg : activePatternGuarded ξ L U c z kind) (v b : ℝ) :
    patternInterim ξ z L U c kind F G v b=
      ∫x : ActivePatternIndex kind→ℝ,
        sourceOwnerPayoff ξ (1-2*ξ) v
          (Function.update x (activePatternFocal kind) b)
          (activePatternResidual c z kind)
          (activePatternQuota z kind+activePatternGap c kind)
          (activePatternQuota z kind) (activePatternFocal kind)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => G) := by
  let f : (ActivePatternIndex kind→ℝ)→ℝ := fun x =>
    sourceOwnerPayoff ξ (1-2*ξ) v x (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)
      (activePatternFocal kind)
  have hf : Measurable f := measurable_sourceOwnerPayoff _ _ _ _ _ _ _
  have hd := measurePreserving_snd
    (μ:=Measure.pi (fun _ : Fin N => F))
    (ν:=Measure.pi (fun _ : Fin N => G))
  have hi := integral_map
    (μ:=(Measure.pi (fun _ : Fin N => F)).prod (Measure.pi (fun _ : Fin N => G)))
    hd.measurable.aemeasurable
    ((hf.comp (measurable_activeSubtypeBids kind b)).aestronglyMeasurable)
  rw [hd.map_eq] at hi
  have hrow : patternInterim ξ z L U c kind F G v b=
      ∫x : Fin N→ℝ, f (activeSubtypeBids kind b x)
        ∂Measure.pi (fun _ : Fin N => G) := by
    change patternInterim ξ z L U c kind F G v b =
      ∫ x, (f ∘ activeSubtypeBids kind b) x ∂Measure.pi (fun _ : Fin N => G)
    rw [hi]
    apply integral_congr_ae
    filter_upwards [] with xy
    simp only [activePhysicalPatternPayoff,if_pos hg]
    rfl
  rw [hrow,integral_activeSubtypeBids G kind b f hf]
  apply integral_congr_ae
  filter_upwards [] with x
  apply sourceOwnerPayoff_eq_of_sum_eq _ _ _ _ _ _ _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2.1.le
  have hs := activePatternOwner_sum_of_ne c z kind hg.2.1
  omega

theorem finite_expect_error_le {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (E : Ω→ Prop) (f : Ω→ℝ) (a ε C : ℝ)
    (hε : 0≤ε) (hgood : ∀ x,¬E x→|f x-a|≤ε)
    (hbad : ∀ x,|f x-a|≤ C) :
    |P.expect f-a|≤ε+C*P.prob E := by
  classical
  rw [←P.expect_const a,←P.expect_sub]
  apply (P.abs_expect_le _).trans
  have hpoint (x : Ω) : |f x-a|≤ε+C*(if E x then 1 else 0) := by
    by_cases hx : E x
    · simp only [if_pos hx,mul_one]
      linarith [hbad x]
    · simp only [if_neg hx,mul_zero,add_zero]
      exact hgood x hx
  apply (P.expect_mono hpoint).trans
  rw [P.expect_add,P.expect_const,P.expect_const_mul,←FiniteLaw.prob_eq_expect]

end FCAppendix.Affine.Hybrid.Finishing01Menus
