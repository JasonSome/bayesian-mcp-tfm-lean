import FCAppendix.Affine.Hybrid.ActivePatternCounts
import FCAppendix.Affine.Hybrid.SourceFiniteMenuError

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Affine.LowBody

def activePatternCountException {N : ℕ} (C : FiniteLaw (Fin 4)) (δ : ℝ)
    (kind : Fin N → Fin 4) : Prop :=
  ∃ k : Fin 4, (N+1 : ℕ)*δ ≤ |(categoryCount k activeFocalPrefix : ℝ)+
    (categoryCount k kind : ℝ)-(N+1 : ℕ)*C.mass k|

def activeGuardExceptionError (h δ δeq : ℝ) (N : ℕ) : ℝ :=
  8*Real.exp (-(N : ℝ)*δ^2/2)+countExceptionError h δeq N

lemma activeGuardExceptionError_tendsto_zero {h δ δeq : ℝ}
    (hh : 0 < h) (hδ : 0 < δ) (heq : 0 < δeq) :
    Tendsto (activeGuardExceptionError h δ δeq) atTop (𝓝 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hn.const_mul_atTop
    (by positivity : 0 < δ^2/2))
  have he : Tendsto (fun N : ℕ => 8*Real.exp (-(N : ℝ)*δ^2/2)) atTop (𝓝 0) := by
    convert hx.const_mul 8 using 1
    · funext N
      congr 2
      ring
    · ring
  change Tendsto (fun N : ℕ => 8*Real.exp (-(N : ℝ)*δ^2/2)+countExceptionError h δeq N) atTop (𝓝 0)
  simpa only [add_zero] using he.add (countExceptionError_tendsto_zero hh heq)

theorem exists_eventual_activePattern_guard_bound (s a h ρ z ξ L U : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hL : 0 < L) (hLU : L ≤ U) (hlower : h/2 < ρ) (hupper : ρ < a+h/2)
    (hq0 : 0 < sourceExposure a h ρ z) (hq1 : sourceExposure a h ρ z < 1)
    (hboxlo : (1-ξ)*U < (1-ξ*sourceExposure a h ρ z)*L)
    (hboxhi : (1-ξ*sourceExposure a h ρ z)*U < L)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M : ℝ)/(M : ℝ)) atTop (𝓝 ρ)) :
    ∃ δ δeq : ℝ, 0 < δ ∧ δ < s ∧ 0 < δeq ∧
      ∀ᶠ N : ℕ in atTop, ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      let C := categoryLaw s a h hs.le ha.le hh.le hsum G
      (∀ kind : Fin N → Fin 4, ¬ activePatternCountException C δ kind →
        activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1 ∨
        activePatternGuarded ξ L U (c (N+1)) z kind) ∧
      (CommonList.iid C N).prob (fun kind => ¬ activePatternGuarded ξ L U (c (N+1)) z kind) ≤
        activeGuardExceptionError h δ δeq N := by
  obtain ⟨δeq,hδeq,_hδeqs,_hlo,_hhi,hties⟩ := exists_eventual_source_count_bounds s a h ρ
    hs ha.le hh hsum hlower hupper c hc
  obtain ⟨δregion,hδregion,hregions⟩ := exists_eventual_typical_finiteMenuError a h ρ z ξ L U
    ha hz0 hz1 hξ hξ1 hL (hL.trans_le hLU) hlower hupper hq0 hq1 hboxlo hboxhi c hc 1 (by norm_num)
  let δ := min δregion (s/2)
  have hδ : 0 < δ := lt_min hδregion (half_pos hs)
  have hδr : δ ≤ δregion := min_le_left _ _
  have hδs : δ < s := (min_le_right δregion (s/2)).trans_lt (by linarith)
  have hregN := (tendsto_add_atTop_nat 1).eventually hregions
  have hn : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprefix : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (N : ℝ)*δ/2 := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ)*δ/2) atTop atTop := by
      convert hn.const_mul_atTop (half_pos hδ) using 1
      funext N
      ring
    exact ht.eventually_ge_atTop 1
  refine ⟨δ,δeq,hδ,hδs,hδeq,?_⟩
  filter_upwards [hregN,hties 1,hprefix] with N hNregion hNties hNprefix
  intro G hG
  letI := hG
  let C := categoryLaw s a h hs.le ha.le hh.le hsum G
  have hpoint : ∀ kind : Fin N → Fin 4, ¬ activePatternCountException C δ kind →
      activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1 ∨
      activePatternGuarded ξ L U (c (N+1)) z kind := by
    intro kind hgood
    by_cases heq : activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1
    · exact Or.inl heq
    right
    have hclose (k : Fin 4) : |(fullCategoryCount activeFocalPrefix kind k : ℝ)-(N+1 : ℕ)*C.mass k| <
        (N+1 : ℕ)*δ := by
      have hg := lt_of_not_ge (fun he => hgood ⟨k,he⟩)
      simpa only [fullCategoryCount,Nat.cast_add] using hg
    have htol : (N+1 : ℕ)*δ ≤ (N+1 : ℕ)*δregion :=
      mul_le_mul_of_nonneg_left hδr (Nat.cast_nonneg _)
    have hA : |(Fintype.card (ActivePatternIndex kind) : ℝ)-(N+1 : ℕ)*a| ≤
        (N+1 : ℕ)*δregion := by
      have hh' := (hclose 1).le.trans htol
      simpa [C,categoryLaw_mass,activePattern_count_active] using hh'
    have hH0 : |(activePatternUpper kind 0 : ℝ)-(N+1 : ℕ)*(h/2)| ≤ (N+1 : ℕ)*δregion := by
      have hh' := (hclose 2).le.trans htol
      rw [show fullCategoryCount activeFocalPrefix kind 2=activePatternUpper kind 0 from
        activePattern_count_upper kind 0] at hh'
      simpa [C,categoryLaw_mass] using hh'
    have hH1 : |(activePatternUpper kind 1 : ℝ)-(N+1 : ℕ)*(h/2)| ≤ (N+1 : ℕ)*δregion := by
      have hh' := (hclose 3).le.trans htol
      rw [show fullCategoryCount activeFocalPrefix kind 3=activePatternUpper kind 1 from
        activePattern_count_upper kind 1] at hh'
      simpa [C,categoryLaw_mass] using hh'
    have hp := hNregion (Fintype.card (ActivePatternIndex kind))
      (activePatternUpper kind 0) (activePatternUpper kind 1) hA hH0 hH1
    have hl := low_count_positive_of_not_exception s a h hs.le ha.le hh.le hsum G
      activeFocalPrefix kind (by omega) hδs hgood
    apply activePatternGuarded_of_region _ _ kind heq
    · exact hp.1
    · rw [←activePattern_count_low]
      omega
  refine ⟨hpoint,?_⟩
  have hbad := forced_fractional_count_exception_le C activeFocalPrefix N hδ.le (by simpa only [Nat.cast_one] using hNprefix)
  have hequal := (hNties G inferInstance activeFocalPrefix).2
  have hsub : (CommonList.iid C N).prob (fun kind => ¬ activePatternGuarded ξ L U (c (N+1)) z kind) ≤
      (CommonList.iid C N).prob (fun kind => activePatternCountException C δ kind ∨
        activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1) := by
    apply FiniteLaw.prob_mono
    intro kind hg
    by_cases hb : activePatternCountException C δ kind
    · exact Or.inl hb
    · exact Or.inr ((hpoint kind hb).resolve_right hg)
  have hu := (CommonList.iid C N).prob_union_le (activePatternCountException C δ)
    (fun kind => activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1)
  have heq' : (CommonList.iid C N).prob
      (fun kind => activePatternCapacity (c (N+1)) kind 0=activePatternCapacity (c (N+1)) kind 1) ≤
        countExceptionError h δeq N := by
    have hz (kind : Fin N → Fin 4) : activePatternUpper kind 0=
        fullCategoryCount activeFocalPrefix kind 2 := (activePattern_count_upper kind 0).symm
    have ho (kind : Fin N → Fin 4) : activePatternUpper kind 1=
        fullCategoryCount activeFocalPrefix kind 3 := (activePattern_count_upper kind 1).symm
    simpa only [activePatternCapacity,←activePattern_count_active,hz,ho,activeResidual] using hequal
  exact hsub.trans (hu.trans (add_le_add hbad heq'))

end FCAppendix.Affine.Hybrid
