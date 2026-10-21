import FCAppendix.Affine.Uniform06.SourceOptimizerFOC
import FCAppendix.Affine.Uniform06.SourcePreciseFamily
import FCAppendix.Affine.Uniform06.CanonicalNativeTransfer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceOptimizerGap

open MeasureTheory Set Filter Topology LowBody Game Bayes
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open CanonicalOptimizer SourceCanonicalOptimizer SourceOptimizerFOC SourcePreciseFamily

theorem fractional_error_bound {η ξ v b d δ : ℝ} {C R : ℝ → ℝ}
    (hη : 0≤η) (hξ : 0<ξ) (hbv : b< v) (hC : 0< C b)
    (hFOC : C b=(v-b)*d)
    (hr : |R b/C b|<δ)
    (hf : |(ξ*b/2)*(d/C b)*(R b/C b)-1|<δ) :
    |(two η C R v b-one C v b)/one C v b-(1-2*η/ξ)| <
      (1+2*η/ξ)*δ := by
  have hκ : 0≤2*η/ξ := div_nonneg (by positivity) hξ.le
  have he : (two η C R v b-one C v b)/one C v b-(1-2*η/ξ)=
      -(R b/C b)-(2*η/ξ)*((ξ*b/2)*(d/C b)*(R b/C b)-1) := by
    rw [relative_advantage_identity hbv hC hFOC]
    field_simp [hξ.ne']
    ring
  rw [he]
  calc
    |-(R b/C b)-(2*η/ξ)*((ξ*b/2)*(d/C b)*(R b/C b)-1)| ≤
        |R b/C b|+(2*η/ξ)*|(ξ*b/2)*(d/C b)*(R b/C b)-1| := by
      simpa only [abs_neg,abs_mul,abs_of_nonneg hκ] using
        abs_sub (-(R b/C b)) ((2*η/ξ)*((ξ*b/2)*(d/C b)*(R b/C b)-1))
    _ < δ+(2*η/ξ)*δ :=
      add_lt_add_of_lt_of_le hr (mul_le_mul_of_nonneg_left hf.le hκ)
    _ = (1+2*η/ξ)*δ := by ring

def gapFactor (i : Row) : ℝ := (1-2*eta i/xi i)/2

theorem gapFactor_pos (i : Row) : 0< gapFactor i :=
  half_pos (source_factor_pos i)

section Family
variable {E : ℕ → Type*}
    (G : ∀ m,E m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,E m → GuardData)
    (cm : ∀ m,E m → (Fin (m-1) → Fin 4) → ℝ)

theorem uniform_optimizer_fractional_gap (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (e : E m) a,((G m e:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i)
    {vmin vmax : ℝ} (hmin : cutoff i/2< vmin) (hminmax : vmin≤ vmax)
    (hmax : vmax< entry i) :
    ∀ ε>0,∀ᶠ m in atTop,∀ e : E m,∀ v∈Icc vmin vmax,
      let b := chosen G g cm i vmin m e v
      let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
      let R := sourceCanonicalDuplicate i m (G m e) (g m e) (cm m e)
      Optimal C v b ∧ 0< b ∧ b< v ∧ 0< one C v b ∧
        b∈Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)) ∧
        |(two (eta i) C R v b-one C v b)/one C v b-(1-2*eta i/xi i)|<ε := by
  let d := x i-vmax/cutoff i
  have ht := cutoff_pos i
  have hd : 0< d := by
    dsimp [d]
    apply sub_pos.mpr
    exact (div_lt_iff₀ ht).mpr (by simpa only [entry] using hmax)
  have hdmax : d≤ x i-1/2 := by
    have hh : (1/2:ℝ)≤ vmax/cutoff i :=
      (le_div_iff₀ ht).mpr (by nlinarith [hmin,hminmax])
    dsimp [d]
    linarith
  have hend : (x i-d)*cutoff i=vmax := by
    dsimp [d]
    rw [sub_sub_cancel,div_mul_cancel₀ _ ht.ne']
  intro ε hε
  let δ := ε/(1+2*eta i/xi i)
  have hcoef : 0<1+2*eta i/xi i := by
    have := div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (eta_pos i).le) (xi_pos i).le
    linarith
  have hδ : 0<δ := div_pos hε hcoef
  have hu := uniform_u19 G g cm i h05 hatom hfields hpsi hK hd hdmax δ hδ
  rw [hend] at hu
  filter_upwards [hu,
    original_optimizer G g cm i h05 hfields hpsi hmin hminmax hmax,
    original_optimizer_FOC G g cm i h05 hatom hfields hpsi hK hmin hminmax hmax]
      with m hm ho hf e v hv
  have hopt := ho e v hv
  have hFOC := hf e v hv
  have ha : cutoff i/2< leftBid i vmin := by unfold leftBid; linarith
  have hb : chosen G g cm i vmin m e v∈Icc (cutoff i/2) vmax :=
    ⟨ha.le.trans hopt.2.1.le,hopt.1.1.2.trans hv.2⟩
  have hk := hm e _ hb
  have he := fractional_error_bound (eta_pos i).le (xi_pos i)
    hFOC.2.2.1 hk.canonical_pos hFOC.2.2.2.2.2 hk.small_duplicate hk.factor
  have hcancel : (1+2*eta i/xi i)*δ=ε := by
    dsimp [δ]
    field_simp [hcoef.ne']
  rw [hcancel] at he
  exact ⟨hFOC.1,hFOC.2.1,hFOC.2.2.1,hFOC.2.2.2.1,hopt.2.2.2.2.1,he⟩

theorem eventual_positive_canonical_gap (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (e : E m) a,((G m e:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i)
    {vmin vmax : ℝ} (hmin : cutoff i/2< vmin) (hminmax : vmin≤ vmax)
    (hmax : vmax< entry i) :
    ∀ᶠ m in atTop,∀ e : E m,∀ v∈Icc vmin vmax,
      let b := chosen G g cm i vmin m e v
      let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
      let R := sourceCanonicalDuplicate i m (G m e) (g m e) (cm m e)
      Optimal C v b ∧ 0< one C v b ∧
        b∈Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)) ∧
        gapFactor i*one C v b< two (eta i) C R v b-one C v b := by
  filter_upwards [uniform_optimizer_fractional_gap G g cm i h05 hatom hfields hpsi hK
    hmin hminmax hmax (gapFactor i) (gapFactor_pos i)] with m hm e v hv
  have hs := hm e v hv
  have hr := (abs_lt.mp hs.2.2.2.2.2).1
  have hfrac : gapFactor i<
      (two (eta i) (sourceCanonicalMarginal i m (G m e) (g m e) (cm m e))
        (sourceCanonicalDuplicate i m (G m e) (g m e) (cm m e)) v
          (chosen G g cm i vmin m e v)-
        one (sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)) v
          (chosen G g cm i vmin m e v))/
      one (sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)) v
        (chosen G g cm i vmin m e v) := by
    unfold gapFactor at hr ⊢
    linarith
  exact ⟨hs.1,hs.2.2.2.1,hs.2.2.2.2.1,(lt_div_iff₀ hs.2.2.2.1).mp hfrac⟩

variable {Seed : Type*} [MeasurableSpace Seed]

theorem original_native_canonical_dominance_gap (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (e : E m) a,((G m e:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i)
    {vmin vmax : ℝ} (hmin : cutoff i/2< vmin) (hminmax : vmin≤ vmax)
    (hmax : vmax< entry i) :
    ∀ᶠ m in atTop,∀ e : E m,∀ v∈Icc vmin vmax,
      let b := chosen G g cm i vmin m e v
      let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
      CanonicalPureTransfer.budget i m (G m e) v+
        eta i*b*LiteralPureComponents.sourcePureDuplicate i m (G m e) b<
          gapFactor i*one C v b →
      ∀ Γ : FiniteGame m 2 (capacity m) Seed,∀ focal : Fin m,
        EntryNativeSource.CountTransport i (G m e:Measure (ℝ × ℝ)) (g m e) (cm m e) Γ focal →
        Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
          (by cases i <;> norm_num [eta,etaQ]) → Γ.g=0 →
        ∃ a : JointAction 2,a.routeCount=2 ∧
          a.bid∈Icc (LowChernoff.physicalFloor i v) (min v (ReceiptGap.cap i)) ∧
          0<(problem Γ focal).payoff v a ∧
          ∀ z : JointAction 2,z.routeCount≤1 →
            (problem Γ focal).payoff v z<
              (problem Γ focal).payoff v a := by
  filter_upwards [eventual_positive_canonical_gap G g cm i h05 hatom hfields hpsi hK
    hmin hminmax hmax,eventually_source_prefix G g cm i h05 hfields hpsi]
      with m hm hp e v hv
  dsimp only
  intro hbudget Γ focal hT hA hg
  have hs := hm e v hv
  have hvH : v≤ sortEnd i := by unfold sortEnd; have ht:=cutoff_pos i; linarith [hv.2]
  have hvcap : v≤ ReceiptGap.cap i := hv.2.trans
    (hmax.le.trans (ReceiptGap.entry_below_cap i).le)
  have hn := CanonicalNativeTransfer.original_native_full_menu_gap i m
    (G m e:Measure (ℝ × ℝ)) (g m e) (hp e).2.1 (cm m e) hvH hvcap
    hs.1 (hbudget.trans hs.2.2.2) Γ focal hT hA hg
  refine ⟨NativeLowRoute.twoAction (chosen G g cm i vmin m e v),rfl,?_,hn⟩
  simpa only [NativeLowRoute.twoAction,max_eq_left hs.1.1.1] using hs.2.2.1

end Family
end FCAppendix.Affine.Uniform06.SourceOptimizerGap
