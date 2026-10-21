import FCAppendix.Affine.Uniform07Finishing.Native.ForcedFocalSeed
import FCAppendix.Affine.Uniform07Finishing.Native.SeedValueInvariance

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open FCAppendix.Affine StrictNative
variable {m : ℕ} [Nonempty (Fin m)]

lemma sourceDrawTag_eq_zero_iff (zs U : ℝ) (u : UserDraw 2) :
    sourceDrawTag zs U u = 0 ↔ u.1.2.bid ≤ zs := by
  by_cases hs : u.1.2.bid ≤ zs <;> by_cases hu : u.1.2.bid ≤ U <;>
    simp [sourceDrawTag,hs,hu]

omit [Nonempty (Fin m)] in

lemma observedContext_seed_equivalent {zs R : ℝ} (hzR : zs < R) (j : Fin 2)
    (L L' : LocalList m)
    (h : ∀ u, L u = L' u ∨ ∃ b b' : ℝ,
      L u = some b ∧ L' u = some b' ∧ b ≤ zs ∧ b' ≤ zs) :
    Weighted.SeedEquivalentContext zs (observedContext R j L) (observedContext R j L') := by
  have htag : ∀ u, StrictTags.tag R R (L u) = StrictTags.tag R R (L' u) := by
    intro u
    rcases h u with he | ⟨b,b',hb,hb',hs,hs'⟩
    · rw [he]
    · simp only [hb,hb',StrictTags.tag,if_pos (hs.trans_lt hzR),if_pos (hs'.trans_lt hzR)]
  have hcount (k : Fin 4) : StrictTags.localCount R R L k = StrictTags.localCount R R L' k := by
    unfold StrictTags.localCount
    simp_rw [htag]
  refine ⟨?_,fun u => ?_⟩
  · simp only [observedContext,hcount]
  · rcases h u with he | ⟨b,b',hb,hb',hs,hs'⟩
    · left
      change broadcastPart R L u = broadcastPart R L' u
      simp only [broadcastPart,StrictTags.lowList,he]
    · right
      refine ⟨b,b',?_,?_,hs,hs'⟩ <;>
        simp only [observedContext,broadcastPart,StrictTags.lowList,hb,hb',StrictTags.tag,
          if_pos (hs.trans_lt hzR),if_pos (hs'.trans_lt hzR),if_true]

def sourceSeedDefaultDraw : UserDraw 2 :=
  ((0,⟨0,le_rfl,2,le_rfl⟩),Equiv.refl (Fin 2))

def restoreNonseedRivals (i : Fin m) (k : RivalIndex i → Fin 3)
    (d : {u : RivalIndex i // k u ≠ 0} → UserDraw 2) : RivalIndex i → UserDraw 2 :=
  fun u => if hu : k u = 0 then sourceSeedDefaultDraw else d ⟨u,hu⟩

omit [Nonempty (Fin m)] in
lemma measurable_restoreNonseedRivals (i : Fin m) (k : RivalIndex i → Fin 3) :
    Measurable (restoreNonseedRivals i k) := by
  apply measurable_pi_lambda
  intro u
  by_cases hu : k u = 0
  · simpa only [restoreNonseedRivals,dif_pos hu] using
      (measurable_const : Measurable (fun _ : {u : RivalIndex i // k u ≠ 0} → UserDraw 2 =>
        sourceSeedDefaultDraw))
  · simpa only [restoreNonseedRivals,dif_neg hu] using
      (measurable_pi_apply (⟨u,hu⟩ : {u : RivalIndex i // k u ≠ 0}))

def erasedFocalContext (R : ℝ) (i : Fin m) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (k : RivalIndex i → Fin 3)
    (d : {u : RivalIndex i // k u ≠ 0} → UserDraw 2) : ClassifiedContext m :=
  observedContext R j (focalLocalList i a τ j (restoreNonseedRivals i k d))

omit [Nonempty (Fin m)] in
lemma measurable_erasedFocalContext (R : ℝ) (i : Fin m) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2) (k : RivalIndex i → Fin 3) :
    Measurable (erasedFocalContext R i a τ j k) :=
  (measurable_observedContext R j).comp
    ((measurable_focalLocalList i a τ j).comp (measurable_restoreNonseedRivals i k))

omit [Nonempty (Fin m)] in

theorem erasedFocalContext_seed_equivalent (i : Fin m) {zs U R : ℝ}
    (hz0 : 0 ≤ zs) (hzR : zs < R) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (d : RivalIndex i → UserDraw 2) (k : RivalIndex i → Fin 3)
    (hcat : ∀ u, sourceDrawTag zs U (d u) = k u)
    (hroute : ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2) :
    Weighted.SeedEquivalentContext zs
      (observedContext R j (focalLocalList i a τ j d))
      (erasedFocalContext R i a τ j k (fun u => d u)) := by
  apply observedContext_seed_equivalent hzR j
  intro u
  by_cases hui : u = i
  · subst u
    left
    simp [focalLocalList,observe,drawsRealization,insertFocalProfile]
  · let r : RivalIndex i := ⟨u,hui⟩
    by_cases hr : k r = 0
    · have hb : (d r).1.2.bid ≤ zs := (sourceDrawTag_eq_zero_iff zs U (d r)).mp
        ((hcat r).trans hr)
      have hk := hroute r hb
      right
      refine ⟨(d r).1.2.bid,0,?_,?_,hb,hz0⟩
      · simp [focalLocalList,observe,drawsRealization,insertFocalProfile,hui,r,hk,firstK_full_two]
      · simp [focalLocalList,observe,drawsRealization,insertFocalProfile,hui,r,
          restoreNonseedRivals,hr,sourceSeedDefaultDraw,firstK_full_two]
    · left
      simp [focalLocalList,observe,drawsRealization,insertFocalProfile,hui,r,
        restoreNonseedRivals,hr]

theorem sourcePlan_erased_focal_factorization
    (i : Fin m) {zs ξ Λ a r U d₀ z t width ε R : ℝ}
    (hz0 : 0 ≤ zs) (hzR : zs < R) (hr : 0 < r) (ha : 0 ≤ a)
    (hzΛ : zs ≤ Λ-a) (hzz : zs ≤ z) (hzU : zs ≤ U) (c : ℕ) (μB : Measure ℝ)
    (A : JointAction 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2)
    (d : RivalIndex i → UserDraw 2) (k : RivalIndex i → Fin 3)
    (hcat : ∀ u, sourceDrawTag zs U (d u) = k u)
    (hroute : ∀ u, (d u).1.2.bid ≤ zs → (d u).1.2.routeCount = 2) :
    Weighted.sourcePlan ξ Λ r U zs c μB
      (Weighted.sourceGuardAlpha ξ Λ a r U d₀ z t width ε c)
      (observedContext R j (focalLocalList i A τ j d)) =
    Weighted.sourcePlanFromSeed ξ Λ r U c
      (Weighted.sourceGuardAlpha ξ Λ a r U d₀ z t width ε c)
      (erasedFocalContext R i A τ j k (fun u => d u))
      (Weighted.sourceSeed μB zs (observedContext R j (focalLocalList i A τ j d))) := by
  rw [Weighted.sourcePlan_eq_fromSeed]
  exact Weighted.seedEquivalent_sourcePlanFromSeed
    (erasedFocalContext_seed_equivalent i hz0 hzR A τ j d k hcat hroute)
    hr ha hzΛ hzz hzU c _

end FCAppendix.Affine.Uniform07Finishing
