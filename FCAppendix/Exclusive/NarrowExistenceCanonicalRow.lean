import FCAppendix.Exclusive.CanonicalGame
import FCAppendix.Exclusive.SourceLowTypePayoff

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Finite

def canonicalAuxGame (m k c : ℕ) (hn : 2 ≤ k+1) (hc : 0 < c) :
    FiniteGame m (k+1) c unitInterval :=
  canonicalGame m (k+1) c hn hc (Measure.dirac (0:ℝ)) ∅ MeasurableSet.empty
    (fun _ => 1) measurable_const (Schedule.once (k+1)) (Schedule.once (k+1)) 0 (by norm_num)

theorem canonical_visible_equilibrium {m k c : ℕ} (hn : 2 ≤ k+1) (hc : 0 < c)
    (j : Fin (k+1)) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ExclusiveEquilibrium (k+1) c (visibleBid L)
      (visibleLottery L (canonicalLottery (k+1) hn c (listBids L))) := by
  let Γ := canonicalAuxGame m k c hn hc
  let B : PosteriorSystem Γ := canonicalPosterior hn hc (Measure.dirac (0:ℝ)) ∅ MeasurableSet.empty
    (fun _ => 1) measurable_const (Schedule.once (k+1)) (Schedule.once (k+1)) 0 (by norm_num)
  have hopt := canonicalGame_proposer_optimal (m := m) hn hc (Measure.dirac (0:ℝ)) ∅ MeasurableSet.empty
    (fun _ => 1) measurable_const (Schedule.once (k+1)) (Schedule.once (k+1)) 0 (by norm_num) j L hL
  have hcommon := canonicalPosterior_common (m := m) hn hc (Measure.dirac (0:ℝ)) ∅ MeasurableSet.empty
    (fun _ => 1) measurable_const (Schedule.once (k+1)) (Schedule.once (k+1)) 0 (by norm_num) j L hL
  have hsym : SymmetricAtList Γ L (canonicalLottery (k+1) hn c (listBids L)) := fun l =>
    canonicalGame_seedLottery hn hc (Measure.dirac (0:ℝ)) ∅ MeasurableSet.empty (fun _ => 1)
      measurable_const (Schedule.once (k+1)) (Schedule.once (k+1)) 0 (by norm_num) l L
  exact visible_exclusiveEquilibrium_of_posterior_ae Γ B j L hopt hcommon _ hsym

theorem canonical_focalMarginal_eq_corridor {m k c : ℕ}
    (P : Corridor (k+1) m c) (i : Fin m) (d : UserProfile m (k+1))
    (hd : GoodProfile P d) {b : ℝ} (hb : b ∈ Icc P.lower P.upper) :
    ExclusiveSource.focalMarginal (k+1) P.proposers c i b d =
      P.allocation (rivalCount i d) (rivalWeight i d) b := by
  classical
  let j : Fin (k+1) := ⟨0,by omega⟩
  let a : JointAction (k+1) := ⟨b,(P.lower_pos.trans_le hb.1).le,k+1,le_rfl⟩
  let x : ℝ × JointAction (k+1) := (0,a)
  let tau : Equiv.Perm (Fin (k+1)) := Equiv.refl _
  have hfeas : FeasibleObservedList j (focalList i b d) :=
    ⟨Function.update d i (x,tau), observe_update_eq_focalList P i d hd x rfl tau j⟩
  have hg := canonical_visible_equilibrium P.proposers P.capacity j (focalList i b d) hfeas
  have he := focalList_marginal (canonicalAuxGame m k c P.proposers P.capacity) P i d hd hb
    (canonicalLottery (k+1) P.proposers c (listBids (focalList i b d))) hg
  simpa only [canonicalLottery_marginal, ExclusiveSource.focalMarginal, canonicalListMarginal] using he

end FCAppendix.Bayes.ExclusiveConstruction
