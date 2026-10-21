import FCAppendix.Game.PosteriorBeliefs

noncomputable section
namespace FCAppendix.Affine.TaggedLocal
open MeasureTheory Game Set
open scoped BigOperators

def tag (d U : ℝ) : Option ℝ → Fin 4
  | none => 3
  | some b => if b≤d then 0 else if b≤U then 1 else 2

theorem measurable_tag (d U : ℝ) : Measurable (tag d U) := by
  intro S hS
  change MeasurableSet ((fun b : ℝ => if b≤d then (0:Fin 4) else if b≤U then 1 else 2) ⁻¹' S)
  exact (Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)) hS

def BidBoxes {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2) (d U : ℝ) : Prop :=
  ∀ i, (kind i=0 → (x.action i).bid≤d) ∧
    (kind i=1 → d<(x.action i).bid ∧ (x.action i).bid≤U) ∧
    (kind i=2 → U<(x.action i).bid)

def ClassRoutes {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2) : Prop :=
  (∀ i, kind i≠2 → x.recipients i=Finset.univ) ∧
  (∀ i, kind i=2 → (x.recipients i).card=1)

theorem tag_of_boxes {m : ℕ} {kind : Fin m → Fin 3} {x : Realization m 2}
    {d U : ℝ} (hdU : d≤U) (hb : BidBoxes kind x d U) (i : Fin m) :
    tag d U (some (x.action i).bid)=(kind i).castSucc := by
  rcases hk : kind i with ⟨k,hklt⟩
  interval_cases k
  · have hh := (hb i).1 (by simp [hk])
    simp [tag,hh]
  · obtain ⟨hlo,hhi⟩ := (hb i).2.1 (by simp [hk])
    simp [tag,not_le.mpr hlo,hhi]
  · have hh := (hb i).2.2 (by simp [hk])
    simp [tag,not_le.mpr (hdU.trans_lt hh),not_le.mpr hh]

def localCount {m : ℕ} (d U : ℝ) (L : LocalList m) (k : Fin 4) : ℕ :=
  ∑ i : Fin m, if tag d U (L i)=k then 1 else 0

theorem measurable_localCount {m : ℕ} (d U : ℝ) (k : Fin 4) :
    Measurable (fun L : LocalList m => localCount d U L k) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag d U).comp (measurable_pi_apply i)) measurable_const)
    measurable_const measurable_const

def lowList {m : ℕ} (d U : ℝ) (L : LocalList m) : LocalList m :=
  fun i => if tag d U (L i)=0 then L i else none

theorem measurable_lowList {m : ℕ} (d U : ℝ) :
    Measurable (lowList (m:=m) d U) := by
  apply measurable_pi_iff.mpr
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag d U).comp (measurable_pi_apply i)) measurable_const)
    (measurable_pi_apply i) measurable_const

def countKind {m : ℕ} (kind : Fin m → Fin 3) (k : Fin 3) : ℕ :=
  ∑ i : Fin m, if kind i=k then 1 else 0

def upperAt {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2) (j : Fin 2) : ℕ :=
  ∑ i : Fin m, if kind i=2 ∧ j∈x.recipients i then 1 else 0

private theorem singleton_two_indicator (S : Finset (Fin 2)) (hS : S.card=1) :
    (if (0:Fin 2)∈S then 1 else 0)+(if (1:Fin 2)∈S then 1 else 0)=(1:ℕ) := by
  classical
  obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hS
  fin_cases j <;> simp

theorem counts_partition {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hr : ClassRoutes kind x) :
    countKind kind 0+countKind kind 1+upperAt kind x 0+upperAt kind x 1=m := by
  classical
  have hterm (i : Fin m) :
      (if kind i=0 then 1 else 0)+(if kind i=1 then 1 else 0)+
      (if kind i=2 ∧ (0:Fin 2)∈x.recipients i then 1 else 0)+
      (if kind i=2 ∧ (1:Fin 2)∈x.recipients i then 1 else 0)=(1:ℕ) := by
    rcases hk : kind i with ⟨k,hklt⟩
    interval_cases k
    · simp
    · simp
    · have hh := singleton_two_indicator (x.recipients i) (hr.2 i (by simp [hk]))
      simpa [hk] using hh
  simp only [countKind,upperAt,←Finset.sum_add_distrib]
  simp_rw [hterm]
  simp

theorem local_counts_correct {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    {d U : ℝ} (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) (j : Fin 2) :
    localCount d U (observe x j) 0=countKind kind 0 ∧
    localCount d U (observe x j) 1=countKind kind 1 ∧
    localCount d U (observe x j) 2=upperAt kind x j := by
  classical
  have hs := tag_of_boxes hdU hb
  have hterm (i : Fin m) :
      (if tag d U (observe x j i)=0 then 1 else 0)=(if kind i=0 then 1 else 0) ∧
      (if tag d U (observe x j i)=1 then 1 else 0)=(if kind i=1 then 1 else 0) ∧
      (if tag d U (observe x j i)=2 then 1 else 0)=
        (if kind i=2 ∧ j∈x.recipients i then 1 else 0) := by
    rcases hk : kind i with ⟨k,hklt⟩
    interval_cases k
    · have hrec := hr.1 i (by simp [hk])
      simp [observe,hrec,hs,hk]
    · have hrec := hr.1 i (by simp [hk])
      simp [observe,hrec,hs,hk]
    · by_cases hj : j∈x.recipients i
      · simp [observe,hj,hs,hk]
      · simp [observe,hj,tag]
  exact ⟨Finset.sum_congr rfl (fun i _ => (hterm i).1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.2)⟩

theorem lowList_observe {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    {d U : ℝ} (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) (j : Fin 2) :
    lowList d U (observe x j)=fun i => if kind i=0 then some (x.action i).bid else none := by
  classical
  funext i
  have hs := tag_of_boxes hdU hb i
  rcases hk : kind i with ⟨k,hklt⟩
  interval_cases k
  · have hrec := hr.1 i (by simp [hk])
    simp [lowList,observe,hrec,hs,hk]
  · have hrec := hr.1 i (by simp [hk])
    simp [lowList,observe,hrec,hs,hk]
  · by_cases hj : j∈x.recipients i
    · simp [lowList,observe,hj,hs,hk]
    · simp [lowList,observe,hj,tag]

theorem reconstruct_other_upper {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    {d U : ℝ} (hdU : d≤U) (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) :
    upperAt kind x 1=m-localCount d U (observe x 0) 0-
      localCount d U (observe x 0) 1-localCount d U (observe x 0) 2 := by
  obtain ⟨hl,ha,hh⟩ := local_counts_correct kind x hdU hb hr 0
  rw [hl,ha,hh]
  have hp := counts_partition kind x hr
  omega

theorem reconstruct_other_residual {m : ℕ} (c : ℕ) (kind : Fin m → Fin 3)
    (x : Realization m 2) {d U : ℝ} (hdU : d≤U)
    (hb : BidBoxes kind x d U) (hr : ClassRoutes kind x) :
    min (countKind kind 0) (c-countKind kind 1-upperAt kind x 1)=
      min (localCount d U (observe x 0) 0)
        (c-localCount d U (observe x 0) 1-
          (m-localCount d U (observe x 0) 0-localCount d U (observe x 0) 1-
            localCount d U (observe x 0) 2)) := by
  obtain ⟨hl,ha,_hh⟩ := local_counts_correct kind x hdU hb hr 0
  rw [←reconstruct_other_upper kind x hdU hb hr,hl,ha]
end FCAppendix.Affine.TaggedLocal
