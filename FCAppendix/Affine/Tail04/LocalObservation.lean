import FCAppendix.Affine.Tail04.ObservableRoles
import FCAppendix.Affine.TaggedLocalInformation

noncomputable section
namespace FCAppendix.Affine.Tail04.Observable
open MeasureTheory Set Game Classical
open FCAppendix.Affine.Hybrid
open scoped BigOperators
namespace Regions
variable (E : Regions)

def localTag : Option ℝ → Fin 4
  | none => 3
  | some b => if b ≤ E.d then 0 else if b ∈ E.privateBids then 2 else 1

lemma measurable_localTag : Measurable E.localTag := by
  intro S hS
  change MeasurableSet
    ((fun b : ℝ => if b ≤ E.d then (0 : Fin 4)
      else if b ∈ E.privateBids then 2 else 1) ⁻¹' S)
  exact (Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite E.measurableSet_privateBids measurable_const measurable_const)) hS

def RoleSupport {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2) : Prop :=
  ∀ i, (kind i = 0 → (x.action i).bid ≤ E.d) ∧
    (kind i = 1 → E.d < (x.action i).bid ∧ (x.action i).bid ∉ E.privateBids) ∧
    (kind i = 2 → (x.action i).bid ∈ E.privateBids)

lemma localTag_of_support {m : ℕ} {kind : Fin m → Fin 3} {x : Realization m 2}
    (hb : E.RoleSupport kind x) (i : Fin m) :
    E.localTag (some (x.action i).bid) = (kind i).castSucc := by
  rcases hk : kind i with ⟨k, hklt⟩
  interval_cases k
  · have hh := (hb i).1 (by simp [hk])
    simp [localTag, hh]
  · obtain ⟨hl, hp⟩ := (hb i).2.1 (by simp [hk])
    simp [localTag, not_le.mpr hl, hp]
  · have hp := (hb i).2.2 (by simp [hk])
    simp [localTag, not_le.mpr (E.private_above_low hp), hp]

def localCount {m : ℕ} (L : LocalList m) (k : Fin 4) : ℕ :=
  ∑ i : Fin m, if E.localTag (L i) = k then 1 else 0

lemma measurable_localCount {m : ℕ} (k : Fin 4) :
    Measurable (fun L : LocalList m => E.localCount L k) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun (E.measurable_localTag.comp (measurable_pi_apply i)) measurable_const)
    measurable_const measurable_const

def roleList {m : ℕ} (k : Fin 4) (L : LocalList m) : LocalList m :=
  fun i => if E.localTag (L i) = k then L i else none

lemma measurable_roleList {m : ℕ} (k : Fin 4) :
    Measurable (E.roleList (m := m) k) := by
  apply measurable_pi_iff.mpr
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun (E.measurable_localTag.comp (measurable_pi_apply i)) measurable_const)
    (measurable_pi_apply i) measurable_const

theorem local_counts {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x) (j : Fin 2) :
    E.localCount (observe x j) 0 = TaggedLocal.countKind kind 0 ∧
    E.localCount (observe x j) 1 = TaggedLocal.countKind kind 1 ∧
    E.localCount (observe x j) 2 = TaggedLocal.upperAt kind x j := by
  have hs := E.localTag_of_support hb
  have hterm (i : Fin m) :
      (if E.localTag (observe x j i) = 0 then 1 else 0) =
        (if kind i = 0 then 1 else 0) ∧
      (if E.localTag (observe x j i) = 1 then 1 else 0) =
        (if kind i = 1 then 1 else 0) ∧
      (if E.localTag (observe x j i) = 2 then 1 else 0) =
        (if kind i = 2 ∧ j ∈ x.recipients i then 1 else 0) := by
    rcases hk : kind i with ⟨k, hklt⟩
    interval_cases k
    · have hrec := hr.1 i (by simp [hk])
      simp [observe, hrec, hs, hk]
    · have hrec := hr.1 i (by simp [hk])
      simp [observe, hrec, hs, hk]
    · by_cases hj : j ∈ x.recipients i
      · simp [observe, hj, hs, hk]
      · simp [observe, hj, localTag]
  exact ⟨Finset.sum_congr rfl (fun i _ => (hterm i).1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.2)⟩

theorem common_roleList {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x)
    (k : Fin 4) (hk : k = 0 ∨ k = 1) (j : Fin 2) :
    E.roleList k (observe x j) =
      fun i => if (kind i).castSucc = k then some (x.action i).bid else none := by
  funext i
  have hs := E.localTag_of_support hb i
  rcases hkind : kind i with ⟨ki, hki⟩
  interval_cases ki
  · have hrec := hr.1 i (by simp [hkind])
    simp [roleList, observe, hrec, hs, hkind]
  · have hrec := hr.1 i (by simp [hkind])
    simp [roleList, observe, hrec, hs, hkind]
  · rcases hk with rfl | rfl
    · by_cases hj : j ∈ x.recipients i <;>
        simp [roleList, observe, hj, hs, hkind]
    · by_cases hj : j ∈ x.recipients i <;>
        simp [roleList, observe, hj, hs, hkind]

def otherPrivateCount {m : ℕ} (L : LocalList m) : ℕ :=
  m - E.localCount L 0 - E.localCount L 1 - E.localCount L 2

lemma measurable_otherPrivateCount {m : ℕ} :
    Measurable (E.otherPrivateCount (m := m)) := by
  exact ((measurable_const.sub (E.measurable_localCount 0)).sub
    (E.measurable_localCount 1)).sub (E.measurable_localCount 2)

theorem otherPrivateCount_zero {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x) :
    E.otherPrivateCount (observe x 0) = TaggedLocal.upperAt kind x 1 := by
  obtain ⟨hl, ha, hp⟩ := E.local_counts kind x hb hr 0
  unfold otherPrivateCount
  rw [hl, ha, hp]
  have h := TaggedLocal.counts_partition kind x hr
  omega

theorem otherPrivateCount_one {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x) :
    E.otherPrivateCount (observe x 1) = TaggedLocal.upperAt kind x 0 := by
  obtain ⟨hl, ha, hp⟩ := E.local_counts kind x hb hr 1
  unfold otherPrivateCount
  rw [hl, ha, hp]
  have h := TaggedLocal.counts_partition kind x hr
  omega

abbrev CommonContext (m : ℕ) := (LocalList m × LocalList m) × (ℕ × ℕ)

def context {m : ℕ} (j : Fin 2) (L : LocalList m) : CommonContext m :=
  ((E.roleList 0 L, E.roleList 1 L),
    if j = 0 then (E.localCount L 2, E.otherPrivateCount L)
    else (E.otherPrivateCount L, E.localCount L 2))

lemma measurable_context {m : ℕ} (j : Fin 2) : Measurable (E.context (m := m) j) := by
  unfold context
  split_ifs
  · exact ((E.measurable_roleList 0).prodMk (E.measurable_roleList 1)).prodMk
      ((E.measurable_localCount 2).prodMk E.measurable_otherPrivateCount)
  · exact ((E.measurable_roleList 0).prodMk (E.measurable_roleList 1)).prodMk
      (E.measurable_otherPrivateCount.prodMk (E.measurable_localCount 2))

theorem context_common {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2)
    (hb : E.RoleSupport kind x) (hr : TaggedLocal.ClassRoutes kind x) :
    E.context 0 (observe x 0) = E.context 1 (observe x 1) := by
  have hlo := E.common_roleList kind x hb hr 0 (Or.inl rfl)
  have hac := E.common_roleList kind x hb hr 1 (Or.inr rfl)
  obtain ⟨_, _, hh0⟩ := E.local_counts kind x hb hr 0
  obtain ⟨_, _, hh1⟩ := E.local_counts kind x hb hr 1
  simp only [context, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  rw [hlo 0, hlo 1, hac 0, hac 1, hh0, hh1,
    E.otherPrivateCount_zero kind x hb hr, E.otherPrivateCount_one kind x hb hr]

def someHighListSlack {m : ℕ} (c : ℕ) (C : CommonContext m) : Prop :=
  (∑ i : Fin m, if C.1.2 i = none then 0 else 1) + min C.2.1 C.2.2 < c

end Regions
end FCAppendix.Affine.Tail04.Observable
