/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Assembly.FiniteFieldNativeMaximalCapacity
import PrimeFactorOscillations.Definitions.NativePrimePairGreedy

/-!
# Persistent native greedy packings

The computable construction only inserts genuine positive prime pairs.
All previous choices persist, and both square rows remain separated.
The subsequent domination proof supplies the exact consumer of the
uniform maximal-capacity theorem.
-/

set_option autoImplicit false
set_option Elab.async false

namespace PrimeFactorOscillations.FiniteFieldIntegerSignature

/-- Native square compatibility is symmetric. -/
theorem nativePrimePairSquareCompatible_symm (a b : Prod Nat Nat)
    (h : nativePrimePairSquareCompatible a b) :
    nativePrimePairSquareCompatible b a := by
  unfold nativePrimePairSquareCompatible at *
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- A single greedy visit never removes a selected label. -/
theorem nativePrimePairGreedyInsert_contains (q : Nat) (M : Finset (Prod Nat Nat))
    (p : Nat) : M <= nativePrimePairGreedyInsert q M p := by
  unfold nativePrimePairGreedyInsert
  split
  . intro a ha
    exact Finset.mem_insert.mpr (Or.inr ha)
  . exact fun a ha => ha

/-- Scanning any lower-endpoint list never removes a selected label. -/
theorem nativePrimePairGreedyScan_contains (q : Nat) (ps : List Nat)
    (M : Finset (Prod Nat Nat)) : M <= nativePrimePairGreedyScan q ps M := by
  induction ps generalizing M with
  | nil => exact fun a ha => ha
  | cons p ps ih =>
    exact fun a ha => ih (nativePrimePairGreedyInsert q M p)
      (nativePrimePairGreedyInsert_contains q M p ha)

/-- New labels at one visit have exactly the current upper endpoint. -/
theorem nativePrimePairGreedyInsert_mem_cases (q : Nat) (M : Finset (Prod Nat Nat))
    (p : Nat) (a : Prod Nat Nat) (ha : Membership.mem (nativePrimePairGreedyInsert q M p) a) :
    Membership.mem M a \/ a.1 + a.2 = q := by
  unfold nativePrimePairGreedyInsert at ha
  split at ha
  . rename_i hGood
    rcases Finset.mem_insert.mp ha with he | hOld
    . subst a
      exact Or.inr (Nat.add_sub_of_le (Nat.le_of_lt hGood.2.2.1))
    . exact Or.inl hOld
  . exact Or.inl ha

/-- New labels over a whole scan still have exactly its upper endpoint. -/
theorem nativePrimePairGreedyScan_mem_cases (q : Nat) (ps : List Nat)
    (M : Finset (Prod Nat Nat)) (a : Prod Nat Nat)
    (ha : Membership.mem (nativePrimePairGreedyScan q ps M) a) :
    Membership.mem M a \/ a.1 + a.2 = q := by
  induction ps generalizing M with
  | nil => exact Or.inl ha
  | cons p ps ih =>
    rcases ih (nativePrimePairGreedyInsert q M p) ha with hOld | hUpper
    . exact nativePrimePairGreedyInsert_mem_cases q M p a hOld
    . exact Or.inr hUpper

/-- A single visit preserves actual prime-pair geometry at its height. -/
theorem nativePrimePairGreedyInsert_geometry (q : Nat) (M : Finset (Prod Nat Nat))
    (p : Nat)
    (hM : forall a : Prod Nat Nat, Membership.mem M a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.1 + a.2 <= q) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyInsert q M p) a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.1 + a.2 <= q := by
  intro a ha
  unfold nativePrimePairGreedyInsert at ha
  split at ha
  . rename_i hGood
    rcases Finset.mem_insert.mp ha with he | hOld
    . subst a
      have hs : p + (q - p) = q := Nat.add_sub_of_le (Nat.le_of_lt hGood.2.2.1)
      refine And.intro hGood.1 (And.intro ?_ (And.intro ?_ ?_))
      . change Nat.Prime (p + (q - p))
        rw [hs]
        exact hGood.2.1
      . exact Nat.sub_pos_of_lt hGood.2.2.1
      . exact le_of_eq hs
    . exact hM a hOld
  . exact hM a ha

/-- A complete scan preserves actual prime-pair geometry. -/
theorem nativePrimePairGreedyScan_geometry (q : Nat) (ps : List Nat)
    (M : Finset (Prod Nat Nat))
    (hM : forall a : Prod Nat Nat, Membership.mem M a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.1 + a.2 <= q) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyScan q ps M) a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.1 + a.2 <= q := by
  induction ps generalizing M with
  | nil => exact hM
  | cons p ps ih =>
    exact ih (nativePrimePairGreedyInsert q M p)
      (nativePrimePairGreedyInsert_geometry q M p hM)

/-- A single visit preserves complete square-row separation. -/
theorem nativePrimePairGreedyInsert_flat (q : Nat) (M : Finset (Prod Nat Nat))
    (p : Nat)
    (hM : forall a : Prod Nat Nat, Membership.mem M a ->
      forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
        nativePrimePairSquareCompatible a b) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyInsert q M p) a ->
      forall b : Prod Nat Nat, Membership.mem (nativePrimePairGreedyInsert q M p) b ->
        Not (a = b) -> nativePrimePairSquareCompatible a b := by
  unfold nativePrimePairGreedyInsert
  split
  . rename_i hGood
    intro a ha b hb hne
    rcases Finset.mem_insert.mp ha with haEq | haOld
    . subst a
      rcases Finset.mem_insert.mp hb with hbEq | hbOld
      . subst b
        exact False.elim (hne rfl)
      . exact hGood.2.2.2 b hbOld
    . rcases Finset.mem_insert.mp hb with hbEq | hbOld
      . subst b
        exact nativePrimePairSquareCompatible_symm _ _ (hGood.2.2.2 a haOld)
      . exact hM a haOld b hbOld hne
  . exact hM

/-- A complete scan preserves complete square-row separation. -/
theorem nativePrimePairGreedyScan_flat (q : Nat) (ps : List Nat)
    (M : Finset (Prod Nat Nat))
    (hM : forall a : Prod Nat Nat, Membership.mem M a ->
      forall b : Prod Nat Nat, Membership.mem M b -> Not (a = b) ->
        nativePrimePairSquareCompatible a b) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyScan q ps M) a ->
      forall b : Prod Nat Nat, Membership.mem (nativePrimePairGreedyScan q ps M) b ->
        Not (a = b) -> nativePrimePairSquareCompatible a b := by
  induction ps generalizing M with
  | nil => exact hM
  | cons p ps ih =>
    exact ih (nativePrimePairGreedyInsert q M p) (nativePrimePairGreedyInsert_flat q M p hM)

/-- Every finite prefix consists of actual positive prime pairs below
its declared natural height. -/
theorem nativePrimePairGreedyPrefix_geometry (Y : Nat) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyPrefix Y) a ->
      Nat.Prime a.1 /\ Nat.Prime (a.1 + a.2) /\ 0 < a.2 /\ a.1 + a.2 <= Y := by
  induction Y with
  | zero =>
    intro a ha
    simp [nativePrimePairGreedyPrefix] at ha
  | succ Y ih =>
    apply nativePrimePairGreedyScan_geometry
    intro a ha
    have hh := ih a ha
    refine And.intro hh.1 (And.intro hh.2.1 (And.intro hh.2.2.1 ?_))
    have hUpper : a.1 + a.2 <= Y := hh.2.2.2
    omega

/-- Every finite prefix keeps both complete square rows separated. -/
theorem nativePrimePairGreedyPrefix_flat (Y : Nat) :
    forall a : Prod Nat Nat, Membership.mem (nativePrimePairGreedyPrefix Y) a ->
      forall b : Prod Nat Nat, Membership.mem (nativePrimePairGreedyPrefix Y) b ->
        Not (a = b) -> nativePrimePairSquareCompatible a b := by
  induction Y with
  | zero =>
    intro a ha
    simp [nativePrimePairGreedyPrefix] at ha
  | succ Y ih => exact nativePrimePairGreedyScan_flat _ _ _ ih

/-- The next height extends the entire preceding selection. -/
theorem nativePrimePairGreedyPrefix_subset_succ (Y : Nat) :
    nativePrimePairGreedyPrefix Y <= nativePrimePairGreedyPrefix (Y + 1) :=
  nativePrimePairGreedyScan_contains _ _ _

/-- The choices persist across arbitrary increasing natural heights. -/
theorem nativePrimePairGreedyPrefix_mono (Y Z : Nat) (hYZ : Y <= Z) :
    nativePrimePairGreedyPrefix Y <= nativePrimePairGreedyPrefix Z := by
  induction Z generalizing Y with
  | zero =>
    have hY : Y = 0 := by omega
    subst Y
    exact fun a ha => ha
  | succ Z ih =>
    by_cases he : Y = Z + 1
    . subst Y
      exact fun a ha => ha
    . have hY : Y <= Z := by omega
      exact fun a ha => nativePrimePairGreedyPrefix_subset_succ Z (ih Y hY ha)


/-- At its birth visit an eligible prime pair is retained or blocked by
one of the selected labels, with both square rows kept in the alternative. -/
theorem nativePrimePairGreedyInsert_birth (q : Nat) (M : Finset (Prod Nat Nat))
    (p : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) :
    Membership.mem (nativePrimePairGreedyInsert q M p) (p, q - p) \/
      exists g : Prod Nat Nat, Membership.mem (nativePrimePairGreedyInsert q M p) g /\
        Or (IsSquare (((q - p) * p) * (g.2 * g.1)))
          (IsSquare (((q - p) * (p + (q - p))) * (g.2 * (g.1 + g.2)))) := by
  classical
  by_cases hAll : forall g : Prod Nat Nat, Membership.mem M g ->
      nativePrimePairSquareCompatible (p, q - p) g
  . apply Or.inl
    have hGood := And.intro hp (And.intro hq (And.intro hpq hAll))
    rw [nativePrimePairGreedyInsert, ite_eq_left hGood]
    exact Finset.mem_insert_self _ _
  . apply Or.inr
    have hBlock : exists g : Prod Nat Nat, Membership.mem M g /\
        Or (IsSquare (((q - p) * p) * (g.2 * g.1)))
          (IsSquare (((q - p) * (p + (q - p))) * (g.2 * (g.1 + g.2)))) := by
      by_contra hNo
      apply hAll
      intro g hg
      refine And.intro ?_ ?_
      . intro hs
        exact hNo (Exists.intro g (And.intro hg (Or.inl hs)))
      . intro hs
        exact hNo (Exists.intro g (And.intro hg (Or.inr hs)))
    choose g hg hRows using hBlock
    exact Exists.intro g
      (And.intro (nativePrimePairGreedyInsert_contains q M p hg) hRows)

/-- A pair whose lower endpoint is visited is retained or permanently
blocked by the end of the complete scan. -/
theorem nativePrimePairGreedyScan_birth (q : Nat) (ps : List Nat)
    (M : Finset (Prod Nat Nat)) (p : Nat) (hMem : Membership.mem ps p)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q) :
    Membership.mem (nativePrimePairGreedyScan q ps M) (p, q - p) \/
      exists g : Prod Nat Nat, Membership.mem (nativePrimePairGreedyScan q ps M) g /\
        Or (IsSquare (((q - p) * p) * (g.2 * g.1)))
          (IsSquare (((q - p) * (p + (q - p))) * (g.2 * (g.1 + g.2)))) := by
  induction ps generalizing M with
  | nil => simp at hMem
  | cons r ps ih =>
    have hCases : p = r \/ Membership.mem ps p := List.mem_cons.mp hMem
    rcases hCases with he | hTail
    . subst r
      have hBirth := nativePrimePairGreedyInsert_birth q M p hp hq hpq
      rcases hBirth with hKept | hBlocked
      . exact Or.inl (nativePrimePairGreedyScan_contains q ps
          (nativePrimePairGreedyInsert q M p) hKept)
      . choose g hg hRows using hBlocked
        exact Or.inr (Exists.intro g (And.intro
          (nativePrimePairGreedyScan_contains q ps (nativePrimePairGreedyInsert q M p) hg)
          hRows))
    . exact ih (nativePrimePairGreedyInsert q M r) hTail

/-- Every actual prime pair below the height is retained or has a
retained blocker. This is the complete support, including long gaps. -/
theorem nativePrimePairGreedyPrefix_retained_or_blocked (Y : Nat) :
    forall a : Prod Nat Nat, Membership.mem (nativeFullPrimePairGapSet Y) a ->
      Membership.mem (nativePrimePairGreedyPrefix Y) a \/
        exists g : Prod Nat Nat, Membership.mem (nativePrimePairGreedyPrefix Y) g /\
          Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
            (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2)))) := by
  induction Y with
  | zero =>
    intro a ha
    have hInfo := (mem_nativeFullPrimePairGapSet_iff 0 a.1 a.2).mp ha
    have hPos : 0 < a.1 := hInfo.1.pos
    have hUpper : a.1 + a.2 <= 0 := hInfo.2.2.2
    omega
  | succ Y ih =>
    intro a ha
    have hInfo := (mem_nativeFullPrimePairGapSet_iff (Y + 1) a.1 a.2).mp ha
    have hUpper : a.1 + a.2 <= Y + 1 := hInfo.2.2.2
    by_cases hPrev : a.1 + a.2 <= Y
    . have hOld : Membership.mem (nativeFullPrimePairGapSet Y) a :=
        (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mpr
          (And.intro hInfo.1 (And.intro hInfo.2.1 (And.intro hInfo.2.2.1 hPrev)))
      rcases ih a hOld with hKept | hBlocked
      . exact Or.inl (nativePrimePairGreedyPrefix_subset_succ Y hKept)
      . choose g hg hRows using hBlocked
        exact Or.inr (Exists.intro g
          (And.intro (nativePrimePairGreedyPrefix_subset_succ Y hg) hRows))
    . have hEq : a.1 + a.2 = Y + 1 := by omega
      have hGap : 0 < a.2 := hInfo.2.2.1
      have hpq : a.1 < Y + 1 := by omega
      have hq : Nat.Prime (Y + 1) := by
        rw [<- hEq]
        exact hInfo.2.1
      have hVisit : Membership.mem (List.range (Y + 1)) a.1 := List.mem_range.mpr hpq
      have hBirth := nativePrimePairGreedyScan_birth (Y + 1) (List.range (Y + 1))
        (nativePrimePairGreedyPrefix Y) a.1 hVisit hInfo.1 hq hpq
      have hGapEq : Y + 1 - a.1 = a.2 := by omega
      have hEta : Prod.mk a.1 a.2 = a := Prod.ext rfl rfl
      simpa only [hGapEq, hEta, nativePrimePairGreedyPrefix] using hBirth

/-- Every omitted actual label has a retained square-row blocker. -/
theorem nativePrimePairGreedyPrefix_dominates (Y : Nat)
    (a : Prod Nat Nat) (ha : Membership.mem (nativeFullPrimePairGapSet Y) a)
    (hNot : Not (Membership.mem (nativePrimePairGreedyPrefix Y) a)) :
    exists g : Prod Nat Nat, Membership.mem (nativePrimePairGreedyPrefix Y) g /\
      Or (IsSquare ((a.2 * a.1) * (g.2 * g.1)))
        (IsSquare ((a.2 * (a.1 + a.2)) * (g.2 * (g.1 + g.2)))) := by
  rcases nativePrimePairGreedyPrefix_retained_or_blocked Y a ha with hKept | hBlocked
  . exact False.elim (hNot hKept)
  . exact hBlocked

/-- A selected label was already present at its own exact birth height. -/
theorem nativePrimePairGreedyPrefix_mem_at_birth (Y : Nat) (a : Prod Nat Nat)
    (ha : Membership.mem (nativePrimePairGreedyPrefix Y) a) :
    Membership.mem (nativePrimePairGreedyPrefix (a.1 + a.2)) a := by
  induction Y with
  | zero => simp [nativePrimePairGreedyPrefix] at ha
  | succ Y ih =>
    have hCases := nativePrimePairGreedyScan_mem_cases (Y + 1) (List.range (Y + 1))
      (nativePrimePairGreedyPrefix Y) a ha
    rcases hCases with hOld | hUpper
    . exact ih hOld
    . rw [hUpper]
      exact ha

/-- Every prefix is exactly the restriction of one decidable global
family to the actual full prime-pair support at that height. -/
theorem nativePrimePairGreedyPrefix_mem_iff (Y : Nat) (a : Prod Nat Nat) :
    Membership.mem (nativePrimePairGreedyPrefix Y) a <->
      Membership.mem nativePrimePairGreedyClass a /\
        Membership.mem (nativeFullPrimePairGapSet Y) a := by
  apply Iff.intro
  . intro ha
    refine And.intro (nativePrimePairGreedyPrefix_mem_at_birth Y a ha) ?_
    exact (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mpr
      (nativePrimePairGreedyPrefix_geometry Y a ha)
  . intro ha
    have hBirth : Membership.mem (nativePrimePairGreedyPrefix (a.1 + a.2)) a := ha.1
    have hHeight : a.1 + a.2 <= Y :=
      ((mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mp ha.2).2.2.2
    exact nativePrimePairGreedyPrefix_mono (a.1 + a.2) Y hHeight hBirth

/-- The complete greedy prefix has the native agreement rate three
eighths for every pair of distinct selected actual labels. -/
theorem nativePrimePairGreedyPrefix_agreement (Y : Nat)
    (a : Prod Nat Nat) (ha : Membership.mem (nativePrimePairGreedyPrefix Y) a)
    (b : Prod Nat Nat) (hb : Membership.mem (nativePrimePairGreedyPrefix Y) b)
    (hne : Not (a = b)) :
    nativeAgreementRate a.1 a.2 b.1 b.2 = 3 / 8 := by
  have ga := nativePrimePairGreedyPrefix_geometry Y a ha
  have gb := nativePrimePairGreedyPrefix_geometry Y b hb
  have hPair : Not (And (a.1 = b.1) (a.2 = b.2)) := by
    intro he
    exact hne (Prod.ext he.1 he.2)
  have hFlat := nativePrimePairGreedyPrefix_flat Y a ha b hb hne
  unfold nativePrimePairSquareCompatible at hFlat
  apply (native_agreement_arithmetic_classification
    a.1 a.2 b.1 b.2 ga.1 ga.2.1 gb.1 gb.2.1 ga.2.2.1 gb.2.2.1 hPair).2.mpr
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hFlat


/-- Every complete greedy prefix is insertion-maximal among flat
families on the exact full actual prime-pair support. -/
theorem nativePrimePairGreedyPrefix_maximal (Y : Nat)
    (a : Prod Nat Nat) (ha : Membership.mem (nativeFullPrimePairGapSet Y) a)
    (hInsert : forall u : Prod Nat Nat,
      Membership.mem (insert a (nativePrimePairGreedyPrefix Y)) u ->
      forall v : Prod Nat Nat, Membership.mem (insert a (nativePrimePairGreedyPrefix Y)) v ->
        Not (u = v) -> nativeAgreementRate u.1 u.2 v.1 v.2 = 3 / 8) :
    Membership.mem (nativePrimePairGreedyPrefix Y) a := by
  classical
  by_contra hNot
  choose g hg hCollision using nativePrimePairGreedyPrefix_dominates Y a ha hNot
  have ga := (mem_nativeFullPrimePairGapSet_iff Y a.1 a.2).mp ha
  have gg := nativePrimePairGreedyPrefix_geometry Y g hg
  have hne : Not (a = g) := by
    intro he
    apply hNot
    rw [he]
    exact hg
  have hPair : Not (And (a.1 = g.1) (a.2 = g.2)) := by
    intro he
    exact hne (Prod.ext he.1 he.2)
  have hRate := hInsert a (Finset.mem_insert_self _ _) g
    (Finset.mem_insert.mpr (Or.inr hg)) hne
  have hRows := (native_agreement_arithmetic_classification
    a.1 a.2 g.1 g.2 ga.1 ga.2.1 gg.1 gg.2.1 ga.2.2.1 gg.2.2.1 hPair).2.mp hRate
  rcases hCollision with hs | hs
  . apply hRows.1
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs
  . apply hRows.2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hs

end PrimeFactorOscillations.FiniteFieldIntegerSignature
