/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.HamiltonianLowWickAnalytic
import PrimeFactorOscillations.Helpers.HamiltonianWickProfileOwnership

/-! # Exhaustive low-degree Wick profiles

The finite classification concerns every composition of total degree at
most six. It does not restrict the dimension or sample a vertex set.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

noncomputable section

namespace PrimeFactorOscillations

def wickTriplePairComposition : Composition 6 where
  blocks := [3, 3]
  blocks_pos := by
    intro i hi
    have hEq : i = 3 := by simpa using hi
    omega
  blocks_sum := by decide

theorem wickVertexProfiles_low_zero :
    wickVertexProfiles 0 0 = {Composition.ones 0} := by decide

theorem wickVertexProfiles_single (e : Nat) (he : 2 <= e) :
    wickVertexProfiles e 1 = {Composition.single (2 * e) (by omega)} := by
  apply Finset.ext
  intro d
  rw [wickVertexProfiles_mem, Finset.mem_singleton]
  constructor
  next =>
    intro h
    exact (Composition.eq_single_iff_length (by omega)).mpr h.1
  next =>
    intro h
    rw [h]
    refine And.intro (Composition.single_length _) ?_
    intro i
    rw [Composition.single_blocksFun]
    omega

theorem wickVertexProfiles_low_four :
    wickVertexProfiles 2 1 = {Composition.single 4 (by decide)} :=
  wickVertexProfiles_single 2 (by omega)

theorem wickVertexProfiles_low_six :
    wickVertexProfiles 3 1 = {Composition.single 6 (by decide)} :=
  wickVertexProfiles_single 3 (by omega)

theorem wickVertexProfiles_low_two_triples :
    wickVertexProfiles 3 2 = {wickTriplePairComposition} := by
  apply Finset.ext
  intro d
  rw [wickVertexProfiles_mem, Finset.mem_singleton]
  constructor
  next =>
    intro h
    have hDLength : d.length = 2 := h.1
    have hLength : d.blocks.length = 2 := h.1
    have hBlocks : d.blocks = [3, 3] := by
      cases hb : d.blocks with
      | nil => simp only [hb, List.length_nil] at hLength; omega
      | cons a xs =>
        cases hx : xs with
        | nil => simp only [hb, hx, List.length_cons, List.length_nil] at hLength; omega
        | cons b ys =>
          cases hy : ys with
          | nil =>
            have hList : d.blocks = [a, b] := by rw [hb, hx, hy]
            have hA : 3 <= a := by
              have hZero : 0 < d.length := by omega
              have h := h.2 (Fin.mk 0 hZero)
              simpa [Composition.blocksFun, hList] using h
            have hB : 3 <= b := by
              have hOne : 1 < d.length := by omega
              have h := h.2 (Fin.mk 1 hOne)
              simpa [Composition.blocksFun, hList] using h
            have hSum := d.blocks_sum
            rw [hList] at hSum
            simp only [List.sum_cons, List.sum_nil] at hSum
            have hAeq : a = 3 := by omega
            have hBeq : b = 3 := by omega
            simpa only [hAeq, hBeq] using hList
          | cons c zs =>
            have hLong : d.blocks.length = 3 + zs.length := by rw [hb, hx, hy]; simp; omega
            omega
    cases d with
    | mk blocks hPos hSum =>
      change blocks = [3, 3] at hBlocks
      cases hBlocks
      rfl
  next =>
    intro h
    rw [h]
    exact And.intro rfl (by decide)

theorem wickVertexProfiles_zero_vertices (e : Nat) (he : 0 < e) :
    wickVertexProfiles e 0 = EmptyCollection.emptyCollection := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hLength := ((wickVertexProfiles_mem e 0 d).mp hd).1
  have hZero := (Composition.length_eq_zero d).mp hLength
  omega

theorem gaussianWickDiagramCoefficient_zero_vertices
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota] [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (e : Nat) (he : 0 < e) :
    gaussianWickDiagramCoefficient z row e 0 = 0 := by
  unfold gaussianWickDiagramCoefficient
  rw [wickVertexProfiles_zero_vertices e he]
  simp only [Finset.sum_empty, Finset.sum_const_zero]

theorem wickSupportLabel_singleton {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (k : Fin ({i} : Finset J).card) :
    wickSupportLabel {i} k = i :=
  Finset.mem_singleton.mp (wickSupportLabel_mem {i} k)

theorem gaussianWickProfile_single
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota]
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (k : Nat) (hk : 0 < k) (label : Fin 1 -> J) :
    gaussianWickProfile z row (Composition.single k hk) label =
      wickVertexCoefficient k * gaussianLinearWickValue z
        (List.replicate k (row (label 0))) := by
  have hProd :
      Finset.prod Finset.univ
        (fun i : Fin (Composition.single k hk).length =>
          wickVertexCoefficient ((Composition.single k hk).blocksFun i)) =
        wickVertexCoefficient k := by
    simp_rw [Composition.single_blocksFun]
    change Finset.prod (Finset.univ : Finset (Fin 1)) (fun _ => wickVertexCoefficient k) = _
    simp
  have hList : wickProfileList (Composition.single k hk) label =
      List.replicate k (label 0) := by
    unfold wickProfileList
    simp_rw [Composition.single_blocksFun]
    change (List.ofFn (fun i : Fin 1 => List.replicate k (label i))).flatten = _
    simp [List.ofFn_succ]
  unfold gaussianWickProfile
  rw [hProd, hList, List.map_replicate]

theorem gaussianWickSupportProfile_single
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota] [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (e : Nat) (he : 0 < e) (i : J) :
    gaussianWickSupportProfile z row e {i} (Composition.single (2 * e) (by omega)) =
      wickVertexCoefficient (2 * e) *
        gaussianLinearWickValue z (List.replicate (2 * e) (row i)) := by
  have hLength : (Composition.single (2 * e) (by omega)).length = ({i} : Finset J).card := by
    rw [Composition.single_length, Finset.card_singleton]
  unfold gaussianWickSupportProfile
  rw [dif_pos hLength]
  have hLabel :
      (fun j : Fin 1 => wickSupportLabel ({i} : Finset J) (Fin.cast hLength j)) =
        (fun _ : Fin 1 => i) := by
    funext j
    exact wickSupportLabel_singleton i (Fin.cast hLength j)
  change gaussianWickProfile z row (Composition.single (2 * e) (by omega))
    (fun j : Fin 1 => wickSupportLabel ({i} : Finset J) (Fin.cast hLength j)) = _
  rw [hLabel]
  exact gaussianWickProfile_single z row (2 * e) (by omega) (fun _ => i)

theorem gaussianWickDiagramCoefficient_single
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota] [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex)
    (e : Nat) (he : 2 <= e) :
    gaussianWickDiagramCoefficient z row e 1 =
      wickVertexCoefficient (2 * e) * Finset.sum Finset.univ
        (fun i => gaussianLinearWickValue z (List.replicate (2 * e) (row i))) := by
  unfold gaussianWickDiagramCoefficient
  rw [wickVertexProfiles_single e he, Finset.powersetCard_one, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Finset.sum_singleton]
  simp_rw [gaussianWickSupportProfile_single z row e (by omega)]
  exact (Finset.mul_sum _ _ _).symm

theorem gaussianWickDiagramCoefficient_low_zero
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota] [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) :
    gaussianWickDiagramCoefficient z row 0 0 = 1 := by
  unfold gaussianWickDiagramCoefficient
  rw [Finset.powersetCard_zero, wickVertexProfiles_low_zero]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  unfold gaussianWickSupportProfile
  rw [dif_pos (show (Composition.ones 0).length = (EmptyCollection.emptyCollection : Finset J).card
    from rfl)]
  unfold gaussianWickProfile wickProfileList
  change 1 * gaussianLinearWickValue z [] = 1
  rw [gaussianLinearWickValue_nil, one_mul]

theorem gaussianWickLowValue_three_profiles
    {Iota J : Type*} [Fintype Iota] [DecidableEq Iota] [Fintype J] [DecidableEq J]
    (z : Iota -> Complex) (row : J -> Iota -> Complex) :
    gaussianWickLowValue z row = 1 +
      gaussianWickDiagramCoefficient z row 2 1 +
      gaussianWickDiagramCoefficient z row 3 1 +
      gaussianWickDiagramCoefficient z row 3 2 := by
  unfold gaussianWickLowValue
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [gaussianWickDiagramCoefficient_low_zero,
    gaussianWickDiagramCoefficient_zero_vertices z row 1 (by omega),
    gaussianWickDiagramCoefficient_zero_vertices z row 2 (by omega),
    gaussianWickDiagramCoefficient_zero_vertices z row 3 (by omega),
    gaussianWickDiagramCoefficient_zero_of_support z row 1 1 (by omega),
    gaussianWickDiagramCoefficient_zero_of_support z row 2 2 (by omega),
    gaussianWickDiagramCoefficient_zero_of_support z row 3 3 (by omega)]
  ring

end PrimeFactorOscillations
