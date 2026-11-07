/-
Copyright (c) 2026 Prime Factor Oscillations contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Factor Oscillations contributors
-/
import PrimeFactorOscillations.Helpers.ThresholdRadialCard

/-! # Distinct reflected points forced by three different radius values -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000

noncomputable section
namespace PrimeFactorOscillations

theorem finite_reflected_five_card {Iota : Type*} [DecidableEq Iota] (j : Iota -> Iota) (r : Iota -> Real)
    (u v w : Iota)
    (hRU : r (j u) = r u) (hRV : r (j v) = r v)
    (hUV : Not (r u = r v)) (hUW : Not (r u = r w)) (hVW : Not (r v = r w))
    (hPairU : Not (u = j u)) (hPairV : Not (v = j v)) :
    ({u, j u, v, j v, w} : Finset Iota).card = 5 := by
  classical
  have hSep : forall x z, Not (r x = r z) -> Not (x = z) :=
    fun _ _ hn heq => hn (congrArg r heq)
  have hUVp := hSep u v hUV
  have hUWp := hSep u w hUW
  have hVWp := hSep v w hVW
  have hUJV : Not (u = j v) := hSep u (j v) (by rw [hRV]; exact hUV)
  have hJUV : Not (j u = v) := hSep (j u) v (by rw [hRU]; exact hUV)
  have hJUJV : Not (j u = j v) := hSep (j u) (j v) (by rw [hRU, hRV]; exact hUV)
  have hJUW : Not (j u = w) := hSep (j u) w (by rw [hRU]; exact hUW)
  have hJVW : Not (j v = w) := hSep (j v) w (by rw [hRV]; exact hVW)
  simp [hPairU, hPairV, hUVp, hUWp, hVWp, hUJV, hJUV, hJUJV, hJUW, hJVW]

theorem finite_reflected_six_card {Iota : Type*} [DecidableEq Iota] (j : Iota -> Iota) (r : Iota -> Real)
    (u v w : Iota)
    (hRU : r (j u) = r u) (hRV : r (j v) = r v) (hRW : r (j w) = r w)
    (hUV : Not (r u = r v)) (hUW : Not (r u = r w)) (hVW : Not (r v = r w))
    (hPairU : Not (u = j u)) (hPairV : Not (v = j v)) (hPairW : Not (w = j w)) :
    (insert (j w) ({u, j u, v, j v, w} : Finset Iota)).card = 6 := by
  classical
  have hFive := finite_reflected_five_card j r u v w hRU hRV hUV hUW hVW hPairU hPairV
  have hSep : forall x z, Not (r x = r z) -> Not (x = z) :=
    fun _ _ hn heq => hn (congrArg r heq)
  have hWU : Not (j w = u) := hSep (j w) u (by rw [hRW]; exact (fun heq => hUW heq.symm))
  have hWJU : Not (j w = j u) := hSep (j w) (j u) (by rw [hRW, hRU]; exact (fun heq => hUW heq.symm))
  have hWV : Not (j w = v) := hSep (j w) v (by rw [hRW]; exact (fun heq => hVW heq.symm))
  have hWJV : Not (j w = j v) := hSep (j w) (j v) (by rw [hRW, hRV]; exact (fun heq => hVW heq.symm))
  have hWW : Not (j w = w) := fun heq => hPairW heq.symm
  have hNot : Not (Membership.mem ({u, j u, v, j v, w} : Finset Iota) (j w)) := by
    simp [hWU, hWJU, hWV, hWJV, hWW]
  rw [Finset.card_insert_of_notMem hNot, hFive]

end PrimeFactorOscillations
